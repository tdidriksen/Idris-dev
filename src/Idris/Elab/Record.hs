{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Record(elabRecord, elabCorecord) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.ElabTerm
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn)
import IRTS.Lang
import Idris.ParseHelpers (opChars)

import Idris.Elab.Type
import Idris.Elab.Data
import Idris.Elab.Utils

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings

import Prelude hiding (id, (.))
import Control.Category

import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower, isAlpha)
import Data.List.Split (splitOn)

--import Util.Pretty(pretty, text)

elabCorecord :: ElabInfo -> SyntaxInfo -> SyntaxInfo -> Docstring (Either Err PTerm) -> [(Name, (Docstring (Either Err PTerm)))] -> FC -> DataOpts -> (PCorecord' PTerm) -> Idris ()
elabCorecord info syn rsyn doc argDocs fc opts (PCorecorddecl tyn tyc projs cons)
    = do let (pNas, pTys) = unzip (map (\ (_, _, n, t, _, _) -> (n, t)) projs)
         -- Save state before building data for elaboration.
         -- As this is only desugaring, any effect on the state should be reverted before further elaboration.
         preState <- getIState 
         -- Add temp type to env for recursive refs
         undef <- isUndefined fc tyn
         (cty, _, _, _) <- buildType info rsyn fc [] tyn tyc
         when undef $ updateContext (addTyDecl tyn (TCon 0 0) cty)
         -- Split all projections into their first explicit argument (the type which the projection is one)
         -- and the rest. I.e. Foo : Bar -> Baz -> Qux splits to (Bar , (Baz -> Qux))
         let (cs, pTys') = unzip $ map splitProj pTys
         -- Are all projections applications where the first argument is of the same family as the type being defined?
         mapM checkProj (zip pNas cs)
         -- Uniform the type parameters in projections
         let pNaTys = zip pNas (uniformProjs [] pTys') -- FIXME
         -- Get constructor result type FIXME: Do this right
         let ty = head cs
         -- Make constructor
         dataCons <- case cons of 
                       Just((doc, argDocs, fc, name, args, pPli)) ->
                         (do orderedCons <- orderConsArgs args pNaTys tyn
                             let consType = cType orderedCons pPli ty
                             return [(doc, argDocs, name, consType, fc, args)])
                       Nothing -> (do let consType = cType pNaTys [] ty
                                      let name = expandNS syn $ sUN ("Mk" ++ (show $ nsroot tyn))
                                      if isOp name then iputStrLn $ show fc ++ ":Warning - can't generate constructor for type " ++ show tyn ++ " because it contains operator characters."
                                                   else return ()
                                      return [(emptyDocstring, [], name, consType, fc, [])])
         -- Revert to old state from before building data for elaboration.
         putIState preState
         -- Elaborate constructed data.
         elabData info rsyn doc argDocs fc (Codata : opts) (PDatadecl tyn tyc dataCons)
         -- Get constructor name and type.
         let (cn, cty_in) = (\ (_, _, n, t, _, _) -> (n, t)) (head dataCons) -- Only one constructor exists.
       
         i <- getIState
         cty <- case lookupTy cn (tt_ctxt i) of
                    [t] -> return t
         -- Are the all the first arguments to the projections alpha equiv?
         mapM (\x -> (checkAlphaEq x cty)) (zip pNas cs) -- FIXME: Should be conv eq?
         --- Make projection and update functions.
         mkProjAndUpdate info rsyn fc tyn cn cty_in
  where
    isOp :: Name -> Bool
    isOp (UN t) = foldr (||) False (map (\x -> x `elem` opChars) (str t))
    isOp (NS n _) = isOp n
    isOp _ = True
    -- Checks the first non-type parameter to be of the same name
    tyIs :: Name -> Type -> Idris ()
    tyIs con (Bind _ _ b) = tyIs con b -- Unbind until we get the last parameter
    tyIs con t | (P _ n' _, _) <- unApply t
        = if n' /= tyn
            then tclift $ tfail (At fc (Elaborating "corecord projection " con (Msg (show n' ++ " is not " ++ show tyn))))
            else return ()
    tyIs con t = tclift $ tfail (At fc (Elaborating "corecord projection " con (Msg (show t ++ " is not " ++ show tyn))))
    -- Checks that's a projection is of the right type
    checkProj :: (Name, PTerm) -> Idris ()
    checkProj (n, t) = (do (cty, _, _, _) <- buildType info syn fc [] n t
                           tyIs n cty)
    -- Checks alpha euivalence between two terms
    checkAlphaEq :: (Name, PTerm) -> Type -> Idris ()
    checkAlphaEq (n, t) ct = return ()
    -- Uniforms projection type variables
    uniformProjs :: [Name] -> [PTerm] -> [PTerm]
    uniformProjs _ = id
    -- Splits a term at the first explicit
    splitProj :: PTerm -> (PTerm, PTerm)
    splitProj (PPi (Exp _ _ _) n t t') = (t, mapPT (rmRefs n) t')
      where
        -- Removes applications of a refs to the name in the term
        rmRefs :: Name -> PTerm -> PTerm
        rmRefs n (PApp fc t' args) = 
          let args' = filter (\x -> getTm x /= (PRef emptyFC n)) args
          in PApp fc (mapPT (rmRefs n) t') args'
        rmRefs n t = t
        
    splitProj (PPi p@(Imp _ _ _) n t t') = let (rt, t'') = splitProj t'
                                             in (rt, (PPi p n t t''))
      
    -- Orders second argument accordingly to first argument
    orderConsArgs :: [Name] -> [(Name, PTerm)] -> Name -> Idris [(Name, PTerm)]
    orderConsArgs [] ys _ = return ys
    orderConsArgs xs ys t = orderConsArgs' xs ys t
      where 
        orderConsArgs' :: [Name] -> [(Name, PTerm)] -> Name -> Idris [(Name, PTerm)]
        orderConsArgs' (x : xs) ys tyn = case lookup x ys of
                                               Just(t) -> (return ((x, t) :)) <*> (orderConsArgs' xs (delete (x, t) ys) tyn)
                                               Nothing -> tclift $ tfail (At fc (Elaborating "record constructor " tyn (Msg (show x ++ " is not in " ++ show tyn))))
        orderConsArgs' [] [] _  = return []
        orderConsArgs' _ _ tyn = tclift $ tfail (At fc (Elaborating "record constructor " tyn (Msg ("Arguments do not match projections in " ++ show tyn)))) -- FIXME: Better error msg
    -- Constructs a constructorr type from a list of projections
    cType :: [(Name, PTerm)] -> [Plicity] -> PTerm -> PTerm
    cType (x : xs) (p : ps) t = PPi p (nsroot (fst x)) (snd x) (cType xs ps t)
    cType (x : xs) [] t = PPi (Exp [] Dynamic False) (nsroot (fst x)) (snd x) (cType xs [] t)
    cType [] _ t = t

elabRecord :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm) -> FC -> Name ->
              PTerm -> DataOpts -> Docstring (Either Err PTerm) -> Name -> PTerm -> Idris ()
elabRecord info syn doc fc tyn ty opts cdoc cn cty_in
    = do elabData info syn doc [] fc opts (PDatadecl tyn ty [(cdoc, [], cn, cty_in, fc, [])])
         mkProjAndUpdate info syn fc tyn cn cty_in

mkProjAndUpdate :: ElabInfo -> SyntaxInfo -> FC -> Name ->
                   Name -> PTerm -> Idris ()
mkProjAndUpdate info syn fc tyn cn cty_in
    = do cty' <- implicit info syn cn cty_in
         i <- getIState

         -- get bound implicits and propagate to setters (in case they
         -- provide useful information for inference)
         let extraImpls = getBoundImpls cty'
         cty <- case lookupTy cn (tt_ctxt i) of
                    [t] -> return (delab i t)
                    _ -> ifail "Something went inexplicably wrong"
         cimp <- case lookupCtxt cn (idris_implicits i) of
                    [imps] -> return imps
         ppos <- case lookupCtxt tyn (idris_datatypes i) of         
                    [ti] -> return $ param_pos ti
         let cty_imp = renameBs cimp cty
         let ptys = getProjs [] cty_imp
         let ptys_u = getProjs [] cty
         let recty = getRecTy cty_imp
         let recty_u = getRecTy cty

         let paramNames = getPNames recty ppos

         -- rename indices when we generate the getter/setter types, so
         -- that they don't clash with the names of the projections
         -- we're generating
         let index_names_in = getRecNameMap "_in" ppos recty
         let recty_in = substMatches index_names_in recty

         logLvl 3 $ show (recty, recty_u, ppos, paramNames, ptys)
         -- Substitute indices with projection functions, and parameters with
         -- the updated parameter name
         let substs = map (\ (n, _) -> 
                             if n `elem` paramNames
                                then (n, PRef fc (mkp n))
                                else (n, PApp fc (PRef fc n)
                                                [pexp (PRef fc rec)])) 
                          ptys 

         -- Generate projection functions
         proj_decls <- mapM (mkProj recty_in substs cimp) (zip ptys [0..])
         logLvl 3 $ show proj_decls
         let nonImp = mapMaybe isNonImp (zip cimp ptys_u)
         let implBinds = getImplB id cty'

         -- Register projections as available left-hand side projections
         let projNames = map (expandNS syn) (map fst ptys_u)
         logLvl 1 $ "projNames: " ++ intercalate ", " (map show projNames)
         -- let projInfo = zip projNames [0..]
         let projTypes = map head proj_decls
         logLvl 1 $ "projTypes: " ++ intercalate ", " (map show projTypes)
         let projInfo = zip4 projTypes projNames (repeat tyn) (repeat cn)
         let insertProjsIn m = foldr (\(t,n,tyn,cn) -> \m' -> addDef n (t,n,tyn,cn) m') m projInfo
         putIState (i { lhs_projections = insertProjsIn (lhs_projections i) })

         -- Generate update functions
         update_decls <- mapM (mkUpdate recty_u index_names_in extraImpls
                                   (getFieldNames cty')
                                   implBinds (length nonImp)) (zip nonImp [0..])
         mapM_ (rec_elabDecl info EAll info) (concat proj_decls)
         logLvl 3 $ show update_decls
--         logLvl 0 $ "update_decls: "
--         mapM_ (logLvl 0) (map show update_decls)
         mapM_ (tryElabSetter info) (update_decls)
  where
    getBoundImpls (PPi (Imp _ _ _) n ty sc) = (n, ty) : getBoundImpls sc
    getBoundImpls _ = []


    isNonImp (PExp _ _ _ _, a) = Just a
    isNonImp _ = Nothing

    getPNames (PApp _ _ as) ppos = getpn as ppos
      where
        getpn as [] = []
        getpn as (i:is) | length as > i,
                          PRef _ n <- getTm (as!!i) = n : getpn as is
                        | otherwise = getpn as is
    getPNames _ _ = []


    tryElabGetter info ((PImp _ _ _ _ _), (fn, ty, val))
        = do i<- getIState
             idrisCatch (do rec_elabDecl info EAll info ty
                            rec_elabDecl info EAll info val)
                        (\v -> do iputStrLn $ show fc ++
                                     ":Warning - can't generate getter for implicit " ++
                                     show fn ++ " (" ++ show ty ++ ")"
                                     ++ "\n" ++ pshow i v
                                  putIState i)
    tryElabGetter info (_, (_, ty, val))
        = do rec_elabDecl info EAll info ty
             rec_elabDecl info EAll info val
    
    tryElabSetter info (fn, ty, val)
        = do i <- getIState
             idrisCatch (do rec_elabDecl info EAll info ty
                            rec_elabDecl info EAll info val)
                        (\v -> --do iputStrLn $ show fc ++
                               --       ":Warning - can't generate setter for " ++
                               --       show fn ++ " (" ++ show ty ++ ")"
                               --      --  ++ "\n" ++ pshow i v
                                  putIState i)

    getImplB k (PPi (Imp l s _) n Placeholder sc)
        = getImplB k sc
    getImplB k (PPi (Imp l s p) n ty sc)
        = getImplB (\x -> k (PPi (Imp l s p) n ty x)) sc
    getImplB k (PPi _ n ty sc)
        = getImplB k sc
    getImplB k _ = k

    renameBs (PImp _ _ _ _ _ : ps) (PPi p n ty s)
        = PPi p (mkImp n) ty (renameBs ps (substMatch n (PRef fc (mkImp n)) s))
    renameBs (_:ps) (PPi p n ty s) = PPi p n ty (renameBs ps s)
    renameBs _ t = t

    getProjs acc (PPi _ n ty s) = getProjs ((n, ty) : acc) s
    getProjs acc r = reverse acc

    getFieldNames (PPi (Exp _ _ _) n _ s) = n : getFieldNames s 
    getFieldNames (PPi _ _ _ s) = getFieldNames s
    getFieldNames _ = []

    getRecTy (PPi _ n ty s) = getRecTy s
    getRecTy t = t

    -- make sure we pick a consistent name for parameters; any name will do
    -- otherwise
    getRecNameMap x ppos (PApp fc t args) 
         = mapMaybe toMN (zip [0..] (map getTm args))
      where
        toMN (i, PRef fc n) 
             | i `elem` ppos = Just (n, PRef fc (mkp n))
             | otherwise = Just (n, PRef fc (sMN 0 (show n ++ x)))
        toMN _ = Nothing
    getRecNameMap x _ _ = []

    rec = sMN 0 "rec"

    -- only UNs propagate properly as parameters (bit of a hack then...)
    mkp (UN n) = sUN ("_p_" ++ str n)
    mkp (MN i n) = sMN i ("p_" ++ str n)
    mkp (NS n s) = NS (mkp n) s

    mkImp (UN n) = sUN ("implicit_" ++ str n)
    mkImp (MN i n) = sMN i ("implicit_" ++ str n)
    mkImp (NS n s) = NS (mkImp n) s

    mkType (UN n) = sUN ("set_" ++ str n)
    mkType (MN i n) = sMN i ("set_" ++ str n)
    mkType (NS n s) = NS (mkType n) s

    mkProj recty substs cimp ((pn_in, pty), pos)
        = do let pn = expandNS syn pn_in -- projection name
             -- use pn_in in the indices, consistently, to avoid clash
             let pfnTy = PTy emptyDocstring [] defaultSyntax fc [] pn
                            (PPi expl rec recty
                               (substMatches substs pty))
             let pls = repeat Placeholder
             let before = pos
             let after = length substs - (pos + 1)
             let args = take before pls ++ PRef fc (mkp pn_in) : take after pls
             let iargs = map implicitise (zip cimp args)
             let lhs = PApp fc (PRef fc pn)
                        [pexp (PApp fc (PRef fc cn) iargs)]
             let rhs = PRef fc (mkp pn_in)
             let pclause = PClause fc pn lhs [] rhs []
             return [pfnTy, PClauses fc [] pn [pclause]]

    implicitise (pa, t) = pa { getTm = t }

    -- If the 'pty' we're updating includes anything in 'substs', we're
    -- updating the type as well, so use recty', otherwise just use
    -- recty
    mkUpdate recty inames extras fnames k num ((pn, pty), pos)
       = do let setname = expandNS syn $ mkType pn
            let valname = sMN 0 "updateval"
            let pn_out = sMN 0 (show pn ++ "_out")
            let pn_in = sMN 0 (show pn ++ "_in")
            let recty_in = substMatches [(pn, PRef fc pn_in)] recty
            let recty_out = substMatches [(pn, PRef fc pn_out)] recty
            let pt = substMatches inames $ 
                       k (implBindUp extras inames (PPi expl pn_out pty
                           (PPi expl rec recty_in recty_out)))
            let pfnTy = PTy emptyDocstring [] defaultSyntax fc [] setname pt
--             let pls = map (\x -> PRef fc (sMN x ("field" ++ show x))) [0..num-1]
            let inames_imp = map (\ (x,_) -> (x, Placeholder)) inames
            let pls = map (\x -> substMatches inames_imp (PRef fc x)) fnames
            let lhsArgs = pls
            let rhsArgs = take pos pls ++ (PRef fc valname) :
                               drop (pos + 1) pls
            let before = pos
            let pclause = PClause fc setname (PApp fc (PRef fc setname)
                                              [pexp (PRef fc valname),
                                               pexp (PApp fc (PRef fc cn)
                                                        (map pexp lhsArgs))])
                                             []
                                             (PApp fc (PRef fc cn)
                                                      (map pexp rhsArgs)) []
            return (pn, pfnTy, PClauses fc [] setname [pclause])

    implBindUp [] is t = t
    implBindUp ((n, ty):ns) is t 
         = let n' = case lookup n is of
                         Just (PRef _ x) -> x
                         _ -> n in
               if n `elem` allNamesIn t 
                  then PPi impl n' ty (implBindUp ns is t)
                  else implBindUp ns is t

