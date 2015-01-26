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
import Idris.IdrisDoc (extract)
import Idris.GuardedRecursion.Helpers

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
import Control.Monad.State.Lazy as LState (evalStateT)
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower, isAlpha)
import Data.List.Split (splitOn)

--import Util.Pretty(pretty, text)

type Cons = (Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, PTerm, FC, [Name])

elabCorecord :: ElabInfo -> SyntaxInfo -> SyntaxInfo -> Docstring (Either Err PTerm) -> [(Name, Docstring (Either Err PTerm))] -> FC -> DataOpts -> PCorecord' PTerm -> Idris ()
elabCorecord info syn rsyn doc argDocs fc opts (PCorecorddecl tyn tyc projs cons)
    = do let (pNas, pTys) = unzip (map (\ (_, _, n, t, _, _) -> (n, t)) projs)
         -- Save state before building data for elaboration.
         i <- getIState 
         -- Add temp type to env for recursive refs
         undef <- isUndefined fc tyn
         (cty, _, _, _) <- buildType info syn fc [] tyn tyc
         when undef $ updateContext (addTyDecl tyn (TCon 0 0) cty)
         -- Split all projections into their first explicit argument (the type which the projection is on)
         -- and the rest. E.g. Foo : Bar -> Baz -> Qux splits to (Bar , (Baz -> Qux))
         pnt <- mapM splitProj (zip pNas pTys)
         let (cs, pTys') = unzip pnt
         -- Are all projections applications where the first argument is of the same family as the type being defined?
         mapM_ checkProj (zip pNas cs)
         -- Are all projections applications on types that are conv equivalent
         let x = (zip pNas cs)
         (_, ty) <- foldM pConvEq (head x) (tail x)
         -- Uniform the type parameters in projections
         names <- namesIn (head cs)
         tnames <- mapM namesIn (tail cs)
         let rnames = map (((nub names) \\) . nub) tnames
         let pTys'' = zipWith ($) (map replaceNames rnames) (tail pTys')
         let uTys = zipWith ($) (map (uniform (head cs)) (tail cs)) pTys''
         let pNaTys = zip pNas (head pTys' : uTys)
         -- Make constructor
         dataCons <- case cons of 
                       Just (doc, argDocs, fc, name, args, pPli) ->
                         (do orderedCons <- orderConsArgs args pNaTys tyn
                             let consType = cType orderedCons pPli ty
                             return [(doc, argDocs, name, consType, fc, [])])
                       Nothing -> (do let consType = cType pNaTys [] ty
                                      name <- if isOp tyn then (do n <- generateConsName
                                                                   iputStrLn $ show fc ++ ":Warning - generated constructor " ++ show n ++ " for type " ++ show tyn ++ "."
                                                                   return n)
                                                          else return (sUN ("Mk" ++ (show $ nsroot tyn)))
                                      return [(emptyDocstring, [], expandNS syn name, consType, fc, [])])
         -- Elaborate constructed data.
         elabData info rsyn doc argDocs fc (Codata : opts) (PDatadecl tyn tyc dataCons)
         -- Make projection and update functions.
         let (cn, cty_in) = (\(_,_,n,t,_,_) -> (n, t)) (head dataCons)
         mkProjAndUpdate info rsyn fc tyn cn cty_in
         -- Build guarded recursive projections.
         -- As the guarded recursive definitions are never run we use postulates.
         ctxt <- getContext
         let cty' = normalise ctxt [] cty
         -- Check if we can build a guarded recursive definition of this type
         when (guardableTC cty')
               -- Get the guarded name. This should already exist from the elaborationg of the codata
           (do gn <- getGuardedName tyn
               -- Create guarded names for projections
               mapM_ guardedNameCtxt pNas
               -- Guard the projection types
               let gpTys = map (guardedPTerm tyn) pTys'
               gpTys' <- mapM (guardNamesIn tyn) gpTys
               -- Prefix projection type with guarded recursive reference
               gty <- guardNamesIn tyn ty
               let gtf = map (prePi gty) gpTys'
               -- Elaborate guarded projections as postulates
               mapM_ elabGuardedPostulate (zip pNas gtf))
  where
    prePi c t = PPi (Exp [] Dynamic False) (sMN 0 "__pi_arg") c t

    namesIn :: PTerm -> Idris [Name]
    namesIn t = filterM f (extract t)
      where
        f :: Name -> Idris Bool
        f n = do i <- getIState
                 case lookupNames n (tt_ctxt i) of
                   [] -> return True
                   _ -> return False
                   
      
    
    replaceNames :: [Name] -> PTerm -> PTerm
    replaceNames ns = mapPT (rn ns)
      where
        rn :: [Name] -> PTerm -> PTerm
        rn ns (PRef fc n)
          | True <- (n `elem` ns) = rn ns (PRef fc (nextName n))
          | otherwise = PRef fc n
        rn _ t = t
    -- Replace old with new
    uniform :: PTerm -> PTerm -> PTerm -> PTerm
    uniform new old = mapPT (replace new old)
      where
        -- Replace i with r if i is m
        replace :: PTerm -> PTerm -> PTerm -> PTerm
        replace r m i
          | m == i = r
          | otherwise = i
    
    pConvEq :: (Name, PTerm) -> (Name, PTerm) -> Idris (Name, PTerm)
    pConvEq (n, t) (n', t') = do (ty , _, _, _) <- buildType info rsyn fc [] n  t
                                 (ty', _, _, _) <- buildType info rsyn fc [] n' t'
                                 i <- getIState
                                 let ctxt = tt_ctxt i
                                 let ucs  = map fst (idris_constraints i)
                                 case LState.evalStateT (convEq ctxt [] ty ty') (0, ucs) of
                                   (OK True) -> return (n, t)
                                   _ -> case LState.evalStateT (convEq ctxt [] (finalise (normalise ctxt [] ty)) (finalise (normalise ctxt [] ty'))) (0, ucs) of
                                                 (OK True) -> return (n, t)
                                                 _ -> tclift $ tfail (At fc (Elaborating "corecord projection " n' (CantConvert
                                                                                                                     (finalise (normalise ctxt [] ty ))
                                                                                                                     (finalise (normalise ctxt [] ty')) (errEnv []))))

      
    generateConsName :: Idris Name
    generateConsName = gen $ sUN "Mk_Infix_Record0"
      where
        gen :: Name -> Idris Name
        gen n = do i <- getIState
                   case lookupTyNameExact (expandNS syn n) (tt_ctxt i) of
                     Just _  -> gen (nextName n)
                     Nothing -> return n
    -- 
    isOp :: Name -> Bool
    isOp (UN t) = foldr (||) False (map (\x -> x `elem` opChars) (str t))
    isOp (NS n _) = isOp n
    isOp _ = True
    -- Checks the first non-type parameter to be of the same name
    tyIs :: Name -> Type -> Idris ()
    tyIs con (Bind _ _ b) = tyIs con b -- Unbind until we get the last parameter
    tyIs con t | (P _ n' _, _) <- unApply t
        = do when (n' /= tyn) (tclift $ tfail (At fc (Elaborating "corecord projection " con (Msg (show n' ++ " is not " ++ show tyn)))))
             return ()
    tyIs con t = tclift $ tfail (At fc (Elaborating "corecord projection " con (Msg (show t ++ " is not " ++ show tyn))))
    -- Checks that's a projection is of the right type
    checkProj :: (Name, PTerm) -> Idris ()
    checkProj (n, t) = (do (cty, _, _, _) <- buildType info syn fc [] n t
                           i <- getIState
                           tyIs n (normalise (tt_ctxt i) [] cty))
    -- Uniforms projection type variables
    uniformProjs :: [Name] -> [PTerm] -> [PTerm]
    uniformProjs _ = id
    -- Splits a term at the first explicit
    splitProj :: (Name, PTerm) -> Idris (PTerm, PTerm)
    splitProj (_, (PPi (Exp _ _ _) n t t')) = return (t, mapPT (rmRefs n) t')
      where
        -- Removes applications of a refs to the name in the term
        rmRefs :: Name -> PTerm -> PTerm
        rmRefs n (PApp fc t' args) = 
          let args' = filter (\x -> getTm x /= (PRef emptyFC n)) args
          in PApp fc (mapPT (rmRefs n) t') args'
        rmRefs n t = t
        
    splitProj (n, (PPi p@(Imp _ _ _ _) n' t t')) = do (rt, t'') <- splitProj (n, t')
                                                      return (rt, (PPi p n' t t''))
    splitProj (n, _) = tclift $ tfail (At fc (Elaborating "corecord projection " tyn (Msg ("Projection " ++ show n ++ " is not a valid projection."))))
      
    -- Orders second argument accordingly to first argument
    orderConsArgs :: [Name] -> [(Name, PTerm)] -> Name -> Idris [(Name, PTerm)]
    orderConsArgs [] ys _ = return ys
    orderConsArgs xs ys t = orderConsArgs' xs ys t
      where 
        orderConsArgs' :: [Name] -> [(Name, PTerm)] -> Name -> Idris [(Name, PTerm)]
        orderConsArgs' (x : xs) ys tyn = case lookup x ys of
                                               Just t -> (return ((x, t) :)) <*> (orderConsArgs' xs (delete (x, t) ys) tyn)
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
         let projNames = map (expandNS syn) (map fst ptys)
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
         -- mapM_ (tryElabSetter info) update_decls
  where
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
                        (\v -> do iputStrLn $ show fc ++
                                      ":Warning - can't generate setter for " ++
                                      show fn ++ " (" ++ show ty ++ ")"
                                     --  ++ "\n" ++ pshow i v
                                  putIState i)

    getBoundImpls (PPi (Imp _ _ _ _) n ty sc) = (n, ty) : getBoundImpls sc
    getBoundImpls _ = []

    getImplB k (PPi (Imp l s _ _) n Placeholder sc)
        = getImplB k sc
    getImplB k (PPi (Imp l s p fa) n ty sc)
        = getImplB (\x -> k (PPi (Imp l s p fa) n ty x)) sc
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
             return [pfnTy, PClauses fc [CausalFn] pn [pclause]]

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

