{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.ElabDecls where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Directives
import Idris.Imports
import Idris.Elab.Term
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn, sendHighlighting)
import IRTS.Lang

import Idris.Elab.Utils
import Idris.Elab.Type
import Idris.Elab.Clause
import Idris.Elab.Data
import Idris.Elab.Record
import Idris.Elab.Class
import Idris.Elab.Instance
import Idris.Elab.Provider
import Idris.Elab.RunElab
import Idris.Elab.Transform
import Idris.Elab.Value

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings hiding (Unchecked)

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
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)


-- Top level elaborator info, supporting recursive elaboration
recinfo :: ElabInfo
recinfo = EInfo [] emptyContext id Nothing Nothing elabDecl'

-- | Return the elaborated term which calls 'main'
elabMain :: Idris Term
elabMain = do (m, _) <- elabVal recinfo ERHS
                           (PApp fc (PRef fc [] (sUN "run__IO"))
                                [pexp $ PRef fc [] (sNS (sUN "main") ["Main"])])
              return m
  where fc = fileFC "toplevel"

-- | Elaborate primitives
elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl' EAll recinfo)
                     (map (\(opt, decl, docs, argdocs) -> PData docs argdocs defaultSyntax (fileFC "builtin") opt decl)
                        (zip4
                         [inferOpts,      eqOpts]
                         [inferDecl,      eqDecl]
                         [emptyDocstring, eqDoc]
                         [[],             eqParamDoc]))
               addNameHint eqTy (sUN "prf")
               mapM_ elabPrim primitives
               -- Special case prim__believe_me because it doesn't work on just constants
               elabBelieveMe
               -- Finally, syntactic equality
               elabSynEq
    where elabPrim :: Prim -> Idris ()
          elabPrim (Prim n ty i def sc tot)
              = do updateContext (addOperator n ty i (valuePrim def))
                   setTotality n tot
                   i <- getIState
                   putIState i { idris_scprims = (n, sc) : idris_scprims i }

          valuePrim :: ([Const] -> Maybe Const) -> [Value] -> Maybe Value
          valuePrim prim vals = fmap VConstant (mapM getConst vals >>= prim)

          getConst (VConstant c) = Just c
          getConst _             = Nothing


          p_believeMe [_,_,x] = Just x
          p_believeMe _ = Nothing
          believeTy = Bind (sUN "a") (Pi Nothing (TType (UVar (-2))) (TType (UVar (-1))))
                       (Bind (sUN "b") (Pi Nothing (TType (UVar (-2))) (TType (UVar (-1))))
                         (Bind (sUN "x") (Pi Nothing (V 1) (TType (UVar (-1)))) (V 1)))
          elabBelieveMe
             = do let prim__believe_me = sUN "prim__believe_me"
                  updateContext (addOperator prim__believe_me believeTy 3 p_believeMe)
                  setTotality prim__believe_me (Partial NotCovering)
                  i <- getIState
                  putIState i {
                      idris_scprims = (prim__believe_me, (3, LNoOp)) : idris_scprims i
                    }

          p_synEq [t,_,x,y]
               | x == y = Just (VApp (VApp vnJust VErased)
                                (VApp (VApp vnRefl t) x))
               | otherwise = Just (VApp vnNothing VErased)
          p_synEq args = Nothing

          nMaybe = P (TCon 0 2) (sNS (sUN "Maybe") ["Maybe", "Prelude"]) Erased
          vnJust = VP (DCon 1 2 False) (sNS (sUN "Just") ["Maybe", "Prelude"]) VErased
          vnNothing = VP (DCon 0 1 False) (sNS (sUN "Nothing") ["Maybe", "Prelude"]) VErased
          vnRefl = VP (DCon 0 2 False) eqCon VErased

          synEqTy = Bind (sUN "a") (Pi Nothing (TType (UVar (-3))) (TType (UVar (-2))))
                     (Bind (sUN "b") (Pi Nothing (TType (UVar (-3))) (TType (UVar (-2))))
                      (Bind (sUN "x") (Pi Nothing (V 1) (TType (UVar (-2))))
                       (Bind (sUN "y") (Pi Nothing (V 1) (TType (UVar (-2))))
                         (mkApp nMaybe [mkApp (P (TCon 0 4) eqTy Erased)
                                               [V 3, V 2, V 1, V 0]]))))
          elabSynEq
             = do let synEq = sUN "prim__syntactic_eq"

                  updateContext (addOperator synEq synEqTy 4 p_synEq)
                  setTotality synEq (Total [])
                  i <- getIState
                  putIState i {
                     idris_scprims = (synEq, (4, LNoOp)) : idris_scprims i
                    }


elabDecls :: ElabInfo -> [PDecl] -> Idris ()
elabDecls info ds = do mapM_ (elabDecl EAll info) ds

elabDecl :: ElabWhat -> ElabInfo -> PDecl -> Idris ()
elabDecl what info d
    = let info' = info { rec_elabDecl = elabDecl' } in
          idrisCatch (withErrorReflection $ elabDecl' what info' d) (setAndReport)

elabDecl' _ info (PFix _ _ _)
     = return () -- nothing to elaborate
elabDecl' _ info (PSyntax _ p)
     = return () -- nothing to elaborate
elabDecl' what info (PTy doc argdocs s f o n nfc ty)
  | what /= EDefns
    = do logLvl 1 $ "Elaborating type decl " ++ show n ++ show o
         elabType info s doc argdocs f o n nfc ty
         return ()
elabDecl' what info (PPostulate b doc s f nfc o n ty)
  | what /= EDefns
    = do logLvl 1 $ "Elaborating postulate " ++ show n ++ show o
         if b 
            then elabExtern info s doc f nfc o n ty
            else elabPostulate info s doc f nfc o n ty
elabDecl' what info (PData doc argDocs s f co d)
  | what /= ETypes
    = do logLvl 1 $ "Elaborating " ++ show (d_name d)
         elabData info s doc argDocs f co d
  | otherwise
    = do logLvl 1 $ "Elaborating [type of] " ++ show (d_name d)
         elabData info s doc argDocs f co (PLaterdecl (d_name d) (d_name_fc d) (d_tcon d))
elabDecl' what info d@(PClauses f o n ps)
  | what /= ETypes
    = do logLvl 1 $ "Elaborating clause " ++ show n
         i <- getIState -- get the type options too
         let o' = case lookupCtxt n (idris_flags i) of
                    [fs] -> fs
                    [] -> []
         elabClauses info f (o ++ o') n ps
elabDecl' what info (PMutual f ps)
    = do case ps of
              [p] -> elabDecl what info p
              _ -> do mapM_ (elabDecl ETypes info) ps
                      mapM_ (elabDecl EDefns info) ps
         -- record mutually defined data definitions
         let datans = concatMap declared (filter isDataDecl ps)
         mapM_ (setMutData datans) datans
         logLvl 1 $ "Rechecking for positivity " ++ show datans
         mapM_ (\x -> do setTotality x Unchecked) datans
         -- Do totality checking after entire mutual block
         i <- get
         mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                         ctxt' <- do ctxt <- getContext
                                     tclift $ simplifyCasedef n (getErasureInfo i) ctxt
                         setContext ctxt')
                 (map snd (idris_totcheck i))
         mapM_ buildSCG (idris_totcheck i)
         mapM_ checkDeclTotality (idris_totcheck i)
         clear_totcheck
  where isDataDecl (PData _ _ _ _ _ _) = True
        isDataDecl _ = False

        setMutData ns n
           = do i <- getIState
                case lookupCtxt n (idris_datatypes i) of
                   [x] -> do let x' = x { mutual_types = ns }
                             putIState $ i { idris_datatypes
                                                = addDef n x' (idris_datatypes i) }
                   _ -> return ()

elabDecl' what info (PParams f ns ps)
    = do i <- getIState
         logLvl 1 $ "Expanding params block with " ++ show ns ++ " decls " ++
                show (concatMap tldeclared ps)
         let nblock = pblock i
         mapM_ (elabDecl' what info) nblock
  where
    pinfo = let ds = concatMap tldeclared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) in
                info { params = newps,
                       inblock = newb }
    pblock i = map (expandParamsD False i id ns
                      (concatMap tldeclared ps)) ps

elabDecl' what info (PNamespace n nfc ps) =
  do mapM_ (elabDecl' what ninfo) ps
     let ns = reverse (map T.pack newNS)
     sendHighlighting [(nfc, AnnNamespace ns Nothing)]
  where
    newNS = maybe [n] (n:) (namespace info)
    ninfo = info { namespace = Just newNS }

elabDecl' what info (PClass doc s f cs n nfc ps pdocs fds ds cn cd)
  | what /= EDefns
    = do logLvl 1 $ "Elaborating class " ++ show n
         elabClass info (s { syn_params = [] }) doc f cs n nfc ps pdocs fds ds cn cd
elabDecl' what info (PInstance doc argDocs s f cs n nfc ps t expn ds)
    = do logLvl 1 $ "Elaborating instance " ++ show n
         elabInstance info s doc argDocs what f cs n nfc ps t expn ds
elabDecl' what info (PRecord doc rsyn fc opts name nfc ps pdocs fs cname cdoc csyn)
    = do logLvl 1 $ "Elaborating record " ++ show name
         elabRecord info what doc rsyn fc opts name nfc ps pdocs fs cname cdoc csyn
{-
  | otherwise
    = do logLvl 1 $ "Elaborating [type of] " ++ show tyn
         elabData info s doc [] f [] (PLaterdecl tyn ty)
-}
elabDecl' _ info (PDSL n dsl)
    = do i <- getIState
         putIState (i { idris_dsls = addDef n dsl (idris_dsls i) })
         addIBC (IBCDSL n)
elabDecl' what info (PDirective i)
  | what /= EDefns = directiveAction i
elabDecl' what info (PProvider doc syn fc nfc provWhat n)
  | what /= EDefns
    = do logLvl 1 $ "Elaborating type provider " ++ show n
         elabProvider doc info syn fc nfc provWhat n
elabDecl' what info (PTransform fc safety old new)
    = do elabTransform info fc safety old new
         return ()
elabDecl' what info (PRunElabDecl fc script ns)
    = do elabRunElab info fc script ns
         return ()
elabDecl' _ info (PCopatterns fc clauses) 
    = do -- Partition clauses into copattern clauses and regular pattern clauses
         -- Elaborate regular pattern clauses as expected
         -- Collect coclauses 
         -- Copattern clause elaboration: Unnest and generate auxiliary functions
         ds <- collectDecls Nothing [] clauses
         logLvl 0 $ "Decls: " ++ show ds
         elabDecls info ds
      where
       collectDecls :: Maybe Name -> [PClause] -> [PDecl] -> Idris [PDecl]
       collectDecls targetName cs ((PClauses pfc opts pn (c@(PCoClause fc n lhs rhs wheres path) : clauses)) : ds) =
         do logLvl 0 $ "Encountered CoClause: " ++ show n
            clause <- extractPath c
            case (targetName, clauseName clause) of
             (Just tn, Just cn) -> if tn == cn
                                   then collectDecls targetName (clause:cs) (PClauses pfc opts pn clauses : ds)
                                   else do ds <- collectDecls (Just cn) [clause] (PClauses pfc opts pn clauses : ds)
                                           return $ PClauses pfc opts tn (reverse cs) : ds
             (Nothing, Just cn) -> collectDecls (Just cn) [clause] (PClauses pfc opts pn clauses : ds)
             (_,       Nothing) -> collectDecls targetName cs (PClauses pfc opts pn clauses : ds)
       collectDecls (Just tn) cs (PClauses fc opts pn [] : []) =
         return [PClauses fc opts tn (reverse cs)]
       collectDecls targetName cs (PClauses fc opts pn [] : ds) = collectDecls targetName cs ds
       collectDecls targetName cs (d : ds) = do logLvl 0 $ "Encountered decl: " ++ show d
                                                ds' <- collectDecls targetName cs ds
                                                return $ d : ds'
       collectDecls _          _  [] = return []

       extractPath :: PClause -> Idris PClause
       extractPath c@(PCoClause fc n lhs@(PApp _ (PRef _ _ n') (lhsArg : _)) rhs wheres path) | n == n' =
         do logLvl 0 $ "Path for name " ++ show n ++ ": " ++ show path
            projection <- findProjection n
            case (projection, nextNameUnderProjection (getTm lhsArg)) of
             (Just (pn, rn, ri), Just (nextFn, nextLhs)) -> 
               do logLvl 0 $ "Found projection " ++ show pn ++ " for lhs: " ++ show lhs ++ " . Next lhs is: " ++ show nextLhs
                  extractPath (PCoClause fc nextFn nextLhs rhs wheres ((pn, rn, ri):path))
             (_, _) -> return c
       extractPath c = return c

       nextNameUnderProjection :: PTerm -> Maybe (Name, PTerm)
       nextNameUnderProjection t@(PApp _ (PRef _ _ n) (arg : _)) = Just (n, t)
       nextNameUnderProjection t@(PRef _ _ n)                    = Just (n, t)
       nextNameUnderProjection _                                 = Nothing

       clauseName :: PClause -> Maybe Name
       clauseName (PClause _ n _ _ _ _) = Just n
       clauseName (PWith _ n _ _ _ _ _) = Just n
       clauseName (PClauseR _ _ _ _ ) = Nothing
       clauseName (PWithR _ _ _ _ _) = Nothing
       clauseName (PCoClause _ n _ _ _ _) = Just n

       findProjection :: Name -> Idris (Maybe (Name, Name, RecordInfo))
       findProjection n_in = 
         do let n = nsroot n_in
            ctxt <- getIState
            logLvl 0 $ "Trying to find projection for name " ++ show n
            let recordCtxt = toAlist $ idris_records ctxt
            let matchingRecords = map (\(rn, ri) -> fmap (\pn -> (pn, rn, ri)) (find (\m -> n == nsroot m) $ record_projections ri)) recordCtxt
            case catMaybes matchingRecords of
              [(pn, recordName, recordInfo)] ->
                do logLvl 0 $ "Found projection: " ++ show pn
                   return $ Just (pn, recordName, recordInfo)
              _ -> 
                do logLvl 0 $ "No projection found"
                   return Nothing
            
            -- logLvl 0 $ "Known projections: " ++ show recordCtxt
            -- let result = fmap (\ri -> (n, ri)) (lookupCtxtExact n recordCtxt)
            -- logLvl 0 $ "Found projection: " ++ show (fmap (\(pn, _) -> pn) result)
            -- return result

       -- hasCopatterns :: PClause -> Bool
       -- hasCopatterns (PCoClause _ _ _ _ _ [_ : _]) = True
       -- hasCopatterns _ = False

       -- toRegularPatternClause :: PClause -> Maybe PClause
       -- toRegularPatternClause (PCoClause fc n lhs rhs wheres (_ : _) = Nothing
       -- toRegularPatternClause (PCoClause fc n lhs rhs wheres []) = Just $ PClause fc n lhs [] rhs wheres
       -- toRegularPatternClause c = Just c
             

       -- partitionClauses :: Name -> FnOpts -> [PClause] -> [PClause] -> Idris [PDecl]
       -- partitionClauses fn fnOpts acc (c@(PCoClause fc n lhs rhs wheres path) : clauses)
       --   do projection <- findProjection n
       --      case (projection, nextNameUnderProjection lhs) of
       --       (Just (pn, recordInfo), Just (nextFn, nextLhs)) -> 
       --         partitionClauses nextFn fnOpts acc (PCoClause fc nextFn nextLhs rhs wheres ((pn,recordInfo):path) : clauses)
       --       (Nothing, _) -> if fn == n 
       --                       then partitionClauses nextFn (c : acc) clauses
       --                       else let clauses' = reverse acc
       --                            in PClauses (fcOf $ head clauses') fn clauses' : partitionClauses n [] clauses
            
        -- 1) is n the name of a projection?
        -- 2) If yes, put it into the path and look at next applied name from lhs
        -- 3) If no, a function name has been found
        -- 4) Recursively find related clauses

       -- fcOf :: PClause -> FC
       -- fcOf (PClause fc _ _ _ _ _) = fc
       -- fcOf (PWith fc _ _ _ _ _ _) = fc
       -- fcOf (PClauseR fc _ _ _ _ _) = fc
       -- fcOf (PWithR fc _ _ _ _ _) = fc
       -- fcOf (PCoClause fc _ _ _ _ _) = fc
       
         
elabDecl' _ _ _ = return () -- skipped this time
