{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.ElabDecls where

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

import Idris.Elab.Utils
import Idris.Elab.Type
import Idris.Elab.Clause
import Idris.Elab.Data
import Idris.Elab.Record
import Idris.Elab.Class
import Idris.Elab.Instance
import Idris.Elab.Provider
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
recinfo = EInfo [] emptyContext id Nothing elabDecl'

-- | Return the elaborated term which calls 'main'
elabMain :: Idris Term
elabMain = do (m, _) <- elabVal recinfo ERHS
                           (PApp fc (PRef fc (sUN "run__IO"))
                                [pexp $ PRef fc (sNS (sUN "main") ["Main"])])
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
          believeTy = Bind (sUN "a") (Pi (TType (UVar (-2))) (TType (UVar (-1))))
                       (Bind (sUN "b") (Pi (TType (UVar (-2))) (TType (UVar (-1))))
                         (Bind (sUN "x") (Pi (V 1) (TType (UVar (-1)))) (V 1)))
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

          synEqTy = Bind (sUN "a") (Pi (TType (UVar (-3))) (TType (UVar (-2))))
                     (Bind (sUN "b") (Pi (TType (UVar (-3))) (TType (UVar (-2))))
                      (Bind (sUN "x") (Pi (V 1) (TType (UVar (-2))))
                       (Bind (sUN "y") (Pi (V 1) (TType (UVar (-2))))
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
elabDecl' what info (PTy doc argdocs s f o n ty)
  | what /= EDefns
    = do iLOG $ "Elaborating type decl " ++ show n ++ show o
         elabType info s doc argdocs f o n ty
         return ()
elabDecl' what info (PPostulate doc s f o n ty)
  | what /= EDefns
    = do iLOG $ "Elaborating postulate " ++ show n ++ show o
         elabPostulate info s doc f o n ty
elabDecl' what info (PData doc argDocs s f co d)
  | what /= ETypes
    = do iLOG $ "Elaborating " ++ show (d_name d)
         elabData info s doc argDocs f co d
  | otherwise
    = do iLOG $ "Elaborating [type of] " ++ show (d_name d)
         elabData info s doc argDocs f co (PLaterdecl (d_name d) (d_tcon d))
elabDecl' what info d@(PClauses f o n ps)
  | what /= ETypes
    = do iLOG $ "Elaborating clause " ++ show n
         i <- getIState -- get the type options too
         unless (hasConsistentLhsProjs ps)
           (do tclift $ tfail (At f (Elaborating "clauses " n (Msg " have left-hand side projections on only some clauses."))))
         ps' <- if ((not (null ps)) && hasLhsProjs (head ps))
                then desugar ps
                else return ps
         let o' = case lookupCtxt n (idris_flags i) of
                    [fs] -> fs
                    [] -> []
         elabClauses info f (o ++ o') n ps'
  where
    hasLhsProjs :: PClause -> Bool
    hasLhsProjs clause =
      case clauseApp clause of
        Just (PLhsProj _ _) -> True
        _                   -> False

    hasConsistentLhsProjs :: [PClause] -> Bool
    hasConsistentLhsProjs clauses =
      case partition hasLhsProjs clauses of
        ([], _) -> True
        (_, []) -> True
        _       -> False
    
    desugar :: [PClause] -> Idris [PClause]
    desugar clauses =
      do expanded <- mapM expandClause clauses
         iLOG $ "Expanded " ++ show (length expanded) ++ " clauses"
         merged <- mergeClauseList expanded
         iLOG $ "Returning " ++ show (length merged) ++ " merged clauses"
         forM_ merged $ \m ->
           do case (clauseApp m) of
               Just app -> iLOG $ "LHS: " ++ show app
               Nothing -> return ()
              iLOG $ "RHS: " ++ show (clauseRhs m)
         return merged
    
    expandClause :: PClause -> Idris PClause
    expandClause (PClause fc n t@(PLhsProj projName app) wis rhs whs) =
      do iLOG $ "expanding clause " ++ show n
         (reducedLhs, expandedRhs) <- expandRhs fc t rhs
         iLOG $ "expanded clause " ++ show n
         return $ PClause fc n reducedLhs wis expandedRhs whs
    expandClause (PWith fc n t@(PLhsProj projName app) wis rhs whs) =
      do iLOG $ "expanding clause " ++ show n
         (reducedLhs, expandedRhs) <- expandRhs fc t rhs
         iLOG $ "expanded clause " ++ show n
         return $ PWith fc n reducedLhs wis expandedRhs whs
    expandClause c = return c

    -- Beware : Also performs reduction!
    expandRhs :: FC -> PTerm -> PTerm -> Idris (PTerm, PTerm)
    expandRhs fc (PLhsProj projName t) rhs =
      do i <- get
         (pn, cn) <- case lookupCtxtName (nsroot projName) (lhs_projections i) of
                       [] -> tclift $ tfail (At fc (NoTypeDecl projName))
                       [(n', (pty, pn, ptyn, cn))] -> return (pn, cn)
                       xs -> case lookupCtxtExact projName (lhs_projections i) of
                              Just (pty, pn, ptyn, cn) -> return (pn, cn)
                              Nothing -> tclift $ tfail (At fc (NoTypeDecl projName))
         cty <- case lookupTyExact cn (tt_ctxt i) of
                  Just ty -> return $ delab i ty
                  Nothing -> tclift $ tfail (At fc (NoTypeDecl cn))
         iLOG $ "Expanded " ++ show projName ++ " to " ++ show pn ++ " with constructor " ++ show cn
         mk <- makeConstructorApp fc pn rhs cn cty
         (reducedLhs, expandedRhs) <- expandRhs fc t mk
         return $ (reducedLhs, expandedRhs) --(reducedLhs, PApp fc (PRef fc projName) [pexp expandedRhs])
    expandRhs _ lhs rhs = return (lhs, rhs)

    makeConstructorApp :: FC -> Name -> PTerm -> Name -> PTerm -> Idris PTerm
    makeConstructorApp fc projName rhs cn cty =
      do i <- get
         delabArgs <- case lookupCtxtExact cn (idris_implicits i) of
                       Just args -> return args
                       Nothing -> ifail $ "No arguments for constructor " ++ show cn  
         args <- makeArgList projName rhs cty delabArgs
         return $ PApp fc (PRef fc cn) args

    makeArgList :: Name -> PTerm -> PTerm -> [PArg] -> Idris [PArg]
    makeArgList projName t (PPi _ n _ b) (delabArg : das) =
      do iLOG $ "Will put " ++ show t ++ " when " ++ show (nsroot projName) ++ " and " ++ show n ++ " are equal" 
         let term = if (nsroot projName) == n then t else Placeholder
         case makeArg term n delabArg of
           Just arg -> do args <- makeArgList projName t b das
                          return $ arg : args 
           Nothing  -> makeArgList projName t b das
    makeArgList _ _ _ _ = return []

    makeArg :: PTerm -> Name -> PArg -> Maybe PArg
    makeArg t _ (PExp _ _ _ _) = Just $ pexp t
    makeArg t n (PImp _ False _ _ _) = Just $ pimp n t False
    makeArg t _ (PConstraint _ _ _ _) = Just $ pconst t
    makeArg t n (PTacImplicit _ _ _ s _) = Just $ ptacimp n s t
    makeArg _ _ _ = Nothing

    -- reduceClause :: PClause -> Idris PClause
    -- reduceClause (PClause fc n t@(PLhsProj projName app) wis (PApp _ (PRef _ projName') [arg]) whs)
    --   | projName == projName' = let nextRhs = getTm arg
    --                             in reduceClause $ PClause fc n app wis nextRhs whs
    --   | otherwise             = tclift $ tfail (reduceError fc projName projName')
    -- reduceClause (PWith fc n t@(PLhsProj projName app) wis (PApp _ (PRef _ projName') [arg]) whs)
    --   | projName == projName' = let nextRhs = getTm arg
    --                             in reduceClause $ PWith fc n app wis nextRhs whs
    --   | otherwise             = tclift $ tfail (reduceError fc projName projName')
    -- reduceClause (PClause fc n (PLhsProj projName app) wis _ whs) =
    --   tclift $ tfail (At fc (Elaborating "left-hand side projection " projName (Msg $ show projName ++ " cannot be reduced because it was expanded incorrectly.")))
    -- reduceClause c = return c

    -- reduceError :: FC -> Name -> Name -> Err
    -- reduceError fc projName projName' =
    --   (At fc (Elaborating "left-hand side projection " projName
    --     (Msg (show projName ++ " and " ++ show projName' ++  " do not reduce. This is an internal issue; please file a bug report."))))

    -- foldAll :: (a -> a -> a) -> [a] -> [a]
    -- foldAll f xs = foldAll' f xs []
    --   where
    --     foldAll' :: (a -> a -> a) -> [a] -> [a] -> [a]
    --     foldAll' f []       _  = []
    --     foldAll' f (x : xs) ys = foldr f x (xs ++ ys) : foldAll' f xs (x : ys)

    mergeClauseList :: [PClause] -> Idris [PClause]
    mergeClauseList clauses =
      do iLOG "Merging"
         -- Get a list of pairs, pairing each clause with the rest of the clauses
         let singledOut = singleOut clauses
         -- Find the clauses which will be subsubmed by other clauses
         (subsumed, keepers) <- partitionM (\(c,other) -> allM (\c' -> clauseCompatible c' c) other) singledOut
         iLOG $ "Subsumed clauses: " ++ intercalate ", " (map show (mapMaybe clauseName (map fst subsumed)))
         iLOG $ "Kept clauses: " ++ intercalate ", " (map show (mapMaybe clauseName (map fst keepers)))         
         -- Check if any keepers are left (when all clauses are intercompatible, all clauses are subsumed by each other)
         case (subsumed, keepers) of
          ([], []) -> return []
          ([], ks) ->
            -- No clauses are subsumed, merge each clause with all other clauses
            do withOther <- forM ks $ \(k,other) ->
                              foldM (\keeper -> \o -> mergeClauses keeper o) k other
               return withOther
          ((s, _) : subs, []) -> -- No keepers, fold up subsumed
            do folded <- foldM mergeClauses s (map fst subs)
               return [folded]
          (subs, ks) ->
            -- Some clauses are subsumed; First merge the subsumed clauses with the kept clauses (keepers)
            do let ks' = singleOut (map fst ks)
               withSubsumed <- forM ks' $ \(k,other) ->
                                 do folded <- foldM (\keeper -> \s -> mergeClauses keeper s) k (map fst subs)
                                    return (folded, other)
               -- Then merge each of the kept clauses with all the other clauses
               withOther <- forM withSubsumed $ \(k,other) ->
                              foldM (\keeper -> \o -> mergeClauses keeper o) k other
               return withOther
                                 

    singleOut :: [a] -> [(a, [a])]
    singleOut xs = singleOut' xs []
      where
        singleOut' :: [a] -> [a] -> [(a, [a])]
        singleOut' []       _  = []
        singleOut' (x : xs) ys = (x, xs ++ ys) : singleOut' xs (x : ys)

    partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
    partitionM p [] = return ([], [])
    partitionM p (x:xs) =
      do (ts, fs) <- partitionM p xs
         p' <- p x
         return $ if p' then (x:ts, fs) else (ts, x:fs)

    allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
    allM p [] = return True
    allM p (x:xs) = p x `andM` allM p xs

    andM :: (Monad m) => m Bool -> m Bool -> m Bool
    andM x y = do a <- x; b <- y; return $ a && b


    mergeClauses :: PClause -> PClause -> Idris PClause
    mergeClauses l@(PClause fc n lhs wis rhs whs) (PClause fc' n' lhs' wis' rhs' whs') =
      do comp <- compatible lhs lhs' 
         if comp 
          then do mergedRhs <- merge rhs rhs'
                  return $ PClause fc n lhs wis mergedRhs whs
          else return l
    mergeClauses l@(PWith fc n lhs wis rhs whs) (PWith fc' n' lhs' wis' rhs' whs') =
      do comp <- compatible lhs lhs' 
         if comp 
          then do mergedRhs <- merge rhs rhs'
                  return $ PWith fc n lhs wis mergedRhs whs
          else return l
    mergeClauses l@(PClause fc n lhs wis rhs whs) (PWith fc' n' lhs' wis' rhs' whs') =
      do comp <- compatible lhs lhs' 
         if comp 
          then do mergedRhs <- merge rhs rhs'
                  return $ PClause fc n lhs wis mergedRhs whs
          else return l
    mergeClauses l@(PWith fc n lhs wis rhs whs) (PClause fc' n' lhs' wis' rhs' whs') =
      do comp <- compatible lhs lhs' 
         if comp 
          then do mergedRhs <- merge rhs rhs'
                  return $ PWith fc n lhs wis mergedRhs whs
          else return l
    mergeClauses l r = return l

    -- allAll :: (a -> a -> Bool) -> [a] -> ([a], [a])
    -- allAll f xs = allAll' f xs []
    --   where
    --     allAll' :: (a -> a -> Bool) -> [a] -> [a] -> ([a], [a])
    --     allAll' f []       _ = ([], [])
    --     allAll' f (x : xs) ys = let (xs', ys') = allAll' f xs (x : ys)
    --                             in if all (f x) (xs ++ ys)
    --                                then ((x : xs'), ys')
    --                                else (xs', (x : ys'))

    clauseCompatible :: PClause -> PClause -> Idris Bool
    clauseCompatible c c' =
      case (clauseApp c, clauseApp c') of
        (Just t, Just t') -> compatible t t'
        _                 -> return False

    {- |
     Tests whether two terms are compatible.
     Two terms are compatible if the second argument
     is more general than the first argument (i.e. the first
     argument has more specific patterns)
    -}
    compatible :: PTerm -> PTerm -> Idris Bool
    compatible (PRef _ n) (PRef _ n') =
      do i <- get
         case (isConName n (tt_ctxt i), isConName n' (tt_ctxt i)) of
          (True,  True)  -> return $ n == n'
          (True,  False) -> return True
          (False, True)  -> return False
          (False, False) -> return True
    compatible (PRef _ _) Placeholder = return True
    compatible (PRef _ n) (PApp _ _ _) = return False
    compatible Placeholder (PRef _ n) =
      do i <- get
         return $ not (isConName n (tt_ctxt i))
    compatible Placeholder Placeholder = return True
    compatible Placeholder (PApp _ _ _) = return False
    compatible (PApp _ _ _) (PRef _ n) =
      do i <- get
         return $ not (isConName n (tt_ctxt i))  
    compatible (PApp _ _ _) Placeholder = return True   
    compatible (PApp _ (PRef _ n) args) (PApp _ (PRef _ n') args')
      | n == n'   = compatibleArgLists args args'
      | otherwise = return False
    compatible _ _ = return False
    
    -- compatible (PApp _ (PRef _ n) args) (PRef _ n') = return False
    -- compatible (PRef _ n) Placeholder =
    --   do i <- get
    --      if isConName n (tt_ctxt i)
    --       then return False
    --       else return True
    -- compatible Placeholder (PRef _ n) =
    --   do i <- get
    --      if isConName n (tt_ctxt i)
    --       then return False
    --       else return True
    -- compatible x y = return False
      -- TODO: This implementation only works for clauses without arguments

    compatibleArgLists :: [PArg] -> [PArg] -> Idris Bool
    compatibleArgLists (a : args) (a' : args') = 
      compatibleArgs a a' `andM` compatibleArgLists args args'
    compatibleArgLists [] [] = return True
    compatibleArgLists [] (_:_) = return False
    compatibleArgLists (_:_) [] = return False    

    compatibleArgs :: PArg -> PArg -> Idris Bool
    compatibleArgs (PExp _ _ _ t) (PExp _ _ _ t') = compatible t t'
    compatibleArgs (PImp _ _ _ _ t) (PImp _ _ _ _ t') = compatible t t'
    compatibleArgs (PConstraint _ _ _ t) (PConstraint _ _ _ t') = compatible t t'
    compatibleArgs (PTacImplicit _ _ _ _ t) (PTacImplicit _ _ _ _ t') = compatible t t'
    compatibleArgs _ _ = return False
    

    merge :: PTerm -> PTerm -> Idris PTerm
    merge l@(PApp fc (PRef rfc n) args) r@(PApp fc' (PRef _ n') args')
      | n == n' = do iLOG $ "Merging terms " ++ show l ++ " and " ++ show r
                     mergedArgs <- zipWithM mergeArgs args args' --mapM mergeArgs $ zipArgs args args'
                     return $ PApp fc (PRef rfc n) mergedArgs
      | otherwise = return l
    merge x y = return x

    zipArgs :: [PArg] -> [PArg] -> [(PArg, Maybe PArg)]
    zipArgs args args' =
      flip map args $ \arg ->
        (arg, flip find args' $ \arg' -> pname arg == pname arg')
    
    mergeArgs :: PArg ->  PArg -> Idris PArg
    mergeArgs (PExp _ _ n t) (PExp _ _ n' t')
      = do iLOG $ "Merging args " ++ show t ++ " and " ++ show t'
           mergedArgTerms <- mergeArgTerms t t'
           iLOG $ "Merged arg term: " ++ show mergedArgTerms
           return $ pexp mergedArgTerms
    mergeArgs (PImp _ inf _ n t) (PImp _ inf' _ n' t')
      = do iLOG $ "Merging args " ++ show t ++ " and " ++ show t'
           mergedArgTerms <- mergeArgTerms t t'
           iLOG $ "Merged arg term: " ++ show mergedArgTerms
           return $ pimp n mergedArgTerms (inf && inf')
    mergeArgs (PConstraint _ _ n t) (PConstraint _ _ n' t')
      = do iLOG $ "Merging args " ++ show t ++ " and " ++ show t'
           mergedArgTerms <- mergeArgTerms t t'
           iLOG $ "Merged arg term: " ++ show mergedArgTerms
           return $ pconst mergedArgTerms
    mergeArgs (PTacImplicit _ _ n s t)  (PTacImplicit _ _ n' s' t')
      = do iLOG $ "Merging args " ++ show t ++ " and " ++ show t'
           mergedArgTerms <- mergeArgTerms t t'
           iLOG $ "Merged arg term: " ++ show mergedArgTerms
           return $ ptacimp n s mergedArgTerms
    mergeArgs x _ = return x
                                 
    mergeArgTerms :: PTerm -> PTerm -> Idris PTerm
    mergeArgTerms Placeholder t           = return t
    mergeArgTerms t           Placeholder = return t
    mergeArgTerms l@(PApp fc (PRef _ n) args) r@(PApp fc' (PRef _ n') args') =
      merge l r
    mergeArgTerms xs ys = return xs

    clauseName :: PClause -> Maybe Name
    clauseName (PClause _ n _ _ _ _) = Just n
    clauseName (PWith _ n _ _ _ _) = Just n
    clauseName _ = Nothing

    clauseApp :: PClause -> Maybe PTerm
    clauseApp (PClause _ _ app _ _ _) = Just app
    clauseApp (PWith _ _ app _ _ _) = Just app
    clauseApp _ = Nothing

    clauseRhs :: PClause -> PTerm
    clauseRhs (PClause _ _ _ _ rhs _) = rhs
    clauseRhs (PWith _ _ _ _ rhs _) = rhs
    clauseRhs (PClauseR _ _ rhs _) = rhs
    clauseRhs (PWithR _ _ rhs _) = rhs

elabDecl' what info (PMutual f ps)
    = do case ps of
              [p] -> elabDecl what info p
              _ -> do mapM_ (elabDecl ETypes info) ps
                      mapM_ (elabDecl EDefns info) ps
         -- record mutually defined data definitions
         let datans = concatMap declared (filter isDataDecl ps)
         mapM_ (setMutData datans) datans
         iLOG $ "Rechecking for positivity " ++ show datans
         mapM_ (\x -> do setTotality x Unchecked) datans
         -- Do totality checking after entire mutual block
         i <- get
         mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                         updateContext (simplifyCasedef n $ getErasureInfo i))
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
         iLOG $ "Expanding params block with " ++ show ns ++ " decls " ++
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

elabDecl' what info (PNamespace n ps) = mapM_ (elabDecl' what ninfo) ps
  where
    ninfo = case namespace info of
                Nothing -> info { namespace = Just [n] }
                Just ns -> info { namespace = Just (n:ns) }
elabDecl' what info (PClass doc s f cs n ps pdocs ds)
  | what /= EDefns
    = do iLOG $ "Elaborating class " ++ show n
         elabClass info (s { syn_params = [] }) doc f cs n ps pdocs ds
elabDecl' what info (PInstance s f cs n ps t expn ds)
    = do iLOG $ "Elaborating instance " ++ show n
         elabInstance info s what f cs n ps t expn ds
elabDecl' what info (PRecord doc s f tyn ty opts cdoc cn cty)
  | what /= ETypes
    = do iLOG $ "Elaborating record " ++ show tyn
         elabRecord info s doc f tyn ty opts cdoc cn cty
  | otherwise
    = do iLOG $ "Elaborating [type of] " ++ show tyn
         elabData info s doc [] f [] (PLaterdecl tyn ty)
elabDecl' _ info (PDSL n dsl)
    = do i <- getIState
         putIState (i { idris_dsls = addDef n dsl (idris_dsls i) })
         addIBC (IBCDSL n)
elabDecl' what info (PDirective i)
  | what /= EDefns = i
elabDecl' what info (PProvider syn fc provWhat n)
  | what /= EDefns
    = do iLOG $ "Elaborating type provider " ++ show n
         elabProvider info syn fc provWhat n
elabDecl' what info (PTransform fc safety old new)
    = do elabTransform info fc safety old new
         return ()
elabDecl' _ _ _ = return () -- skipped this time

