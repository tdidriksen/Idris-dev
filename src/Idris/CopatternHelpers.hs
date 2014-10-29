{-# LANGUAGE PatternGuards #-}

module Idris.CopatternHelpers (desugarLhsProjs,
                               hasLhsProjs,
                               hasConsistentLhsProjs) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error
import Idris.Delaborate

import Idris.Core.TT hiding (subst)
import Idris.Core.Evaluate

import Control.Monad
import Control.Monad.State.Strict as State
import Data.List
import Data.Maybe

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

desugarLhsProjs :: [PClause] -> Idris [PClause]
desugarLhsProjs clauses =
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
  do compSet <- compatible lhs lhs'
     case compSet of
      Just cs -> do mergedRhs <- merge rhs (subst cs rhs')
                    iLOG $ "Substitutions: " ++ intercalate ", " (map show cs) 
                    return $ PClause fc n lhs wis mergedRhs whs
      Nothing -> return l
     -- if comp 
     --  then do mergedRhs <- merge rhs rhs'
     --          return $ PClause fc n lhs wis mergedRhs whs
     --  else return l
mergeClauses l@(PWith fc n lhs wis rhs whs) (PWith fc' n' lhs' wis' rhs' whs') =
  do compSet <- compatible lhs lhs'
     case compSet of
      Just cs -> do mergedRhs <- merge rhs (subst cs rhs')
                    return $ PWith fc n lhs wis mergedRhs whs
      Nothing -> return l
mergeClauses l@(PClause fc n lhs wis rhs whs) (PWith fc' n' lhs' wis' rhs' whs') =
  do compSet <- compatible lhs lhs'
     case compSet of
      Just cs -> do mergedRhs <- merge rhs (subst cs rhs')
                    return $ PClause fc n lhs wis mergedRhs whs
      Nothing -> return l
mergeClauses l@(PWith fc n lhs wis rhs whs) (PClause fc' n' lhs' wis' rhs' whs') =
  do compSet <- compatible lhs lhs'
     case compSet of
      Just cs -> do mergedRhs <- merge rhs (subst cs rhs')
                    return $ PWith fc n lhs wis mergedRhs whs
      Nothing -> return l
mergeClauses l r = return l

type Substitution = (Name, PTerm)

subst :: [Substitution] -> PTerm -> PTerm
subst subs t = mapPT (subst' subs) t
  where
    subst' subs t@(PRef _ n)
      | Just t' <- lookup n subs = t'
      | otherwise = t
    subst' subs t@(PLam x ty body)
      | Just _ <- lookup x subs = t
      | otherwise = PLam x (subst' subs ty) (subst' subs body)
    subst' subs t@(PPi pl n a b)
      | Just _ <- lookup n subs = t
      | otherwise = PPi pl n (subst' subs a) (subst' subs b)
    subst' subs t@(PLet x ty e b)
      | Just _ <- lookup x subs = t
      | otherwise = PLet x (subst' subs ty) (subst' subs e) (subst' subs b)
    subst' _ t = t 


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
    (Just t, Just t') -> do c <- compatible t t'
                            return $ isJust c
    _                 -> return False


{- |
 Tests whether two terms are compatible.
 Two terms are compatible if the second argument
 is more general than the first argument (i.e. the first
 argument has more specific patterns)
-}
compatible :: PTerm -> PTerm -> Idris (Maybe [Substitution])
compatible x y = do i <- get
                    return $ fmap reverse (compatible' i x y [])

compatible' :: IState -> PTerm -> PTerm -> [Substitution] -> Maybe [Substitution]
compatible' ist t@(PRef _ n) (PRef _ n') subs =
  let sub = (n', t)
  in case (isConName n (tt_ctxt ist), isConName n' (tt_ctxt ist)) of
       (True,  True)  -> if n == n' then return subs else Nothing
       (True,  False) -> return $ sub : subs
       (False, True)  -> Nothing
       (False, False) -> return $ sub : subs
compatible' _ (PRef _ _) Placeholder subs = return subs
compatible' _ (PRef _ n) (PApp _ _ _) _ = Nothing
compatible' ist Placeholder (PRef _ n) subs =
  if isConName n (tt_ctxt ist) then Nothing else return subs
compatible' _ Placeholder Placeholder subs = return subs
compatible' _ Placeholder (PApp _ _ _) _ = Nothing
compatible' ist t@(PApp _ _ _) (PRef _ n) subs =
  if isConName n (tt_ctxt ist) then Nothing else return $ (n, t) : subs
compatible' _ (PApp _ _ _) Placeholder subs = return subs
compatible' ist (PApp _ (PRef _ n) args) (PApp _ (PRef _ n') args') subs
 | n == n'   = compatibleArgLists ist args args' subs
 | otherwise = Nothing

-- compatible (PRef _ n) (PRef _ n') =
--   do i <- get
--      case (isConName n (tt_ctxt i), isConName n' (tt_ctxt i)) of
--       (True,  True)  -> return $ n == n'
--       (True,  False) -> return True
--       (False, True)  -> return False
--       (False, False) -> return True
-- compatible (PRef _ _) Placeholder = return True
-- compatible (PRef _ n) (PApp _ _ _) = return False
-- compatible Placeholder (PRef _ n) =
--   do i <- get
--      return $ not (isConName n (tt_ctxt i))
-- compatible Placeholder Placeholder = return True
-- compatible Placeholder (PApp _ _ _) = return False
-- compatible (PApp _ _ _) (PRef _ n) =
--   do i <- get
--      return $ not (isConName n (tt_ctxt i))  
-- compatible (PApp _ _ _) Placeholder = return True   
-- compatible (PApp _ (PRef _ n) args) (PApp _ (PRef _ n') args')
--   | n == n'   = compatibleArgLists args args'
--   | otherwise = return False
-- compatible _ _ = return False


-- compatible :: PTerm -> PTerm -> Idris Bool
-- compatible (PRef _ n) (PRef _ n') =
--   do i <- get
--      case (isConName n (tt_ctxt i), isConName n' (tt_ctxt i)) of
--       (True,  True)  -> return $ n == n'
--       (True,  False) -> return True
--       (False, True)  -> return False
--       (False, False) -> return True
-- compatible (PRef _ _) Placeholder = return True
-- compatible (PRef _ n) (PApp _ _ _) = return False
-- compatible Placeholder (PRef _ n) =
--   do i <- get
--      return $ not (isConName n (tt_ctxt i))
-- compatible Placeholder Placeholder = return True
-- compatible Placeholder (PApp _ _ _) = return False
-- compatible (PApp _ _ _) (PRef _ n) =
--   do i <- get
--      return $ not (isConName n (tt_ctxt i))  
-- compatible (PApp _ _ _) Placeholder = return True   
-- compatible (PApp _ (PRef _ n) args) (PApp _ (PRef _ n') args')
--   | n == n'   = compatibleArgLists args args'
--   | otherwise = return False
-- compatible _ _ = return False

compatibleArgLists :: IState -> [PArg] -> [PArg] -> [Substitution] -> Maybe [Substitution]
compatibleArgLists ist (a : args) (a' : args') subs = 
  do subs' <- compatibleArgs ist a a' subs
     compatibleArgLists ist args args' subs'
compatibleArgLists _ [] [] subs = return subs
compatibleArgLists _ [] (_:_) _ = Nothing
compatibleArgLists _ (_:_) [] _ = Nothing  

compatibleArgs :: IState -> PArg -> PArg -> [Substitution] -> Maybe [Substitution]
compatibleArgs ist (PExp _ _ _ t) (PExp _ _ _ t') subs = compatible' ist t t' subs
compatibleArgs ist (PImp _ _ _ _ t) (PImp _ _ _ _ t') subs = compatible' ist t t' subs
compatibleArgs ist (PConstraint _ _ _ t) (PConstraint _ _ _ t') subs = compatible' ist t t' subs
compatibleArgs ist (PTacImplicit _ _ _ _ t) (PTacImplicit _ _ _ _ t') subs = compatible' ist t t' subs
compatibleArgs _ _ _ _ = Nothing


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
