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
import Control.Applicative
import Data.List
import Data.Maybe

-- constructorForType :: Name -- ^ The name of the clause
--                       -> Idris PTerm
-- constructorForType clauseName =
--   do i <- get
--      ty <- case lookupTyNameExact (nsroot clauseName) (tt_ctxt i) of
--             Just ty' -> return $ delab i ty'

-- argType :: PTerm -> (PTerm -> PTerm)
-- argType (PPi p n a b) = \result -> PPi p n a (argType b

-- splitType :: PTerm -> (PTerm, PTerm)
-- splitType (PPi _ n a b@(PPi _ _ _)) = ()
-- splitType _

type Path = [Name]

path :: PClause -> (PClause, Path)
path (PClause fc n (PLhsProj pn t) wis rhs whs) =
  let (c, p) = path (PClause fc n t wis rhs whs)
  in (c, reverse (pn:p))
path (PWith fc n (PLhsProj pn t) wis rhs whs) =
  let (c, p) = path (PWith fc n t wis rhs whs)
  in (c, reverse (pn:p))
path c = (c, [])

-- splitType :: PTerm -> (PTerm -> PTerm, PTerm) 
-- splitType (PPi pl n a b) =
--   let (f, b') = splitType b
--   in (PPi pl n a . f, b')
-- splitType t = (id, t)

-- 1. Nat -> MkB Nat
-- 2. Split type: (Nat, B Nat)
-- 3. Unapply result type: B [Nat]
-- 4. Find constructor for B: MkB : a -> MkB a
-- 5. Instantiate constructor: Nat -> MkB Nat
-- 6. Delaborate with implicit arguments

normalisedType :: Name -> Idris Type
normalisedType n =
  do i <- get
     (nty, ty) <- case lookupTyNameExact n (tt_ctxt i) of
                   Just (_, ty') -> return $ (normalise (tt_ctxt i) [] ty', ty')
                   Nothing -> undefined
     iLOG $ "Written type: " ++ show ty
     iLOG $ "Normalized type: " ++ show nty
     return nty

splitType :: Type -> ([(Name, Type)], Type)
splitType ty = (getArgTys ty, getRetTy ty)

constructorFor :: Name -> Idris PTerm
constructorFor n =
  do i <- get
     normTy <- normalisedType n
     let (argTys, retTy) = splitType normTy
     let (ty, tyArgs) = unApply retTy
     tyName <- typeName ty
     constrName <- constructorName tyName
     constrType <- normalisedType constrName
     let (constrArgTys, constrRetTy) = splitType constrType
     let (constrRetName, constrRetArgs) = unApply constrRetTy
     let instantiatedConstrType = substTerms (zip constrRetArgs tyArgs) constrType
     iLOG $ "Instantiated type: " ++ show instantiatedConstrType
     return $ delab i instantiatedConstrType

substTerms :: Eq n => [(TT n, TT n)] -> TT n -> TT n
substTerms subs t = foldr (\(old,new) -> \t' -> substTerm old new t') t subs
     
typeName :: Type -> Idris Name
typeName ty = case freeNames ty of
               [] -> undefined
               [tyName] -> return tyName
               _ -> undefined

-- FIXME : Fail properly
constructorName :: Name -> Idris Name
constructorName n =
  do i <- get
     typeInfo <- case lookupCtxtExact n (idris_datatypes i) of
                  Just ti -> return ti
                  Nothing -> undefined
     case con_names typeInfo of
      [] -> undefined
      [conName] -> return conName
      _ -> undefined

constructorType :: Name -> Idris Type
constructorType n =
  do i <- get
     ty <- case lookupTyNameExact n (tt_ctxt i) of
             Just (_, ty') -> return ty'
             Nothing -> undefined
     return ty

-- | Tests whether the input clause has one or more left-hand side projections.
-- In other words, 'hasLhsProjs' tests whether a clause involves copatterns.
hasLhsProjs :: PClause -> Bool
hasLhsProjs clause =
  case clauseLhs clause of
    Just (PLhsProj _ _) -> True
    _                   -> False

{- | Tests whether a collection of clauses
     makes consistent use of left-hand side projections.
     Consistent use means that either all or none of the
     clauses in the input list have left-hand side projections.
-}
hasConsistentLhsProjs :: [PClause] -> Bool
hasConsistentLhsProjs clauses =
  case partition hasLhsProjs clauses of
    ([], _) -> True
    (_, []) -> True
    _       -> False

{-| Desugars a list of clauses with left-hand side projections
    to an equivalent list of clauses without left-hand side
    projections. The desugared versions use constructors
    on their right-hand sides.

    For a standard Stream definition, a stream of zeros:
     zeros : Stream Nat
     &hd zeros = Z
     &tl zeros = zeros
    Desugars to:
     zeros : Stream Nat
     zeros = Z :: zeros
-}
desugarLhsProjs :: Name -> [PClause] -> Idris [PClause]
desugarLhsProjs name clauses =
  if True
  then mergedCopatterns
  else do _ <- constructorFor name
          return []
  where
    splitCopatterns :: [PClause] -> Idris [PClause]
    splitCopatterns = undefined

    mergedCopatterns =
      do expanded <- mapM expandClause clauses
         iLOG $ "Expanded " ++ show (length expanded) ++ " clauses"
         merged <- mergeClauseList expanded
         iLOG $ "Returning " ++ show (length merged) ++ " merged clauses"
         forM_ merged $ \m ->
           do case (clauseLhs m, clauseName m) of
               (Just app, Just n) ->
                 do iLOG $ "LHS: " ++ show app
                    _ <- constructorFor n
                    return ()
               _ -> return ()
              iLOG $ "RHS: " ++ show (clauseRhs m)
         return merged

{-| Expands a clause with left-hand side projections into
    a clause using constructors. For arguments where a
    clause defines no term, a metavariable is inserted.

    For a standard Stream definition, a stream of zeros,
    the clauses:
     &hd zeros = Z
     &tl zeros = zeros
    are expanded into:
     zeros = Z :: ?zerostl
     zeros = ?zeroshd :: zeros
-}
expandClause :: PClause -> Idris PClause
expandClause (PClause fc n t@(PLhsProj projName app) wis rhs whs) =
  do iLOG $ "expanding clause " ++ show n
     (reducedLhs, expandedRhs) <- expandRhs fc n t rhs
     iLOG $ "expanded clause " ++ show n
     return $ PClause fc n reducedLhs wis expandedRhs whs
expandClause (PWith fc n t@(PLhsProj projName app) wis rhs whs) =
  do iLOG $ "expanding clause " ++ show n
     (reducedLhs, expandedRhs) <- expandRhs fc n t rhs
     iLOG $ "expanded clause " ++ show n
     return $ PWith fc n reducedLhs wis expandedRhs whs
expandClause c = return c


{-| Expands the right-hand side (fourth argument) and
    reduces the left-hand side (third argument)
    of a clause with copatterns.
    The left-hand side is reduced by removing any left-hand side
    projections, while the right-hand side is expanded into
    a constructor. Metavariables are inserted in the
    right-hand side for constructor arguments where a
    clause defines no term.

    The following program:
     cycle : Nat -> Nat -> Stream Nat
     &hd cycle y _ = y
     &tl cycle Z n = cycle n n
     &tl cycle (S m) n = cycle m n
    expands into:
     cycle : Nat -> Nat -> Stream Nat
     cycle y _ = y :: ?cycletl
     cycle Z n = ?cyclehd :: cycle n n
     cycle (S m) n = ?cyclehd :: cycle m n
-}
expandRhs :: FC -- ^ The source information for the clause
             -> Name -- ^ The name of the clause
             -> PTerm -- ^ The left-hand side of the clause
             -> PTerm -- ^ The right-hand side of the clause
             -> Idris (PTerm, PTerm) -- ^ (reduced left-hand side, expanded right-hand side)
expandRhs fc fnName (PLhsProj projName t) rhs =
  do i <- get
     iLOG $ "Expanding projection: " ++ show projName              
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
     mk <- makeConstructorApp fc fnName pn rhs cn cty
     (reducedLhs, expandedRhs) <- expandRhs fc fnName t mk
     return $ (reducedLhs, expandedRhs) --(reducedLhs, PApp fc (PRef fc projName) [pexp expandedRhs])
expandRhs _ _ lhs rhs = return (lhs, rhs)

{-| Creates a constructor for an expanded right-hand side for a
    clause with copatterns.
    Based on a constructor name and a type for the constructor,
    'makeConstructorApp' creates a new right-hand side for a clause
    with copatterns by embedding the given right-hand side in
    a constructor application. For constructor arguments
    where the clause defines no term, a metavariable is inserted.

    For the following program:
     cycle : Nat -> Nat -> Stream Nat
     &hd cycle y _ = y
     &tl cycle Z n = cycle n n
     &tl cycle (S m) n = cycle m n
    the following constructor applications would be created:
     y :: ?cycletl
     ?cyclehd :: cycle n n
     ?cyclehd :: cycle m n
-}
makeConstructorApp :: FC -- ^ The source information for the clause
                      -> Name -- ^ The name of the clause
                      -> Name -- ^ The name of the projection for which we make a constructor
                      -> PTerm -- ^ The right-hand side which should be embedded into the created constructor.
                      -> Name -- ^ The name of the created constructor
                      -> PTerm -- ^ The type of the created constructor
                      -> Idris PTerm -- ^ A constructor with the fourth argument embedded.
makeConstructorApp fc fnName projName rhs cn cty =
  do i <- get
     delabArgs <- case lookupCtxtExact cn (idris_implicits i) of
                   Just args -> return args
                   Nothing -> ifail $ "No arguments for constructor " ++ show cn  
     args <- makeArgList fnName projName rhs cty delabArgs
     return $ PApp fc (PRef fc cn) args

{-| Creates a list of 'PArg' where a term is inserted
    in the position described by the left-hand side projection.
    Metavariables are inserted for the remaining arguments.

    If the constructor type is:
     (x : A) -> (y : B) -> C
    then
     &y foo = b
    will lead to the following arguments:
     [?foox, b]
-}
makeArgList :: Name -- ^ The name of the clause for which the argument list is created
               -> Name -- ^ The name of the projection for which the term should be inserted
               -> PTerm -- ^ The term to insert
               -> PTerm -- ^ The constructor type
               -> [PArg] -- ^ The delaborated args for the constructor
               -> Idris [PArg] -- ^ A list of arguments where the third argument is inserted in the position given by the second argument
makeArgList fnName projName t (PPi _ n _ b) (delabArg : das) =
  do iLOG $ "Will put " ++ show t ++ " when " ++ show (nsroot projName) ++ " and " ++ show n ++ " are equal"
     let metavarName = sUN $ show (nsroot fnName) ++ show (nsroot n)
     let metavar = PMetavar metavarName
     let term = if (nsroot projName) == n then t else metavar
     case makeArg term n delabArg of
       Just arg -> do args <- makeArgList fnName projName t b das
                      return $ arg : args 
       Nothing  -> makeArgList fnName projName t b das
makeArgList _ _ _ _ _ = return []


{-| 'makeArg' creates a new 'PArg' with the first
    argument as its term. Produces the same kind of
    'PArg' as the one given as the third argument.
-}
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

{-| Merges two lists of clauses with copatterns together,
    removing clauses with equivalent left-hand sides.
    Also, clauses which are fully contained by other
    clauses (subsumed) are removed.

    The following clauses:
     cycle : Nat -> Nat -> Stream Nat
     &hd cycle y _ = y
     &tl cycle Z n = cycle n n
     &tl cycle (S m) n = cycle m n
    will after expansion look like:
     cycle : Nat -> Nat -> Stream Nat
     cycle y _ = y :: ?cycletl
     cycle Z n = ?cyclehd :: cycle n n
     cycle (S m) n = ?cyclehd :: cycle m n
    and will then be merged to result in:
     cycle : Nat -> Nat -> Stream Nat
     cycle Z n = Z :: cycle n n
     cycle (S m) n = (S m) :: cycle m n
-}
mergeClauseList :: [PClause] -> Idris [PClause]
mergeClauseList clauses =
  do iLOG "Merging"
     i <- get
     let ctxt = tt_ctxt i
     -- 1. Get a list of pairs, pairing each clause with the rest of the clauses
     let singledOut = singleOut clauses
     -- 2. Remove equivalent clauses from the output
     iLOG $ "Before removing duplicates: " ++ intercalate ", "  (map show (mapMaybe clauseName (map fst singledOut)))
     let noDuplicates = nubBy (\(c,_) (c',_) -> clauseEq ctxt c c') singledOut
     iLOG $ "After removing duplicates: " ++ intercalate ", "  (map show (mapMaybe clauseName (map fst noDuplicates)))
     -- 3. Remove subsumed clauses
     resultingClauses <- removeSubsumed noDuplicates -- Move some logging in here
     iLOG $ "After removing subsumed: " ++ intercalate ", "  (map show (mapMaybe clauseName (map fst resultingClauses)))
     foldedClauses <- forM resultingClauses $ \(clause, other) -> foldM (\c o -> mergeClauses c o) clause other
     return foldedClauses
  where
    removeSubsumed :: [(PClause, [PClause])] -> Idris [(PClause, [PClause])]
    removeSubsumed [] = return []
    removeSubsumed [c] = return [c]
    removeSubsumed cs = filterM (\(c,other) -> (liftM not) $ isSubsumed c other) cs

    isSubsumed :: PClause -> [PClause] -> Idris Bool
    isSubsumed c other = allM (\c' -> clauseCompatible c' c) other


{-| 'singleOut' pairs each elements of a list
    with all the remaining elements of the list.
    > singleOut [1,2,3] == [(1,[2,3]),(2,[1,3]),(3,[1,2])]
-}
singleOut :: [a] -> [(a, [a])]
singleOut xs = singleOut' xs []
  where
    singleOut' :: [a] -> [a] -> [(a, [a])]
    singleOut' []       _  = []
    singleOut' (x : xs) ys = (x, xs ++ ys) : singleOut' xs (x : ys)

-- partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
-- partitionM p [] = return ([], [])
-- partitionM p (x:xs) =
--   do (ts, fs) <- partitionM p xs
--      p' <- p x
--      return $ if p' then (x:ts, fs) else (ts, x:fs)

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p [] = return True
allM p (x:xs) = let andM = liftM2 (&&) in p x `andM` allM p xs

{-| Replaces the right-hand side of the second argument with
    the first argument.
-}
replaceRhs :: PTerm -> PClause -> PClause
replaceRhs newrhs (PClause fc n lhs wis _ whs) = PClause fc n lhs wis newrhs whs
replaceRhs newrhs (PWith fc n lhs wis _ whs) = PWith fc n lhs wis newrhs whs
replaceRhs newrhs (PClauseR fc wis _ whs) = PClauseR fc wis newrhs whs
replaceRhs newrhs (PWithR fc wis _ whs) = PWithR fc wis newrhs whs

replaceWheres :: [PDecl] -> PClause -> PClause
replaceWheres newwheres (PClause fc n lhs wis rhs _) = PClause fc n lhs wis rhs newwheres
replaceWheres newwheres (PWith fc n lhs wis rhs _) = PWith fc n lhs wis rhs newwheres
replaceWheres newwheres (PClauseR fc wis rhs _) = PClauseR fc wis rhs newwheres
replaceWheres newwheres (PWithR fc wis rhs _) = PWithR fc wis rhs newwheres


mergeWheres :: PClause -> PClause -> PClause
mergeWheres l r =
  case (clauseWheres l, clauseWheres r) of
   ([], []) -> l
   (_, []) -> l
   ([], ys) -> replaceWheres ys l
   (xs, ys) -> replaceWheres (xs ++ ys) l
      

mergeClauses :: PClause -> PClause -> Idris PClause
mergeClauses l r
 | Just lhsl <- clauseLhs l,
   Just lhsr <- clauseLhs r
 = do let rhsl = clauseRhs l
      let rhsr = clauseRhs r
      compSet <- icompatible lhsl lhsr
      case compSet of
       Just cs -> do iLOG $ "Substitutions (" ++ show lhsl ++ ", " ++ show lhsr ++ ") : " ++ intercalate ", " (map show cs)
                     mergedRhs <- merge rhsl (subst cs rhsr)
                     return $ mergeWheres (replaceRhs mergedRhs l) r
       Nothing -> return l
 | otherwise = return l

type Substitution = (Name, PTerm)

subst :: [Substitution] -> PTerm -> PTerm
subst subs t = mapPT (subst' subs) t
  where
    subst' subs t@(PRef _ n)
      | Just t' <- lookup n subs = t'
      | otherwise = t
    subst' subs t@(PLam fc x ty body)
      | isJust $ lookup x subs = t
      | otherwise = PLam fc x (subst' subs ty) (subst' subs body)
    subst' subs t@(PPi pl n a b)
      | isJust $ lookup n subs = t
      | otherwise = PPi pl n (subst' subs a) (subst' subs b)
    subst' subs t@(PLet fc x ty e b)
      | isJust $ lookup x subs = t
      | otherwise = PLet fc x (subst' subs ty) (subst' subs e) (subst' subs b)
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
  case (clauseLhs c, clauseLhs c') of
    (Just t, Just t') -> liftM isJust $ icompatible t t'
    _                 -> return False

{-| Antisymmetry for clauses
-}
clauseEq :: Context -> PClause -> PClause -> Bool
clauseEq ctxt clause clause'
  | Just c  <- clauseLhs clause,
    Just c' <- clauseLhs clause' = isJust (compatible ctxt c c') && isJust (compatible ctxt c' c)
  | otherwise                    = False


icompatible :: PTerm -> PTerm -> Idris (Maybe [Substitution])
icompatible x y = do i <- get
                     return $ compatible' (tt_ctxt i) x y []

{- |
 Tests whether two terms are compatible, and returns
 a list of necessary substitutions if they are.
 Two terms are compatible if the third argument
 is more general than the second argument (i.e. the second
 argument has more specific patterns)
-}
compatible :: Context -> PTerm -> PTerm -> Maybe [Substitution]
compatible ctxt x y = fmap reverse (compatible' ctxt x y [])

compatible' :: Context -> PTerm -> PTerm -> [Substitution] -> Maybe [Substitution]
compatible' ctxt t@(PRef _ n) (PRef _ n') subs =
  let sub = (n', t)
  in case (isConName n ctxt, isConName n' ctxt) of
       (True,  True)  -> if n == n' then return subs else Nothing
       (True,  False) -> return $ sub : subs
       (False, True)  -> Nothing
       (False, False) -> return $ if n == n' then subs else sub : subs
compatible' _ (PRef _ _) Placeholder subs = return subs
compatible' _ (PRef _ _) (PApp _ _ _) _ = Nothing
compatible' ctxt Placeholder (PRef _ n) subs
 | isConName n ctxt = Nothing
 | otherwise        = return subs
compatible' _ Placeholder Placeholder subs = return subs
compatible' _ Placeholder (PApp _ _ _) _ = Nothing
compatible' ctxt t@(PApp _ _ _) (PRef _ n) subs
 | isConName n ctxt = Nothing
 | otherwise        = return $ (n, t) : subs
compatible' _ (PApp _ _ _) Placeholder subs = return subs
compatible' ctxt (PApp _ (PRef _ n) args) (PApp _ (PRef _ n') args') subs
 | n == n'   = compatibleArgLists ctxt args args' subs
 | otherwise = Nothing
compatible' _ _ _ _ = Nothing

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

compatibleArgLists :: Context -> [PArg] -> [PArg] -> [Substitution] -> Maybe [Substitution]
compatibleArgLists ctxt (a : args) (a' : args') subs = 
  do subs' <- compatibleArgs ctxt a a' subs
     compatibleArgLists ctxt args args' subs'
compatibleArgLists _ [] [] subs = return subs
compatibleArgLists _ [] (_:_) _ = Nothing
compatibleArgLists _ (_:_) [] _ = Nothing  

compatibleArgs :: Context -> PArg -> PArg -> [Substitution] -> Maybe [Substitution]
compatibleArgs ctxt (PExp _ _ _ t) (PExp _ _ _ t') subs = compatible' ctxt t t' subs
compatibleArgs ctxt (PImp _ _ _ _ t) (PImp _ _ _ _ t') subs = compatible' ctxt t t' subs
compatibleArgs ctxt (PConstraint _ _ _ t) (PConstraint _ _ _ t') subs = compatible' ctxt t t' subs
compatibleArgs ctxt (PTacImplicit _ _ _ _ t) (PTacImplicit _ _ _ _ t') subs = compatible' ctxt t t' subs
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
mergeArgTerms (PMetavar _) t            = return t
mergeArgTerms t            (PMetavar _) = return t
mergeArgTerms l@(PApp fc (PRef _ n) args) r@(PApp fc' (PRef _ n') args') =
  merge l r
mergeArgTerms xs ys = return xs

clauseName :: PClause -> Maybe Name
clauseName (PClause _ n _ _ _ _) = Just n
clauseName (PWith _ n _ _ _ _) = Just n
clauseName _ = Nothing

clauseLhs :: PClause -> Maybe PTerm
clauseLhs (PClause _ _ app _ _ _) = Just app
clauseLhs (PWith _ _ app _ _ _) = Just app
clauseLhs _ = Nothing

clauseRhs :: PClause -> PTerm
clauseRhs (PClause _ _ _ _ rhs _) = rhs
clauseRhs (PWith _ _ _ _ rhs _) = rhs
clauseRhs (PClauseR _ _ rhs _) = rhs
clauseRhs (PWithR _ _ rhs _) = rhs

clauseWheres :: PClause -> [PDecl]
clauseWheres (PClause _ _ _ _ _ wheres) = wheres
clauseWheres (PWith _ _ _ _ _ wheres) = wheres
clauseWheres (PClauseR _ _ _ wheres) = wheres
clauseWheres (PWithR _ _ _ wheres) = wheres
