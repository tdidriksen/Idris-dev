\documentclass{article}
%include polycode.fmt
\begin{document}
This file documents the translation from TT to a guarded recursion calculus with clocks, GR.

\begin{code}
{-# LANGUAGE PatternGuards #-}
module Idris.GuardedRecursion.GR(checkGuardedRecursive) where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Typecheck
import Idris.Core.Evaluate

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Control.Monad
import Control.Monad.State.Strict as State
import Control.Monad.State.Lazy as LazyState

import Data.List
\end{code}


\begin{code}
laterName :: Name
laterName = sNS (sUN "Later") ["GuardedRecursion"]

laterRef :: Name -> Idris Term
laterRef n =
  do ctxt <- getContext
     -- case lookupTyName laterName ctxt of
     --  names -> ifail $ "When checking " ++ show n ++ " Later names: " ++ intercalate ", " (map (show . fst) names)
     case lookupP laterName ctxt of
      [laterP] -> return laterP
      _ -> ifail "Later type does not exist!"
     -- case lookupDef laterName ctxt of
     --  [TyDecl tcon@(TCon _ _) ty] -> return $ P tcon laterName ty
     --  [def] -> ifail $ "Def for Later: " ++ show def
     --  xs -> ifail $ "LaterDef: " ++ intercalate ", " (map show xs) --ifail "Later type does not exist!"case lookupP laterName ctxt of
--      [laterP] -> return laterP
--      _ -> ifail "Later type does not exist!"

nextName :: Name
nextName = sNS (sUN "Next") ["GuardedRecursion"]

nextRef :: Idris Term
nextRef =
  do ctxt <- getContext
     case lookupDef nextName ctxt of
      [TyDecl dcon@(DCon _ _ _) ty] -> return $ P dcon nextName ty
      _ -> ifail "Data constructor Next does not exist!"

applyNext :: Term -> Idris Term
applyNext t =
  do next <- nextRef
     return $ App next t

composeName :: Name
composeName = sNS (sUN "compose") ["GuardedRecursion"]

composeRef :: Idris Term
composeRef =
  do ctxt <- getContext
     case lookupTyExact composeName ctxt of
      Just ty -> return $ P Ref composeName ty
      Nothing -> ifail "Function 'compose' does not exist!"

applyCompose :: Term -> Term -> Idris Term
applyCompose f arg =
  do compose <- composeRef
     return $ App (App compose f) arg 

checkGuardedRecursive :: Name -> Idris Totality
checkGuardedRecursive n =
  do ctxt <- getContext
     case lookupDef n ctxt of
        [CaseOp _ _ _ _ clauses _] ->
          do --evalStateT (buildGR n clauses) emptyGEnv
             _ <- fixFunction n clauses
             
             return $ Partial NotProductive
        _ -> return $ Partial NotProductive

fixFunction :: Name -> [([Name], Term, Term)] -> Idris [([Name], Term, Term)]
fixFunction n clauses =
  do forM_ clauses $ \(pvs, lhs, rhs) ->
       do iLOG $ show ("GR_LHS: " ++ showEnvDbg [] lhs)
          iLOG $ show ("GR_RHS: " ++ showEnvDbg [] rhs)
     ctxt <- getContext
     ty <- case lookupTyExact n ctxt of
            Just ty' -> return ty'
            Nothing -> ifail "Seemingly defined function has no definition"
     recRef <- recursiveRef n ty
     let replaceRec = subst n recRef
     let recsReplaced = map (\(pvs,lhs,rhs) -> (pvs,lhs,replaceRec rhs)) clauses
     forM_ recsReplaced $ \(_,_,rhs) -> iLOG $ "GR " ++ show n ++ " after subst: " ++ (showEnvDbg [] rhs)
     return recsReplaced

applyLater :: Name -> Type -> Idris Type
applyLater n ty =
  do later <- laterRef n
     return $ App later ty

unapplyLater :: Type -> Either Type (Type, Type)
unapplyLater ty@(App f x)
  | isLater f = Right (f, x)
unapplyLater ty = Left ty

recursiveRef :: Name -> Type -> Idris Type
recursiveRef name ty =
  do laterType <- applyLater name ty
     return $ P Ref (sMN 0 (show name ++ "_rec")) laterType


-- stripLaters :: Type -> (Int, Type)
-- stripLaters (App (P (DCon _ _ _) n@(NS (UN later) [gr])) ty) =
--   | later == txt "Later" && gr == txt "GuardedRecursion" =
--       let (i, ty') = stripLaters ty in (1 + i, ty')
--   | otherwise = (0, ty)
-- stripLaters ty = (0, ty)

stripLaters :: Type -> Type
stripLaters (App f x)
  | isLater f = stripLaters x
stripLaters ty = ty

isLater :: Type -> Bool
isLater (P (DCon _ _ _) (n@(NS (UN later) [gr])) ty)
  | later == txt "Later" && gr == txt "GuardedRecursion" = True
isLater _ = False

isLaterApp :: Type -> Bool
isLaterApp (App f x)
  | isLater f = True
isLaterApp _ = False

data Availability =
    Now
  | Later Availability
  deriving Eq

instance Ord Availability where
  compare Now Now = EQ
  compare Now (Later _) = LT
  compare (Later _) Now = GT
  compare (Later x) (Later y) = compare x y

availability :: Type -> Availability
availability ty
  | Right (_, x) <- unapplyLater ty = Later (availability x)
availability _ = Now

delayBy :: Availability -> Availability -> Availability
delayBy Now a = a
delayBy (Later a) b = delayBy a (Later b)

-- compareAvailability :: Type -> Type -> Ordering
-- compareAvailability a b
--   | Left a' <- unapplyLater a,
--     Left b' <- unapplyLater b       = EQ
--   | Left _ <- unapplyLater a,
--     Right _ <- unapplyLater b       = LT
--   | Right _ <- unapplyLater a,
--     Left _ <- unapplyLater b        = GT
--   | Right (_, ax) <- unapplyLater a,
--     Right (_, bx) <- unapplyLater b = compareAvailability ax bx

before :: Type -> Type -> Bool
before ty ty' = (availability ty) < (availability ty')

after :: Type -> Type -> Bool
after = undefined

congruentWith :: Type -> Type -> Bool
congruentWith = undefined

guardedDataConstructor :: Name -> Idris Term
guardedDataConstructor = undefined

guardedRef :: Name -> Idris Term
guardedRef = undefined

substFreeNames :: Term -> Idris Term
substFreeNames tm = undefined

typeOf :: Term -> Env -> Idris Type
typeOf t env =
  do ctxt <- getContext
     case check ctxt env (forget t) of
      OK (_,t') -> return t'
      Error e -> ierror e

checkGoal :: Term -> Type -> Env -> Idris Bool
checkGoal tm goal env =
  do tmType <- typeOf tm env
     ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env tmType goal) (0, ucs) of
      tc -> case tc of
              OK () -> return True
              _ -> return False
      
\end{code}

We now define the function 'epsilon' which builds guarded recursive terms from TT terms. The first is the starting point for the transformation, and the second argument is the target type. The target type denotes the desired type of the built term. If we cannot build a guarded recursive term of the desired type, the algorithm aborts.
\begin{code}
epsilon :: Term -> Availability -> Env -> Idris Term
epsilon p@(P Bound n a) goal env =
  do case compare (availability a) goal of
      EQ -> return p
      LT -> applyNext p
      GT -> ifail $ "Term " ++ show p ++ " is available too late."
epsilon (P Ref n a) goal env =
  do gRef@(P Ref n' a') <- guardedRef n
     case compare (availability a') goal of
      EQ -> return gRef
      LT -> applyNext gRef
      GT -> ifail $ "Term " ++ show gRef ++ " is available too late."
epsilon (P (DCon _ _ _) n a) goal env =
  do gDCon@(P (DCon _ _ _) n' a') <- guardedDataConstructor n
     case compare (availability a') goal of
      EQ -> return gDCon
      LT -> applyNext gDCon
      GT -> ifail $ "Term " ++ show gDCon ++ " is available too late."
epsilon p@(P (TCon _ _) n a) goal env =
  return p
epsilon (Bind n binder sc) goal env =
  epsilon sc goal ((n, binder) : env)
epsilon app@(App f x) goal env =
  do feps <- epsilon f goal env -- f is now later according to goal
     ftype <- typeOf feps env -- get type of built function
     let fArgTys = map snd $ getArgTys (stripLaters ftype)
     let fRetTy = getRetTy $ stripLaters ftype
     let fFirstArg = head fArgTys -- If this fails, f is not a function!
     xeps <- epsilon x (delayBy goal (availability fFirstArg)) env
     case (goal, availability fRetTy) of
      (Now, Now) -> return $ App feps xeps
      (Now, Later _) -> ifail $ "Term " ++ show app ++ " is available too late"
      (Later _, Now) -> applyCompose feps xeps
      (Later _, Later _) -> return $ App feps xeps
epsilon tm _ _ = return tm

--epsilon :: Term -> Type -> Env -> Magic
--epsilon p@(P Bound n a) b = return p
--epsilon 
-- epsilon :: Term -> Type -> Magic
-- epsilon p@(P Bound n a) goalTy = eps p a goalTy
-- epsilon p@(P Ref n a) goalTy =
--   do gTy <- guardedType n
--      eps (P Ref n gTy) gTy goalTy
-- epsilon p@(P (DCon _ _ _) n a) goalTy = guardedDataConstructor n
-- epsilon p@(P (TCon _ _ _) n a) goalTy = return p

-- epsilon tm goalTy env =
--   do goalReached <- checkGoal app goalTy env
--      case goalReached of
--       True  -> return tm
--       False -> check tm goalTy env

-- build :: Term -> Availability -> Env -> Idris Term
-- build p@(P Ref n a) goal env =
--   do pref@(P Ref n' gTy) <- guardedRef n
--      case compare (availability gTy) goal of
--       EQ -> return pref
--       LT -> return $ build applyNext goal env
--       GT -> ifail $ "Term " ++ show p ++ " is available too late."
-- build app@(App f x) goal env =
  
  
--   do let (f, args) = unApply app
--      let retTy = getRetTy f
--      case compare (availability retTy) goal of
--       LT -> do nextedf <- build f goal env
--                return $ build (mkApp nextedf args) goal env
--       GT -> ifail $ "Term " ++ show app ++ " is available too late."
--       EQ ->
--   where
--     applyNexts :: Term -> Idris Term

-- infer :: Term -> Env -> Idris Term
-- infer (P (DCon _ _ _) n a) env = guardedDataConstructor n
-- infer t _ = return t

-- check :: Term -> Type -> Env -> Idris Term
-- check (P Ref n a) goal env =
--   do pref@(P Ref n' gTy) <- guardedRef n
--      case compare (availability gTy) (availability goal) of
--       EQ -> return pref
--       LT -> epsilon (applyNext pref) goal env
--       GT -> ifail "Term " ++ show p ++ " is available too late."
-- check app@(App f x) goal env =
--   do let gAvail = availability goal
--      let (f, args) = unApply app
--      let retTy = getRetTy f
--      let retTyAvail = availability retTy

--   where
--     delay tm ty
--       | availability ty < gAvail = applyNext ty
 

--      let (f, args) = unApply app
--      checkedf <- check f goal env
--      let argTys = getArgTys checkedf
--      let retTy = getRetTy checkedf
--      epsArgs <- mapM (\(arg, argGoal) -> (epsilon arg argGoal, (availability argGoal)) (zip args argTys))
--      buildApp checkedf (availability goal) epsArgs
--   where
--     buildApp :: Term -> [(Term, Type)] -> Term
--     buildApp f ((arg, argGoal) : args) =
--       do case compare (availability goal) (availability argGoal) of
          
     
--check t _ _ = return t

     --  appTy <- typeOf app env
     -- case compare (availability appTy) (availability goal) of
     --  EQ -> epsilon (App f x) goal env
     --  LT -> 
  
     -- feps <- epsilon f'

--      eps (availability fty) (availability xty)
--   where
--     eps Now Now =

-- buildCompose :: Term -> Type -> Idris Term
-- buildCompose (App f x) goalType =
--   | f `before` x = 

-- analyze :: Term -> Idris Term
-- analyze p@(P Bound n a) = return p
-- analyze (P Ref n a) =
--   do gTy <- guardedType n
--      return $ P Ref n gTy
-- analyze (P (DCon _ _ _) n a) = guardedDataConstructor n
-- analyze p@(P (TCon _ _ _) n a) = return p
-- analyze (Bind n binder tm) =
--   do tm' <- analyze tm
--      return $ Bind n binder tm'
-- analyze (App f x) =
--   do f' <- analyze f
--      x' <- analyze x
--      return $ App f' x'
-- analyze t = return t
     

-- eps :: Term -> Type -> Type -> Idris Term
-- eps tm tmTy goalTy = eps' tm tmTy goalTy (compareAvailability tmTy goalTy)

-- eps' :: Term -> Type -> Type -> Ordering -> Idris Term
-- eps' p@(P Bound n a) b EQ = return p
-- eps' p@(P Bound n a) b GT = ifail "Term " ++ show p ++ " is available too late."
-- eps' p@(P Bound n a) b LT = return $ applyNext p
  

-- checkGR :: Term -> Type -> Idris Bool
-- checkGR 
      
-- epsilon (P Ref x2 x3) y = _epsilon_body
-- epsilon (P (DCon { nt_tag = x1_nt_tag, nt_arity = x1_nt_arity, nt_unique = x1_nt_unique }) x2 x3) y = _epsilon_body
-- epsilon (P (TCon { nt_tag = x1_nt_tag, nt_arity = x1_nt_arity }) x2 x3) y = _epsilon_body
-- epsilon (V x) y = _epsilon_body
-- epsilon (Bind (UN x1) x2 x3) y = _epsilon_body
-- epsilon (Bind (NS x11 x12) x2 x3) y = _epsilon_body
-- epsilon (Bind (MN x11 x12) x2 x3) y = _epsilon_body
-- epsilon (Bind NErased x2 x3) y = _epsilon_body
-- epsilon (Bind (SN x1) x2 x3) y = _epsilon_body
-- epsilon (Bind (SymRef x1) x2 x3) y = _epsilon_body
-- epsilon (App x1 x2) y = _epsilon_body
-- epsilon (Constant x) y = _epsilon_body
-- epsilon (Proj x1 x2) y = _epsilon_body
-- epsilon Erased y = _epsilon_body
-- epsilon Impossible y = _epsilon_body
-- epsilon (TType x) y = _epsilon_body
-- epsilon (UType x) y = _epsilon_body

  -- Hent type
  -- Lav Later-postulat til rekursiv reference
  -- Analyser:
    -- Hvis DCON: udskift
    -- Hvis rekursiv reference: udskift
    --
       
\end{code}


\end{document}
