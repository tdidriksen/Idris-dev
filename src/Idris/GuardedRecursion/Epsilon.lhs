\documentclass{article}
%include polycode.fmt
\begin{document}

\begin{code}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Epsilon where
import Idris.Core.TT
import Idris.AbsSyntaxTree
import Idris.Error
import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Helpers
import Control.Monad
epsFail tm msg = ifail $ "Cannot build guarded recursive term from term " ++ show tm ++ ": " ++ msg
\end{code}

\begin{code}
epsilon :: Name -> Term -> Type -> Idris Term
epsilon recName t a = epsilonCheck EmptyClock recName [] t a
epsilonCheck :: Clock -> Name -> Env -> Term -> Type -> Idris Term
-- Check next
epsilonCheck Kappa recName env (unapplyNext -> Just t) (unapplyLater -> Just a) =
  do nexted <- epsilonCheck Kappa recName env t a
     applyNext nexted
-- Next error cases
epsilonCheck _ recName env tm@(unapplyNext -> Just t) (unapplyLater -> Nothing) =
  epsFail tm "Next application occurred outside later context."
epsilonCheck EmptyClock recName env tm@(unapplyNext -> Just t) _ =
  epsFail tm "Next application with empty clock environment."
  
-- Check forall (clock abstraction)
epsilonCheck EmptyClock recName env (unapplyLambdaKappa -> Just t) (unapplyForall -> Just a) =
  do freeClockTm <- epsilonCheck Kappa recName env t a
     applyLambdaKappa freeClockTm
-- Forall error cases
epsilonCheck Kappa recName env tm@(unapplyLambdaKappa -> Just t) (unapplyForall -> Just a) =
  epsFail tm "Clock abstraction in context with open clock."
epsilonCheck _ recName env tm@(unapplyLambdaKappa -> Just t) (unapplyForall -> Nothing) =
  epsFail tm "Clock abstraction not expected to have Forall type."
  
-- Check apply (clock application)
epsilonCheck Kappa recName env (unapplyApply -> Just t) a@(unapplyForall -> Nothing) =
  do forallA <- applyForall a
     unappliedTm <- epsilonCheck EmptyClock recName env t forallA
     applyApply unappliedTm
epsilonCheck EmptyClock recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Nothing) =
  epsFail tm "Clock application with empty clock environment."
epsilonCheck _ recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Just _) =
  epsFail tm "Expected forall type as result of clock application."
  
-- Check fix (by nexting recursive reference)
epsilonCheck Kappa recName env p@(P Ref refn pty) (unapplyLater -> Just a) | refn == recName =
  do recRef <- epsilonCheck Kappa recName env p a
     applyNext recRef
-- Fix error cases
epsilonCheck EmptyClock recName env p@(P Ref refn pty) (unapplyLater -> Just a) | refn == recName =
  epsFail p "Accessing recursive reference with empty clock context."
epsilonCheck _ recName env p@(P Ref refn pty) (unapplyLater -> Nothing) | refn == recName =
  epsFail p "Recursive reference not expected to be available later."
  
-- Check tensor
epsilonCheck Kappa recName env (unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Just b') =
  do fType <- typeOf f env
     laterA <- applyLater' a
     fChecked <- epsilonCheck Kappa recName env f fType
     argChecked <- epsilonCheck Kappa recName env arg laterA
     applyCompose a b av fChecked argChecked
-- Tensor error cases
epsilonCheck EmptyClock recName env t@(unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Just b') =
  epsFail t "Compose application with empty clock environment."
epsilonCheck _ recName env t@(unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Nothing) =
  epsFail t "Compose application not expected to be available later."
-- Binders
epsilonCheck clock recName env (Bind n binder sc) (debindFirstArg -> Just a) =
  do bindEps <- epsilonCheck clock recName ((n, binder):env) sc a
     return $ Bind n binder bindEps
     
-- Conversion check to see if term already has the required type.
-- If not, try to infer a term that does.
epsilonCheck clock recName env t a =
  do t' <- guardedTerm t
     ok <- checkGoal t' a env
     if ok
      then return t'
      else epsilonInfer clock recName env t' a
\end{code}


\begin{code}
epsilonInfer :: Clock -> Name -> Env -> Term -> Type -> Idris Term
\end{code}

Infer tensor

K,G |- eps f : Later' (A -> B)    K,G |- eps x : Later' A
---------------------------------------------------------
        K,G |- eps (f tensor x) : Later' A

\begin{code}
epsilonInfer Kappa recName env app@(App f x) a | Just a' <- unapplyLater a, Just _ <- unapplyLater a' =
  do appNext <- applyNext app
     epsilonCheck Kappa recName env appNext a'
epsilonInfer Kappa recName env (App f x) b | Just b' <- unapplyLater b, Nothing <- unapplyLater b' =
  do fType <- typeOf f env
     let fNowType = nowType fType
     a <- firstArg fNowType
     laterA <- applyLater' a
     laterAtoB <- applyLater' fNowType
     fEps <- epsilonCheck Kappa recName env f laterAtoB
     xEps <- epsilonCheck Kappa recName env x laterA
     now <- nowRef
     composeApp <- applyCompose a b' now fEps xEps
     epsilonCheck Kappa recName env composeApp b
  where
    firstArg :: Type -> Idris Type
    firstArg ty =
      case getArgTys (nowType ty) of
       []    -> epsFail ty "Is not a function type."
       ((_,x):_) -> return x
\end{code}

Infer next

K,G |- eps t : A
----------------------
K,G |- eps (Next t) : Later' A
\begin{code}
epsilonInfer Kappa recName env t a@(unapplyLater -> Just a') =
  do tEps <- epsilonCheck Kappa recName env t a'
     tNext <- applyNext tEps
     epsilonCheck Kappa recName env t a
\end{code}

Infer forall

K,G |- eps t : A
-----------------
E,G |- eps (lambdaKappa t) : forall A
\begin{code}
epsilonInfer EmptyClock recName env t a@(unapplyForall -> Just a') =
  do tEps <- epsilonCheck Kappa recName env t a'
     tLambdaKappa <- applyLambdaKappa tEps
     epsilonCheck EmptyClock recName env tLambdaKappa a
\end{code}

Infer clock application

E, G |- eps t : forall A
-----------------------
K, G |- eps (apply t) : A (A not forall.A, since only one clock)
\begin{code}
epsilonInfer Kappa recName env t a@(unapplyForall -> Nothing) =
  do forallA <- applyForall a
     tEps <- epsilonCheck EmptyClock recName env t forallA
     tApply <- applyApply tEps
     epsilonCheck Kappa recName env tApply a
\end{code}

\begin{code}
epsilonInfer clock recName env app@(App f x) a =
  do let (f', args) = unApply app
     f'Type <- typeOf f' env
     let argTys = map snd $ getArgTys f'Type
     argEps <- forM (zip args argTys) $ \(arg, argTy) ->
                do delayedType <- delayBy a argTy
                   epsilonCheck clock recName env arg delayedType
     epsilonCheck clock recName env (mkApp f' argEps) a
     
\end{code}

\begin{code}
epsilonInfer _ _ _ t a = epsFail t $ "Could not infer a guarded recursive term from type" ++ show a
\end{code}






-- \begin{code}

-- epsilon :: Clock -> Name -> Env -> Term -> Type -> Idris Term
-- \end{code}

-- Quantification over clocks
-- \begin{code}
-- -- User-supplied \Kappa
-- epsilon EmptyClock recName env (unapplyLambdaKappa -> Just tm) (unapplyForall -> Just ty) =
--   do body <- epsilon Kappa recName env tm ty
--      applyLambdaKappa body
-- -- Inferred \Kappa
-- epsilon EmptyClock recName env tm (unapplyForall -> Just ty) =
--   do body <- epsilon Kappa recName env tm ty
--      applyLambdaKappa body
-- -- Error: Forall under forall
-- epsilon Kappa _ _ tm (unapplyForall -> Just ty) =
--   epsFail tm "Attempt to open more than one clock."
-- \end{code}

-- Free variables
-- \begin{code}
-- -- Inferred recursive reference - The user cannot put the 'next' him/herself!
-- epsilon Kappa recName env p@(P Ref n _) (unapplyLater -> Just ty) | n == recName =
--   do recursiveRef <- epsilon Kappa recName env p ty
--      applyNext recursiveRef
-- -- Error: Recursive reference is not expected to be available later.
-- epsilon _ recName env p@(P Ref n _) (unapplyLater -> Nothing) | n == recName =
--   epsFail p "Attempt to build recursive reference outside a later context."

-- -- Inferred next on free variable
-- epsilon Kappa recName env p@(P Ref n (unapplyLater -> Nothing)) (unapplyLater -> Just goal) =
--   do ref <- epsilon Kappa recName env p goal
--      applyNext ref
-- -- Recursively remove later from free variables
-- epsilon Kappa recName env (P Ref n (unapplyLater -> Just pty)) (unapplyLater -> Just goal) =
--   epsilon Kappa recName env (P Ref n pty) goal
-- -- Error: Free variable is unexpectedly later
-- epsilon _ recName env p@(P Ref n (unapplyLater -> Just _)) (unapplyLater -> Nothing) =
--   epsFail p "Free variable is available too late."

-- epsilon Kappa recName env p@(P Ref n (unapplyForall -> Just pty)) goal
--   | Nothing <- unapplyForall goal =
--       do applyp <- applyApply p
--          epsilon Kappa recName env applyp goal
--   | Just goal' <- unapplyForall goal =
--       epsilon Kappa recName env (P Ref n pty) goal'
     
-- \end{code}

-- Bound variables
-- \begin{code}

-- \end{code}

-- Data constructors
-- \begin{code}

-- \end{code}

-- Type constructors
-- \begin{code}

-- \end{code}

-- Binders
-- \begin{code}
-- -- Binders add variables to the context
-- epsilon clock recName env (Bind n binder sc) goal =
--   epsilon clock recName ((n, binder):env) sc goal

-- \end{code}

-- Application
-- \begin{code}

-- \end{code}


-- Catch-all
-- \begin{code}
-- -- No rules apply, do nothing
-- epsilon _ _ _ tm _ = return tm

"The bin"
\begin{code}
-- epsilonInfer Kappa recName env p@(P Bound n pty) (unapplyLater -> Just a)
--   | Nothing <- unapplyLater pty,
--     Nothing <- unapplyForall pty =
--       do p' <- epsilonCheck Kappa recName env p a
--          applyNext p'
-- epsilonInfer Kappa recName env p@(P Ref n pty) (unapplyLater -> Just a) =
--   do gref@(P Ref n' pty') <- guardedRef n -- guardedRef :: Term -> Idris (Maybe Term)
--      inferFromGuardedRef gref
--   where
--     inferFromGuardedRef (P Ref n'' (unapplyLater -> Just pty'')) =
--       epsilonCheck Kappa recName env (P Ref n'' pty'') a
--     inferFromGuardedRef p'@(P Ref n'' (unapplyLater -> Nothing)) =
--       do ref <- epsilonCheck Kappa recName env p' a
--          applyNext ref
--     inferFromGuardedRef tm = epsFail tm ("Tried to infer from Ref, but got " ++ show tm) 
-- epsilonInfer Kappa recName env (P (DCon _ _ _) n pty) (unapplyLater -> Just a) =
--   do gdcon <- guardedDataConstructor n
--      epsDCon <- epsilonCheck Kappa recName env gdcon a
--      applyNext epsDCon
-- epsilonInfer _ _ _ p@(P (TCon _ _) _ _) _ = return p
-- epsilonInfer Kappa recName env app@(App f x) goal@(unapplyLater -> Just a) =
--   do fType <- typeOf f env
--      xType <- typeOf x env
     
-- epsilonInfer Kappa recName env p (unapplyLater -> Just a) =
--   do p' <- epsilonCheck Kappa recName env p a
--      applyNext p'
-- epsilonInfer EmptyClock recName env p@(P Bound n pty) (unapplyForall -> Just a)
--   | Nothing <- unapplyLater pty,
--     Nothing <- unapplyForall pty =
--       do p' <- epsilonCheck Kappa recName env p a
--          applyLambdaKappa p'
-- epsilonInfer EmptyClock recName env p@(P Ref n pty) (unapplyForall -> Just a) =
--   do gref@(P Ref n' pty') <- guardedRef n -- guardedRef :: Term -> Idris (Maybe Term)
--      inferFromGuardedRef gref
--   where
--     inferFromGuardedRef (P Ref n'' (unapplyForall -> Just pty'')) =
--       epsilonCheck Kappa recName env (P Ref n'' pty'') a
--     inferFromGuardedRef p'@(P Ref n'' (unapplyForall -> Nothing)) =
--       do ref <- epsilonCheck Kappa recName env p' a
--          applyLambdaKappa ref
--     inferFromGuardedRef tm = epsFail tm ("Tried to infer from Ref, but got " ++ show tm) 
-- epsilonInfer EmptyClock recName env (P (DCon _ _ _) n pty) (unapplyForall -> Just a) =
--   do gdcon <- guardedDataConstructor n
--      epsDCon <- epsilonCheck Kappa recName env gdcon a
--      applyLambdaKappa epsDCon
-- epsilonInfer EmptyClock recName env app@(App f x) (unapplyForall -> Just a) =
--   do appType <- typeOf app env
--      case unapplyForall appType of
--       Just forallAppType -> return app
--       Nothing            -> do fType <- typeOf f env
--                                xType <- typeOf x env
--                                fChecked <- epsilonCheck Kappa recName env f fType
--                                xChecked <- epsilonCheck Kappa recName env x xType
--                                applyLambdaKappa (App fChecked xChecked)
-- epsilonInfer EmptyClock recName env p (unapplyForall -> Just a) =
--   do p' <- epsilonCheck Kappa recName env p a
--      applyLambdaKappa p'
\end{code}

\end{document}
