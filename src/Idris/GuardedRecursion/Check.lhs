\documentclass{article}
%include polycode.fmt
\long\def\ignore#1{}
\begin{document}

\ignore{
\begin{code}

{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Check(checkGR) where

import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.Typecheck hiding (check)

import Idris.AbsSyntax

import Idris.GuardedRecursion.Error
import Idris.GuardedRecursion.Helpers

import Control.Monad.State.Lazy as LazyState hiding (fix)

checkGR :: Env -> (Name, Type) -> Term -> Type -> Idris Totality
checkGR = check Closed
                         
\end{code}
}
\begin{code}
check :: Clock -> Env -> (Name, Type) -> Term -> Type -> Idris Totality
check Open g (n, ty) (recursiveRef n -> Extracted t) a =
  do a' <- laterThan g ty a
     check Open g (n, ty) t a
check _ _ (n, ty) (recursiveRef n -> _) _ = return $ Partial NotProductive
\end{code}
\[\frac { \sqcup ;\Gamma \quad \vdash \quad A\quad :\quad Type\quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \quad \vdash \quad \forall \kappa .A\quad :\quad Type }\]
\begin{code}
check Closed g n (forallK -> Extracted a) t@(TType _)
  = check Open g n a t
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad A\quad :\quad Type }{ \sqcup ;\Gamma \quad \vdash \quad \rhd A\quad :\quad Type }
\]
\begin{code}
check Open g n (later -> Extracted a) t@(TType _)
  = check Open g n a t
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad t\quad :\quad A }{ \sqcup ;\Gamma \quad \vdash \quad next\quad (t)\quad :\quad \rhd A }
\]
\begin{code}
check Open g n (next -> Extracted t) (later -> Extracted a) 
  = check Open g n t a
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad t\quad :\quad \rhd (A\quad \rightarrow \quad B)\quad \quad \sqcup ;\Gamma \quad \vdash \quad u\quad :\quad \rhd A }{ \sqcup ;\Gamma \quad \vdash \quad t\quad \circledast \quad u\quad :\quad \rhd B }
\]
\begin{code}
check Open g n (tensor -> Extracted (t, u)) (later -> Extracted b) =
  do ty <- typeOf t g
     atob <- unlater ty
     a <- debind atob
     check Open g n u =<< laterK a
     check Open g n t =<< laterK atob
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad A\quad :\quad Type\quad \quad \sqcap ;\Gamma ,\Gamma '\quad \vdash \quad t\quad :\quad \forall \kappa .A\quad \quad nofc(\Gamma ) }{ \sqcup ;\Gamma ,\Gamma '\quad \vdash \quad apply\quad (t)\quad :\quad A }
\]
\begin{code}
check Open g n (apply -> Extracted t) a
  = do aTy <- typeOf a g
       case aTy of
         (TType _) -> do forallA <- forall a
                         check Closed g n t forallA
         _ -> return $ Partial NotProductive
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad t\quad :\quad A\quad \quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \quad \vdash \quad \Lambda \kappa .t\quad :\quad \forall \kappa .A } 
\]
\begin{code}
check Closed g n (lambdaKappa -> Extracted t) (forallK -> Extracted a) 
  = check Open g n t a
-- Not GR
check d g n (App t t') b =
  do ty <- typeOf t g
     a <- debind ty
     check d g n t ty
     check d g n t' a
check d g n (Bind n' b t) a =
  check d ((n', b) : g) n t a
check d g n (P _ _ ty) a =
  ifM (cEq g ty a)
      (return $ Total [])
      (return $ Partial NotProductive)
check _ _ _ t a = do iLOG $ "Guarded recursion catch all hit with \n" ++ show t ++ "\n of type \n" ++ show a
                     return $ Partial NotProductive
\end{code}
\ignore{
\begin{code}
next :: Term -> Extract Term
next (unapplyNext -> Just t) = return t
next _ = Nope

later :: Type -> Extract Type
later (unapplyLater -> Just a) = return a
later _ = Nope

unlater :: Type -> Idris Type
unlater (unapplyLater -> Just a) = return a
unlater _ = translateError Undefined

laterK :: Type -> Idris Type
laterK = applyLater'

tensor :: Term -> Extract (Term, Term)
tensor (unApply -> (f, as))
  | isCompose f = do let t = head (tail as)
                     let u = head as
                     return (t, u)
tensor _ = Nope

apply :: Term -> Extract Term
apply (unapplyApply -> Just t) = return t
apply _ = Nope                

lambdaKappa :: Term -> Extract Term
lambdaKappa (unapplyLambdaKappa -> Just t) = return t
lambdaKappa _ = Nope                      

forallK :: Type -> Extract Type
forallK (unapplyForall -> Just a) = return a
forallK _ = Nope                 

forall :: Type -> Idris Type
forall = applyForall

fix :: Term -> Extract (Term, Term)
fix = undefined

expectsClock :: TT Name -> Bool
expectsClock t
  = isLater'  t ||
    isLater   t ||
    isForall  t ||
    isNext    t ||
    isCompose t ||
    isApply   t ||
    isLambdaKappa t

guardedType :: Type -> Idris Bool
guardedType (P Ref n (TType _)) =
  do ist <- get
     return $ n `elem` (map snd (guarded_renames ist))
guardedType _ = return False

-- 
checkFix :: Env -> Type -> Term -> Term -> Idris ()
checkFix = undefined

debind :: Type -> Idris Type
debind (Bind n b t) = return $ binderTy b
debind _ = translateError Undefined

debind' :: Type -> Type -> Env -> Idris Type
debind' (Bind n b t) ty env =
  ifM (cEq env t ty)
      (return $ binderTy b)
      (do rest <- debind' t ty env
          return $ Bind n b rest)
debind' _ _ _ = translateError Undefined  

cEq :: Env -> Type -> Type -> Idris Bool
cEq env ty ty' =
  do ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env ty ty') (0, ucs) of
      tc -> case tc of
              OK () -> return True
              _ -> return False

tyEq :: Env -> Type -> Type -> Idris ()
tyEq env ty ty' =
  do ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env ty ty') (0, ucs) of
      tc -> case tc of
              OK _ -> return ()
              Error e -> translateError $ Misc (show e)
  
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM = liftM3 (\c l r -> if c then l else r)

recursiveRef :: Name -> Term -> Extract Term
recursiveRef n (unapplyNext -> Just t@(P Ref n' _))
  | n == n' = return t
recursiveRef _ _ = Nope

laterThan :: Env -> Type -> Type -> Idris Type
laterThan env ty (unapplyLater -> Just ty') = do tyEq env ty ty'
                                                 return ty'

\end{code}
}
\end{document}
