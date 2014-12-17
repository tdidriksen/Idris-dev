\documentclass{article}
%include polycode.fmt
\long\def\ignore#1{}
\begin{document}

\ignore{
\begin{code}

{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Check(checkGR) where

import Idris.Core.TT
import Idris.Core.Typecheck hiding (check)

import Idris.AbsSyntax

import Idris.GuardedRecursion.Error
import Idris.GuardedRecursion.Helpers

import Control.Monad.State.Lazy as LazyState hiding (fix)

checkGR :: Env -> Term -> Type -> Idris ()
checkGR env = check Closed env
\end{code}
}
\begin{code}
check :: Clock -> Env -> Term -> Type -> Idris ()
\end{code}
\[\frac { \sqcup ;\Gamma \quad \vdash \quad A\quad :\quad Type\quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \quad \vdash \quad \forall \kappa .A\quad :\quad Type }\]
\begin{code}
check Closed g (forallK -> Extracted a) t@(TType _)
  = check Open g a t
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad A\quad :\quad Type }{ \sqcup ;\Gamma \quad \vdash \quad \rhd A\quad :\quad Type }
\]
\begin{code}
check Open g (later -> Extracted a) t@(TType _)
  = check Open g a t         
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad t\quad :\quad A }{ \sqcup ;\Gamma \quad \vdash \quad next\quad (t)\quad :\quad \rhd A }
\]
\begin{code}
check Open g (next -> Extracted t) (later -> Extracted a) 
  = check Open g t a
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad t\quad :\quad \rhd (A\quad \rightarrow \quad B)\quad \quad \sqcup ;\Gamma \quad \vdash \quad u\quad :\quad \rhd A }{ \sqcup ;\Gamma \quad \vdash \quad t\quad \circledast \quad u\quad :\quad \rhd B }
\]
\begin{code}
check Open g (tensor -> Extracted (t, u)) (later -> Extracted b) =
  do ty <- typeOf t g
     atob <- unlater ty
     a <- debind atob $ until b
     check Open g u =<< laterK a
     check Open g t =<< laterK atob
  where
    until :: Type -> (Type -> Idris Bool)
    until = cEq g
\end{code}

\begin{code}
check Open g (fix -> Extracted (x, t)) a 
  = checkFix g a x t
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad t\quad :\quad A\quad \quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \quad \vdash \quad \Lambda \kappa .t\quad :\quad \forall \kappa .A } 
\]
\begin{code}
check Open g (apply -> Extracted t) a@(TType u)
  = do check Open g a (TType u)
       forallA <- forall a
       check Closed g t forallA
\end{code}
\[
\frac { \sqcup ;\Gamma \quad \vdash \quad A\quad :\quad Type\quad \quad \sqcap ;\Gamma ,\Gamma '\quad \vdash \quad t\quad :\quad \forall \kappa .A\quad \quad nofc(\Gamma ) }{ \sqcup ;\Gamma ,\Gamma '\quad \vdash \quad apply\quad (t)\quad :\quad A }
\]
\begin{code}
check Closed g (lambdaKappa -> Extracted t) (forallK -> Extracted a) 
  = check Open g t a
-- Failure --
-- Missing Clocks
check Closed _ t a
  | expectsClock t || expectsClock a = translateError MissingClock
-- Missing Laters
check _ _ (next -> Extracted _) (later -> Nope)
  = translateError MissingLater
check _ _ (tensor -> Extracted _) (later -> Nope)
  = translateError MissingLater
-- Missing Quantification
check _ _ (lambdaKappa -> Extracted _) (forallK -> Nope)
  = translateError MissingForall
-- Apply Fresh
check d g t (forallK -> Extracted a)
  = ifM (guardedType a)
    (translateError Undefined)
    (check d g t a)
-- Not GR       
check _ _ t a = translateError $ Misc ("Not yet implemented GR on " ++ show t ++ " : " ++ show a)
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

debind :: Type -> (Type -> Idris Bool) -> Idris Type
debind (Bind n b t) cond =
  ifM (cond t)
      (return $ binderTy b)
      (do rest <- debind t cond
          return $ Bind n b rest)
debind _ _ = translateError Undefined  

cEq :: Env -> Type -> Type -> Idris Bool
cEq env ty ty' =
  do ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env ty ty') (0, ucs) of
      tc -> case tc of
              OK () -> return True
              _ -> return False

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM = liftM3 (\c l r -> if c then l else r)
\end{code}
}
\end{document}
