\documentclass{minimal}
%include polycode.fmt
\long\def\ignore#1{}

\usepackage{listings}
\lstnewenvironment{code}{\lstset{language=Haskell,basicstyle=\small}}{}

\begin{document}

\ignore{
\begin{code}

{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Check(checkGR) where

import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.Typecheck hiding (check)

import Idris.AbsSyntax

import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.Error

import Control.Monad.State.Lazy as LazyState hiding (fix)

checkGR :: Modality -> Env -> (Name, Type) -> Term -> Type -> Idris Totality
checkGR Causal g r (lambdaKappa -> Extracted t) (forallK -> Extracted a) = check Open g r t a
checkGR Causal _ _ _ _ = return $ Partial (NotGuardedRecursive [])
checkGR NonCausal g r t a = check Closed g r t a
                         
\end{code}
}
\begin{code}
check :: Clock -> Env -> (Name, Type) -> Term -> Type -> Idris Totality

check Open g (n, (forallK -> Extracted ty)) (causalRecursiveRef n -> Extracted t) a =
     (a `laterThan` ty) g
     
check Open g (n, ty) (acausalRecursiveRef n -> Extracted t) a =
     (a `laterThan` ty) g
     
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, A\, :\, Type\quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \, \vdash \, \forall \kappa .A\, : \, Type }
\]
\begin{code}

check Closed g n (forallK -> Extracted a) ty@(TType _) =
     requires
       (nofc n g)
       (check Open g n a ty)
     
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, A\, :\, Type }{ \sqcup ;\Gamma \, \vdash \, \rhd A\, : \, Type }
\]
\begin{code}

check Open g n (later -> Extracted a) t@(TType _) =
     check Open g n a t
  
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, t\, : \, A }{ \sqcup ;\Gamma \, \vdash \, next\quad (t)\, : \, \rhd A }
\]
\begin{code}

check Open g n (next -> Extracted t) (later -> Extracted a) =
     check Open g n t a
  
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, t\, : \, \rhd (A\, \rightarrow \, B)\quad \quad \sqcup ;\Gamma \, \vdash \, u\, : \, \rhd A }{ \sqcup ;\Gamma \, \vdash \, t\quad \circledast \quad u\, : \, \rhd B }
\]
\begin{code}

check Open g n (tensor -> Extracted (t, u, l, a, b')) (laterN l -> Extracted b) =
  do c <- cEq g b' b
     if c
       then (do aToB <- (a `to` b) g
                requires
                  (check Open g n t =<< laterK aToB)
                  (check Open g n u =<< laterK a))
       else return $ Partial (NotGuardedRecursive [(TensorTypeMismatch b b')])
     
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, A\, : \, Type\quad \quad \sqcap ;\Gamma ,\Gamma '\, \vdash \, t\, : \, \forall \kappa .A\quad \quad nofc(\Gamma ) }{ \sqcup ;\Gamma ,\Gamma '\, \vdash \, apply\quad (t)\, : \, A }
\]
\begin{code}

check Open g n (apply -> Extracted t) a =
  do aTy <- typeOfMaybe a g
     case aTy of
       Just(TType _) -> do forallA <- forall a
                           requires
                             (nofc n g)
                             (check Closed g n t forallA)
       _ -> return $ Partial (NotGuardedRecursive [ApplyWithoutType])
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, t\, : \, A\quad \quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \, \vdash \, \Lambda \kappa .t\, : \, \forall \kappa .A } 
\]
\begin{code}

check Closed g n (lambdaKappa -> Extracted t) (forallK -> Extracted a) =
     requires
       (nofc n g)
       (check Open g n t a)
\end{code}
\hrulefill
Not Guarded Recursion:
\begin{code}
check d g n term@(App t t') b =
  do b' <- typeOf term g
     ty <- typeOf t g
     (a,_) <- debind ty
     c <- cEq g b b'
     if c
       then requires
              (check d g n t ty)
              (check d g n t' a)
       else return $ Partial (NotGuardedRecursive [])
check d g n (Bind n' b t) a =
  check d ((n', b) : g) n t a
check d g (n, _) (P _ n' ty) a
  | n /= n' =
    do c <- (cEq g ty a)
       if c then
         (do c' <- clockedType ty
             if (not c' || isOpen d)
                   then return $ Total []
                   else return $ Partial (NotGuardedRecursive [OpenClockNeeded ty]))
         else
             return $ Partial (NotGuardedRecursive [TypeMismatch ty a])
check _ _ _ t a = return $ Partial (NotGuardedRecursive [Misc t a])
\end{code}
\ignore{
\begin{code}
next :: Term -> Extract Term
next (unapplyNext -> Just t) = return t
next _ = Nope

later :: Type -> Extract Type
later (unapplyLater -> Just a) = return a
later _ = Nope

laterN :: Availability -> Type -> Extract Type
laterN n (unapplyLaterUntilNow n -> Just ty) = return ty
laterN _ _ = Nope

laterK :: Type -> Idris Type
laterK = applyLater'

tensor :: Term -> Extract (Term, Term, Availability, Type, Type)
tensor (unapplyCompose -> Just(a, b, (termAvailability' -> Just l), t, u)) = return (t, u, l, a, b)
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

debind :: Type -> Idris (Type, Type)
debind (Bind _ b t) = return $ (binderTy b, t)
debind _ = translateError Undefined

unapp :: Term -> Maybe Term
unapp (unapplyApply -> Just t) = Just t
unapp (App t t') = unapp t
unapp _ = Nothing

causalRecursiveRef :: Name -> Term -> Extract Term
causalRecursiveRef n (unapplyNext >=> unapp -> Just t@(P Ref n' _))
  | n == n' = Extracted t
causalRecursiveRef _ _ = Nope

acausalRecursiveRef :: Name -> Term -> Extract Term
acausalRecursiveRef n (unapplyNext -> Just (unApply -> (t@(P Ref n' _),_)))
  | n == n' = return t
acausalRecursiveRef _ _ = Nope              

laterThan :: Type -> Type -> Env -> Idris Totality
laterThan (unapplyLater -> Just ty') ty env = do c <- cEq env ty ty'
                                                 if c
                                                   then (return $ Total [])
                                                   else return $ Partial (NotGuardedRecursive [WrongRecRefType])
laterThan _ _ _ = return $ Partial (NotGuardedRecursive [WrongRecRefType])

requires :: Idris Totality -> Idris Totality -> Idris Totality
requires t1 t2 = do t  <- t1
                    t' <- t2
                    return $ mergeTotal t t'

nofc :: (Name, Type) -> Env -> Idris Totality
nofc n env =
  do tos <- mapM (c n) env
     return $ foldr mergeTotal (Total []) tos
  where
    c :: (Name, Type) -> (Name, Binder (TT Name)) -> Idris Totality
    c r (n', b) = do let term = P Bound n' (binderTy b)
                     check Closed [] r term (binderTy b)

\end{code}
}
\end{document}
