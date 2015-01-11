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

import Idris.GuardedRecursion.Error
import Idris.GuardedRecursion.Helpers

import Control.Monad.State.Lazy as LazyState hiding (fix)

checkGR :: Env -> (Name, Type) -> Term -> Type -> Idris Totality
checkGR = check Closed
                         
\end{code}
}
\begin{code}
check :: Clock -> Env -> (Name, Type) -> Term -> Type -> Idris Totality

check Open g (n, (forallK -> Extracted ty)) (causalRecursiveRef n -> Extracted t) a =
  (ty `laterThan` a) g
     
check Open g (n, ty) (acausalRecursiveRef n -> Extracted t) a =
  (ty `laterThan` a) g
     
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, A\, :\, Type\quad \quad nofc(\Gamma ) }{ \sqcap ;\Gamma \, \vdash \, \forall \kappa .A\, : \, Type }
\]
\begin{code}

check Closed g n (forallK -> Extracted a) t@(TType _) =
  requires
    (nofc n g)
    (check Open g n a t)

     
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

check Open g n (tensor -> Extracted (t, u, a, b')) (later -> Extracted b) =
  do --iLOG $ "Tensor a " ++ show a
     --  iLOG $ "Tensor b' " ++ show b'
     -- iLOG $ "Tensor b " ++ show b
     aToB <- (a `to` b') g
      -- eq b and b'
     requires
       (check Open g n u =<< laterK a)
       (check Open g n t =<< laterK aToB)
     
\end{code}
\hrulefill 
\[
\frac { \sqcup ;\Gamma \, \vdash \, A\, : \, Type\quad \quad \sqcap ;\Gamma ,\Gamma '\, \vdash \, t\, : \, \forall \kappa .A\quad \quad nofc(\Gamma ) }{ \sqcup ;\Gamma ,\Gamma '\, \vdash \, apply\quad (t)\, : \, A }
\]
\begin{code}

check Open g n (apply -> Extracted t) a =
  do aTy <- typeOf a g
     case aTy of
       (TType _) -> do forallA <- forall a
                       requires
                         (nofc n g)
                         (check Closed g n t forallA)
       _ -> do iLOG $ "Expected " ++ show aTy ++ " to be of type type"
               return $ Partial NotProductive
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
check d g n (App t t') b =
  do ty <- typeOf t g
     (a,_) <- debind ty
     requires
       (check d g n t ty)
       (check d g n t' a)
check d g n (Bind n' b t) a =
  check d ((n', b) : g) n t a
check d g (n, _) (P _ n' ty) a
  | n /= n' =
    do c <- (cEq g ty a)
       if c then
         (do c' <- clockedType ty
             if (not c || isOpen d)
                   then (return $ Total [])
                   else (do iLOG $ "Not productive. \n c: " ++ show c' ++ " \n ty: " ++ show ty ++ " \n d: " ++ show (isOpen d)
                            return $ Partial NotProductive))
         else
         (do iLOG $ "Not productive because \n" ++ show ty ++ "\n and\n " ++ show a ++ "\n were not equal. cEq was " ++ show c
             return $ Partial NotProductive)
check _ _ _ t a = do iLOG $ "Catch all..." ++ show t ++ " and " ++ show a
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

tensor :: Term -> Extract (Term, Term, Type, Type)
tensor (unapplyCompose -> Just(a, b, _, t, u)) = Extracted(t, u, a, b)
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
{-
expectsClock :: TT Name -> Bool
expectsClock t
  = isLater'  t ||
    isLater   t ||
    isForall  t ||
    isNext    t ||
    isCompose t ||
    isApply   t ||
    isLambdaKappa t
-}
guardedType :: Type -> Idris Bool
guardedType (P Ref n (TType _)) =
  do ist <- get
     return $ n `elem` (map snd (guarded_renames ist))
guardedType _ = return False

-- 
debind :: Type -> Idris (Type, Type)
debind (Bind n b t) = return $ (binderTy b, t)
debind _ = translateError Undefined

{-
debind' :: Type -> Type -> Env -> Idris Type
debind' (Bind n b t) ty env =
  ifM (cEq env t ty)
      (return $ binderTy b)
      (do rest <- debind' t ty env
          return $ Bind n b rest)
debind' _ _ _ = translateError Undefined  
-}
cEq :: Env -> Type -> Type -> Idris Bool
cEq env ty ty' =
  do ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env ty ty') (0, ucs) of
      tc -> case tc of
              OK () -> return True
              Error e -> do iLOG $ "cEq err: " ++ show e
                            return False

tyEq :: Env -> Type -> Type -> Idris ()
tyEq env ty ty' =
  do ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env ty ty') (0, ucs) of
      tc -> case tc of
              OK _ -> return ()
              Error e -> translateError $ Misc (show e)
  
causalRecursiveRef :: Name -> Term -> Extract Term
causalRecursiveRef n (unapplyNext >=> unapplyApply -> Just t@(P Ref n' _))
  | n == n' = return t
causalRecursiveRef _ _ = Nope

acausalRecursiveRef :: Name -> Term -> Extract Term
acausalRecursiveRef n (unapplyNext -> Just t@(P Ref n' _))
  | n == n' = return t
acausalRecursiveRef _ _ = Nope              


laterThan :: Type -> Type -> Env -> Idris Totality
laterThan ty (unapplyLater -> Just ty') env = do c <- cEq env ty ty'
                                                 if c
                                                   then (return $ Total [])
                                                   else (do iLOG $ "laterThan failed because \n" ++ show ty ++ "\n and\n " ++ show ty' ++ "\n were not equal."
                                                            return $ Partial NotProductive)

requires :: Idris Totality -> Idris Totality -> Idris Totality
requires t1 t2 = do t  <- t1
                    t' <- t2
                    return $ mergeTotal t t'

mergeTotal :: Totality -> Totality -> Totality
mergeTotal (Total _) t = t
mergeTotal t (Total _) = t

requires3 :: Idris Totality -> Idris Totality -> Idris Totality -> Idris Totality
requires3 t1 t2 t3 = requires t1 (requires t2 t3)

nofc :: (Name, Type) -> Env -> Idris Totality
nofc n env =
  do tos <- mapM (c n) env
     return $ foldr mergeTotal (Total []) tos
  where
    c :: (Name, Type) -> (Name, Binder (TT Name)) -> Idris Totality
    c r (n, b) = check Closed [] r (P Bound n (binderTy b)) (binderTy b)

clockedType :: Type -> Idris Bool
clockedType (Bind _ _ sc) = clockedType sc
clockedType (unApply -> (P _ n _, _)) =
  do i <- get
     return $ n `elem` (map snd (guarded_renames i))
clockedType _ = return False     

isOpen :: Clock -> Bool
isOpen Open = True
isOpen _ = False

to :: Type -> Type -> Env -> Idris Type
to a b env = do aK <- typeOf a env
                bK <- typeOf b env
                c <- cEq env aK bK
                iLOG $ show c
                iLOG $ show aK
                iLOG $ show bK
                return $ Bind (sUN "__pi_arg") (Pi a aK) b
\end{code}
}
\end{document}
