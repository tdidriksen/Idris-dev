{-# LANGUAGE ViewPatterns #-}
{-|
  This file contains functions for interfacing with the Idris definitions
  from the GuarededRecursion namespace in /libs/prelude/Builtins.idr
-}

module Idris.GuardedRecursion.BuiltinHandlers where

import Idris.Core.TT hiding (nextName)

import Idris.AbsSyntaxTree

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Helpers

import Control.Monad


-- General helpers

applyUnary :: Idris Term -> Idris Term -> Idris Term
applyUnary t t' = liftM2 App t t'

applyBinary :: Idris Term -> Idris Term -> Idris Term -> Idris Term
applyBinary a b c = applyUnary (applyUnary a b) c

unapplyUnary :: (Term -> Bool) -> Term -> Maybe Term
unapplyUnary p (App a b) | p a = Just b
unapplyUnary _ _ = Nothing

unapplyBinary :: (Term -> Bool) -> Term -> Maybe Term
unapplyBinary p (App (App a _) b) | p a = Just b
unapplyBinary _ _ = Nothing

isRef :: Name -> Term -> Bool
isRef n (P Ref n' _) | n == n' = True
isRef _ _ = False

isDCon :: Name -> Term -> Bool
isDCon n (P (DCon _ _ _) n' _) | n == n' = True
isDCon _ _ = False

isTCon :: Name -> Term -> Bool
isTCon n (P (TCon _ _) n' _) | n == n' = True
isTCon _ _ = False

--

applyApplyClock :: Type -> Term -> Idris Term
applyApplyClock a t = applyBinary applyClockRef (return a) (return t)

applyFix :: Type -> Term -> Idris Term
applyFix a f = applyBinary fixRef (return a) (return f)

applyForallClocks :: Type -> Idris Type
applyForallClocks ty = applyUnary forallClocksRef (return ty)

unapplyForallClocks :: Type -> Maybe Type
unapplyForallClocks ty = unapplyUnary (isTCon forallClocksName) ty

applyLambdaClock :: Type -> Term -> Idris Term
applyLambdaClock ty tm = applyBinary lambdaClockRef (return ty) (return tm)

applyLater' :: Type -> Idris Type
applyLater' ty = applyUnary later'Ref (return ty)

unapplyLater' :: Type -> Maybe Type
unapplyLater' ty = unapplyUnary (isTCon later'Name) ty

unapplyNLater :: Type -> Maybe Type
unapplyNLater (App (App later (unapplyTomorrow -> Just av)) ty)
  | isTCon laterName later = return $ App (App later av) ty
unapplyNLater _ = Nothing

unapplyLater :: Type -> Maybe Type
unapplyLater (unapplyLater' -> Just ty) = return ty
unapplyLater (unapplyNLater -> Just ty) = return ty
unapplyLater _ = Nothing

applyLaters :: Int -> Type -> Idris Type
applyLaters n ty
  | n <= 0 = return ty
  | otherwise = applyLater' =<< applyLaters (n-1) ty

unapplyLaters :: Type -> (Int, Type)
unapplyLaters (unapplyLater -> Just ty) =
  let (n, ty') = unapplyLaters ty
  in (n+1, ty')
unapplyLaters ty = (0, ty)

applyLaterApp :: Type -> Type -> Int -> Term -> Term -> Idris Term
applyLaterApp a b n f x =
  do av <- availability (n-1) -- Subtract one due to type of laterApp
     laterApp <- laterAppRef
     return $ mkApp laterApp [a, b, av, f, x]

applyNext :: Type -> Term -> Idris Term
applyNext ty tm = applyBinary nextRef (return ty) (return tm)

applyNexts :: Term -> Type -> Int -> Idris Term
applyNexts t a n
  | n > 0  = do laterA <- applyLater' a
                nextApp <- applyNext a t
                applyNexts nextApp laterA (n-1)
  | n <= 0 = return t

unapplyNext :: Term -> Maybe Term
unapplyNext t = unapplyBinary (isDCon nextName) t

unapplyNexts :: Term -> Int -> Maybe Term
unapplyNexts (unapplyNext -> Just t) n
  | n > 0  = unapplyNexts t (n-1)
unapplyNexts (unapplyNext -> Nothing) n
  | n > 0  = Nothing
unapplyNexts t _ = return t

applyTomorrow :: Term -> Idris Term
applyTomorrow t = applyUnary tomorrowRef (return t)

unapplyTomorrow :: Term -> Maybe Term
unapplyTomorrow t = unapplyUnary (isDCon tomorrowName) t

availability :: Int -> Idris Term
availability n
  | n <= 0    = nowRef
  | otherwise = applyTomorrow =<< availability (n-1)

unapplyDelay :: Term -> Maybe Term
unapplyDelay (App (App (App delay lazyType) delayType) tm)
  | isDelay delay && isLazyCodata lazyType = Just tm
  where
    isDelay :: Term -> Bool
    isDelay (P _ (UN delay) _) = delay == txt delayStr
    isDelay _ = False
unapplyDelay _ = Nothing

unapplyForce :: Term -> Maybe Term
unapplyForce (App (App (App force lazyType) forceType) tm)
  | isForce force && isLazyCodata lazyType = Just tm
  where
    isForce :: Term -> Bool
    isForce (P _ (UN force) _) = force == txt forceStr
    isForce _ = False
unapplyForce _ = Nothing

isLazyCodata :: Term -> Bool
isLazyCodata (P _ (UN lazyCodata) _) = lazyCodata == txt lazyCodataStr
isLazyCodata _ = False

unapplyLazy' :: Type -> Maybe Type
unapplyLazy' (App (App lazy' lazyType) ty)
  | isLazy' lazy' && isLazyCodata lazyType = Just ty
  where
    isLazy' :: Term -> Bool
    isLazy' (P _ (UN lazy') _) = lazy' == txt lazy'Str
    isLazy' _ = False
unapplyLazy' _ = Nothing

removeLaziness :: Term -> Term
removeLaziness t = mapTT withoutLazyOps t
  where
    withoutLazyOps :: Term -> Term
    withoutLazyOps (unapplyDelay -> Just tm) = tm
    withoutLazyOps (unapplyForce -> Just tm) = tm
    withoutLazyOps (unapplyLazy' -> Just ty) = ty
    withoutLazyOps tm = tm  
