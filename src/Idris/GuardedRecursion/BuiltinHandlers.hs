{-# LANGUAGE ViewPatterns #-}
{-|
  This file contains functions for interfacing with the Idris definitions
  from the GuarededRecursion namespace in /libs/prelude/Builtins.idr
-}

module Idris.GuardedRecursion.BuiltinHandlers where

import Idris.Core.TT

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Helpers

import Control.Monad


-- General helpers

applyUnary :: GR Term -> GR Term -> GR Term
applyUnary t t' = liftM2 App t t'

applyBinary :: GR Term -> GR Term -> GR Term -> GR Term
applyBinary a b c = applyUnary (applyUnary a b) c

unapplyUnary :: (Term -> Bool) -> Term -> Maybe Term
unapplyUnary p (App a b) | p a = Just b
unapplyUnary _ _ = Nothing

unapplyBinary :: (Term -> Bool) -> Term -> Maybe Term
unapplyBinary p (App (App a _) b) | p a = Just b
unapplyBInary _ _ = Nothing

isRef :: Name -> Term -> Bool
isRef n (P Ref n' _) | n == n' = True
isRef _ _ = False

isTCon :: Name -> Term -> Bool
isTCon n (P (TCon _ _) n' _) | n == n' = True
isTCon _ _ = False

--

applyFix :: Type -> Term -> GR Term
applyFix a f = applyBinary fixRef (return a) (return f)

applyForallKappa :: Type -> GR Type
applyForallKappa ty = applyUnary forallKappaRef (return ty)

unapplyForallKappa :: Type -> Maybe Type
unapplyForallKappa ty = unapplyUnary (isTCon forallKappaName) ty

applyLambdaKappa :: Type -> Term -> GR Term
applyLambdaKappa ty tm = applyBinary lambdaKappaRef (return ty) (return tm)

applyLater' :: Type -> GR Type
applyLater' ty = applyUnary later'Ref (return ty)

applyNext :: Type -> Term -> GR Term
applyNext ty tm = applyBinary nextRef (return ty) (return tm)

unapplyLater :: Type -> Maybe Type
unapplyLater = undefined
