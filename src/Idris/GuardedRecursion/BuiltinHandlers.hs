module Idris.GuardedRecursion.BuiltinHandlers where

{-|
  This file contains functions for interfacing with the Idris definitions
  from the GuarededRecursion namespace in /libs/prelude/Builtins.idr
-}

import Idris.Core.TT

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Helpers

import Control.Monad


-- General helpers

applyUnary :: GR Term -> GR Term -> GR Term
applyUnary t t' = liftM2 App t t'

applyBinary :: GR Term -> GR Term -> GR Term -> GR Term
applyBinary a b c = applyUnary (applyUnary a b) c


-- 

applyNext :: Type -> Term -> GR Term
applyNext ty tm = applyBinary nextRef (return ty) (return tm)

unapplyLater :: Type -> Maybe Type
unapplyLater = undefined
