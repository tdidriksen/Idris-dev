{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Check(checkGR) where

import Idris.Core.TT
import Idris.AbsSyntaxTree
import Idris.Error

data GRError = Misc String
               | Undefined

type GR a = Either GRError a

data Extract a = Extracted a | Nope

checkGR :: Type -> Term -> Idris ()
checkGR ty te = case check Empty ty te of
                  Left err -> translateError err
                  Right _  -> return ()

translateError :: GRError -> Idris ()
translateError (Misc s) = ifail s
translateError Undefined = ifail "Undefined error in guarded recursion checker."

data ClockEnv = Empty | Something

check :: ClockEnv -> Type -> Term -> GR ()
-- Next
check ce (unlift -> Extracted a) (advance -> Extracted t)
  = check ce a t
-- Tensor
check ce (unlift -> Extracted b) (relax -> Extracted (t, u))
  = do ft <- getFunTy t
       a <- getArgTy ft
       check ce a u
       check ce ft t
-- 
check _ _ _ = Left Undefined

advance :: Term -> Extract Term
advance = undefined

unlift :: Type -> Extract Type
unlift = undefined

relax :: Term -> Extract (Term, Term)
relax = undefined

getFunTy :: Term -> GR Type
getFunTy = undefined

getArgTy :: Type -> GR Type
getArgTy = undefined
