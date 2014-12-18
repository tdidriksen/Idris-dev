module Idris.GuardedRecursion.GRLhs where

import Idris.GuardedRecursion.Helpers
import Idris.Core.TT
import Idris.AbsSyntax
import Idris.Error(ifail)

-- |guards a left hand side.
guardedLHS :: Term -> Idris Term
guardedLHS = guardedTT
--guardedLHS t = ifail $ (show t) ++ "is not a left hand side." -- FIXME
                                      
