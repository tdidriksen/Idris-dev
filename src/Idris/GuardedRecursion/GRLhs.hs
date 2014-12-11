module Idris.GuardedRecursion.GRLhs where

import Idris.GuardedRecursion.GuardedRecursionHelpers
import Idris.Core.TT
import Idris.AbsSyntax
import Idris.Error(ifail)

-- |guards a left hand side.
guardedLHS :: Term -> Idris Term
guardedLHS (App (P Ref n t) t') = do gn <- getGuardedName n
                                     gt <- guardedTT t
                                     gt' <- guardedTT t'
                                     return $ App (P Ref gn gt) gt'
guardedLHS t = ifail $ (show t) ++ "is not a left hand side." -- FIXME
                                      
