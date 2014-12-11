module Idris.GuardedRecursion.Error where

import Idris.AbsSyntaxTree
import Idris.Error

data GRError = Misc String
               | Undefined

translateError :: GRError -> Idris ()
translateError (Misc s) = ifail s
translateError Undefined = ifail "Undefined error in guarded recursion checker."
