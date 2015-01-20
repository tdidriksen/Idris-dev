module Idris.GuardedRecursion.Error where

import Idris.AbsSyntaxTree
import Idris.Error
import Idris.Core.TT

data GRError = Undefined

translateError :: GRError -> Idris a
translateError Undefined = ifail "Undefined error in guarded recursion checker."
