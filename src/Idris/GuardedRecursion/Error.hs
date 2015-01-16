module Idris.GuardedRecursion.Error where

import Idris.AbsSyntaxTree
import Idris.Error
import Idris.Core.TT

data GRError =   Misc String
               | Undefined

translateError :: GRError -> Idris a
translateError (Misc s) = ifail $ "Misc GR Error " ++ s
translateError Undefined = ifail "Undefined error in guarded recursion checker."
