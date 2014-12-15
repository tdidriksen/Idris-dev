module Idris.GuardedRecursion.Error where

import Idris.AbsSyntaxTree
import Idris.Error
import Idris.Core.TT

data GRError =   Misc String
               | MissingClock
               | MissingLater
               | MissingForall
               | NotTypeType Type  
               | Undefined
               | UnexpectedClockInEnv  

translateError :: GRError -> Idris a
translateError (Misc s) = ifail s
translateError MissingClock = ifail "Expected a clock in the environment, but none was found."
translateError Undefined = ifail "Undefined error in guarded recursion checker."
