module Idris.GuardedRecursion.Error where

import Idris.Core.TT
import Idris.AbsSyntax
import Idris.Error

grFail :: GRErrorReason -> Idris a
grFail err = tclift $ tfail (GuardedRecursionFailed err)
