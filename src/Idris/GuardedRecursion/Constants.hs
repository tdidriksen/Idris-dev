module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.GuardedRecursion.Helpers

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Control.Monad.Reader

-- NAMES AS STRINGS

guardedRecursionStr = "GuardedRecursion"
nextStr = "Next"
later'Str = "Later'"


-- NAMES AS NAMES

guardedNS :: [String]
guardedNS = [guardedRecursionStr]

inGuardedNS :: String -> Name
inGuardedNS s = sNS (sUN s) guardedNS

nextName = inGuardedNS nextStr
later'Name = inGuardedNS later'Str

-- REFS

ref :: Name -> GR Term
ref n =
  do ctxt <- lift getContext
     case lookupP n ctxt of
      [nP] -> return nP
      _ -> lift (ifail $ "Term " ++ show n ++ " does not exist!")

nextRef = ref nextName

-- PTERM REFS

later'PTRef :: PTerm
later'PTRef = later'PTRefFC emptyFC

later'PTRefFC :: FC -> PTerm
later'PTRefFC fc = PRef fc later'Name

-- OTHER STRINGS

guardedPrefix = "guarded_"
forallPrefix  = "forall_"
