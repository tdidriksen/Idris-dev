module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.GuardedRecursion.Helpers

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Control.Monad.Reader

-- NAMES AS STRINGS

forallKappaStr = "ForallKappa"
guardedRecursionStr = "GuardedRecursion"
later'Str = "Later'"
nextStr = "Next"



-- NAMES AS NAMES

guardedNS :: [String]
guardedNS = [guardedRecursionStr]

inGuardedNS :: String -> Name
inGuardedNS s = sNS (sUN s) guardedNS

forallKappaName = inGuardedNS forallKappaStr

nextName = inGuardedNS nextStr
later'Name = inGuardedNS later'Str

-- REFS

ref :: Name -> GR Term
ref n =
  do ctxt <- lift getContext
     case lookupP n ctxt of
      [nP] -> return nP
      _ -> lift (ifail $ "Term " ++ show n ++ " does not exist!")

forallKappaRef = ref forallKappaName
nextRef = ref nextName

-- PTERM REFS

later'PTRef :: PTerm
later'PTRef = later'PTRefFC emptyFC

later'PTRefFC :: FC -> PTerm
later'PTRefFC fc = PRef fc later'Name

-- OTHER STRINGS

guardedPrefix = "guarded_"
forallPrefix  = "forall_"
