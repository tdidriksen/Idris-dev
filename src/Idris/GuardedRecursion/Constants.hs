module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.GuardedRecursion.Helpers

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Control.Monad.Reader

-- NAMES AS STRINGS

applyClockStr = "applyClock"
delayStr = "Delay"
fixStr = "fix"
forallClocksStr = "ForallClocks"
forceStr = "Force"
guardedRecursionStr = "GuardedRecursion"
lambdaClockStr = "LambdaClock"
laterStr = "Later"
later'Str = "Later'"
laterAppStr = "laterApp"
lazy'Str = "Lazy'"
lazyCodataStr = "LazyCodata"
nextStr = "Next"
nowStr = "Now"
tomorrowStr = "Tomorrow"



-- NAMES AS NAMES

guardedNS :: [String]
guardedNS = [guardedRecursionStr]

inGuardedNS :: String -> Name
inGuardedNS s = sNS (sUN s) guardedNS

applyClockName = inGuardedNS applyClockStr
fixName = inGuardedNS fixStr
forallClocksName = inGuardedNS forallClocksStr
lambdaClockName = inGuardedNS lambdaClockStr
laterName = inGuardedNS laterStr
later'Name = inGuardedNS later'Str
laterAppName = inGuardedNS laterAppStr
nextName = inGuardedNS nextStr
nowName = inGuardedNS nowStr
tomorrowName = inGuardedNS tomorrowStr


-- REFS

ref :: Name -> Idris Term
ref n =
  do ctxt <- getContext
     case lookupP n ctxt of
      [nP] -> return nP
      _ -> ifail $ "Term " ++ show n ++ " does not exist!"

applyClockRef = ref applyClockName
fixRef = ref fixName
forallClocksRef = ref forallClocksName
lambdaClockRef = ref lambdaClockName
later'Ref = ref later'Name
laterAppRef = ref laterAppName
nextRef = ref nextName
nowRef = ref nowName
tomorrowRef = ref tomorrowName

-- PTERM REFS

later'PTRef :: PTerm
later'PTRef = later'PTRefFC emptyFC

later'PTRefFC :: FC -> PTerm
later'PTRefFC fc = PRef fc later'Name

-- OTHER STRINGS

guardedPrefix = "guarded_"
forallPrefix  = "forall_"
