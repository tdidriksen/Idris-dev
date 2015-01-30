module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

-- STRINGS

guardedRecursion, guardedPrefix, laterStr, later'Str, nextStr, composeStr, availStr, nowStr, tomorrowStr, forallStr, lambdaKappaStr, applyStr, delayStr, lazyCodataStr, forceStr, lazy'Str, liftComposeStr :: String
guardedRecursion = "GuardedRecursion"
guardedPrefix = "guarded_"
laterStr = "Later"
later'Str = "Later'"
nextStr = "Next"
composeStr = "compose"
availStr = "Availability"
nowStr = "Now"
tomorrowStr = "Tomorrow"
forallStr = "Forall"
lambdaKappaStr = "LambdaKappa"
applyStr = "apply"
delayStr = "Delay"
lazyCodataStr = "LazyCodata"
forceStr = "Force"
lazy'Str = "Lazy'"
liftComposeStr = "liftCompose"

-- NAMES

guardedNS :: [String]
guardedNS = [guardedRecursion]

later'Name, nextName, laterName, composeName, liftComposeName :: Name
later'Name = sNS (sUN later'Str) guardedNS
laterName = sNS (sUN laterStr) guardedNS
nextName = sNS (sUN nextStr) guardedNS
composeName = sNS (sUN composeStr) guardedNS
liftComposeName = sNS (sUN liftComposeStr) guardedNS

availabilityName, nowName, tomorrowName :: Name
availabilityName = sNS (sUN availStr) guardedNS
nowName = sNS (sUN nowStr) guardedNS
tomorrowName = sNS (sUN tomorrowStr) guardedNS

forallName :: Name
forallName = sNS (sUN forallStr) guardedNS

lambdaKappaName :: Name
lambdaKappaName = sNS (sUN lambdaKappaStr) guardedNS

applyName :: Name
applyName = sNS (sUN applyStr) guardedNS

-- REFS

ref :: Name -> Idris Term
ref n =
  do ctxt <- getContext
     case lookupP n ctxt of
      [nP] -> return nP
      _ -> ifail $ "Term " ++ show n ++ " does not exist!"

applyRef :: Idris Term
applyRef = ref applyName

composeRef :: Idris Term
composeRef = ref composeName

forallRef :: Idris Type
forallRef = ref forallName

lambdaKappaRef :: Idris Term
lambdaKappaRef = ref lambdaKappaName

laterRef :: Idris Term
laterRef = ref laterName

later'Ref :: Idris Term
later'Ref = ref later'Name

liftComposeRef :: Idris Term
liftComposeRef = ref liftComposeName

nextRef :: Idris Term
nextRef = ref nextName

nowRef :: Idris Term
nowRef = ref nowName

tomorrowRef :: Idris Term
tomorrowRef = ref tomorrowName

-- PT REFS

laterPTRef :: PTerm
laterPTRef = laterPTRefFC emptyFC

laterPTRefFC :: FC -> PTerm
laterPTRefFC fc = PRef fc later'Name
