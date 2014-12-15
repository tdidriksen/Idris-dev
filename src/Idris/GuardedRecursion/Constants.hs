module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

-- STRINGS

guardedRecursion, guardedPrefix, laterStr, later'Str, nextStr, composeStr, availStr, nowStr, tomorrowStr, forallStr, lambdaKappaStr, applyStr :: String
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
applyStr = "Apply"

-- NAMES

guardedNS :: [String]
guardedNS = [guardedRecursion]

later'Name, nextName, laterName, composeName :: Name
later'Name = sNS (sUN later'Str) guardedNS
laterName = sNS (sUN laterStr) guardedNS
nextName = sNS (sUN nextStr) guardedNS
composeName = sNS (sUN composeStr) guardedNS

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

applyRef :: Idris Term
applyRef =
  do ctxt <- getContext
     case lookupP applyName ctxt of
       [applyP] -> return applyP
       _ -> ifail "Function 'apply' does not exist!"

composeRef :: Idris Term
composeRef =
  do ctxt <- getContext
     case lookupP composeName ctxt of
      [composeP] -> return composeP
      _ -> ifail "Function 'compose' does not exist!"

forallRef :: Idris Type
forallRef =
  do ctxt <- getContext
     case lookupP forallName ctxt of
       [forallP] -> return forallP
       _ -> ifail "Forall type does not exist!" 

laterRef :: Idris Term
laterRef =
  do ctxt <- getContext
     case lookupP laterName ctxt of
      [laterP] -> return laterP
      _ -> ifail "Later type does not exist!"

later'Ref :: Idris Term
later'Ref =
  do ctxt <- getContext
     case lookupP later'Name ctxt of
      [later'P] -> return later'P
      _ -> ifail "Later' type does not exist!"

nextRef :: Idris Term
nextRef =
  do ctxt <- getContext
     case lookupP nextName ctxt of
      [nextP] -> return nextP
      _ -> ifail "Data constructor Next does not exist!"
nowRef :: Idris Term
nowRef =
  do ctxt <- getContext
     case lookupP nowName ctxt of
      [nowP] -> return nowP
      _ -> ifail "Data constructor 'Now' does not exist!"

tomorrowRef :: Idris Term
tomorrowRef =
  do ctxt <- getContext
     case lookupP tomorrowName ctxt of
      [tomorrowP] -> return tomorrowP  -- 
      _ -> ifail "Data constructor 'Tomorrow' does not exist!"

lambdaKappaRef :: Idris Term
lambdaKappaRef =
  do ctxt <- getContext
     case lookupP lambdaKappaName ctxt of
       [lambdaKP] -> return lambdaKP
       _ -> ifail "Data constructor 'LambdaKappa' does not exists!"

-- PT REFS

laterPTRef :: PTerm
laterPTRef = laterPTRefFC emptyFC

laterPTRefFC :: FC -> PTerm
laterPTRefFC fc = PRef fc later'Name
