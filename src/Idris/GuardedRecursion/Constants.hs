module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

-- NAMES
guardedNamespace :: String
guardedNamespace = "GuardedRecursion"

guardedPrefix :: String
guardedPrefix = "guarded_"

guardedNS :: [String]
guardedNS = [guardedNamespace]

later'Name, nextName, laterName, composeName :: Name
later'Name = sNS (sUN "Later'") guardedNS
laterName = sNS (sUN "Later") guardedNS
nextName = sNS (sUN "Next") guardedNS
composeName = sNS (sUN "compose") guardedNS

availabilityName, nowName, tomorrowName :: Name
availabilityName = sNS (sUN "Availability") guardedNS
nowName = sNS (sUN "Now") guardedNS
tomorrowName = sNS (sUN "Tomorrow") guardedNS

forallName :: Name
forallName = sNS (sUN "Forall") guardedNS

lambdaKappaName :: Name
lambdaKappaName = sNS (sUN "LambdaKappa") guardedNS


-- REFS

composeRef :: Idris Term
composeRef =
  do ctxt <- getContext
     case lookupP composeName ctxt of
      [composeP] -> return composeP
      _ -> ifail "Function 'compose' does not exist!"

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

-- PT REFS

laterPTRef :: PTerm
laterPTRef = laterPTRefFC emptyFC

laterPTRefFC :: FC -> PTerm
laterPTRefFC fc = PRef fc later'Name
