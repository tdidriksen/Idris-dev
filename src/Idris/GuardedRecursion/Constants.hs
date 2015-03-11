module Idris.GuardedRecursion.Constants where

import Idris.Core.TT hiding (nextName)
import Idris.Core.Evaluate

import Idris.GuardedRecursion.Helpers

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Control.Monad.Reader

-- NAMES AS STRINGS

fixStr = "fix"
forallKappaStr = "ForallKappa"
guardedRecursionStr = "GuardedRecursion"
lambdaKappaStr = "LambdaKappa"
later'Str = "Later'"
nextStr = "Next"



-- NAMES AS NAMES

guardedNS :: [String]
guardedNS = [guardedRecursionStr]

inGuardedNS :: String -> Name
inGuardedNS s = sNS (sUN s) guardedNS

fixName = inGuardedNS fixStr
forallKappaName = inGuardedNS forallKappaStr
lambdaKappaName = inGuardedNS lambdaKappaStr
later'Name = inGuardedNS later'Str
nextName = inGuardedNS nextStr


-- REFS

ref :: Name -> GR Term
ref n =
  do ctxt <- lift getContext
     case lookupP n ctxt of
      [nP] -> return nP
      _ -> lift (ifail $ "Term " ++ show n ++ " does not exist!")

fixRef = ref fixName
forallKappaRef = ref forallKappaName
lambdaKappaRef = ref lambdaKappaName
later'Ref = ref later'Name
nextRef = ref nextName

-- PTERM REFS

later'PTRef :: PTerm
later'PTRef = later'PTRefFC emptyFC

later'PTRefFC :: FC -> PTerm
later'PTRefFC fc = PRef fc later'Name

-- OTHER STRINGS

guardedPrefix = "guarded_"
forallPrefix  = "forall_"
