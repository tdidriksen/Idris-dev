module Idris.GuardedRecursion.CheckGR where

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.GuardedRecursion.Helpers

import Control.Monad

checkGuardedRecursive :: Name -> Idris Totality
checkGuardedRecursive n =
  do ctxt <- getContext
     case lookupDef n ctxt of
        [CaseOp _ _ _ _ clauses _] ->
          do --evalStateT (buildGR n clauses) emptyGEnv
             _ <- fixFunction n clauses
             
             return $ Partial NotProductive
        _ -> return $ Partial NotProductive

fixFunction :: Name -> [([Name], Term, Term)] -> Idris [([Name], Term, Term)]
fixFunction n clauses =
  do forM_ clauses $ \(pvs, lhs, rhs) ->
       do iLOG $ show ("GR_LHS: " ++ showEnvDbg [] lhs)
          iLOG $ show ("GR_RHS: " ++ showEnvDbg [] rhs)
     ctxt <- getContext
     ty <- case lookupTyExact n ctxt of
            Just ty' -> return ty'
            Nothing -> ifail "Seemingly defined function has no definition"
     recRef <- recursiveRef n ty
     let replaceRec = subst n recRef
     let recsReplaced = map (\(pvs,lhs,rhs) -> (pvs,lhs,replaceRec rhs)) clauses
     forM_ recsReplaced $ \(_,_,rhs) -> iLOG $ "GR " ++ show n ++ " after subst: " ++ (showEnvDbg [] rhs)
     return recsReplaced

recursiveRef :: Name -> Type -> Idris Type
recursiveRef name ty =
  do laterType <- applyLater' ty
     return $ P Ref (sMN 0 (show name ++ "_rec")) laterType
