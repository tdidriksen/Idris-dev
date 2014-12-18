module Idris.GuardedRecursion.CheckGR where

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.Epsilon (epsilon)
import Idris.GuardedRecursion.Check (checkGR)

import Control.Monad

checkGuardedRecursive :: Name -> Idris Totality
checkGuardedRecursive n =
  do ctxt <- getContext
     case lookupDef n ctxt of
        [CaseOp _ ty _ _ clauses _] ->
          do --evalStateT (buildGR n clauses) emptyGEnv
             _ <- checkFunction n ty clauses
             
             return $ Partial NotProductive
        _ -> return $ Partial NotProductive

checkFunction :: Name -> Type -> [([Name], Term, Term)] -> Idris Totality
checkFunction name ty clauses =
  do gName <- guardedNameCtxt name
     gTy <- guardedType ty
     gClauses <- forM clauses $ \clause -> guardedRecursiveClause gName gTy clause
     checkRhsSeq <- forM gClauses $ \(_,rhs) -> checkGR [] rhs gTy
     return $ Partial NotProductive
     --idrisCatch (sequence checkRhsSeq) (\e -> )    

guardedType :: Type -> Idris Type
guardedType = guardedTT

guardedLHS :: Term -> Idris Term
guardedLHS = guardedTT

guardedRecursiveClause :: Name -> Type -> ([Name], Term, Term) -> Idris (Term, Term)
guardedRecursiveClause _ _ (_, lhs, Impossible) = return (lhs, Impossible)
guardedRecursiveClause name ty (_, lhs, rhs) =
  do glhs <- guardedLHS lhs
     grhs <- epsilon name rhs ty
     return (glhs, grhs)
     

-- fixFunction :: Name -> [([Name], Term, Term)] -> Idris [([Name], Term, Term)]
-- fixFunction n clauses =
--   do forM_ clauses $ \(pvs, lhs, rhs) ->
--        do iLOG $ show ("GR_LHS: " ++ showEnvDbg [] lhs)
--           iLOG $ show ("GR_RHS: " ++ showEnvDbg [] rhs)
--      ctxt <- getContext
--      ty <- case lookupTyExact n ctxt of
--             Just ty' -> return ty'
--             Nothing -> ifail "Seemingly defined function has no definition"
--      recRef <- recursiveRef n ty
--      let replaceRec = subst n recRef
--      let recsReplaced = map (\(pvs,lhs,rhs) -> (pvs,lhs,replaceRec rhs)) clauses
--      forM_ recsReplaced $ \(_,_,rhs) -> iLOG $ "GR " ++ show n ++ " after subst: " ++ (showEnvDbg [] rhs)
--      return recsReplaced

-- recursiveRef :: Name -> Type -> Idris Type
-- recursiveRef name ty =
--   do laterType <- applyLater' ty
--      return $ P Ref (sMN 0 (show name ++ "_rec")) laterType
