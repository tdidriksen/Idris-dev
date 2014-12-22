{-# LANGUAGE ViewPatterns #-}
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
import Control.Monad.State

checkGuardedRecursive :: Name -> Idris Totality
checkGuardedRecursive n =
  do ctxt <- getContext
     case lookupDef n ctxt of
        [CaseOp _ ty _ _ clauses _] ->
          do forM_ clauses $ \(pvs, lhs, rhs) ->
               do iLOG $ show ("GR_LHS: " ++ showTT lhs)
                  iLOG $ show ("GR_RHS: " ++ showTT rhs)
             _ <- checkFunction n ty clauses
             
             return $ Partial NotProductive
        _ -> return $ Partial NotProductive

checkFunction :: Name -> Type -> [([Name], Term, Term)] -> Idris Totality
checkFunction name ty clauses =
  do let expTy = explicitNames ty
     let expClauses = flip map clauses $ \(pvs, lhs, rhs) -> (pvs, explicitNames lhs, explicitNames rhs)
     gName <- getGuardedNameSoft name
     gTy <- guardedType expTy
     ist <- get
     ctxt <- getContext
     gClauses <- forM expClauses $ \clause -> guardedRecursiveClause gName gTy clause
     iLOG $ show "Guarded type: " ++ showTT gTy
     forM_ gClauses $ \(lhs, rhs) ->
       do iLOG $ show ("GR_LHS_EPS: " ++ showTT lhs)
          iLOG $ show ("GR_RHS_EPS: " ++ showTT rhs)
     --checkRhsSeq <- forM gClauses $ \(_,rhs) -> checkGR [] (gName, gTy) rhs gTy
     return $ Partial NotProductive
     --idrisCatch (sequence checkRhsSeq) (\e -> )    

guardedType :: Type -> Idris Type
guardedType ty =
  do gTy <- guardedTT' ty
     universallyQuantify gTy

universallyQuantify :: Type -> Idris Type
universallyQuantify (Bind n binder@(Pi (unapplyForall -> Just ty) kind) sc) =
  do quantifiedSc <- universallyQuantify sc
     return $ Bind n binder quantifiedSc
universallyQuantify (Bind n (Pi ty@(unapplyForall -> Nothing) kind) sc) =
  do quantifiedSc <- universallyQuantify sc
     forallTy <- applyForall ty
     return $ Bind n (Pi forallTy kind) quantifiedSc
universallyQuantify ty = applyForall ty

guardedLHS :: Term -> Idris Term
guardedLHS = guardedTT'

guardedRecursiveClause :: Name -> Type -> ([Name], Term, Term) -> Idris (Term, Term)
guardedRecursiveClause _ _ (_, lhs, Impossible) = return (lhs, Impossible)
guardedRecursiveClause name ty (_, lhs, rhs) =
  do rhsTy <- typeOf rhs []
     gRhsTy <- guardedType (explicitNames rhsTy)
     ist <- get
     ctxt <- getContext
     put $ ist { tt_ctxt = addTyDecl name Ref gRhsTy ctxt }
     glhs <- guardedLHS lhs
     iLOG $ "Guarded LHS: " ++ showTT glhs
     grhs <- epsilon name (explicitNames rhs) gRhsTy
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
