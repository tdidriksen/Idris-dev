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

import Data.List
import qualified Data.Map as M

import Control.Monad
import Control.Monad.State

checkGuardedRecursive :: Name -> Idris Totality
checkGuardedRecursive n =
  do ctxt <- getContext
     skip <- isLhsProj n
     if skip
        then return $ Partial NotProductive
        else do case lookupDef n ctxt of
                 [CaseOp _ ty _ _ clauses _] ->
                   do logLvl 0 $ "Checking function " ++ show n
                      forM_ clauses $ \(pvs, lhs, rhs) ->
                        do iLOG $ show ("GR_LHS: " ++ showTT lhs)
                           iLOG $ show ("GR_RHS: " ++ showTT rhs)
                      ctxt <- getContext
                      t <- case lookupTyExact n ctxt of
                            Just nty -> checkFunction n nty clauses
                            Nothing -> checkFunction n ty clauses
                      -- i <- get
                      -- case lookupCtxt n (idris_flags i) of
                      --  [fnOpts] -> setFlags n (fnOpts \\ [CausalFn])
                      --  _ -> return ()
                      logLvl 0 $ "Checked function " ++ show n ++ ":"
                      logLvl 0 $ show t
                      return t
                 _ -> return $ Partial NotProductive

isLhsProj :: Name -> Idris Bool
isLhsProj name = do i <- get
                    case M.lookup name (lhs_projections i) of
                     Just _ -> return True
                     Nothing -> return False

checkFunction :: Name -> Type -> [([Name], Term, Term)] -> Idris Totality
checkFunction name ty clauses =
  do let expTy = explicitNames ty
     let expClauses = flip map clauses $ \(pvs, lhs, rhs) -> (pvs, explicitNames lhs, explicitNames rhs)
     gName <- getGuardedNameSoft name
     modality <- modalityOf name
     iLOG $ show gName ++ " is " ++ show modality
     iLOG $ "expTy : " ++ showTT expTy
     gTy <- guardedType expTy modality
     iLOG $ "gTy : " ++ show gTy
     ist <- get
     ctxt <- getContext
     gClauses <- forM expClauses $ \clause -> guardedRecursiveClause gName gTy clause modality
     iLOG $ show "Guarded type: " ++ show gTy
     forM_ gClauses $ \(lhs, rhs, _) ->
       do iLOG $ show ("GR_LHS_EPS: " ++ show lhs)
          iLOG $ show ("GR_LHS_EPS_AST: " ++ showTT lhs)
          iLOG $ show ("GR_RHS_EPS: " ++ show rhs)
          iLOG $ show ("GR_RHS_EPS_AST: " ++ showTT rhs)
     checkRhsSeq <- forM gClauses $ \(lhs,rhs,rhTy) -> guardedRecursiveCheck modality gName gTy lhs rhs rhTy 
     iLOG $ "Checked: " ++ show name
     iLOG $ show checkRhsSeq
     return $ foldr mergeTotal (Total []) checkRhsSeq
     --idrisCatch (sequence checkRhsSeq) (\e -> )    

guardedType :: Type -> Modality -> Idris Type
guardedType ty modality =
  do gTy <- guardedTT' ty
     universallyQuantify modality gTy

universallyQuantify :: Modality -> Type -> Idris Type
universallyQuantify NonCausal (Bind n binder@(Pi _ (unapplyForall -> Just ty) kind) sc) =
  do quantifiedSc <- universallyQuantify NonCausal sc
     return $ Bind n binder quantifiedSc
universallyQuantify NonCausal (Bind n (Pi implInfo ty@(unapplyForall -> Nothing) kind) sc) =
  do quantifiedSc <- universallyQuantify NonCausal sc
     forallTy <- applyForall ty
     return $ Bind n (Pi implInfo forallTy kind) quantifiedSc
universallyQuantify NonCausal (unapplyForall -> Just ty) = return ty
universallyQuantify NonCausal ty@(unapplyForall -> Nothing) = return ty
universallyQuantify Causal ty = applyForall ty

guardedLHS :: Term -> Idris Term
guardedLHS lhs = guardedTT' (removeLaziness lhs)

guardedRecursiveCheck :: Modality -> Name -> Type -> Term -> Term -> Type -> Idris Totality
guardedRecursiveCheck modality recName ty lhs rhs rhTy =
  do env <- buildGuardedEnv modality lhs
     let appliedType = case unapplyForall ty of
                         Just ty' -> ty'
                         Nothing -> ty
     recTy <- applyForall $ withoutParams appliedType
     checkGR modality env (recName, recTy) rhs rhTy
                         

guardedRecursiveClause :: Name -> Type -> ([Name], Term, Term) -> Modality -> Idris (Term, Term, Type)
guardedRecursiveClause _ _ (_, lhs, Impossible) _ = return (lhs, Impossible, Impossible)
guardedRecursiveClause name ty (_, lhs, rhs) modality =
  do ctxt <- getContext
     rhsTy <- typeOf rhs (buildEnv lhs)
     gRhsTy <- guardedType rhsTy modality
     ist <- get
     put $ ist { tt_ctxt = addTyDecl name Ref ty ctxt }
     glhs <- guardedLHS lhs
     iLOG $ "Guarded LHS: " ++ show glhs
     let appliedType = case unapplyForall ty of
                        Just ty' -> ty'
                        Nothing -> ty
     iLOG $ "appliedType : " ++ show appliedType
     gEnv <- buildGuardedEnv modality lhs
     grhs <- epsilon modality name rhs gRhsTy (parameterArgs glhs appliedType) gEnv
     return (glhs, grhs, gRhsTy)
     

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
