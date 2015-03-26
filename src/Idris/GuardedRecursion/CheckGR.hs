module Idris.GuardedRecursion.CheckGR(checkGuardedRecursive) where

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.AbsSyntax

import Idris.GuardedRecursion.BuiltinHandlers
import Idris.GuardedRecursion.Causal
import Idris.GuardedRecursion.Exports
import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.InferTerm
import Idris.GuardedRecursion.Renaming

import Control.Monad.Reader

import Data.Maybe

type Clause = ([Name], Term, Term)
type Clauses = [Clause]

checkGuardedRecursive :: Name -> Idris Totality
checkGuardedRecursive n =
  do ctxt <- getContext
     case lookupDef n ctxt of
       [CaseOp _ ty _ _ clauses _] ->
         do modality <- modalityOf n
            checkFunction n modality (explicitNames ty) clauses
       _ -> return $ Partial NotProductive

checkFunction :: Name -> Modality -> Type -> Clauses -> Idris Totality
checkFunction n Causal ty clauses =
  do fixDefType <- causalFixDefType ty
     gRhss <- forM clauses $ \(pvs,lhs,rhs) ->
               do let rhs' = removeLaziness rhs
                  iLOG $ "Input type: " ++ show ty
                  iLOG $ "FixDefType: " ++ show fixDefType
                  iLOG $ "After parameters: " ++ show (typeAfterParameters fixDefType)
                  env <- causalEnv pvs lhs ty
                  (grecRef, recEntry) <- causalRecRef pvs fixDefType
                  let env' = recEntry : env
                  iLOG $ "Causal env: " ++ show env'
                  recRefTy <- recRefType fixDefType
                  iLOG $ "Type of recursive reference: " ++ show recRefTy
                  (newRhs, recRef) <- replaceRecursiveReference n rhs' ty env'
                  iLOG $ "rhs : " ++ show rhs
                  iLOG $ "rhs' : " ++ show rhs'
                  iLOG $ "newRhs: " ++ show newRhs
                  iLOG $ "recRef: " ++ show recRef
                  initIE <- initInfEnv env' recRef grecRef
                  let rhsTy = getRetTy (typeAfterParameters fixDefType)
                  iLOG $ "rhsTy : " ++ show rhsTy
                  grTerm <- runReaderT (inferGRTerm newRhs rhsTy Causal recRef) initIE
                  iLOG $ "grTerm : " ++ show grTerm
                  grTermTy <- typeOf grTerm env'
                  iLOG $ "grTermTy : " ++ show grTermTy
     (GuardedRename rename) <- createAndAddRename n
     iLOG $ "Added new rename: " ++ show rename
     i <- getIState
     putIState $ i { tt_ctxt = addTyDecl rename Ref fixDefType (tt_ctxt i) }
     return $ Partial NotProductive
checkFunction _ _ _ _ = return $ Partial NotProductive

initInfEnv :: Env -> Term -> Term -> Idris InfEnv
initInfEnv gamma iota giota =
  do phi <- fetchGuardedRenames
     let pi = []
     return $ IE iota giota phi pi gamma
  where
    fetchGuardedRenames :: Idris [Renaming]
    fetchGuardedRenames =
      do i <- getIState
         let renames = guarded_renames i
         return $ mapMaybe isGuarded renames

    isGuarded :: (Name, GuardedRename) -> Maybe (Name, Name)
    isGuarded (n, GuardedRename rn) = return (n, rn)
    isGuarded _ = Nothing

    -- recRefPlaceholder :: Type -> Term
    -- recRefPlaceholder = 
