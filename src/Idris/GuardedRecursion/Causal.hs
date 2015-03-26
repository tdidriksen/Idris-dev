{-# LANGUAGE ViewPatterns #-}

module Idris.GuardedRecursion.Causal where

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.GuardedRecursion.BuiltinHandlers
import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.InferTerm
import Idris.GuardedRecursion.Renaming

import Idris.AbsSyntax

import Control.Monad.Reader

import qualified Data.Foldable as F
import Data.List



-- boundNamesIn :: TT n -> [Name]
-- boundNamesIn p@(P Bound _ ty) = p : boundNamesIn ty
-- boundNamesIn (P nt _ ty) | nt /= Bound = boundNamesIn ty
-- boundNamesIn (Bind n binder sc) = F.foldr' (\t acc -> boundNamesIn t ++ acc) (boundNamesIn sc) binder
-- boundNamesIn (App t t') = boundNamesIn t ++ boundNamesIn t'
-- boundNamesIn (Proj tm _) = boundNamesIn tm
-- boundNamesIn _ = []

-- splitFixDefType :: Type -> (Type -> Type, Type)
-- splitFixDefType ty = splitqt ty id
--   where
--     splitqt :: Type -> (Type -> Type) -> (Type -> Type, Type)
--     splitqt (unapplyForallKappa -> Just ty) f = (f, ty)
--     splitqt (Bind n binder sc) f = splitqt sc (Bind n binder . f)

-- splitFixDefType :: Type -> ([(Name, Binder Type)], Type)
-- splitFixDefType ty = splitqt ty []
--   where
--     splitqt :: Type -> [(Name, Binder Type)] -> ([(Name, Binder Type)], Type)
--     splitqt (unapplyForallKappa -> Just ty) binders = (binders, ty)
--     splitqt (Bind n binder sc) binders = splitqt sc (binders ++ [(n, binder)])


{-|
repeat : (a : Type) -> a -> Stream a
repeat a x = MkStream a x (repeat a x)

grepeat' : (a : Type) -> Later' (a -> gStream a) -> a -> gStream a
grepeat' a rec x = gMkStream a x (laterApp rec (Next x))

grepeat : (a : Type) -> ForallKappa (a -> gStream a)
grepeat a = /\k. fix(grepeat' a)
-}

--guardedLhs :: Term -> GR (Term, Term)

-- causalFixDef :: GR (Term, Term)
-- causalFixDef = (fixDefLhs, fixDefRhs)

-- This function only handles parameters when they are bound before any non-parameters
-- fixDefType :: Type -> GR Type
-- fixDefType (Bind n binder sc)
--   | occursBoundIn n sc = do qsc <- fixDefType sc
--                             return $ Bind n binder qsc
-- fixDefType ty = applyForallKappa ty

-- splitFixDefType :: Type -> ([(Name, Binder Type)], Type)
-- splitFixDefType ty = splitqt ty []
--   where
--     splitqt :: Type -> [(Name, Binder Type)] -> ([(Name, Binder Type)], Type)
--     splitqt (unapplyForallKappa -> Just ty) binders = (binders, ty)
--     splitqt (Bind n binder sc) binders = splitqt sc (binders ++ [(n, binder)])

causalFixDefType :: Type -> Idris Type
causalFixDefType ty = applyForallClocks =<< causalFixDefTypeUnderQuantifier [] ty

causalFixDefTypeUnderQuantifier :: Env -> Type -> Idris Type
causalFixDefTypeUnderQuantifier env (Bind n (Pi impl ty kind) sc) =
  do renamedType <- renameType env ty
     let renamedBinder = Pi impl renamedType kind
     sc' <- causalFixDefTypeUnderQuantifier ((n, renamedBinder):env) sc
     return $ Bind n renamedBinder sc'
causalFixDefTypeUnderQuantifier env ty = renameType env ty

renameType :: Env -> Type -> Idris Type
renameType env (Bind n (Pi impl ty kind) sc) =
  do renamedBinderTy <- renameType env ty
     sc' <- renameType ((n, Pi impl renamedBinderTy kind):env) sc
     return $ Bind n (Pi impl renamedBinderTy kind) sc'
renameType env (unapplyLazy' -> Just ty) =
  renameType env ty
renameType env ty =
  do ctxt <- getContext
     iLOG $ "rename ty: " ++ show ty
     let (f, args) = unApply (explicitNames (normalise ctxt env ty))
     case f of
      P nt n pty ->
         do rename <- fetchGuardedRename n
            case rename of
             Just rn -> do renamedArgs <- mapM (renameType env) args
                           return $ mkApp (P nt rn pty) renamedArgs
             Nothing -> return ty
      ty' -> return ty'

splitCausalType :: Type -> ([(Name, Binder Type)], Type)
splitCausalType (unapplyForallClocks -> Just ty) =
  splitCausalType ty
splitCausalType ty = splitType ty


typeAfterParameters :: Type -> Type
typeAfterParameters ty = snd (splitCausalType ty)

recRefType :: Type -> Idris Type
recRefType ty = applyLater' (typeAfterParameters ty)

causalRecRef :: [Name] -> Type -> Idris (Term, (Name, Binder Type))
causalRecRef pvs ty = do ctxt <- getContext
                         let recName = uniqueNameCtxt ctxt (sUN "rec") pvs
                         recTy <- recRefType ty
                         return ((P Ref recName recTy),(recName, PVar recTy))

causalEnv :: [Name] -> Term -> Type -> Idris Env
causalEnv pvs lhs ty = do let (_, args) = unApply lhs
                          iLOG $ "pvs: " ++ show pvs
                          entries <- foldArgs pvs [] args
                          return $ nubBy (\(x,_) (y,_) -> x == y) entries
  where    
    addEnvEntries :: [Name] -> Env -> Term -> Maybe Type -> Idris Env
    addEnvEntries pvs env (P Bound n ty) Nothing
      | n `elem` pvs = do renamedType <- renameType env ty
                          return $ (n, PVar renamedType) : env
    addEnvEntries pvs env (P Bound n ty) (Just ty')
      | n `elem` pvs = return $ (n, PVar ty') : env
    addEnvEntries pvs env t@(App _ _) _ =
      do let (f, args) = unApply t
         entriesFromRename env args f
      where
       entriesFromRename :: Env -> [Term] -> Term -> Idris Env
       entriesFromRename env args (P nt n ty) =
        do renameTy <- typeOfGuardedRename n env
           case renameTy of
            Just rnTy ->
             do let argWithTy = zip args (map snd (getArgTys (explicitNames rnTy)))
                foldM (\acc (arg, argTy) -> addEnvEntries pvs acc arg (Just argTy)) env argWithTy
            Nothing -> foldArgs pvs env args
       entriesFromRename env args _ = foldArgs pvs env args
    addEnvEntries _ env _ _ = return env

    foldArgs pvs env args = foldM (\acc arg -> addEnvEntries pvs acc arg Nothing) env args

     
     
                   

-- fixDefLhs :: Name -> Term -> Type -> GR Term
-- fixDefLhs n lhs guardedTy =
--   do let (P Ref n ty, args) = unApply lhs
--      guardedArgs <- guardedParamArgs args
--      ctxt <- lift getContext
--      let guardedName = uniqueNameCtxt ctxt [] n
--      return $ mkApp (P Ref guardedName ty) guardedArgs

-- guardedParamArgs :: [Term] -> Type -> GR [Term]
-- guardedParamArgs args guardedTy =
--   let (paramBinders, _) = splitFixDefType guardedTy
--   in guardedArgs paramBinders [] args
--   where
--    guardedArgs :: [(Name, Binder Term)] -> [(Name, Term)] -> [Term] -> GR [Term]
--    guardedArgs (p:params) inScope (arg:args) =
--     do gArg <- guardedArg p inScope arg
--        gArgs <- guardedArgs params (inScope ++ [(fst p, binderTy (snd p))]) args
--        return $ gArg : gArgs
--    guardedArgs [] _ _ = return []
--    guardedArgs _ _ [] = ifail $ "Function has fewer arguments than is described by its type" 

--    guardedArg :: (Name, Binder Term) -> [(Name, Term)] -> Term -> GR Term
--    guardedArg (pName, pBinder) inScope p@(P Bound n nTy) = 
--      do hasCoType <- hasCoinductiveType p
--         if hasCoType
--            then return $ P Bound n (substNames inScope (binderTy pBinder))
--            else return p
--    guardedArg (pName, pBinder) inScope (App f x) =
--      do matchesCodata <- matchesOnCoinductiveData (App f x) inScope
--         if matchesCodata
--            then lift $ ifail $ "Argument pattern " ++ show (App f x) ++ " pattern matches on coinductive data"
--            else do f' <- guardedArg (pName, pBinder) inScope f
--                    x' <- guardedArg (pName, pBinder) inScope x
--                    return $ App f' x'
--    guardedArg _ _ t = return t

--     guardedArgs :: [(Name, Type)] -> [(Name, Type)] -> [Term] -> GR [Term]
--     guardedArgs ((a, aTy):argTys) inScope ((P Bound n nTy):args) =
--       do let aTy' = substNames inScope aTy
--          args' <- guardedArg argTys ((a, (P Bound n aTy')):inScope) args
--          return $ P Bound n aTy' : args'
--     guardedArgs ((a, aTy):argTys) inScope ((App f x):args) =
--       do -- Check if type is coinductive
--          hasCoType <- hasCoinductiveType (App f x) inScope
--          -- If yes, fail
--          if hasCoType
--             then -- fail
--             else 
         -- If no, call recursively
         -- matchesOnCoinductiveData = mapMTT ...

-- fixDefRhs :: Type -> Name -> Type -> [Term] -> GR Term
-- fixDefRhs fixDefTy auxName auxType params = 
--   do let (_, typeUnderQuantifier) = splitFixDefType fixDefTy
--      let fixedTerm = mkApp (P Ref auxName auxType) params
--      fix <- applyFix typeUnderQuantifier fixedTerm
--      applyLambdaKappa typeUnderQuantifier fix

-- recRefTypeBinder :: Type -> Env -> GR (Name, Binder Type)
-- recRefTypeBinder ty env = do ty' <- applyLater' ty
--                              ty'ty <- typeOf ty' env
--                              ctxt <- lift getContext
--                              let recBinderName = uniqueNameCtxt ctxt (sUN "rec") (map fst env)
--                              return (recBinderName, (Pi Nothing ty' ty'ty))


-- auxDefType :: Type -> GR Type
-- auxDefType ty = do fixTy <- fixDefType ty
--                    let (params, typeUnderQuantifier) = splitFixDefType fixTy
--                    recTyBinder <- recRefTypeBinder typeUnderQuantifier (bindersIn fixTy)
--                    return $ bindAll (params ++ [recTyBinder]) typeUnderQuantifier

-- auxDefLhs :: Term -> GR Term
-- auxDefLhs _ = undefined

-- auxDefRhs :: Term -> Type -> GR Term
-- auxDefRhs rhs guardedTy = inferGRTerm rhs guardedTy Open Causal

