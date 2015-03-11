{-# LANGUAGE ViewPatterns #-}

module Idris.GuardedRecursion.InferCausalFixedPoint where

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.GuardedRecursion.BuiltinHandlers
import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.InferTerm

import Idris.AbsSyntax

import Control.Monad.Reader

import qualified Data.Foldable as F



-- boundNamesIn :: TT n -> [Name]
-- boundNamesIn p@(P Bound _ ty) = p : boundNamesIn ty
-- boundNamesIn (P nt _ ty) | nt /= Bound = boundNamesIn ty
-- boundNamesIn (Bind n binder sc) = F.foldr' (\t acc -> boundNamesIn t ++ acc) (boundNamesIn sc) binder
-- boundNamesIn (App t t') = boundNamesIn t ++ boundNamesIn t'
-- boundNamesIn (Proj tm _) = boundNamesIn tm
-- boundNamesIn _ = []

occursBoundIn :: Name -> Type -> Bool
-- If shadowed, the given name does not occur. Instead, the newly binded name occurs.
occursBoundIn n (Bind n' binder sc) | n == n' = False
occursBoundIn n (Bind n' binder sc) = F.foldr' (\t acc -> occursBoundIn n t || acc) (occursBoundIn n sc) binder
occursBoundIn n (P Bound n' ty) | n == n' = True
occursBoundIn n (P _ _ ty) = occursBoundIn n ty
occursBoundIn n (App t t') = occursBoundIn n t || occursBoundIn n t'
occursBoundIn n (Proj t _) = occursBoundIn n t
occursBoundIn n _ = False

splitFixDefType :: Type -> (Type -> Type, Type)
splitFixDefType ty = splitqt ty id
  where
    splitqt :: Type -> (Type -> Type) -> (Type -> Type, Type)
    splitqt (unapplyForallKappa -> Just ty) f = (f, ty)
    splitqt (Bind n binder sc) f = splitqt sc (Bind n binder . f)


{-|
repeat : (a : Type) -> a -> Stream a
repeat a x = MkStream a x (repeat a x)

grepeat' : (a : Type) -> Later' (a -> gStream a) -> a -> gStream a
grepeat' a rec x = gMkStream a x (laterApp rec (Next x))

grepeat : (a : Type) -> ForallKappa (a -> gStream a)
grepeat a = /\k. fix(grepeat' a)
-}



-- causalFixDef :: GR (Term, Term)
-- causalFixDef = (fixDefLhs, fixDefRhs)

-- This function only handles parameters when they are bound before any non-parameters
fixDefType :: Type -> GR Type
fixDefType (Bind n binder sc)
  | occursBoundIn n sc = do qsc <- fixDefType sc
                            return $ Bind n binder qsc
fixDefType ty = applyForallKappa ty

fixDefLhs :: GR Term
fixDefLhs = undefined

fixDefRhs :: Type -> Name -> Type -> [Term] -> GR Term
fixDefRhs fixDefTy auxName auxType params = 
  do let (_, typeUnderQuantifier) = splitFixDefType fixDefTy
     let fixedTerm = mkApp (P Ref auxName auxType) params
     fix <- applyFix typeUnderQuantifier fixedTerm
     applyLambdaKappa typeUnderQuantifier fix

recRefType :: Type -> Env -> GR (Type -> Type)
recRefType ty env = do ty' <- applyLater' ty
                       ty'ty <- typeOf ty' env
                       ctxt <- lift getContext
                       let recBinderName = uniqueNameCtxt ctxt (sUN "rec") (map fst env)
                       return $ Bind recBinderName (Pi Nothing ty' ty'ty)

auxDefType :: Type -> GR Type
auxDefType ty = do fixTy <- fixDefType ty
                   let (paramsPart, quantifiedPart) = splitFixDefType fixTy
                   recRefTy <- recRefType quantifiedPart (bindersIn fixTy)
                   return $ (paramsPart . recRefTy) quantifiedPart

auxDefLhs :: Term -> GR Term
auxDefLhs _ = undefined

auxDefRhs :: Term -> Type -> GR Term
auxDefRhs rhs guardedTy = inferGRTerm rhs guardedTy Open Causal

