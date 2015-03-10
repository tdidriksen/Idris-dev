{-|
repeat : (a : Type) -> a -> Stream a
repeat a x = MkStream a x (repeat a x)

grepeat' : (a : Type) -> Later' (a -> gStream a) -> a -> gStream a
grepeat' a rec x = gMkStream a x (laterApp rec (Next x))

grepeat : (a : Type) -> ForallKappa (a -> gStream a)
grepeat a = /\k. fix(grepeat' a)
-}

module Idris.GuardedRecursion.InferCausalFixedPoint where

import Idris.Core.TT

import Idris.GuardedRecursion.BuiltinHandlers
import Idris.GuardedRecursion.Helpers

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

-- This function only handles parameters when they are bound before any non-parameters
quantifiedType :: Type -> GR Type
quantifiedType (Bind n binder sc)
  | occursBoundIn n sc = do qsc <- quantifiedType sc
                            return $ Bind n binder qsc
quantifiedType ty = applyForallKappa ty

--occursBoundIn n ty = 
           
-- quantifiedType :: Type -> GR Type
-- quantifiedType ty = applyForallKappa ty

-- liftedType :: Type -> Type
-- liftedType ty = liftedType' ty [] []
--  where
--    liftedType' (Bind n (Pi _ ty _) sc) binders used = let boundVarsInTy = fst $ boundVars ty
                                                          

-- universallyQuantify :: Modality -> Type -> Idris Type
-- universallyQuantify NonCausal (Bind n binder@(Pi _ (unapplyForall -> Just ty) kind) sc) =
-- do quantifiedSc <- universallyQuantify NonCausal sc
-- return $ Bind n binder quantifiedSc
-- universallyQuantify NonCausal (Bind n (Pi implInfo ty@(unapplyForall -> Nothing) kind) sc) =
-- do quantifiedSc <- universallyQuantify NonCausal sc
-- forallTy <- applyForall ty
-- return $ Bind n (Pi implInfo forallTy kind) quantifiedSc
-- universallyQuantify NonCausal (unapplyForall -> Just ty) = return ty
-- universallyQuantify NonCausal ty@(unapplyForall -> Nothing) = return ty
-- universallyQuantify Causal ty = applyForall ty
