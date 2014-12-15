{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Check(checkGR) where

import Idris.Core.TT
import Idris.AbsSyntaxTree

import Idris.GuardedRecursion.Error
import Idris.GuardedRecursion.Helpers

import Control.Applicative

data Extract a = Extracted a | Nope

instance Functor Extract where
  fmap _ Nope          = Nope
  fmap f (Extracted a) = Extracted (f a)

instance Applicative Extract where
  pure = Extracted
  (Extracted f) <*> (Extracted a) = Extracted (f a)
  Nope <*> _ = Nope
  _ <*> Nope = Nope

instance Monad Extract where
  (Extracted x) >>= k = k x
  Nope          >>= _ = Nope

  (Extracted _ ) >> k = k
  Nope           >> _ = Nope

  return = Extracted
  fail _ = Nope

checkGR :: Type -> Term -> Idris ()
checkGR ty te = check EmptyClock ty te

check :: Clock -> Term -> Type -> Idris ()
-- Next
check Kappa (next -> Extracted t) (later -> Extracted a) 
  = check Kappa t a
-- Tensor
check Kappa (tensor -> Extracted (t, u)) (later -> Extracted b)
  = do a <- argTy t
       laterA <- laterK a
       laterAtoB <- laterK $ a `to` b
       check Kappa u laterA
       check Kappa t laterAtoB
-- Fix
check Kappa (fix -> Extracted (x, t)) a 
  = checkFix a x t
-- Kappa Application
check Kappa (applyKappa -> Extracted t) a 
  = do isTypeType a
       forallA <- forall a
       check Kappa t forallA
-- Kappa Abstraction
check ce (lambdaKappa -> Extracted t) (forallK -> Extracted a) 
  = do emptyEnv ce
       check Kappa t a
-- Failure --
-- Missing Clocks
check EmptyClock t a
  | expectsClock t || expectsClock a = translateError MissingClock
-- Missing Laters
check _ (next -> Extracted _) (later -> Nope)
  = translateError MissingLater
check _ (tensor -> Extracted _) (later -> Nope)
  = translateError MissingLater
-- Missing Quantification
check _ (lambdaKappa -> Extracted _) (forallK -> Nope)
  = translateError MissingForall
-- Not GR       
check _ _ _ = undefined

next :: Term -> Extract Term
next (unApply -> (f, as))
  | isNext f = return $ head as
next _ = Nope

later :: Type -> Extract Type
later (App f a)
  | isLater f = return a
later _ = Nope

laterK :: Type -> Idris Type
laterK = applyLater'

tensor :: Term -> Extract (Term, Term)
tensor (unApply -> (f, as))
  | isCompose f = do let t = head (tail as)
                     let u = head as
                     return (t, u)
tensor _ = Nope

applyKappa :: Term -> Extract Term
applyKappa (unApply -> (f, as))
  | isApply f = return $ head as
applyKappa _ = Nope                

lambdaKappa :: Term -> Extract Term
lambdaKappa (unApply -> (f, as))
  | isLambdaKappa f = return $ head as
lambdaKappa _ = Nope                      

isTypeType :: Type -> Idris ()
isTypeType (TType _) = return ()
isTypeType t = translateError (NotTypeType t)

forallK :: Type -> Extract Type
forallK (App f a)
  | isForall f = return a
forallK _ = Nope                 

forall :: Type -> Idris Type
forall = applyForall

emptyEnv :: Clock -> Idris ()
emptyEnv EmptyClock = return ()
emptyEnv _ = translateError UnexpectedClockInEnv

fix :: Term -> Extract (Term, Term)
fix = undefined

argTy :: Term -> Idris Type
argTy (unApply -> (f, _))
  = case f of
      (P _ _ ty) -> return $ snd (last (getArgTys ty))
      _ -> translateError Undefined

expectsClock :: TT Name -> Bool
expectsClock t
  = isLater'  t ||
    isLater   t ||
    isForall  t ||
    isNext    t ||
    isCompose t ||
    isApply   t ||
    isLambdaKappa t

to :: Type -> Type -> Type
to a b = Bind (sUN "__pi_arg") (Pi a undefined) b

-- 
checkFix :: Type -> Term -> Term -> Idris ()
checkFix = undefined
                  
