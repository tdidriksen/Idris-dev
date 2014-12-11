\documentclass{article}
%include polycode.fmt
\begin{document}

\begin{code}
{-# LANGUAGE ViewPatterns #-}
module Idris.GuardedRecursion.Epsilon where

import Idris.Core.TT

import Idris.AbsSyntaxTree
import Idris.Error

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Helpers

epsilon :: Name -> Term -> Type -> Env -> Clock -> Idris Term
epsilon recName (lambdaKappaTerm -> Just tm) (forallType -> Just ty) env EmptyClock =
  epsilon recName tm ty env Kappa
epsilon recName tm (forallType -> Just ty) env EmptyClock = undefined
--  epsilon recName ()
epsilon _ tm (forallType -> Just ty) _ Kappa =
  ifail $ "Cannot build guarded recursive term from term " ++ show tm ++ ": Attempt to open more than one clock."
-- epsilon recName (P Ref n _) (laterType -> Just ty) env Kappa
--   | n == recName = applyNext 

\end{code}

\end{document}
