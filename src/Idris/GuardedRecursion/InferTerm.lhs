\begin{code}
{-# LANGUAGE ViewPatterns #-}
module Idris.GuardedRecursion.InferTerm(inferGRTerm) where

import Idris.Core.TT

import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.BuiltinHandlers
\end{code}

\begin{code}
\end{code}


\begin{code}
inferGRTerm :: Term -> Type -> GR Term
inferGRTerm _ _ = undefined
\end{code}

\begin{code}
infer :: Clock -> Modality -> Term -> GR Term
infer _ _ e = return e
\end{code}

\begin{code}
check :: Clock -> Modality -> Term -> Type -> GR Term
check Open modality e (unapplyLater -> Just a) =
  do e' <- check Open modality e a
     applyNext e' a
check _ _ e _ = return e
\end{code}
