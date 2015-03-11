\begin{code}
{-# LANGUAGE ViewPatterns #-}
module Idris.GuardedRecursion.InferTerm(inferGRTerm) where

import Idris.Core.TT

import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.BuiltinHandlers

import Control.Monad.Reader
\end{code}

\begin{code}
\end{code}


\begin{code}
inferGRTerm :: Term -> Type -> Clock -> Modality -> GR Term
inferGRTerm _ _ _ _ = undefined
\end{code}

\begin{code}
infer :: Clock -> Modality -> Term -> GR (Term, Type)
\end{code}

The App rule:

IE |- f : A -> B => g up A' -> B'   IE |- x : A => y down A'
------------------------------------------------------------
         IE |- f x : B => g y : B'
\begin{code}
infer clock modality (App f x) =
  do (g, a'tob') <- infer clock modality f
     (a', b') <- debind a'tob'
     y <- check clock modality x a'
     return (App g y, b')
\end{code}

The Refl rule:

----------------------
IE |- e : A => e up A
\begin{code}
infer clock modality e =
  do ie <- ask
     let gamma = typingContext ie
     a <- typeOf e gamma
     return (e, a)
\end{code}

\begin{code}
check :: Clock -> Modality -> Term -> Type -> GR Term

\end{code}
The Next rule:

IE |- e : A => e' : A 
---------------------------------
IE |- e : A => Next e' : Later A
\begin{code}
check Open modality e (unapplyLater -> Just a) =
  do e' <- check Open modality e a
     applyNext e' a
check _ _ e _ = return e
\end{code}
