\begin{code}
{-# LANGUAGE ViewPatterns #-}
module Idris.GuardedRecursion.InferTerm(inferGRTerm) where

import Idris.Core.TT

import Idris.AbsSyntax
import Idris.Error

import Idris.GuardedRecursion.Helpers
import Idris.GuardedRecursion.BuiltinHandlers

import Control.Monad.Reader
\end{code}

\begin{code}
\end{code}


\begin{code}
inferGRTerm :: Term -> Type -> Modality -> Term -> GR Term
inferGRTerm tm ty modality iota = do lift $ iLOG "Entering inference"
                                     checkCheck Open modality iota tm ty
\end{code}

\begin{code}
inferInfer :: Bool -> Clock -> Modality -> Term -> Term -> GR (Term, Type)
inferInfer True = infer
inferInfer False = infer'
  where
    infer' clock modality iota e =
      do (e', a) <- infer clock modality iota e
         case unapplyForallClocks a of
          Just a' -> do e'' <- lift $ applyApplyClock a' e'
                        return (e'', a')
          Nothing -> return (e', a)

synchronize :: Clock -> Modality -> Term -> Term -> Term -> GR (Int, Term, Term)
synchronize clock modality iota f x =
  do (f', f'Ty) <- inferInfer False clock modality iota f
     (x', x'Ty) <- inferInfer True clock modality iota x
     let (n, f'Ty') = unapplyLaters f'Ty
     let (m, _) = unapplyLaters x'Ty
     disambiguate f' x' (m-n) f'Ty f'Ty'
  where
    disambiguate f' x' n _ f'Ty' | n < 0 = 
      do ((_,a),_) <- debind f'Ty'
         x'Next <- checkCheck clock modality iota x' =<< (lift $ applyLaters n a)
         return (n, f', x'Next)
    disambiguate f' x' n f'Ty _ | n > 0 =
      do f'Next <- checkCheck clock modality iota f' =<< (lift $ applyLaters (abs n) f'Ty)
         return (abs n, f'Next, x')
    disambiguate f' x' n _ _ | n == 0 =
      return (0, f', x')

\end{code}

\begin{code}
infer :: Clock -> Modality -> Term -> Term -> GR (Term, Type)
\end{code}

The App rule:

IE |- f : A -> B => g up A' -> B'   IE |- x : A => y down A'
------------------------------------------------------------
         IE |- f x : B => g y : B'
\begin{code}
infer clock modality iota (App f x) =
  do lift $ iLOG $ "infer App: " ++ show (App f x)
     --(n, g, y) <- synchronize clock modality iota f x
     (g, a'tob') <- inferInfer False clock modality iota f
     -- let (n, ty) = unapplyLaters a'tob'
     -- ((a'Name,a'), b') <- debind ty
     --let (_, ty) = unapplyLaters a'tob'
     lift $ iLOG $ "g : " ++ show g
     lift $ iLOG $ "a'tob' : " ++ show a'tob'
     let (n, ty) = unapplyLaters a'tob'
     ((a'Name,a'),b') <- debind ty
     --(y, yTy) <- inferInfer True clock modality iota x
     --let (m, yTy') = unapplyLaters yTy
     disambiguate g n a'Name a' b' a'tob'
  where
    disambiguate g n a'Name a' b' a'tob'
      | a'Name `occursBoundIn` b',
        Just g' <- unapplyNexts g n =
          do lift $ iLOG $ "g' : " ++ show g'
             y <- checkCheck clock modality iota x a'
             lift $ iLOG $ "y : " ++ show y
             nextApp <- lift $ applyNexts (App g' y) b' n
             laterB' <- typeOf' nextApp
             return (nextApp, laterB')
      | n <= 0 = do lift $ iLOG $ "infer App no laters"
                    (yInferred, yiTy) <- inferInfer True clock modality iota x
                    lift $ iLOG $ "yInferred : " ++ show yInferred
                    lift $ iLOG $ "yiTy : " ++ show yiTy
                    let (m, yiTy') = unapplyLaters yiTy
                    let (a'L, _) = unapplyLaters a'
                    if m == a'L
                       then do laterB' <- lift $ applyLaters m b'
                               return (App g yInferred, instantiate yInferred laterB')
                       else if m > 0
                               then do lift $ iLOG $ "g : " ++ show g
                                       g' <- lift $ applyNexts g a'tob' m
                                       lift $ iLOG $ "g' : " ++ show g'
                                       laterApp <- lift $ applyLaterApp a' b' m g' yInferred
                                       laterB' <- lift $ applyLaters m b'
                                       lift $ iLOG $ "laterB' : " ++ show laterB'
                                       return (laterApp, laterB')
                               else do lift $ iLOG $ "ELSE"
                                       y <- checkCheck clock modality iota x a' 
                                       lift $ iLOG $ show (App g y)
                                       return (App g y, instantiate y b')
      -- | n <= 0,
      --   m > 0  = do lift $ iLOG $ "infer App no fun laters"
      --               g' <- lift $ applyNexts g a'tob' m
      --               laterApp <- lift $ applyLaterApp a' b' m g' z
      --               laterB' <- lift $ applyLaters m b'
      --               return (laterApp, laterB')
      | n > 0  = do lift $ iLOG $ "infer App later : " ++ show (App g x) 
                    laterB' <- lift $ applyLaters n b'
                    y <- checkCheck clock modality iota x =<< (lift $ applyLaters n a')
                    laterApp <- lift $ applyLaterApp a' b' n g y
                    lift $ iLOG $ show laterApp
                    return (laterApp, laterB')

\end{code}

The phi rule:

IE |- e =phi= e'      IE |- e' : A'
------------------------------------
      IE |- e : A => e' |> A'

\begin{code}
-- infer clock modality e =
--   do lift $ iLOG $ "phi: " ++ show e
--      e' <- phiEq e
--      lift $ iLOG $ "e phiEq: " ++ show e'
--      ie <- ask
--      let gamma = typingContext ie
--      a' <- lift $ typeOf e' gamma
--      return (e', a')

infer clock modality iota e
  | e == iota =
     do lift $ iLOG $ "recRef " ++ show e
        ie <- ask
        let grRecRef = guardedRecursiveReference ie
        grRecRefTy <- typeOf' grRecRef
        return (grRecRef, grRecRefTy)
  | otherwise =
     do lift $ iLOG $ "phi: " ++ show e
        e' <- phiEq e
        lift $ iLOG $ "e phiEq: " ++ show e'
        a' <- typeOf' e'
        return (e', a')     
\end{code}

The Refl rule:

----------------------
IE |- e : A => e up A
\begin{code}
-- This rule is currently subsumed by the phi rule. The effect should be equivalent.
infer clock modality iota e =
  do lift $ iLOG $ "Refl: " ++ show e
     a <- typeOf' e
     return (e, a)
\end{code}

\begin{code}
checkCheck :: Clock -> Modality -> Term -> Term -> Type -> GR Term
checkCheck clock modality iota e a =
  do ie <- ask
     let env = typingContext ie
     ok <- lift $ checkGoal env e a
     if ok
        then return e
        else do e' <- check clock modality iota e a
                ok' <- lift $ checkGoal env e' a
                if ok'
                   then return e'
                   else lift $ ifail "ERROR"
\end{code}

\begin{code}
check :: Clock -> Modality -> Term -> Term -> Type -> GR Term

\end{code}
The Next rule:

IE |- e : A => e' : A 
---------------------------------
IE |- e : A => Next e' : Later A
\begin{code}
check Open modality iota e (unapplyLater -> Just a') | e /= iota && not (isApp e) =
  do lift $ iLOG $ "Next: " ++ show e
     e' <- checkCheck Open modality iota e a'
     lift $ applyNext a' e'

-- check Open modality iota (App f x) a@(unapplyLater -> Just _) =
--   do (g, gTy) <- inferInfer False Open modality iota f
--      let (req, b) = unapplyLaters a
--      let (n, gTy') = unapplyLaters gTy
--      ((a'Name,a'), b') <- debind gTy'
--      g' <- lift $ applyNexts g gTy (req-n)
--      y <- checkCheck Open modality iota x =<< (lift $ applyLaters req a')
--      disambiguate g y req a'Name a' b'
--   where
--     disambiguate g y req a'Name a' b'
--       | a'Name `occursBoundIn` b',
--         Just g' <- unapplyNexts g req,
--         Just y' <- unapplyNexts y req =
--           do nextApp <- lift $ applyNexts (App g' y') b' req
--              laterB' <- typeOf' nextApp
--              return nextApp
--       | otherwise =
--           do laterB' <- lift $ applyLaters req b'                    
--              laterApp <- lift $ applyLaterApp a' b' req g y
--              lift $ iLOG $ show laterApp
--              return laterApp
\end{code}

The LambdaKappa rule:

     IE |- e : A => e' <| B
----------------------------------------------
IE |- e : A => LambdaClock e' <| ForallClocks B
\begin{code}
check Closed modality iota e (unapplyForallClocks -> Just b) =
  do lift $ iLOG $ "LambdaClock: " ++ show e
     e' <- checkCheck Open modality iota e b
     lift $ applyLambdaClock b e'
\end{code}

Infer rule:

IE |- e : A => e' |> B
----------------------
IE |- e : A => e' <| B
\begin{code}
check clock modality iota e b =
  do lift $ iLOG $ "check catch-all: " ++ show e
     (e', b') <- inferInfer True clock modality iota e
     disambiguate e' b b'
  where
    disambiguate e' b@(unapplyForallClocks -> Nothing) (unapplyForallClocks -> Just b') =
      do ok <- cEq' b b'
         if ok
            then do lift $ iLOG $ "applyClock: " ++ show e'
                    lift $ applyApplyClock b' e'
            else return e'
    disambiguate e' _ _ =
      do --lift $ iLOG $ "checkinfer: " ++ show e
         -- (e', b') <- infer clock modality iota e
         lift $ iLOG $ "inferred: " ++ show e'
         return e'
\end{code}

\begin{code}
phiEq :: Term -> GR Term
phiEq t = do ie <- ask
             let phi = renamingContext ie
             gt <- lift $ guardedTT phi t
             return gt

-- tryCheck :: Clock -> Modality -> Term -> Term -> Type -> (Type -> GR Type) -> GR (Either Term (Term, Type))
-- tryCheck clock modality iota e a f =
--   do a' <- f a
--      catchError ((checkCheck clock modality iota e a' >>= \e' -> return (Left e'))
--                 (const $ (inferclock modality iota e a >>= \e' -> (e', False))
\end{code}
