\documentclass{article}
%include polycode.fmt
\begin{document}

\begin{code}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Idris.GuardedRecursion.Epsilon where

import Idris.Core.TT
import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Error

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Helpers

import Data.List

import Control.Monad

debugEpsilon = True

epsFail tm msg = ifail $ "Cannot build guarded recursive term from term " ++ show tm ++ ": " ++ msg

epsLog :: String -> Term -> Type -> Idris ()
epsLog rule tm ty =
  let error = show rule ++ ": Term " ++ show tm ++ " should have type " ++ show ty
  in if debugEpsilon then iLOG $ error else return ()

epsLogInfer rule tm (Just tmty) goalty = iLOG $ show rule ++ ": Term" ++ showTT tm ++ " has type " ++ showTT tmty ++ " with goal " ++ showTT goalty
epsLogInfer rule tm Nothing goalty = iLOG $ show rule ++ ": Term" ++ showTT tm ++ " with goal " ++ showTT goalty
\end{code}

\begin{code}
epsilon :: Modality -> Name -> Term -> Type -> [Term] -> Env -> Idris Term
epsilon modality recName t a params env =
  do t' <- guardedTT' (removeLaziness t)
     iLOG $ "params : " ++ intercalate ", " (map show params)
     iLOG $ "Before fixing : " ++ showTT t'
     fixed <- fixRecursiveRef modality env params recName (allTTNames t') t'
     iLOG $ "Epsilon start"
     iLOG $ "Trying to infer that term " ++ show recName ++ ":\n" ++ show fixed ++ "\nhas type:\n" ++ show a
     case modality of
      Causal    -> epsilonCheck Causal Closed recName env fixed a
      NonCausal -> epsilonCheck NonCausal Open recName env fixed a

epsilonCheck :: Modality -> Clock -> Name -> Env -> Term -> Term -> Idris Term
epsilonCheck modality clock recName env t a =
  do ok <- checkGoal t a env
     if ok
        then return t
        else infer
             --(\err -> epsFail t "Top-level conversion check failed.")
  where infer = epsilonInfer modality clock recName env t a

epsilonInfer :: Modality -> Clock -> Name -> Env -> Term -> Type -> Idris Term
epsilonInfer Causal Open recName env recRef@(unapplyNext >=> unapplyApply -> Just (P Ref n _)) (unapplyLater -> Just (unapplyLater -> Nothing)) | n == recName =
  do iLOG "Found recursive ref (causal)"
--     epsLog "Recursive ref (causal" recRef
     return recRef
epsilonInfer Causal Open recName env recRef@(unapplyNext >=> unapplyApply -> Just (P Ref n _)) (unapplyLater -> Just a@(unapplyLater -> Just _)) | n == recName =
  do iLOG "Found later recursive ref (causal)"
     applyNext a =<< epsilonCheck Causal Open recName env recRef a
epsilonInfer NonCausal Open recName env recRef@(P Ref n _) _ | n == recName =
  do iLOG "Found recursive ref (non-causal)"
     return recRef
epsilonInfer NonCausal Open recName env recRef@(unApply -> (P Ref n _, args)) a | n == recName =
  do iLOG "Found later recursive ref"
     applyNext a =<< epsilonCheck NonCausal Open recName env recRef a
     
-- Binders
epsilonInfer modality clock recName env tm@(Bind n (Let letty letval) sc) a =
  do epsLog "Let binder check" tm a
     gLetVal <- epsilonCheck modality clock recName env letval letty
     let gBinder = Let letty gLetVal
     bindEps <- epsilonCheck modality clock recName ((n, gBinder):env) sc a
     return $ Bind n gBinder sc
epsilonInfer modality clock recName env tm@(Bind n binder sc) ty@(debindFirstArg -> Just a)
  | Just _ <- debindFirstArg $ binderTy binder =
      do epsLog "Function arg binder check" tm ty
         bindEps <- epsilonCheck modality clock recName ((n, binder):env) sc a
         return $ Bind n binder bindEps
epsilonInfer modality clock recName env tm@(Bind n binder sc) a
  | Nothing <- debindFirstArg $ binderTy binder =
      do epsLog "Other binder check" tm a
         bindEps <- epsilonCheck modality clock recName ((n, binder):env) sc a
         return $ Bind n binder bindEps

-- Infer tensor
-- epsilonInfer modality Open recName env t@(App f x) a | Just a' <- unapplyLater a, Just _ <- unapplyLater a' =
--   do epsLog "App Later-Later" t a
--      t' <- epsilonCheck modality Open recName env t a'
--      applyNext a' t'
epsilonInfer modality Open recName env t@(App _ _) b'@(unapplyLater -> Just b) =
  do epsLog "Tensor infer" t b'
     iLOG $ "Tensor term " ++ showTT t
     idrisCatch (applyWhenAvailable (epsilonCheck modality Open recName env) t b')  --(applyNext b =<< epsilonCheck modality Open recName env t b)
                (\err -> do iLOG $ "Error : " ++ show err
                            epsLog "Inferring tensor" t b'
                            --let (f, args) = unApply t
                            (prefix, remainingArgs) <- nextPrefix t b'
                            tensor <- inferTensor prefix remainingArgs
                            ok <- checkGoal tensor b' env
                            if ok
                               then return tensor
                               else do iLOG $ "tensor: " ++ show tensor
                                       iLOG $ "Tensor inference failed"
                                       epsFail t "Tensor inference can never be well-typed")
  where
    nextPrefix :: Term -> Type -> Idris (Term, [Term])
    nextPrefix f laterGoal@(unapplyLater -> Just goal) =
      do (prefix,remainingArgs) <- nextPrefix f goal
         prefixTy <- typeOf prefix env
         prefixRetTy <- distributeLater prefixTy >>= \ty -> return $ getRetTy ty
         nextedPrefix <- case compareAvailability prefixRetTy laterGoal of
                          LT -> applyNext prefixTy prefix
                          _ -> return prefix
         iLOG $ "Returning prefix : " ++ show nextedPrefix
         return (nextedPrefix, remainingArgs)
    nextPrefix (unApply -> (f, args)) b =
      do fType <- typeOf f env --(ifail $ "Function " ++ show f ++ " has no type.")
         let fTyBinders = binders fType
         let fEpsTy = bindAll fTyBinders b
         iLOG $ "fEpsTy : " ++ show fEpsTy
         epsF <- idrisCatch (epsilonCheck modality Open recName env f fEpsTy) (\_ -> return f)
         (prefix, remainingArgs)  <- nextPrefix' epsF args
         iLOG $ "Found prefix : " ++ show prefix
         return (prefix, remainingArgs)

    nextPrefix' :: Term -> [Term] -> Idris (Term, [Term])
    nextPrefix' f (x:args) =
      do iLOG "nextPrefix'"
         iLOG $ "f : " ++ show f
         iLOG $ "x : " ++ show x
         appType <- typeOfMaybe (App f x) env
         case appType of
          Just _ -> nextPrefix' (App f x) args
          Nothing -> return (f, x:args)
    
         -- fType' <- typeOfMaybe f env
         -- fType <- case fType' of
         --            Just ty -> return ty
         --            Nothing -> epsFail f $ "Function has no type."
         -- let argTys = map snd $ getArgTys fType
         -- xTy <- if not $ null argTys
         --           then return $ head argTys
         --           else epsFail f "Term does not have function type"
         -- epsX <- epsilonCheck modality Open recName env x xTy
         -- appTy' <- typeOfMaybe (App f epsX) env
         -- case appTy' of
         --  Just _  -> nextPrefix' (App f x) args
         --  Nothing -> do fTy <- typeOf f env
         --                f' <- applyNext fTy f
         --                return (f', args)
    nextPrefix' f [] = return (f, [])


    inferTensor :: Term -> [Term] -> Idris Term
    inferTensor f (x:args) =
      do -- Get type of function
         fType'' <- typeOfMaybe f env
         fType' <- case fType'' of
                    Just ty -> return ty
                    Nothing -> epsFail f "Function has no type"
         -- Distribute laters in function type
         fType <- distributeLater fType'  -- fType' `whenNow` b'
         iLOG $ "fType' : " ++ show fType'
         iLOG $ "fType : " ++ show fType
         -- Conversion check with goal
         ok <- cEq env (getRetTy fType) b'
         if ok
            then do (composeA, composeB, _) <- debindType (fType' `whenNow` b')
                    iLOG $ "composeA : " ++ show composeA
                    iLOG $ "composeB : " ++ show composeB
                    (a,b,_) <- debindType fType
                    --iLOG $ "atob : " ++ show atob
                    iLOG $ "a : " ++ show a
                    iLOG $ "b : " ++ show b
                    --laterAtoB <- delayBy b' atob --atob `availableWith` b'
                    --iLOG $ "laterAtoB : " ++ show laterAtoB
                    --epsF <- epsilonCheck modality Open recName env f laterAtoB
                    --iLOG $ "epsF : " ++ show epsF
                    --laterA <- delayBy b' a -- a `availableWith` b'
                    --iLOG $ "laterA : " ++ show laterA
                    epsX <- epsilonCheck modality Open recName env x a
                    iLOG $ "epsX : " ++ show epsX
                    avB' <- tensorAvailabilityOf (b' `whenNow` composeB)
                    iLOG $ "avB' " ++ show avB'
                    tensorFX <- applyCompose composeA composeB avB' f epsX
                    iLOG $ "tensorFX : " ++ show tensorFX
                    inferTensor tensorFX args
            else ifail $ "Return type " ++ show (getRetTy fType) ++ " of function " ++ show f ++ " can never be part of a well-typed type with type " ++ show b'  
    inferTensor f [] = return f
         
    availableWith :: Type -> Type -> Idris Type
    availableWith (unapplyLater -> Just a) (unapplyLater -> Just b) =
      applyLater' =<< availableWith a b
    availableWith a@(unapplyLater -> Nothing) (unapplyLater -> Just b) =
      applyLater' =<< availableWith a b
    availableWith a@(unapplyLater -> Just _) b@(unapplyLater -> Nothing) =
      ifail $ "Cannot make " ++ show a ++ " available with " ++ show b
    availableWith a@(unapplyLater -> Nothing) (unapplyLater -> Nothing) =
      return a
     
     
-- Tensor error cases
epsilonInfer _ Closed recName env t@(unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Just b') =
  epsFail t "Compose application with empty clock environment."
epsilonInfer _ _ recName env t@(unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Nothing) =
  epsFail t "Compose application not expected to be available later."


-- Infer next
epsilonInfer modality Open recName env t ty@(unapplyLater -> Just a) =
  do epsLog "Next infer" t ty
     t' <- epsilonCheck modality Open recName env t a
     applyNext a t'

-- Next error cases
epsilonInfer _ _ recName env tm@(unapplyNext -> Just t) (unapplyLater -> Nothing) =
  epsFail tm "Next application occurred outside later context."
epsilonInfer _ Closed recName env tm@(unapplyNext -> Just t) _ =
  epsFail tm "Next application with empty clock environment."


-- Infer forall
epsilonInfer modality Closed recName env tm@(unapplyLambdaKappa -> Nothing) ty@(unapplyForall -> Just a) =
  do epsLog "LambdaKappa infer" tm ty
     recEps <- epsilonCheck modality Open recName env tm a
     hasForall <- hasForallType recEps
     case hasForall of
      Just _ -> return recEps
      Nothing -> applyLambdaKappa a recEps
  where
    hasForallType :: Term -> Idris (Maybe Term)
    hasForallType t = do tyMaybe <- typeOfMaybe t env
                         case tyMaybe of
                          Just ty' -> return $ unapplyForall ty'
                          Nothing -> return Nothing
-- Forall error cases
epsilonInfer _ Open recName env tm@(unapplyLambdaKappa -> Just t) (unapplyForall -> Just a) =
  epsFail tm "Clock abstraction in context with open clock."
epsilonInfer _ _ recName env tm@(unapplyLambdaKappa -> Just t) (unapplyForall -> Nothing) =
  epsFail tm "Clock abstraction not expected to have Forall type."
  
epsilonInfer _ Closed recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Nothing) =
  epsFail tm "Clock application with empty clock environment."
epsilonInfer _ _ recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Just _) =
  epsFail tm "Expected forall type as result of clock application."

epsilonInfer modality clock recName env app@(App _ _) a =
  do epsLog "App recurse" app a
     let (f, args) = unApply app
     iLOG $ "f : " ++ show f
     fType <- typeOf' f env (ifail $ "Function " ++ show f ++ " has no type.")
     let fTyBinders = binders fType
     let fEpsTy = bindAll fTyBinders a
     iLOG $ "fEpsTy : " ++ show fEpsTy
     epsF <- epsilonCheck modality Open recName env f fEpsTy
     epsFX <- epsApp epsF args
     ok <- checkGoal epsFX a env
     if ok
        then return epsFX
        else epsFail app "Ill-typed function application."
  where
    epsApp :: Term -> [Term] -> Idris Term
    epsApp f (x:args) =
      do iLOG "epsApp"
         iLOG $ "f : " ++ show f
         iLOG $ "x : " ++ show x
         fType' <- typeOfMaybe f env
         fType <- case fType' of
                    Just ty -> return ty
                    Nothing -> epsFail f $ "Function has no type."
         (xTy, _, _) <- debindType fType
         -- epsF <- epsilonCheck modality clock recName env f atob
         -- let argTys = map snd $ getArgTys fType
         -- xTy <- if not $ null argTys
         --           then return $ head argTys
         --           else epsFail f "Term does not have function type"
         epsX <- epsilonCheck modality clock recName env x =<< delayBy a xTy
         epsApp (App f epsX) args
    epsApp f [] = return f
 
epsilonInfer modality Open recName env tm@(unapplyApply -> Nothing) a@(unapplyForall -> Nothing) =
  do tmTyMaybe <- typeOfMaybe tm env
     case tmTyMaybe of
      Just tmTy -> case unapplyForall tmTy of
                     Just appliedTy -> do epsLog "Apply infer" tm a
                                          applyApply appliedTy tm
                     Nothing -> do iLOG $ "Epsilon done: No apply necessary"
                                   return tm
      Nothing -> return tm

-- Conversion check to see if term already has the required type.
-- If not, try to infer a term that does.
epsilonInfer modality clock recName env t a =
  do iLOG $  "Epsilon done: " ++ showTT t
     return t
\end{code}


\begin{code}
-- epsilonInfer :: Clock -> Name -> Env -> Term -> Maybe Type -> Type -> Idris Term
-- -- Unhandled cases
-- epsilonInfer _ _ _ t@(Proj _ _) _ _ = epsFail t "Infererence from Proj terms not supported"
-- epsilonInfer _ _ _ t@(V _) _ _ = epsFail t "Inference from de Bruijn indices not supported"
-- epsilonInfer _ _ _ t@(Erased) _ _ = epsFail t "Inference from Erased terms not supported"
-- -- Impossible, type of types and uniqueness type universes are ignored
-- epsilonInfer _ _ _ t@(Impossible) _ _ = return t
-- epsilonInfer _ _ _ t@(TType _) _ _ = return t
-- epsilonInfer _ _ _ t@(UType _) _ _ = return t
\end{code}

Infer clock application

C, G |- eps t : forall A
-------------------------
O, G |- eps (apply t) : A (A not forall.A, since only one clock)  -- 
\begin{code}
-- epsilonInfer Open recName env t ty@(Just (unapplyForall -> Just tTy)) a@(unapplyForall -> Nothing) =
--   do epsLogInfer "Apply infer" t ty a
--      --forallA <- applyForall a
--      --tEps <- epsilonCheck Closed recName env t forallA
--      tApply <- applyApply t --tEps
--      epsilonCheck Open recName env tApply a
\end{code}

Infer forall
                    
O,G |- eps t : A
-----------------
C,G |- eps (lambdaKappa t) : forall A
\begin{code}
-- epsilonInfer Closed recName env t tTy@(Just (unapplyForall -> Nothing)) a@(unapplyForall -> Just a') =
--   do epsLogInfer "LambdaKappa infer Just" t tTy a
--      --tEps <- epsilonCheck Open recName env t a'
--      tLambdaKappa <- applyLambdaKappa t --tEps
--      epsilonCheck Closed recName env tLambdaKappa a

-- epsilonInfer Closed recName env t tTy@(Just (unapplyForall -> Just _)) a@(unapplyForall -> Just a') =
--   do epsLogInfer "LambdaKappa infer no-action" t tTy a
--      return t

-- epsilonInfer Closed recName env t Nothing a@(unapplyForall -> Just a') =
--   do epsLogInfer "LambdaKappa infer Nothing" t Nothing a
--      tEps <- epsilonCheck Open recName env t a'
--      tEpsTy <- typeOfMaybe tEps env
--      let forallTy = tEpsTy >>= \ty -> unapplyForall ty
--      case forallTy of
--       Just _ -> return tEps
--       Nothing -> applyLambdaKappa tEps
\end{code}


Infer tensor

O,G |- eps f : Later' (A -> B)    O,G |- eps x : Later' A
---------------------------------------------------------
        O,G |- eps (f tensor x) : Later' A

\begin{code}
-- epsilonInfer Open recName env app@(App f x) appTy a | Just a' <- unapplyLater a, Just _ <- unapplyLater a' =
--   do epsLogInfer "Tensor infer later-later" app appTy a
--      appNext <- applyNext app
--      epsilonCheck Open recName env appNext a'

-- epsilonInfer Open recName env (App f x) appTy b | Just b' <- unapplyLater b, Nothing <- unapplyLater b' =
--   do epsLogInfer "Tensor infer" (App f x) appTy b
--      fType <- typeOfMaybe f env
--      let fNowType = nowType fType
--      a <- firstArg fNowType
--      laterA <- applyLater' a
--      laterAtoB <- applyLater' fNowType
--      fEps <- epsilonCheck Open recName env f laterAtoB
--      xEps <- epsilonCheck Open recName env x laterA
--      now <- nowRef
--      composeApp <- applyCompose a b' now fEps xEps
--      epsilonCheck Open recName env composeApp b
--   where
--     firstArg :: Type -> Idris Type
--     firstArg ty =
--       case getArgTys (nowType ty) of
--        []    -> epsFail ty "Is not a function type."
--        ((_,x):_) -> return x
-- epsilonInfer clock recName env app@(App f x) _ a =
--   do epsLog "App recurse" app a
--      let (f', args) = unApply app
--      if (isDelay f' && isLazyCodata (head args))
--        then do iLOG $ "Removing delay"
--                (epsilonCheck clock recName env (mkApp (head (tail args)) (tail (tail args))) a)
--        else do (Just f'Type) <- typeOfMaybe f' env
--                let argTys = map snd $ getArgTys f'Type
--                argEps <- forM (zip args argTys) $ \(arg, argTy) ->
--                           do delayedType <- delayBy a argTy
--                              epsilonCheck clock recName env arg delayedType
--                return (mkApp f' argEps)

\end{code}

Infer next

O,G |- eps t : A
----------------------
O,G |- eps (Next t) : Later' A
\begin{code}
-- epsilonInfer Open recName env t tTy a@(unapplyLater -> Just a') =
--   do epsLogInfer "Next infer" t tTy a
--      tEps <- epsilonCheck Open recName env t a'
--      tNext <- applyNext tEps
--      epsilonCheck Open recName env tNext a
\end{code}

\begin{code}
-- epsilonInfer clock recName env app@(App f x) appTy a =
--   do epsLogInfer "App recurse" app appTy a
--      let (f', args) = unApply app
--      f'Type <- typeOfMaybe f' env
--      let argTys = map snd $ getArgTys f'Type
--      argEps <- forM (zip args argTys) $ \(arg, argTy) ->
--                 do delayedType <- delayBy a argTy
--                    epsilonCheck clock recName env arg delayedType
--      epsilonCheck clock recName env (mkApp f' argEps) a
\end{code}

\begin{code}
--epsilonInfer _ _ _ t _ a = return t  --epsFail t $ "Could not infer a guarded recursive term from type " ++ showTT a
\end{code}






-- \begin{code}

-- epsilon :: Clock -> Name -> Env -> Term -> Type -> Idris Term
-- \end{code}

-- Quantification over clocks
-- \begin{code}
-- -- User-supplied \Open
-- epsilon Closed recName env (unapplyLambdaKappa -> Just tm) (unapplyForall -> Just ty) =
--   do body <- epsilon Open recName env tm ty
--      applyLambdaKappa body
-- -- Inferred \Open
-- epsilon Closed recName env tm (unapplyForall -> Just ty) =
--   do body <- epsilon Open recName env tm ty
--      applyLambdaKappa body
-- -- Error: Forall under forall
-- epsilon Open _ _ tm (unapplyForall -> Just ty) =
--   epsFail tm "Attempt to open more than one clock."
-- \end{code}

-- Free variables
-- \begin{code}
-- -- Inferred recursive reference - The user cannot put the 'next' him/herself!
-- epsilon Open recName env p@(P Ref n _) (unapplyLater -> Just ty) | n == recName =
--   do recursiveRef <- epsilon Open recName env p ty
--      applyNext recursiveRef
-- -- Error: Recursive reference is not expected to be available later.
-- epsilon _ recName env p@(P Ref n _) (unapplyLater -> Nothing) | n == recName =
--   epsFail p "Attempt to build recursive reference outside a later context."

-- -- Inferred next on free variable
-- epsilon Open recName env p@(P Ref n (unapplyLater -> Nothing)) (unapplyLater -> Just goal) =
--   do ref <- epsilon Open recName env p goal
--      applyNext ref
-- -- Recursively remove later from free variables
-- epsilon Open recName env (P Ref n (unapplyLater -> Just pty)) (unapplyLater -> Just goal) =
--   epsilon Open recName env (P Ref n pty) goal
-- -- Error: Free variable is unexpectedly later
-- epsilon _ recName env p@(P Ref n (unapplyLater -> Just _)) (unapplyLater -> Nothing) =
--   epsFail p "Free variable is available too late."

-- epsilon Open recName env p@(P Ref n (unapplyForall -> Just pty)) goal
--   | Nothing <- unapplyForall goal =
--       do applyp <- applyApply p
--          epsilon Open recName env applyp goal
--   | Just goal' <- unapplyForall goal =
--       epsilon Open recName env (P Ref n pty) goal'
     
-- \end{code}

-- Bound variables
-- \begin{code}

-- \end{code}

-- Data constructors
-- \begin{code}

-- \end{code}

-- Type constructors
-- \begin{code}

-- \end{code}

-- Binders
-- \begin{code}
-- -- Binders add variables to the context
-- epsilon clock recName env (Bind n binder sc) goal =
--   epsilon clock recName ((n, binder):env) sc goal

-- \end{code}

-- Application
-- \begin{code}

-- \end{code}


-- Catch-all
-- \begin{code}
-- -- No rules apply, do nothing
-- epsilon _ _ _ tm _ = return tm

"The bin"
\begin{code}
-- epsilonInfer Open recName env p@(P Bound n pty) (unapplyLater -> Just a)
--   | Nothing <- unapplyLater pty,
--     Nothing <- unapplyForall pty =
--       do p' <- epsilonCheck Open recName env p a
--          applyNext p'
-- epsilonInfer Open recName env p@(P Ref n pty) (unapplyLater -> Just a) =
--   do gref@(P Ref n' pty') <- guardedRef n -- guardedRef :: Term -> Idris (Maybe Term)
--      inferFromGuardedRef gref
--   where
--     inferFromGuardedRef (P Ref n'' (unapplyLater -> Just pty'')) =
--       epsilonCheck Open recName env (P Ref n'' pty'') a
--     inferFromGuardedRef p'@(P Ref n'' (unapplyLater -> Nothing)) =
--       do ref <- epsilonCheck Open recName env p' a
--          applyNext ref
--     inferFromGuardedRef tm = epsFail tm ("Tried to infer from Ref, but got " ++ show tm) 
-- epsilonInfer Open recName env (P (DCon _ _ _) n pty) (unapplyLater -> Just a) =
--   do gdcon <- guardedDataConstructor n
--      epsDCon <- epsilonCheck Open recName env gdcon a
--      applyNext epsDCon
-- epsilonInfer _ _ _ p@(P (TCon _ _) _ _) _ = return p
-- epsilonInfer Open recName env app@(App f x) goal@(unapplyLater -> Just a) =
--   do fType <- typeOfMaybe f env
--      xType <- typeOfMaybe x env
     
-- epsilonInfer Open recName env p (unapplyLater -> Just a) =
--   do p' <- epsilonCheck Open recName env p a
--      applyNext p'


-- epsilonInfer Closed recName env p@(P Bound n pty) (unapplyForall -> Just a)
--   | Nothing <- unapplyLater pty,
--     Nothing <- unapplyForall pty =
--       do p' <- epsilonCheck Open recName env p a
--          applyLambdaKappa p'
-- epsilonInfer Closed recName env p@(P Ref n pty) (unapplyForall -> Just a) =
--   do gref@(P Ref n' pty') <- guardedRef n -- guardedRef :: Term -> Idris (Maybe Term)
--      inferFromGuardedRef gref
--   where
--     inferFromGuardedRef (P Ref n'' (unapplyForall -> Just pty'')) =
--       epsilonCheck Open recName env (P Ref n'' pty'') a
--     inferFromGuardedRef p'@(P Ref n'' (unapplyForall -> Nothing)) =
--       do ref <- epsilonCheck Open recName env p' a
--          applyLambdaKappa ref
--     inferFromGuardedRef tm = epsFail tm ("Tried to infer from Ref, but got " ++ show tm) 
-- epsilonInfer Closed recName env (P (DCon _ _ _) n pty) (unapplyForall -> Just a) =
--   do gdcon <- guardedDataConstructor n
--      epsDCon <- epsilonCheck Open recName env gdcon a
--      applyLambdaKappa epsDCon
-- epsilonInfer Closed recName env app@(App f x) (unapplyForall -> Just a) =
--   do appType <- typeOfMaybe app env
--      case unapplyForall appType of
--       Just forallAppType -> return app
--       Nothing            -> do fType <- typeOfMaybe f env
--                                xType <- typeOfMaybe x env
--                                fChecked <- epsilonCheck Open recName env f fType
--                                xChecked <- epsilonCheck Open recName env x xType
--                                applyLambdaKappa (App fChecked xChecked)
-- epsilonInfer Closed recName env p (unapplyForall -> Just a) =
--   do p' <- epsilonCheck Open recName env p a
--      applyLambdaKappa p'
\end{code}

\end{document}
