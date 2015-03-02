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
Epsilon is the entry function for the inference system.
\begin{code}
epsilon :: Modality -> Name -> Term -> Type -> [Term] -> Env -> Idris Term
epsilon modality recName t a params env =
  do t' <- guardedTT' modality (removeLaziness t)
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
  where infer = epsilonInfer modality clock recName env t a

epsilonInfer :: Modality -> Clock -> Name -> Env -> Term -> Type -> Idris Term
epsilonInfer Causal Open recName env recRef@(unapplyNext >=> unapplyApply -> Just (P Ref n _)) (unapplyLater -> Just (unapplyLater -> Nothing)) | n == recName =
  do iLOG "Found recursive ref (causal)"
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
epsilonInfer modality Open recName env t@(App _ _) b'@(unapplyLater -> Just b) =
  do epsLog "Tensor infer" t b'
     iLOG $ "Tensor term " ++ showTT t
     idrisCatch (applyWhenAvailable (epsilonCheck modality Open recName env) t b')  
                (\err -> do iLOG $ "Error : " ++ show err
                            epsLog "Inferring tensor" t b'
                            --let (f, args) = unApply t
                            (prefix, remainingArgs) <- nextPrefix t b'
                            tensor <- inferTensor prefix remainingArgs
                            ok <- checkGoal tensor b' env
                            if ok
                               then return tensor
                               else do iLOG $ "Tensor inference failed"
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
         epsF <- idrisCatch (epsilonCheck modality Open recName env f fEpsTy) (\_ -> return f)
         (prefix, remainingArgs)  <- nextPrefix' epsF args
         iLOG $ "Found prefix : " ++ show prefix
         return (prefix, remainingArgs)

    nextPrefix' :: Term -> [Term] -> Idris (Term, [Term])
    nextPrefix' f (x:args) =
      do iLOG "nextPrefix'"
         appType <- typeOfMaybe (App f x) env
         case appType of
          Just _ -> nextPrefix' (App f x) args
          Nothing -> return (f, x:args)
    nextPrefix' f [] = return (f, [])


    inferTensor :: Term -> [Term] -> Idris Term
    inferTensor f (x:args) =
      do -- Get type of function
         fType'' <- typeOfMaybe f env
         fType' <- case fType'' of
                    Just ty -> return ty
                    Nothing -> epsFail f "Function has no type"
         -- Distribute laters in function type
         fType <- distributeLater fType' 
         -- Conversion check with goal
         ok <- cEq env (getRetTy fType) b'
         if ok
            then do (composeA, composeB, _) <- debindType (fType' `whenNow` b')
                    (a,b,_) <- debindType fType
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

