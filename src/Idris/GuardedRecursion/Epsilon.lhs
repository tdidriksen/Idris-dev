xb\documentclass{article}
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
epsilon :: Modality -> Name -> Term -> Type -> Env -> Idris Term
epsilon modality recName t a env =
  do t' <- guardedTT' (removeLaziness t)
     fixed <- fixRecursiveRef modality recName t'
     iLOG $ "Epsilon start"
     iLOG $ "Trying to infer that term " ++ show recName ++ ":\n" ++ show fixed ++ "\nhas type:\n" ++ show a
     case modality of
      Causal    -> epsilonCheck Causal Closed recName env fixed a
      NonCausal -> epsilonCheck NonCausal Open recName env fixed a

epsilonCheck :: Modality -> Clock -> Name -> Env -> Term -> Type -> Idris Term

epsilonCheck Causal Open recName env recRef@(unapplyNext >=> unapplyApply -> Just (P Ref n _)) (unapplyLater -> Just (unapplyLater -> Nothing)) | n == recName =
  do iLOG "Found recursive ref (causal)"
     return recRef
epsilonCheck NonCausal Open recName env recRef@(unapplyNext -> Just (P Ref n _)) (unapplyLater -> Just (unapplyLater -> Nothing)) | n == recName =
  do iLOG "Found recursive ref"
     return recRef

-- Check fix (by nexting recursive reference)
-- epsilonCheck Open recName env p@(P Ref refn pty) ty@(unapplyLater -> Just a) | refn == recName =
--   do epsLog "Recursive ref check" p ty
--      recRef <- epsilonCheck Open recName env p a
--      applyNext recRef
-- -- Fix error cases
-- epsilonCheck Closed recName env p@(P Ref refn pty) (unapplyLater -> Just a) | refn == recName =
--   epsFail p "Accessing recursive reference with empty clock context."
-- epsilonCheck Closed recName env p@(P Ref refn (unapplyForall -> Just _)) (unapplyForall -> Just _) | refn == recName =
--   return p 
--epsilonCheck _ recName env p@(P Ref refn pty) (unapplyLater -> Nothing) | refn == recName =
--  epsFail p "Recursive reference not expected to be available later."

-- Binders
epsilonCheck modality clock recName env tm@(Bind n (Let letty letval) sc) a =
  do epsLog "Let binder check" tm a
     gLetTy <- guardedTT letty
     gLetVal <- epsilonCheck modality clock recName env letval gLetTy
     let gBinder = Let gLetTy gLetVal
     bindEps <- epsilonCheck modality clock recName ((n, gBinder):env) sc a
     return $ Bind n gBinder sc
epsilonCheck modality clock recName env tm@(Bind n binder sc) ty@(debindFirstArg -> Just a)
  | Just _ <- debindFirstArg $ binderTy binder =
      do epsLog "Function arg binder check" tm ty
         bindEps <- epsilonCheck modality clock recName ((n, binder):env) sc a
         return $ Bind n binder bindEps
epsilonCheck modality clock recName env tm@(Bind n binder sc) a
  | Nothing <- debindFirstArg $ binderTy binder =
      do epsLog "Other binder check" tm a
         bindEps <- epsilonCheck modality clock recName ((n, binder):env) sc a
         return $ Bind n binder bindEps

-- Check tensor
-- epsilonCheck Open recName env tm@(unapplyCompose -> Just (a, b, av, f, arg)) ty@(unapplyLater -> Just b') =
--   do epsLog "Tensor check" tm ty
--      (Just fType) <- typeOfMaybe f env
--      laterA <- applyLater' a
--      fChecked <- epsilonCheck Open recName env f fType
--      argChecked <- epsilonCheck Open recName env arg laterA
--      applyCompose a b av fChecked argChecked
-- Infer tensor
epsilonCheck modality Open recName env t@(App f x) a | Just a' <- unapplyLater a, Just _ <- unapplyLater a' =
  do t' <- epsilonCheck modality Open recName env t a'
     applyNext a' t'
epsilonCheck modality Open recName env t@(App _ _) b' | Just b <- unapplyLater b', Nothing <- unapplyLater b =
  do epsLog "Tensor infer" t b'
     idrisCatch (applyNext b =<< epsilonCheck modality Open recName env t b)
                (\_ -> do iLOG "Inferring tensor"
                          let (f, args) = unApply t
                          tensor <- inferTensor f args
                          ok <- checkGoal tensor b' env
                          if ok
                             then return tensor
                             else do iLOG $ "tensor: " ++ show tensor
                                     iLOG $ "Tensor inference failed"
                                     return t)
  where
    inferTensor :: Term -> [Term] -> Idris Term
    inferTensor f (x:args) =
      do iLOG "inferTensor"
         iLOG $ "f : " ++ show f
         iLOG $ "x : " ++ show x
         appTy' <- typeOfMaybe (App f x) env
         case appTy' of
          Just _  -> inferTensor (App f x) args
          Nothing -> 
           do atob <- typeOf f env
              iLOG $ "atob : " ++ show atob
              (a, b) <- debind atob
              iLOG $ "a : " ++ show a
              iLOG $ "b : " ++ show b
              laterA <- a `availableWith` b'
              iLOG $ "laterA : " ++ show laterA
              laterAtoB <- atob `availableWith` b'
              iLOG $ "laterAtoB : " ++ show laterAtoB
              --epsF <- epsilonCheck modality Open recName env f laterAtoB
              --iLOG $ "epsF : " ++ show epsF
              epsX <- epsilonCheck modality Open recName env x laterA
              iLOG $ "epsX : " ++ show epsX
              tensorFX <- applyCompose' a b f epsX
              iLOG $ "tensorFX : " ++ show tensorFX
              inferTensor tensorFX args
    inferTensor f [] = return f
         
    debind :: Type -> Idris (Type, Type)
    debind (unapplyLater -> Just ty) = debind ty
    debind (unapplyForall -> Just ty) = debind ty
    debind (Bind n (Pi ty kind) sc) = return (ty, sc)
    debind ty = ifail $ "Cannot debind non-function type: " ++ show ty
         
    availableWith :: Type -> Type -> Idris Type
    availableWith (unapplyLater -> Just a) (unapplyLater -> Just b) =
      applyLater' =<< availableWith a b
    availableWith a@(unapplyLater -> Nothing) (unapplyLater -> Just b) =
      applyLater' =<< availableWith a b
    availableWith a@(unapplyLater -> Just _) b@(unapplyLater -> Nothing) =
      ifail $ "Cannot make " ++ show a ++ " available with " ++ show b
    availableWith a@(unapplyLater -> Nothing) (unapplyLater -> Nothing) =
      return a
     
     
  --    let (f, args) = unApply t
  --    fTy <- typeOf f env
  --    laterFTy <- fTy `availableWith` b'
  --    epsF <- epsilonCheck modality Open recName env laterFTy
  --    distFTy <- distributeLater laterFTy
  --    let laterArgTys = map snd $ getArgTys distFTy
  --    epsArgs <- forM (zip args laterArgTys) $ \(arg, argTy) ->
  --                 epsilonCheck modality Open recName env arg =<< argTy `availableWith` b'
     
  --    atob' <- typeOfMaybe f env
     
  -- where
  --   inferCompose :: Maybe Type -> Idris Term
  --   inferCompose (Just atob) =
  --     do iLOG "Tensor Just"
  --        let argTys = map snd $ getArgTys atob
  --        let a = head argTypes
  --        iLOG $ "a : " ++ show a
  --        epsF <- epsilonCheck modality Open recName env f =<< atob `availableWith` b'
  --        epsX <- epsilonCheck modality Open recName env x =<< a `availableWith` b'
  --        iLOG $ "epsF : " ++ show epsF
  --        iLOG $ "epsX : " ++ show epsX
  --        applyCompose' a b epsF epsX      
  --   inferCompose Nothing =
      
    
  --   inferCompose :: Term -> [Term] -> Term
  --   inferCompose f (x:args) =
  --     do atob <- typeOf f env
  --        laterAtoB <- atob `availableWith` b'
  --        epsF <- epsilonCheck modality Open recName env laterAtoB
  --        (c, d) <- debind laterAtoB
  --        laterC <- c `availableWith` b'
  --        epsX <- epsilonCheck modality Open recName env x laterC
  --        composeFX <- applyCompose' c d          
    

  --    let (f, args) = unApply t
  --    iLOG $ "f : " ++ show f
  --    fType <- typeOf' f env (ifail $ "Function " ++ show f ++ " has no type.")
  --    epsF <- epsilonCheck modality Open recName env f fType
  --    epsFTy <- typeOf epsF env
  --    epsApp' <- epsApp epsF epsFTy args
  --    case epsApp' of
  --     Right (tm, tmTy) -> do iLOG "Tensor right"
  --                            iLOG $ "b : " ++ show b
  --                            applyNext b tm
  --     Left (f', atob, [arg]) ->
  --       do iLOG $ "f' : " ++ show f'
  --          iLOG $ "atob : " ++ show atob
  --          iLOG $ "args' : " ++ intercalate "," (map show args')
  --          iLOG $ "b : " ++ show b
  --          let a = head $ map snd (getArgTys atob)
  --          applyCompose' a b f' arg
  --     Left (f', atob, args') ->
  --       do iLOG $ "f' : " ++ show f'
  --          iLOG $ "atob : " ++ show atob
  --          iLOG $ "args' : " ++ intercalate "," (map show args')
  --          iLOG $ "b : " ++ show b
  --          let a = head $ map snd (getArgTys atob)
  --          ifail "Tensor left"
  --       --inferTensor f' atob args'           
  -- where
  --   epsApp :: Term -> Type -> [Term] -> Idris (Either (Term, Type, [Term]) (Term, Type))
  --   epsApp f fTy (x:args) =
  --     do iLOG "epsApp (tensor)"
  --        iLOG $ "f: " ++ show f
  --        iLOG $ "fTy : " ++ show fTy
  --        iLOG $ "x: " ++ show x
  --        case unapplyLater fTy of
  --         Just atob -> return $ Left (f, atob, (x:args))
  --         Nothing ->
  --           do let argTys = map snd $ getArgTys fTy
  --              let xTy = head argTys
  --              epsX <- epsilonCheck modality Open recName env x xTy
  --              fxTy' <- typeOfMaybe (App f epsX) env
  --              case fxTy' of
  --               Just fxTy -> epsApp (App f epsX) fxTy args
  --               Nothing   -> return $ Left (f, fTy, (x:args))
  --   epsApp f fTy [] = return $ Right (f, fTy)

  --   -- inferTensor :: Term -> Type -> [Term] -> Idris Term
  --   -- inferTensor f atob (x:args) =
  --   --   do epsF <- epsilonCheck modality Open recName env f =<< atob `availableWith` b'
  --   --      let f'ArgTys = map snd $ getArgTys atob
  --   --      let a = head f'ArgTys
  --   --      let b = tail f'ArgTys
  --   --      epsX <- epsilonCheck modality Open recName env x =<< a `availableWith` b'
  --   --      compose <- applyCompose' a b epsF epsX
  --   --      laterB <- applyLater' b
  --   --      inferTensor compose 
                  


      -- do fType' <- typeOfMaybe f env (ifail $ "Function " ++ show f ++ " has no type.")
      --    case fType' of
      --     Just fType ->
      --       do let argTys = map snd $ getArgTys fType
      --          let xTy = head argTys
      --          epsX <- epsilonCheck modality clock recName env x =<< delayBy a xTy
      --          epsApp (App f epsX) args
      --     Nothing -> return $ Left (f, 
      -- epsApp f [] = return $ Right f
     
     -- fApply <- case unapplyNext f of
     --            Just tm -> return tm
     --            Nothing -> return f --ifail "Cannot unapply Next"
     -- fRef <- case unapplyApply fApply of
     --          Just tm -> return tm
     --          Nothing -> return fApply --ifail "Cannot unapply Apply"
     -- iLOG $ "fRef : " ++ show fRef
     -- iLOG $ "fApply : " ++ show fApply
     -- fRefType <- typeOf fRef env
     -- iLOG $ "fRefType : " ++ show fRefType
     -- fApplyType <- typeOf fApply env
     -- iLOG $ "fApplyType : " ++ show fApplyType
     -- fTypeM <- typeOfMaybe f env
  --    iLOG $ "f : " ++ show f
  --    iLOG $ "x : " ++ show x
  --    iLOG $ "b : " ++ show b
  --    iLOG $ "b' : " ++ show b'
  --    -- let (f', args) = unApply t
  --    -- f'Ty <- typeOf f' env
  --    -- iLOG $ "f' : " ++ show f'
  --    -- iLOG $ "f'Ty : " ++ show f'Ty
  --    atob <- typeOf f env
  --    -- atob <- case fTypeM of
  --    --          Just ty -> return ty
  --    --          Nothing -> epsFail f "Function does not have a type"
  --    iLOG $ "atob : " ++ show atob
  --    distAtoB <- distributeLater atob
  --    iLOG $ "distAtoB : " ++ show distAtoB
  --    let argTypes = map snd (getArgTys distAtoB)
  --    let a = head argTypes
  --    -- (a, b) <- case debind atob of
  --    --            Just (ax,bx) -> return (ax,bx)
  --    --            Nothing      -> epsFail f "Function does not have function type"
  --    -- iLOG $ "atob : " ++ show atob
  --    iLOG $ "a : " ++ show a
  --    epsF <- epsilonCheck modality Open recName env f =<< atob `availableWith` b'
  --    epsX <- epsilonCheck modality Open recName env x =<< a `availableWith` b'
  --    iLOG $ "epsF : " ++ show epsF
  --    iLOG $ "epsX : " ++ show epsX
  --    applyCompose' a b epsF epsX
  -- where
  --   availableWith :: Type -> Type -> Idris Type
  --   availableWith (unapplyLater -> Just a) (unapplyLater -> Just b) =
  --     applyLater' =<< availableWith a b
  --   availableWith a@(unapplyLater -> Nothing) (unapplyLater -> Just b) =
  --     applyLater' =<< availableWith a b
  --   availableWith a@(unapplyLater -> Just _) b@(unapplyLater -> Nothing) =
  --     ifail $ "Cannot make " ++ show a ++ " available with " ++ show b
  --   availableWith a@(unapplyLater -> Nothing) (unapplyLater -> Nothing) =
  --     return a
      
  -- where
  --   debind :: Type -> Maybe (Type, Type)
  --   debind (Bind n (Pi ty kind) sc) = Just (ty, sc)
  --   debind _ = Nothing
     

  --    delayedFType <- delayBy b fType
  --    distDelayedFType <- distributeLater delayedFType
  --    -- iLOG $ "fType : " ++ show fType
  --    -- iLOG $ "delayedFType : " ++ show delayedFType
  --    -- iLOG $ "distDelayedFType : " ++ show distDelayedFType
  --    let xTy = head $ map snd (getArgTys distDelayedFType)
  --    -- iLOG $ "f : " ++ show f
  --    -- iLOG $ "x : " ++ show x
  --    -- iLOG $ "xTy : " ++ show xTy
  --    -- iLOG $ "b : " ++ show b
  --    fEps <- epsilonCheck Open recName env f delayedFType
  --    xEps <- epsilonCheck Open recName env x xTy
  --    -- iLOG $ "fEps : " ++ show fEps
  --    -- iLOG $ "xEps : " ++ show xEps
  --    now <- nowRef
  --    applyCompose delayedFType xTy now fEps xEps

-- Tensor error cases
epsilonCheck _ Closed recName env t@(unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Just b') =
  epsFail t "Compose application with empty clock environment."
epsilonCheck _ _ recName env t@(unapplyCompose -> Just (a, b, av, f, arg)) (unapplyLater -> Nothing) =
  epsFail t "Compose application not expected to be available later."



-- Check next
-- epsilonCheck Open recName env tm@(unapplyNext -> Just t) ty@(unapplyLater -> Just a) =
--   do epsLog "Next check" tm ty
--      nexted <- epsilonCheck Open recName env t a
--      applyNext nexted
-- Infer next
epsilonCheck modality Open recName env t ty@(unapplyLater -> Just a) =
  do epsLog "Next infer" t ty
     t' <- epsilonCheck modality Open recName env t a
     applyNext a t'
  --    t'Type <- typeOfMaybe t' env
  --    case t'Type of
  --     Just ty' -> availableWith t' ty' ty
  --     Nothing -> applyNext t'
  -- where
  --   availableWith :: Term -> Type -> Type -> Idris Term
  --   availableWith tm (unapplyLater -> Just a) (unapplyLater -> Just b) =
  --     availableWith tm a b
  --   availableWith tm (unapplyLater -> Just a) (unapplyLater -> Nothing) =
  --     epsFail tm "Term is available too late."
  --   availableWith tm tmTy@(unapplyLater -> Nothing) (unapplyLater -> Just a) =
  --     do tm' <- availableWith tm tmTy a
  --        applyNext tm'
  --   availableWith tm (unapplyLater -> Nothing) (unapplyLater -> Nothing) =
  --     return tm
-- Next error cases
epsilonCheck _ _ recName env tm@(unapplyNext -> Just t) (unapplyLater -> Nothing) =
  epsFail tm "Next application occurred outside later context."
epsilonCheck _ Closed recName env tm@(unapplyNext -> Just t) _ =
  epsFail tm "Next application with empty clock environment."


-- Check forall (clock abstraction)
-- epsilonCheck Closed recName env tm@(unapplyLambdaKappa -> Just t) ty@(unapplyForall -> Just a) =
--   do epsLog "LambdaKappa check" tm ty
--      freeClockTm <- epsilonCheck Open recName env t a
--      applyLambdaKappa freeClockTm
-- Infer forall
epsilonCheck modality Closed recName env tm@(unapplyLambdaKappa -> Nothing) ty@(unapplyForall -> Just a) =
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
epsilonCheck _ Open recName env tm@(unapplyLambdaKappa -> Just t) (unapplyForall -> Just a) =
  epsFail tm "Clock abstraction in context with open clock."
epsilonCheck _ _ recName env tm@(unapplyLambdaKappa -> Just t) (unapplyForall -> Nothing) =
  epsFail tm "Clock abstraction not expected to have Forall type."
  
-- Check apply (clock application)
-- epsilonCheck Open recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Nothing) =
--   do epsLog "Apply check" tm a
--      forallA <- applyForall a
--      unappliedTm <- epsilonCheck Closed recName env t forallA
--      applyApply unappliedTm
-- --epsilonCheck Open recName env tm@(unapplyApply -> Nothing) a@(unapplyForall -> Nothing) =
  --  do epsLog "Apply infer" tm a
     
epsilonCheck _ Closed recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Nothing) =
  epsFail tm "Clock application with empty clock environment."
epsilonCheck _ _ recName env tm@(unapplyApply -> Just t) a@(unapplyForall -> Just _) =
  epsFail tm "Expected forall type as result of clock application."

epsilonCheck modality clock recName env app@(App _ _) a =
  do epsLog "App recurse" app a
     let (f, args) = unApply app
     iLOG $ "f : " ++ show f
     fType <- typeOf' f env (ifail $ "Function " ++ show f ++ " has no type.")
     epsF <- epsilonCheck modality Open recName env f fType
     epsApp epsF args
  where
    epsApp :: Term -> [Term] -> Idris Term
    epsApp f (x:args) =
      do iLOG "epsApp"
         iLOG $ "f : " ++ show f
         iLOG $ "x : " ++ show x
         fType' <- typeOfMaybe f env
         fType <- case fType' of
                    Just ty -> return ty
                    Nothing -> epsFail f $ "Function " ++ show f ++ " has no type."
         let argTys = map snd $ getArgTys fType
         xTy <- if not $ null argTys
                   then return $ head argTys
                   else epsFail f "Term does not have function type"
         epsX <- epsilonCheck modality clock recName env x =<< delayBy a xTy
         epsApp (App f epsX) args
    epsApp f [] = return f
 
  --     do epsLog "App recurse" app a
  --        (g, gTy, args) <- appType app []
  --        let argTys = map snd $ getArgTys gTy
  --        case (args, argTys) of
  --         ((arg:as), (argTy:tys)) ->
  --              do delayedType <- delayBy a argTy
  --                 xEps <- epsilonCheck modality clock recName env arg delayedType
  --                 epsilonCheck modality clock recName env (mkApp g (xEps:as)) a
  --         ([], _) -> return g
  --         _ -> epsFail app "Application can never reach a well-typed state"
  -- -- do epsLog "App recurse" app a
  -- --    ok <- checkGoal app a env
  -- --    if ok
  -- --       then return app
  -- --       else do (g, gTy, args) <- appType app []
  -- --               let argTys = map snd $ getArgTys gTy
  -- --               case (args, argTys) of
  -- --                ((arg:as), (argTy:tys)) ->
  -- --                     do delayedType <- delayBy a argTy
  -- --                        xEps <- epsilonCheck modality clock recName env arg delayedType
  -- --                        epsilonCheck modality clock recName env (mkApp g (xEps:as)) a
  -- --                _ -> epsFail app "Application can never reach a well-typed state"
  -- where
  --   appType :: Term -> [Term] -> Idris (Term, Type, [Term])
  --   appType app'@(App f' x') args =
  --     do app'Type <- typeOfMaybe app' env
  --        case app'Type of
  --         Just ty -> return (app', ty, args)
  --         Nothing -> appType f' (x':args)
  --   appType tm args =
  --     do tmTyM <- typeOfMaybe tm env
  --        case tmTyM of
  --         Just ty -> return (tm, ty, args)
  --         Nothing -> ifail $ "Term " ++ show tm ++ " has no type"                  
                        
  -- do epsLog "App recurse" app a
  --    let (f', args) = unApply app
  --    f'TypeMaybe <- typeOfMaybe f' env
  --    f'Type <- case f'TypeMaybe of
  --               Just ty -> return ty
  --               Nothing -> epsFail f' "Function does not have a type"
  --    let argTys = map snd $ getArgTys f'Type
  --    let argsWithTys = zip args argTys
  --    ctxt <- getContext
  --    let params = parameters f' ctxt
  --    iLOG $ "params: " ++ intercalate ", " (map show params)
  --    let paramArgs = map (\(i,_) -> (i, argsWithTys !! i)) params
  --    paramArgEps <- forM paramArgs $ \(i, (arg, argTy)) ->
  --                     do delayedType <- delayBy a argTy
  --                        (i, epsilonCheck modality clock recName env arg delayedType)
  --    return (mkApp f' argEps)
 
    
  -- do epsLog "App recurse" app a
  --    let (f', args) = unApply app
  --    f'TypeMaybe <- typeOfMaybe f' env
  --    f'Type <- case f'TypeMaybe of
  --               Just ty -> return ty
  --               Nothing -> epsFail f' "Function does not have a type"
  --    let argTys = map snd $ getArgTys f'Type
  --    argEps <- forM (zip args argTys) $ \(arg, argTy) ->
  --               do delayedType <- delayBy a argTy
  --                  epsilonCheck modality clock recName env arg delayedType
  --    return (mkApp f' argEps)

epsilonCheck modality Open recName env tm@(unapplyApply -> Nothing) a@(unapplyForall -> Nothing) =
  do tmTyMaybe <- typeOfMaybe tm env
     case tmTyMaybe of
      Just tmTy -> case unapplyForall tmTy of
                     Just _ -> do epsLog "Apply infer" tm a
                                  applyApply tmTy tm
                     Nothing -> do iLOG $ "No apply necessary"
                                   return tm
      Nothing -> return tm

-- Conversion check to see if term already has the required type.
-- If not, try to infer a term that does.
epsilonCheck modality clock recName env t a =
  do iLOG $  "Epsilon done: " ++ showTT t
     return t
     --iLOG "Going into inference mode!"
     -- tTy <- typeOfMaybe t env
     -- ok <- idrisCatch (checkGoal t a env) (\err -> return False)
     -- if ok
     --  then do epsLog "Epsilon done" t a; return t
     --  else do iLOG "Going into inference mode!"
     --          epsilonInfer clock recName env t tTy a
              
  -- do epsLog "Inference mode?" t a
  --    --return t
  --    --tTy <- typeOfMaybe t env -- Problem: typeOfMaybe makes conversion check with context
  --                        -- Solution? : Take term type as input, and take it apart by hand.
     
  --    ok <- idrisCatch (checkGoal t a env) (\err -> return False)
  --    if ok
  --     then do epsLog "Epsilon done" t a; return t
  --     else do iLOG "Going into inference mode!"
  --             epsilonInfer clock recName env t a a
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
