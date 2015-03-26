{-# LANGUAGE ViewPatterns #-}

module Idris.GuardedRecursion.Helpers where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.Typecheck

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.State.Lazy as LazyState

import qualified Data.Traversable as Tr

import qualified Data.Foldable as F

------- TYPE DEFINITIONS -------
-- rho
type Renaming = (Name, Name)
-- pi
type ProjRenaming = (Name, (Name, Name))

data InfEnv = IE { recursiveReference :: Term, --iota
                   guardedRecursiveReference :: Term,
                   renamingContext :: [Renaming], -- phi
                   projRenamingContext :: [ProjRenaming], -- Pi
                   typingContext :: Env } -- Gamma

type GR a = ReaderT InfEnv Idris a

data Clock = Open | Closed

-- | The 'Modality' type is a property of a guarded
-- recursive function. Any such function is either 'Causal',
-- meaning that the clock of the input determines the
-- clock of the output, or 'NonCausaul', meaning that there
-- is no connection between the clocks in the in- and output.
data Modality = Causal | NonCausal deriving Show

modalityOf :: Name -> Idris Modality
modalityOf n = do i <- get
                  case lookupCtxt n (idris_flags i) of
                   [fnOpts] -> if CausalFn `elem` fnOpts then return Causal else return NonCausal
                   _ -> return NonCausal

------ INTERFACING WITH THE TYPE CHECKER

cEq :: Env -> Type -> Type -> Idris Bool
cEq env ty ty' =
  do ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env ty ty') (0, ucs) of
      tc -> case tc of
              OK () -> return True
              Error e -> do iLOG $ "cEq err: " ++ show e
                            return False

cEq' :: Type -> Type -> GR Bool
cEq' ty ty' = do ie <- ask
                 let env = typingContext ie
                 lift $ cEq env (explicitNames ty) (explicitNames ty')

checkGoal :: Env -> Term -> Type -> Idris Bool
checkGoal env tm ty =
  do tmTy' <- idrisCatch (typeOf tm env >>= \ty' -> return $ Just ty') (const (return Nothing))
     case tmTy' of
      Just tmTy ->
        do iLOG "cEq"
           iLOG $ "tm : " ++ show tm
           iLOG $ "ty : " ++ show ty
           iLOG $ "tmTy : " ++ show tmTy
           cEq env tmTy ty
      Nothing -> return False

typeOf :: Term -> Env -> Idris Type
typeOf t env =
  do ctxt <- getContext
     case check ctxt env (forget t) of
      OK (_,t') -> return t' -- normaliseLater (explicitNames t')
      Error e -> ierror e

typeOf' :: Term -> GR Type
typeOf' t = do ie <- ask
               let env = typingContext ie
               lift $ typeOf t env


------ AUXILIARY TT FUNCTIONS

bindersIn :: TT n -> [(n, Binder (TT n))]
bindersIn (Bind n binder sc) = (n,binder) : bindersIn sc
bindersIn _ = []

debind :: Type -> GR ((Name, Type), Type)
debind (Bind n (Pi _ ty kind) sc) = return ((n, ty), sc)
debind e = lift $ ifail $ "Cannot debind non-function type: " ++ show e

guardedTT :: [Renaming] -> Term -> Idris Term
guardedTT renames tm = mapMTT withGuardedNames tm
  where
    withGuardedNames :: Term -> Idris Term
    withGuardedNames (P nt n _) | nt /= Bound = guardedP n
    withGuardedNames t = return t
    
    guardedP :: Name -> Idris Term
    guardedP n =
      do let n' = case lookup n renames of
                   Just rn -> rn
                   Nothing -> n
         ctxt <- getContext
         case lookupP n' ctxt of 
          [p] -> return p
          _ -> ifail $ "Name " ++ show n' ++ " has no definition."

hasCoinductiveType :: Term -> Env -> GR Bool
hasCoinductiveType t env =
  do ty <- lift $ typeOf t env
     isCoinductive ty env

isApp :: Term -> Bool
isApp (App _ _) = True
isApp _ = False

isCoinductive :: Type -> Env -> GR Bool
isCoinductive ty env =
  do ist <- lift get
     let ((P _ n _), args) = unApply (normalise (tt_ctxt ist) env ty)
     case lookupCtxtExact n (idris_datatypes ist) of
      Just ti -> return $ codata ti
      Nothing -> lift $ ifail $ "Cannot determine whether type " ++ show ty ++ " is coinductive"

mapMTT :: Monad m => (TT n -> m (TT n)) -> TT n -> m (TT n)
mapMTT f (P nameType n ty) =
  do ty' <- mapMTT f ty
     f (P nameType n ty')
mapMTT f (Bind n binder sc) =
  do sc' <- mapMTT f sc
     binder' <- Tr.forM binder (mapMTT f)
     f (Bind n binder' sc')
mapMTT f (App a b) =
  do a' <- mapMTT f a
     b' <- mapMTT f b
     f (App a' b')
mapMTT f (Proj tm i) =
  do tm' <- mapMTT f tm
     f (Proj tm' i)
mapMTT f tm = f tm

mapTT :: (TT n -> TT n) -> TT n -> TT n
mapTT f (P nt n ty) = f (P nt n (mapTT f ty))
mapTT f (Bind n binder sc) = f (Bind n (fmap (mapTT f) binder) (mapTT f sc))
mapTT f (App t t') = f (App (mapTT f t) (mapTT f t'))
mapTT f (Proj t i) = f (Proj (mapTT f t) i)
mapTT f t = f t

occursBoundIn :: Name -> Type -> Bool
-- If shadowed, the given name does not occur. Instead, the newly binded name occurs.
occursBoundIn n (Bind n' binder sc) | n == n' = False
occursBoundIn n (Bind n' binder sc) =
  F.foldr' (\t acc -> occursBoundIn n t || acc) (occursBoundIn n sc) binder
occursBoundIn n (P Bound n' ty) | n == n' = True
occursBoundIn n (P _ _ ty) = occursBoundIn n ty
occursBoundIn n (App t t') = occursBoundIn n t || occursBoundIn n t'
occursBoundIn n (Proj t _) = occursBoundIn n t
occursBoundIn n _ = False

replaceRecursiveReference :: Name -> Term -> Type -> Env -> Idris (Term, Term)
replaceRecursiveReference n tm ty env =
  do let (params, recType) = splitType ty
     iLOG $ "params : " ++ show params
     iLOG $ "recType : " ++ show recType
     let numberOfParams = length params
     iLOG $ "numberOfParams: " ++ show numberOfParams
     ctxt <- getContext
     let placeholder = P Ref (uniqueNameCtxt ctxt (sUN "rec") (map fst env ++ allTTNames tm)) recType
     r <- replaceRecRef numberOfParams placeholder tm
     return (r, placeholder)
  where
    replaceRecRef :: Int -> Term -> Term -> Idris Term
    replaceRecRef numberOfParams placeholder (unapplyRecRef n -> Just (f, args)) =
      do iLOG $ "args : " ++ show args
         return $ mkApp placeholder (drop numberOfParams args)
    replaceRecRef numberOfParams placeholder p@(P _ _ _) = return p
    replaceRecRef numberOfParams placeholder (Bind n binder sc) =
      liftM (\b -> Bind n b ty) (Tr.forM binder (replaceRecRef numberOfParams placeholder))
    replaceRecRef numberOfParams placeholder (App f x) =
      liftM2 App (replaceRecRef numberOfParams placeholder f) (replaceRecRef numberOfParams placeholder x)
    replaceRecRef numberOfParams placeholder (Proj tm i) =
      liftM (\t -> Proj t i) (replaceRecRef numberOfParams placeholder tm)
    replaceRecRef _ _ tm = return tm
                                                           
    -- isRecursiveReference :: Name -> Term -> Bool
    -- isRecursiveReference n (P Ref n' pty) = n == n'
    -- isRecursiveReference _ _ = False

    unapplyRecRef :: Name -> Term -> Maybe (Term, [Term])
    unapplyRecRef recName (unApply -> unapp@((P Ref n _), _)) | n == recName = Just unapp
    unapplyRecRef _ _ = Nothing
  

splitType :: Type -> ([(Name, Binder Type)], Type)
splitType (Bind n binder@(Pi _ _ _) sc)
  | n `occursBoundIn` sc = let (params, rest) = splitType sc
                           in ((n,binder):params, rest)
splitType ty = ([], ty)


-- matchesOnCoinductiveData :: Term -> Env -> GR Bool
-- matchesOnCoinductiveData (P _ _ _) = return False
-- matchesOnCoinductiveData (App f x) =
--   do yes <- hasCoinductiveType (App f x) env
--      if yes
--         then return yes
--         else do yesF <- matchesOnCoinductiveData f
--                 yesX <- matchesOnCoinductiveData x
--                 return $ yesF || yesX
-- matchesOnCoinductiveData (Bind n binder sc) =
--   matchesOnCoinductiveData sc
-- matchesOnCoinductiveData (Proj t i) =
--   matchesOnCoinductiveData t
-- matchesOnCoinductiveData _ = return False
