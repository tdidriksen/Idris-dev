module Idris.GuardedRecursion.Helpers where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.Typecheck

import Idris.AbsSyntaxTree
import Idris.AbsSyntax
import Idris.Error

import Control.Monad.Reader
import Control.Monad.State

------- TYPE DEFINITIONS -------
-- rho
type Renaming = (Name, Name)
-- pi
type ProjRenaming = (Name, (Name, Name))

data InfEnv = IE { recursiveReference :: Term, --iota
                   renamingContext :: [Renaming], -- phi
                   projRenamingContext :: [ProjRenaming], -- Pi
                   typingContext :: Env } -- Gamma

type GR a = ReaderT InfEnv Idris a

data Modality = Causal | NonCausal

data Clock = Open | Closed


------ INTERFACING WITH THE TYPE CHECKER

typeOf :: Term -> Env -> GR Type
typeOf t env =
  do ctxt <- lift getContext
     case check ctxt env (forget t) of
      OK (_,t') -> return t' -- normaliseLater (explicitNames t')
      Error e -> lift $ ierror e


------ AUXILIARY TT FUNCTIONS

bindersIn :: TT n -> [(n, Binder (TT n))]
bindersIn (Bind n binder sc) = (n,binder) : bindersIn sc
bindersIn _ = []

debind :: Type -> GR (Type, Type)
debind (Bind n (Pi _ ty kind) sc) = return (ty, sc)
debind e = lift $ ifail $ "Cannot debind non-function type: " ++ show e

hasCoinductiveType :: Term -> Env -> GR Bool
hasCoinductiveType t env =
  do ty <- typeOf t env
     isCoinductive ty env

isCoinductive :: Type -> Env -> GR Bool
isCoinductive ty env =
  do ist <- lift get
     let ((P _ n _), args) = unApply (normalise (tt_ctxt ist) env ty)
     case lookupCtxtExact n (idris_datatypes ist) of
      Just ti -> return $ codata ti
      Nothing -> lift $ ifail $ "Cannot determine whether type " ++ show ty ++ " is coinductive"
