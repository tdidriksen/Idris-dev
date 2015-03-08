module Idris.GuardedRecursion.Helpers where

import Idris.Core.TT

import Idris.AbsSyntaxTree

import Control.Monad.Reader

------- DEFINITIONS -------
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
