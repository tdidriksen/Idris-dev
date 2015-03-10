module Idris.GuardedRecursion.Exports where

import Idris.Core.TT

------- DEFINITIONS -------

data GuardedProjectionNames = GuardedProjectionNames { guardedProj :: Name
                                                     , forallProj  :: Name
                                                     }

data GuardedRename = GuardedRename Name | ProjectionRename GuardedProjectionNames

instance Show GuardedRename where
  show (GuardedRename n) = show n
  show (ProjectionRename gn) = "(" ++ show (guardedProj gn) ++ ", " ++ show (forallProj gn) ++ ")"
