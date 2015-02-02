module Idris.GuardedRecursion.Exports where

import Idris.Core.TT

data GuardedProjectionNames = GuardedProjectionNames { guardedProj :: Name
                                                     , forallProj  :: Name
                                                     } deriving (Show)

type GuardedRename = Either Name GuardedProjectionNames

unpackRename :: GuardedRename -> Name
unpackRename (Left  n) = n
unpackRename (Right g) = guardedProj g
