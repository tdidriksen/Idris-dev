module Idris.GuardedRecursion.Renaming where

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Exports
import Idris.GuardedRecursion.Error

import Idris.Core.TT
import Idris.Core.Evaluate

import Idris.AbsSyntax
import Idris.AbsSyntaxTree

import qualified Data.Text as T

------- UNPACKING -------

-- | If the name is a projection name gets get guarded name, otherwise just the name.
unpackGuardedName :: GuardedRename -> Name
unpackGuardedName (GuardedRename n) = n
unpackGuardedName (ProjectionRename g) = guardedProj g

-- | If the name is a projection name unpacks unpack forall name, otherwise just the name.
unpackForallName :: GuardedRename -> Name
unpackForallName (GuardedRename n) = n
unpackForallName (ProjectionRename g) = forallProj g

------- RENAMING -------

guardedName = prefixName guardedPrefix
forallName = prefixName forallPrefix

-- |prefixName s n prefixes n with s
prefixName :: String -> Name -> Name
prefixName s (UN t) = UN (prefixTxt s t)
prefixName s (NS n ns) = NS (prefixName s n) ns
prefixName s (MN i t) = MN i (prefixTxt s t)
prefixName s (SN sn) = SN (prefixSpecialName s sn)
prefixName _ n = n

prefixSpecialName :: String -> SpecialName -> SpecialName
prefixSpecialName s (WhereN i n n') = WhereN i (prefixName s n) (prefixName s n')
prefixSpecialName s (WithN i n) = WithN i (prefixName s n)
prefixSpecialName s (InstanceN n ts) = InstanceN (prefixName s n) ts
prefixSpecialName s (ParentN n t) = ParentN (prefixName s n) t
prefixSpecialName s (MethodN n) = MethodN $ prefixName s n
prefixSpecialName s (CaseN n) = CaseN $ prefixName s n
prefixSpecialName s (ElimN n) = ElimN $ prefixName s n
prefixSpecialName s (InstanceCtorN n) = InstanceCtorN $ prefixName s n

prefixTxt :: String -> T.Text -> T.Text
prefixTxt s t = txt (s ++ (str t))

------- STATE OPERATIONS -------

-- | Adds a rename to the context.
addRename :: Name -> GuardedRename -> Idris ()
addRename name guardedName = do i <- getIState
                                case lookup name (guarded_renames i) of
                                  Just rn -> return () -- grFail (RenamingFailed $ "Attemped to add new rename " ++ show guardedName ++ " for " ++ show name ++ " which already has rename " ++ show rn)
                                  Nothing -> putIState (i { guarded_renames = (name, guardedName) : (guarded_renames i) })


-- | Looks for rename for the given name. Returns it if found, fails if it does not exist.
fetchRename :: Name -> Idris GuardedRename
fetchRename name = do i <- getIState
                      rename <- maybeFetchRename name
                      case rename of
                        Just rn -> return rn
                        Nothing -> grFail (RenamingFailed $ "A rename for " ++ show name ++ " does not exist")

-- | Lookup rename for input name. If the rename is not a projection rename, return it. Otherwise, return nothing.
fetchGuardedRename :: Name -> Idris (Maybe Name)
fetchGuardedRename n = do i <- getIState
                          rename <- maybeFetchRename n
                          case rename of
                           Just (GuardedRename n) -> return $ Just n
                           _                      -> return Nothing

-- | Looks for rename for the given name. Just name if its found, Nothing if it does not exist.
maybeFetchRename :: Name -> Idris (Maybe GuardedRename)
maybeFetchRename name = do i <- getIState
                           return $ lookup name (guarded_renames i)

-- | Creates a regular rename, adds it to the context, and returns the created rename.
createAndAddRename :: Name -> Idris GuardedRename
createAndAddRename name = do let guardedRename = GuardedRename $ guardedName name
                             addRename name guardedRename
                             return guardedRename

-- | Same as createAndAddRename, but specifically for projections. Both a guarded and a forall name is created.                             
createAndAddProjRename :: Name -> Idris GuardedRename
createAndAddProjRename name = do let guardedRename = ProjectionRename $ GuardedProjectionNames (guardedName name) (forallName name)
                                 addRename name guardedRename
                                 return guardedRename

typeOfGuardedRename :: Name -> Env -> Idris (Maybe Type)
typeOfGuardedRename n env = do rn <- fetchGuardedRename n
                               ctxt <- getContext
                               case rn of
                                Just n' -> return $ lookupTyExact n' ctxt
                                Nothing -> return Nothing
                     
