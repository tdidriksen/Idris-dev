module Idris.GuardedRecursion.GuardedTypes where

import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Renaming

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.TT

------- GUARDED PTERM TYPES -------

isGuardableTC :: Type -> Bool
isGuardableTC (Bind _ b t) = isGuardableTC (binderTy b) && isGuardableTC t
isGuardableTC (TType _) = True
isGuardableTC _ = False

-- | Delays all recursive references.
guardedConstructor :: Name -> PTerm -> PTerm
guardedConstructor tn (PPi pl n ty sc)
  = let ty' = if isRecRef 
              then PApp emptyFC later'PTRef [pexp ty]
              else ty
    in PPi pl n ty' (guardedConstructor tn sc)
       where
         isRecRef = ty `isRefTo` tn         
guardedConstructor _ t = t       

isRefTo :: PTerm -> Name -> Bool
isRefTo (PApp _ (PRef _ n) _) tn = (nsroot tn) == (nsroot n)
isRefTo (PRef _ n)            tn = (nsroot tn) == (nsroot n)
isRefTo _ _ = False


guardNamesIn :: SyntaxInfo -> PTerm -> Idris PTerm
guardNamesIn syn pt = mapMPT guardRef pt
  where
    guardRef :: PTerm -> Idris PTerm
    guardRef (PRef fc name) = do name' <-
                                   (do rn <- maybeFetchRename (expandNS syn name)
                                       logLvl 0 $ "Fetched: " ++ show rn ++ " for " ++ show name
                                       return $ case rn of
                                         Just n -> unpackGuardedName n
                                         Nothing -> name)
                                 return $ PRef fc name'                               
    guardRef t = return t
