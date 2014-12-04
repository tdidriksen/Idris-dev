{-# LANGUAGE PatternGuards #-}

module Idris.GuardedRecursionHelpers (boxingFunctions,
                                      guardedName,
                                      getGuardedName,
                                      guardedConstructor,
                                      guardNamesIn,
                                      guardedTerm,
                                      elabGuardedPostulate,
                                      withGuardedNS,
                                      guardedNameCtxt) where

import Idris.AbsSyntax
import Idris.Docstrings (emptyDocstring)
import Idris.Error

import Idris.Elab.Type (elabPostulate)

import Idris.Core.Evaluate
import Idris.Core.TT

import Prelude
import Data.Maybe

import qualified Data.Text as T

-- |Creates a guarded version of a name.
guardedName :: Name -> Name
guardedName (UN t) = UN (guardedText t)
guardedName (NS n ns) = NS (guardedName n) (guardedNS ns)
guardedName (MN i t) = MN i (guardedText t)
guardedName n = n

-- |Adds a rename to the guarded context.
addGuardedRename :: Name -> Name -> Idris ()
addGuardedRename n gn = do i <- getIState
                           case lookup n (guarded_renames i) of
                             Just _ -> ifail $ "Name already exists " ++ show n -- Fix me
                             Nothing -> putIState (i { guarded_renames = (n, gn) : (guarded_renames i) })

-- |Creates and adds a rename to the guarded context.
guardedNameCtxt :: Name -> Idris Name
guardedNameCtxt n = do let gn = guardedName n
                       addGuardedRename n gn
                       return gn

-- |Looks up a name for its guarded version in the context.
getGuardedName :: Name -> Idris Name
getGuardedName n = do i <- getIState
                      case lookup n (guarded_renames i) of
                        Just n' -> return n'
                        Nothing -> ifail $ "Name not found " ++ show n -- Fix me

-- |Looks up a name for its guarded version in the context. If it does not exist it creates one.                        
getGuardedNameSoft :: Name -> Idris Name
getGuardedNameSoft n = do i <- getIState
                          case lookup n (guarded_renames i) of
                            Just n' -> return n'
                            Nothing -> guardedNameCtxt n

guardedText :: T.Text -> T.Text
guardedText t = txt ("guarded_" ++ str t)

-- |A PTerm representing a reference to Later
laterRef :: PTerm
laterRef = laterRefFC emptyFC

laterRefFC :: FC -> PTerm
laterRefFC fc = PRef fc (sUN "Later")

applyLater :: PTerm -> PTerm
applyLater t = PApp emptyFC laterRef [pexp t]

applyLaterFC :: FC -> PTerm -> PTerm
applyLaterFC fc t = PApp fc (laterRefFC fc) [pexp t]

guardedNamespace :: String
guardedNamespace = "GuardedRecursion"

-- |Prefixes a namespace with the guarded recursion namespace.
guardedNS :: [T.Text] -> [T.Text]
guardedNS ns = ns ++ [(txt guardedNamespace)]

-- |Same as guardedNS but on strings.
guardedNSs :: [String] -> [String]
guardedNSs ss = map str (guardedNS (map txt ss))

-- |Same as guardedNS but on SyntaxInfo level.
withGuardedNS :: SyntaxInfo -> SyntaxInfo
withGuardedNS syn = syn { syn_namespace = guardedNSs (syn_namespace syn) }



-- |elabGuardedPostulate (n, ty) elaborates:
-- |  postulate gn = ty
-- |where gn is the guarded name of n
elabGuardedPostulate :: (Name, PTerm) -> Idris ()
elabGuardedPostulate (n, ty) = do gn <- getGuardedName n
                                  let syn = withGuardedNS defaultSyntax
                                  iLOG $ show (syn_namespace syn)                                      
                                  iLOG $ "Created postulate " ++ show gn ++ " with type " ++ show ty ++ " from " ++ show n ++ " for checking for guarded recursion."
                                  elabPostulate (toplevel { namespace = Just (syn_namespace syn) }) syn emptyDocstring emptyFC [] gn ty

-- |guardedTerm tyn t inserts laters on references to tyn in t                                  
guardedTerm :: Name -> PTerm -> PTerm
guardedTerm tyn t
  | isName t = applyLater t
  where
    isName :: PTerm -> Bool
    isName (PApp _ (PRef _ n) _) = n == tyn || n == (nsroot tyn)
    isName (PRef _ n) = n == tyn || n == (nsroot tyn)
    isName _ = False
guardedTerm tyn (PPi p n t t') = PPi p n (guardedTerm tyn t) (guardedTerm tyn t')
guardedTerm _ t = t 

guardedConstructor :: Name -> PTerm -> PTerm
guardedConstructor tyn (PPi p n t t')
  = PPi p n (guardedTerm tyn t) (guardedConstructor tyn t')
guardedConstructor _ t = t

-- |guardNamesIn n t replaces all occurences of n in t with the guarded version
-- |If n is a unique name it also replaces occurences without namespaces.
guardNamesIn :: Name -> PTerm -> Idris PTerm
guardNamesIn n t = do i <- getIState
                      case lookupNames (nsroot n) (tt_ctxt i) of
                        [_] -> guardRootNamesIn n t
                        _   -> guardExactNamesIn n t
                        
guardRootNamesIn :: Name -> PTerm -> Idris PTerm
guardRootNamesIn n t = do gn <- getGuardedName n
                          let gt = substMatch (nsroot n) (PRef emptyFC gn) t
                          guardExactNamesIn n gt
                          
guardExactNamesIn :: Name -> PTerm -> Idris PTerm
guardExactNamesIn n t = do gn <- getGuardedName n
                           return $ substMatch n (PRef emptyFC gn) t
                             
boxingFunctions :: Name -> Name -> [PTerm] -> Idris ()
boxingFunctions n gn as = do let a = PApp emptyFC (PRef emptyFC n ) (map pexp as)
                             let b = PApp emptyFC (PRef emptyFC gn) (map pexp as)
                             let syn = withGuardedNS defaultSyntax
                             let box = pi b a
                             let boxN = boxName n
                             let unbox = pi a b
                             let unboxN = unboxName n
                             elabPostulate (toplevel { namespace = Just (syn_namespace syn) }) syn emptyDocstring emptyFC [] boxN box
                             elabPostulate (toplevel { namespace = Just (syn_namespace syn) }) syn emptyDocstring emptyFC [] unboxN unbox
                             i <- getIState
                             putIState (i { guarded_boxing = (n, (boxN, unboxN)) : (guarded_boxing i) })
                             
  where
    pi a b = PPi (Exp [] Dynamic False) (sUN "__pi_arg") a b

    prefixTxt :: String -> T.Text -> T.Text
    prefixTxt s t = txt (s ++ (str t))

    prefixName :: String -> Name -> Name
    prefixName s (UN t) = UN (prefixTxt s t)
    prefixName s (NS n ns) = NS (prefixName s n) (guardedNS ns)
    prefixName s (MN i t) = MN i (prefixTxt s t)
    prefixName _ n = n

    boxName = prefixName "box"
    unboxName = prefixName "unbox"

{-
guardableTC :: Type -> Bool
guardableTC (PPi _ _ t t') = guardableTC t && guardableTC t'
guardableTC TType = True
guardableTC _ = False-}
