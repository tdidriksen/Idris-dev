{-# LANGUAGE PatternGuards, PatternSynonyms #-}

module Idris.GuardedRecursion.Helpers where

import Idris.AbsSyntax
import Idris.Docstrings (emptyDocstring)
import Idris.Error

import Idris.Elab.Type (elabPostulate)

import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.Typecheck hiding (isType)

import Idris.GuardedRecursion.Constants hiding (guardedNS)

import Data.Maybe
import Data.List

import Control.Monad
import Control.Monad.State.Lazy as LazyState

import qualified Data.Text as T

-- FROM GR.lhs
data Clock =
    EmptyClock
  | Kappa

applyCompose :: Type -> Type -> Availability -> Term -> Term -> Idris Term
applyCompose a b av f arg =
  do compose <- composeRef
     avTT <- availabilityTerm av
     return $ App (App (App (App (App compose a) b) avTT) f) arg

applyLater :: Availability -> Type -> Idris Type
applyLater av ty =
  do later <- laterRef
     avTT <- availabilityTerm av
     return $ App (App later avTT) ty

applyLater' :: Type -> Idris Type
applyLater' ty =
  do later' <- later'Ref
     return $ App later' ty

applyNext :: Term -> Idris Term
applyNext t =
  do next <- nextRef
     return $ App next t


isLater' :: Type -> Bool
isLater' (P (DCon _ _ _) (n@(NS (UN later) [gr])) ty)
  | later == txt "Later'" && gr == txt "GuardedRecursion" = True
isLater' _ = False

isLater :: Type -> Bool
isLater (P Ref (NS (UN later) [gr]) _)
  | later == txt "Later" && gr == txt "GuardedRecursion" = True
isLater _ = False

unapplyLater :: Type -> Idris (Type, Availability)
unapplyLater t = unapply' t Now
  where
    unapply' :: Type -> Availability -> Idris (Type, Availability)
    unapply' (App f x) av
     | isLater' f = unapply' x (Tomorrow av)
    unapply' (App (App f x) y) av
     | isLater f =
         do xAv <- termAvailability x
            unapply' y (delayBy xAv av)
    unapply' ty av = return (ty, av) 

guardedRef :: Name -> Idris Term
guardedRef = undefined

typeOf :: Term -> Env -> Idris Type
typeOf t env =
  do ctxt <- getContext
     case check ctxt env (forget t) of
      OK (_,t') -> return t'
      Error e -> ierror e

checkGoal :: Term -> Type -> Env -> Idris Bool
checkGoal tm goal env =
  do tmType <- typeOf tm env
     ctxt <- getContext
     ist <- get
     let ucs = map fst (idris_constraints ist)
     case LazyState.evalStateT (convertsC ctxt env tmType goal) (0, ucs) of
      tc -> case tc of
              OK () -> return True
              _ -> return False

-- Availability
{-| Availability is a property on a type, indicating the moment
    at which a value becomes available on a time stream
-}
data Availability =
    Now
  | Tomorrow Availability
  deriving Eq

instance Ord Availability where
  compare Now Now = EQ
  compare Now (Tomorrow _) = LT
  compare (Tomorrow _) Now = GT
  compare (Tomorrow x) (Tomorrow y) = compare x y

availability :: Type -> Idris Availability
availability ty = liftM snd (unapplyLater ty)

delayBy :: Availability -> Availability -> Availability
delayBy Now a = a
delayBy (Tomorrow a) b = delayBy a (Tomorrow b)

termAvailability :: Term -> Idris Availability
termAvailability (P Ref name ty)
  | name == nowName = return Now
termAvailability (App (P Ref name ty) arg)
  | name == tomorrowName = liftM Tomorrow (termAvailability arg)
termAvailability tm = ifail $ "Term " ++ show tm ++ " is not an Availability term."

availabilityTerm :: Availability -> Idris Term
availabilityTerm Now = nowRef
availabilityTerm (Tomorrow n) =
  liftM2 App tomorrowRef (availabilityTerm n)

pattern TConApp tag arity name pty x =
  App (P (TCon tag arity) name pty) x
pattern DConApp tag arity unique name pty x =
  App (P (DCon tag arity unique) name pty) x

isType :: Name -> Type -> Maybe Type
isType tyName (TConApp _ _ n _ x)
  | n == tyName = Just x
isType _ _ = Nothing

forallType ty = isType forallName ty

isDCon :: Name -> Term -> Maybe Term
isDCon tmName (DConApp _ _ _ name _ x)
  | name == lambdaKappaName = Just x
isDCon _ _ = Nothing

lambdaKappaTerm :: Term -> Maybe Term
lambdaKappaTerm tm = isDCon lambdaKappaName tm


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
                             Just _ -> tclift $ tfail (Elaborating "guarded recursion of " n (Msg $ "A guarded recursive name already exist for " ++ show n))
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
                        Nothing -> tclift $ tfail (Elaborating "guarded recursion of " n (Msg $ "A guarded recursive name for " ++ show n ++ " could not be found."))

-- |Looks up a name for its guarded version in the context. If it does not exist it creates one.                        
getGuardedNameSoft :: Name -> Idris Name
getGuardedNameSoft n = do i <- getIState
                          case lookup n (guarded_renames i) of
                            Just n' -> return n'
                            Nothing -> guardedNameCtxt n

-- |Prefixes a name with "guarded_"
guardedText :: T.Text -> T.Text
guardedText = prefixTxt guardedPrefix

-- |prefixTxt s t prefixes t with s
prefixTxt :: String -> T.Text -> T.Text
prefixTxt s t = txt (s ++ (str t))

-- |prefixName s n prefixes n with s
prefixName :: String -> Name -> Name
prefixName s (UN t) = UN (prefixTxt s t)
prefixName s (NS n ns) = NS (prefixName s n) ns
prefixName s (MN i t) = MN i (prefixTxt s t)
prefixName _ n = n

-- |Prefixes a namespace with the guarded recursion namespace.
guardedNS :: [T.Text] -> [T.Text]
guardedNS ns = ns ++ [(txt guardedNamespace)]

-- |Same as guardedNS but on strings.
guardedNSs :: [String] -> [String]
guardedNSs ss = map str (guardedNS (map txt ss))

-- |Same as guardedNS but on SyntaxInfo level.
withGuardedNS :: SyntaxInfo -> SyntaxInfo
withGuardedNS syn = syn { syn_namespace = guardedNSs (syn_namespace syn) }

-- |inNS ns n puts n in namespace ns
inNS :: [T.Text] -> Name -> Name
inNS ns' (NS n ns)  = (NS n (ns' ++ ns))

inNSs :: [String] -> Name -> Name
inNSs ss = inNS (map txt ss)

inNSo :: T.Text -> Name -> Name
inNSo n = inNS [n]

inNSos :: String -> Name -> Name
inNSos s = inNSo (txt s)

-- |A PTerm representing a reference to Later
applyPTLater :: PTerm -> PTerm
applyPTLater = applyPTLaterFC emptyFC

applyPTLaterFC :: FC -> PTerm -> PTerm
applyPTLaterFC fc t = PApp fc (laterPTRefFC fc) [pexp t]

-- |elabGuardedPostulate (n, ty) elaborates:
-- |  postulate gn = ty
-- |where gn is the guarded name of n
elabGuardedPostulate :: (Name, PTerm) -> Idris ()
elabGuardedPostulate (n, ty) = do gn <- getGuardedName n
                                  let syn = withGuardedNS defaultSyntax
                                  logLvl 3 $ "Created postulate " ++ show gn ++ " with type " ++ show ty ++ " from " ++ show n ++ " for checking for guarded recursion."
                                  elabPostulate (toplevel { namespace = Just (syn_namespace syn) }) syn emptyDocstring emptyFC [] gn ty

-- |guardedTerm tyn t inserts laters on references to tyn in t                                  
guardedTerm :: Name -> PTerm -> PTerm
guardedTerm tyn t
  | isName t = applyPTLater t
  where
    isName :: PTerm -> Bool
    isName (PApp _ (PRef _ n) _) = n == tyn || n == (nsroot tyn)
    isName (PRef _ n) = n == tyn || n == (nsroot tyn)
    isName _ = False
guardedTerm tyn (PPi p n t t') = PPi p n (guardedTerm tyn t) (guardedTerm tyn t')
guardedTerm _ t = t 

-- |Similar to guardedTerm but only guards left hand sides of pi types.
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

-- |guardRootNamesIn n t replaces any references to n in t                                                
guardRootNamesIn :: Name -> PTerm -> Idris PTerm
guardRootNamesIn n t = do gn <- getGuardedName n
                          let gt = substMatch (nsroot n) (PRef emptyFC gn) t
                          guardExactNamesIn n gt

-- |guardExactNamesIn n t replaces references to exactly n in t                          
guardExactNamesIn :: Name -> PTerm -> Idris PTerm
guardExactNamesIn n t = do gn <- getGuardedName n
                           return $ substMatch n (PRef emptyFC gn) t

-- |boxingFunction n gn as creates the postulates:
-- |  boxn : gn -> n
-- |  unboxn: n -> gn                           
boxingFunctions :: Name -> Name -> [PTerm] -> Idris ()
boxingFunctions n gn as = do let a = PApp emptyFC (PRef emptyFC n ) (map pexp as)
                             let b = PApp emptyFC (PRef emptyFC gn) (map pexp as)
                             let syn = withGuardedNS defaultSyntax
                             let box = pi b a
                             let boxN = inNSos guardedNamespace (boxName n)
                             let unbox = pi a b
                             let unboxN = inNSos guardedNamespace (unboxName n)
                             elabPostulate (toplevel { namespace = Just (syn_namespace syn) }) syn emptyDocstring emptyFC [] boxN box
                             elabPostulate (toplevel { namespace = Just (syn_namespace syn) }) syn emptyDocstring emptyFC [] unboxN unbox
                             i <- getIState
                             iLOG $ "(Un)boxing functions created for " ++ show n
                             putIState (i { guarded_boxing = (n, (boxN, unboxN)) : (guarded_boxing i) })
                             
  where
    pi :: PTerm -> PTerm -> PTerm
    pi = PPi (Exp [] Dynamic False) (sUN "__pi_arg")

    boxName :: Name -> Name
    boxName = prefixName "box"
    unboxName :: Name -> Name
    unboxName = prefixName "unbox"

-- |Checks if a type constructor is simply typed.
-- |Only binders and types are allowed.
guardableTC :: Type -> Bool
guardableTC (Bind _ b t) = guardableTC (binderTy b) && guardableTC t
guardableTC (TType _) = True
guardableTC _ = False


-- |Same as guardedTT, but ignoring names in the given list.
guardedTTIgnore :: [Name] -> Term -> Idris Term
guardedTTIgnore is t = do let fn = is \\ (freeNames t)
                          i <- getIState
                          let gns = mapMaybe (\y -> lookup y (guarded_renames i)) fn
                          ctxt <- getContext
                          let ps = concat $ map (\n -> lookupP n ctxt) gns
                          return $ substNames (zip gns ps) t

-- |guards all free names in the term.
guardedTT :: Term -> Idris Term
guardedTT = guardedTTIgnore []                 
