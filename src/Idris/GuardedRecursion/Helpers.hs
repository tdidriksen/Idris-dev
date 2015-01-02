{-# LANGUAGE PatternGuards, PatternSynonyms, ViewPatterns #-}

module Idris.GuardedRecursion.Helpers where

import Idris.AbsSyntax
import Idris.Docstrings (emptyDocstring)
import Idris.Error

import Idris.Elab.Type (elabPostulate)

import Idris.Core.Evaluate
import Idris.Core.TT hiding (nextName)
import Idris.Core.Typecheck hiding (isType)

import Idris.GuardedRecursion.Constants

import Control.Applicative

import Data.Maybe
import Data.List

import Data.Traversable as Tr

import Control.Monad
import Control.Monad.State.Lazy as LazyState

import qualified Data.Text as T

data Extract a = Extracted a | Nope

data Clock = Open | Closed

instance Functor Extract where
  fmap _ Nope          = Nope
  fmap f (Extracted a) = Extracted (f a)

instance Applicative Extract where
  pure = Extracted
  (Extracted f) <*> (Extracted a) = Extracted (f a)
  Nope <*> _ = Nope
  _ <*> Nope = Nope

instance Monad Extract where
  (Extracted x) >>= k = k x
  Nope          >>= _ = Nope

  (Extracted _ ) >> k = k
  Nope           >> _ = Nope

  return = Extracted
  fail _ = Nope

applyApply :: Term -> Idris Term
applyApply tm =
  do apply <- applyRef
     return $ App apply tm

unapplyApply :: Term -> Maybe Term
unapplyApply tm = unapplyRef applyName tm

applyCompose :: Type -> Type -> Term -> Term -> Term -> Idris Term
applyCompose a b av f arg =
  do compose <- composeRef
     return $ App (App (App (App (App compose a) b) av) f) arg

pattern Compose compose a b av f arg = App (App (App (App (App compose a) b) av) f) arg

unapplyCompose :: Term -> Maybe (Type, Type, Term, Term, Term)
unapplyCompose (Compose compose a b av f arg)
  | isCompose compose = Just (a, b, av, f, arg)
unapplyCompose _ = Nothing

pattern Delay delay lazyType delayType t = App (App (App delay lazyType) delayType) t

unapplyDelay :: Term -> Maybe Term
unapplyDelay (Delay delay lazyType _ tm)
  | isDelay delay && isLazyCodata lazyType = Just tm
unapplyDelay _ = Nothing

removeDelay :: Term -> Term
removeDelay t = mapTT withoutDelay t
  where
    withoutDelay :: Term -> Term
    withoutDelay (unapplyDelay -> Just tm) = tm
    withoutDelay tm = tm

applyForall :: Type -> Idris Type
applyForall ty =
  do forall <- forallRef
     return $ App forall ty

applyLater :: Availability -> Type -> Idris Type
applyLater av ty =
  do later <- laterRef
     avTT <- availabilityTerm av
     return $ App (App later avTT) ty

applyLater' :: Type -> Idris Type
applyLater' ty =
  do later' <- later'Ref
     return $ App later' ty

unapplyLater' :: Type -> Maybe Type
unapplyLater' ty = unapplyType later'Name ty

unapplyTomorrow :: Term -> Maybe Term
unapplyTomorrow tm = unapplyDataConstructor tomorrowName tm

unapplyNLater :: Type -> Maybe Type
unapplyNLater (App (App later (unapplyTomorrow -> Just av)) ty)
 | isLater later = Just $ App (App later av) ty
unapplyNLater _ = Nothing
                      
unapplyLater :: Type -> Maybe Type
unapplyLater (unapplyLater' -> Just ty) = Just ty
unapplyLater (unapplyNLater -> Just ty) = Just ty
unapplyLater _ = Nothing

applyLambdaKappa :: Term -> Idris Term
applyLambdaKappa tm =
  do lambdaKappa <- lambdaKappaRef
     return $ App lambdaKappa tm

unapplyLambdaKappa :: Term -> Maybe Term
unapplyLambdaKappa tm = unapplyDataConstructor lambdaKappaName tm

applyNext :: Term -> Idris Term
applyNext t =
  do next <- nextRef
     return $ App next t

unapplyNext :: Term -> Maybe Term
unapplyNext tm = unapplyDataConstructor nextName tm

isApply :: Term -> Bool
isApply (P Ref (NS (UN apply) [gr]) _)
  | apply == txt applyStr && gr == txt guardedRecursion = True
isApply _ = False                                                          

isLater' :: Type -> Bool
isLater' (P (DCon _ _ _) (n@(NS (UN later) [gr])) ty)
  | later == txt later'Str && gr == txt guardedRecursion = True
isLater' _ = False

isLater :: Type -> Bool
isLater (P Ref (NS (UN later) [gr]) _)
  | later == txt laterStr && gr == txt guardedRecursion = True
isLater _ = False

isForall :: Type -> Bool
isForall (P (TCon _ _) (NS (UN forall) [gr]) _)
  | forall == txt forallStr && gr == txt guardedRecursion = True
isForall _ = False                                                            

isNext :: Term -> Bool
isNext (P Ref (NS (UN next) [gr]) _)
  | next == txt nextStr && gr == txt guardedRecursion = True
isNext _ = False                                                         

isCompose :: Term -> Bool
isCompose (P Ref (NS (UN compose) [gr]) _)
  | compose == txt composeStr && gr == txt guardedRecursion = True
isCompose _ = False

isDelay :: Term -> Bool
isDelay (P _ (UN delay) _) | delay == txt delayStr = True
isDelay _ = False

isLazyCodata :: Term -> Bool
isLazyCodata (P _ (UN lazyCodata) _) | lazyCodata == txt lazyCodataStr = True
isLazyCodata _ = False

isLambdaKappa :: Term -> Bool
isLambdaKappa (P Ref (NS (UN lambdaKappa) [gr]) _)
  | lambdaKappa == txt lambdaKappaStr && gr == txt guardedRecursion = True
isLambdaKappa _ = False                                                                      

guardedTerm :: Term -> Idris Term
guardedTerm p@(P Bound n ty)      = return p
guardedTerm (P Ref n ty)          = guardedRef n
guardedTerm (P (DCon _ _ _) n ty) = guardedDataConstructor n
guardedTerm p@(P (TCon _ _) n ty) = return p
guardedTerm (Bind n binder sc)    = guardedTerm sc
guardedTerm (App f x)             = liftM2 App (guardedTerm f) (guardedTerm x)
guardedTerm tm                    = return tm

guardedRef :: Name -> Idris Term
guardedRef = undefined

guardedDataConstructor :: Name -> Idris Term
guardedDataConstructor = undefined

typeOfMaybe :: Term -> Env -> Idris (Maybe Type)
typeOfMaybe t env = idrisCatch (typeOf t env >>= \t' -> return $ Just t') (\_ -> return Nothing)

typeOf :: Term -> Env -> Idris Type
typeOf t env =
  do ctxt <- getContext
     case check ctxt env (forget t) of
      OK (_,t') -> return t'
      Error e -> ierror e

checkGoal :: Term -> Type -> Env -> Idris Bool
checkGoal tm goal env =
  do tmType <- typeOf tm env
     iLOG $ "Conversion checking " ++ showTT tmType ++ " and " ++ showTT goal
     ctxt <- getContext
     ist <- get
     -- let ucs = map fst (idris_constraints ist)
     case convEq' ctxt (map fst (filter isHole env)) tmType goal of
      tc -> case tc of
             OK True -> do iLOG $ "Conversion check succeeded"; return True
             _ -> do iLOG $ "Conversion check failed"; return False
     -- catchError (LazyState.evalStateT (convertsC ctxt env tmType goal) (0, ucs)) of
     --  tc -> case tc of
     --          OK () -> return True
     --          _ -> return False

debindFirstArg :: Type -> Maybe Type
debindFirstArg (Bind _ (Pi t _) _) = Just t
debindFirstArg _ = Nothing

nowType :: Type -> Type
nowType    (unapplyLater -> Just ty) = nowType ty
nowType ty@(unapplyLater -> Nothing) = ty


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

-- availability :: Type -> Idris Availability
-- availability ty = liftM snd (unapplyLater ty)

-- delayBy :: Availability -> Availability -> Availability
-- delayBy Now a = a
-- delayBy (Tomorrow a) b = delayBy a (Tomorrow b)

delayBy :: Type -> Type -> Idris Type
delayBy (unapplyLater -> Just ty) ty' =
  do delayed <- delayBy ty ty'
     applyLater' delayed
delayBy (unapplyLater -> Nothing) ty' =
  return ty'

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

unapplyType :: Name -> Type -> Maybe Type
unapplyType tyName (TConApp _ _ n _ x)
  | n == tyName = Just x
unapplyType _ _ = Nothing

unapplyForall :: Term -> Maybe Term
unapplyForall ty = unapplyType forallName ty

unapplyDataConstructor :: Name -> Term -> Maybe Term
unapplyDataConstructor tmName (DConApp _ _ _ name _ x)
  | name == tmName = Just x
unapplyDataConstructor _ _ = Nothing

unapplyRef :: Name -> Term -> Maybe Term
unapplyRef tmName (App (P Ref name _) x)
  | name == tmName = Just x
unapplyRef _ _ = Nothing

-- |Creates a guarded version of a name.
guardedName :: Name -> Name
guardedName (UN t) = UN (guardedText t)
guardedName (NS n ns) = NS (guardedName n) (placeInGuardedNS ns)
guardedName (MN i t) = MN i (guardedText t)
guardedName n = n

-- |Adds a rename to the guarded context.
addGuardedRename :: Name -> Name -> Idris ()
addGuardedRename n gn = do i <- getIState
                           case lookup n (guarded_renames i) of
                             Just _ -> tclift $ tfail (Elaborating "guarded recursion of " n (Msg $ "A guarded recursive name already exists for " ++ show n))
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
placeInGuardedNS :: [T.Text] -> [T.Text]
placeInGuardedNS ns = ns ++ [(txt guardedRecursion)]

-- |Same as guardedNS but on strings.
placeInGuardedNSs :: [String] -> [String]
placeInGuardedNSs ss = map str (placeInGuardedNS (map txt ss))

-- |Same as guardedNS but on SyntaxInfo level.
withGuardedNS :: SyntaxInfo -> SyntaxInfo
withGuardedNS syn = syn { syn_namespace = placeInGuardedNSs (syn_namespace syn) }

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
guardedPTerm :: Name -> PTerm -> PTerm
guardedPTerm tyn t
  | isName t = applyPTLater t
  where
    isName :: PTerm -> Bool
    isName (PApp _ (PRef _ n) _) = n == tyn || n == (nsroot tyn)
    isName (PRef _ n) = n == tyn || n == (nsroot tyn)
    isName _ = False
guardedPTerm tyn (PPi p n t t') = PPi p n (guardedPTerm tyn t) (guardedPTerm tyn t')
guardedPTerm _ t = t 

-- |Similar to guardedPTerm but only guards left hand sides of pi types.
guardedConstructor :: Name -> PTerm -> PTerm
guardedConstructor tyn (PPi p n t t')
  = PPi p n (guardedPTerm tyn t) (guardedConstructor tyn t')
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
                             let boxN = inNSs guardedNS (boxName n)
                             let unbox = pi a b
                             let unboxN = inNSs guardedNS (unboxName n)
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

guardedTT' :: Term -> Idris Term
guardedTT' tm = mapMTT withGuardedNames tm
  where
    withGuardedNames :: Term -> Idris Term
    withGuardedNames (P nt n _) | nt /= Bound = guardedP n
    withGuardedNames t = return t
    
    guardedP :: Name -> Idris Term
    guardedP n =
      do i <- get
         gname <- case lookup n $ guarded_renames i of
                   Just n' -> return n'
                   Nothing -> return n
         let ctxt = tt_ctxt i
         case lookupP gname ctxt of 
          [p] -> return p
          _ -> ifail $ "Name " ++ show gname ++ " has no definition."



mapMTT :: Monad m => (TT n -> m (TT n)) -> TT n -> m (TT n)
mapMTT f (P nameType n ty) =
  do ty' <- mapMTT f ty
     f (P nameType n ty')
mapMTT f (Bind n binder sc) =
  do sc' <- mapMTT f sc
     binder' <- Tr.forM binder f
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
mapTT f (Bind n binder sc) = f (Bind n (fmap f binder) (mapTT f sc))
mapTT f (App t t') = f (App (mapTT f t) (mapTT f t'))
mapTT f (Proj t i) = f (Proj (mapTT f t) i)
mapTT f t = f t

showTT :: Term -> String
showTT (P nametype n ty) = "(P " ++ showNameType nametype ++ " " ++ show n ++ " " ++ showTT ty ++ ")"
showTT (V i) = "V " ++ show i
showTT (Bind n binder sc) = "(Bind " ++ show n ++ " " ++ showBinder binder ++ " " ++ showTT sc ++ ")"
showTT (App f x) = "(App " ++ showTT f ++ " " ++ showTT x ++ ")"
showTT (Constant c) = "(Constant ++ " ++ show c ++ ")"
showTT (Proj t i) = "(Proj " ++ showTT t ++ " " ++ show i ++ ")"
showTT Erased = "Erased"
showTT Impossible = "Impossible"
showTT (TType _) = "TType"
showTT (UType _) = "UType"

showNameType :: NameType -> String
showNameType Ref = "Ref"
showNameType Bound = "Bound"
showNameType (DCon tag _ _) = "(DCon " ++ show tag ++ ")"
showNameType (TCon tag _) = "(TCon " ++ show tag ++ ")"

showBinder :: Binder Term -> String
showBinder (Lam ty) = "Lam " ++ showTT ty
showBinder (Pi ty kind) = "Pi " ++ showTT ty ++ " " ++ showTT kind
showBinder (Let ty val) = "Let " ++ showTT ty ++ " " ++ showTT val
showBinder (NLet ty val) = "NLet " ++ showTT ty ++ " " ++ showTT val
showBinder (Hole ty) = "Lam " ++ showTT ty
showBinder (GHole e ty) = "GHole " ++ show e ++ " " ++ showTT ty
showBinder (Guess ty val) = "Guess " ++ showTT ty ++ " " ++ showTT val
showBinder (PVar ty) = "PVar " ++ showTT ty
showBinder (PVTy ty) = "PVTy " ++ showTT ty
