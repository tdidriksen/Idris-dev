
{-# LANGUAGE PatternGuards, PatternSynonyms, ViewPatterns #-}

module Idris.GuardedRecursion.Helpers where

-- Idris General
import Idris.AbsSyntax
import Idris.Docstrings (emptyDocstring)
import Idris.Error
-- Idris Elaboration
import Idris.Elab.Type (elabPostulate)
-- Idris Core
import Idris.Core.Evaluate
import Idris.Core.TT hiding (nextName)
import Idris.Core.Typecheck hiding (isType)
-- Idris Guarded Recursion
import Idris.GuardedRecursion.Constants
import Idris.GuardedRecursion.Error

import Data.Maybe
import Data.List
import Data.Traversable as Tr hiding (mapM)

import Data.Foldable (foldr')
import qualified Data.Foldable as F

import Control.Applicative

import Control.Monad
import Control.Monad.State.Lazy as LazyState

import qualified Data.Text as T

-----------------------------------------------------
----------------- DATA DECLARATIONS -----------------
-----------------------------------------------------

-- | Availability is a property on a type, indicating the moment
-- at which a value becomes available on a time stream.
data Availability =
    Now
  | Tomorrow Availability
  deriving Eq

instance Ord Availability where
  compare Now Now = EQ
  compare Now (Tomorrow _) = LT
  compare (Tomorrow _) Now = GT
  compare (Tomorrow x) (Tomorrow y) = compare x y

-- | The 'Clock' type is the clock environment for a
-- guarded recursion system with a singleton clock.
data Clock = Open | Closed    

-- | The 'Extracted' type encapsualtes the result of trying to
-- extract an 'a' from something.
-- It is equivalent to 'Maybe'
data Extract a = Extracted a | Nope

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

-- | The 'Modality' type is a property of a guarded
-- recursive function. A such function is either 'Causal',
-- meaning that the clock of the input determines the
-- clock of the output, or 'NonCausaul', meaning that there
-- is no connection between the clocks in the in- and output.
data Modality = Causal | NonCausal deriving Show

------------------------------------------
----------------- NAMING -----------------
------------------------------------------

-- |Adds a rename to the guarded context.
addGuardedRename :: Name -> Name -> Idris ()
addGuardedRename n gn = do i <- getIState
                           case lookup n (guarded_renames i) of
                             Just _ -> tclift $ tfail (Elaborating "guarded recursion of " n (Msg $ "A guarded recursive name already exists for " ++ show n))
                             Nothing -> putIState (i { guarded_renames = (n, gn) : (guarded_renames i) })

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

-- |Creates a guarded version of a name.
guardedName :: Name -> Name
guardedName (UN t) = UN (guardedText t)
guardedName (NS n ns) = NS (guardedName n) ns --(placeInGuardedNS ns)
guardedName (MN i t) = MN i (guardedText t)
-- FIX ME: We need to figure out more about what special names are so we can figure out how to "guard" them.
-- Total hack!
guardedName (SN s) = sUN (show s)
guardedName n = n

-- |Creates and adds a rename to the guarded context.
guardedNameCtxt :: Name -> Idris Name
guardedNameCtxt n = do let gn = guardedName n
                       addGuardedRename n gn
                       return gn

-- |inNS ns n puts n in namespace ns
inNS :: [T.Text] -> Name -> Name
inNS ns (NS n ns')  = NS n   (ns ++ ns')
inNS ns name        = NS name ns

inNSs :: [String] -> Name -> Name
inNSs ss = inNS (map txt ss)

inNSo :: T.Text -> Name -> Name
inNSo n = inNS [n]

inNSos :: String -> Name -> Name
inNSos s = inNSo (txt s)                         

-- |Prefixes a namespace with the guarded recursion namespace.
placeInGuardedNS :: [T.Text] -> [T.Text]
placeInGuardedNS ns = ns ++ [(txt guardedRecursion)]

-- |Same as guardedNS but on strings.
placeInGuardedNSs :: [String] -> [String]
placeInGuardedNSs ss = map str (placeInGuardedNS (map txt ss))                       

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

-- |Same as guardedNS but on SyntaxInfo level.
withGuardedNS :: SyntaxInfo -> SyntaxInfo
withGuardedNS syn = syn { syn_namespace = placeInGuardedNSs (syn_namespace syn) }


-------------------------------------------------------
----------------- FUNCTION OPERATIONS -----------------
-------------------------------------------------------
  
modalityOf :: Name -> Idris Modality
modalityOf n = do i <- get
                  case lookupCtxt n (idris_flags i) of
                   [fnOpts] -> if CausalFn `elem` fnOpts then return Causal else return NonCausal
                   _ -> return NonCausal

-- | Builds an environment from a left hand side 
-- for checking right hand sides. Simply just finds
-- all P Bounds.                   
buildEnv :: Term -> Env
buildEnv term = nubBy (\(x,_) (y,_) -> x == y) (bounded term)
  where
    bounded :: Term -> Env
    bounded (P Bound n ty) = [(n, PVar ty)]
    bounded (Bind _ binder sc) =
      let l = bounded sc in
      let r = bb binder in
      l ++ r
      where
        -- Ignore kinds?
        bb :: Binder Term -> Env
        bb b' = bounded (binderTy b')
    bounded (App t t') = bounded t ++ bounded t'
    bounded (Proj t _) = bounded t
    bounded _ = []                   

-----------------------------------------
----------------- PTERM -----------------
-----------------------------------------
                   
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
                                  let syn = defaultSyntax
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
                   

--------------------------------------
----------------- TT -----------------
--------------------------------------

debindType :: Type -> Idris (Type, Type, Type)
debindType (unapplyLater -> Just ty) = debindType ty
debindType (unapplyForall -> Just ty) = debindType ty
debindType atob@(Bind n (Pi ty kind) sc) = return (ty, sc, atob)
debindType ty = ifail $ "Cannot debind non-function type: " ++ show ty


---- TYPE (UN)APPLICATIONS ----

applyForall :: Type -> Idris Type
applyForall ty =
  do forall <- forallRef
     return $ App forall ty
     
unapplyForall :: Type -> Maybe Type
unapplyForall ty = unapplyType forallName ty
     
applyLater :: Availability -> Type -> Idris Type
applyLater av ty =
  do later <- laterRef
     avTT <- availabilityTerm av
     return $ App (App later avTT) ty

unapplyLater :: Type -> Maybe Type
unapplyLater (unapplyLater' -> Just ty) = Just ty
unapplyLater (unapplyNLater -> Just ty) = Just ty
-- unapplyLater (Bind n (Pi (unapplyLater' -> Just piTy) kind) sc) =
--   do sc' <- unapplyLater sc
--      return $ (Bind n (Pi piTy kind) sc')
unapplyLater _ = Nothing

applyLater' :: Type -> Idris Type
applyLater' ty =
  do later' <- later'Ref
     return $ App later' ty

unapplyLater' :: Type -> Maybe Type
unapplyLater' ty = unapplyType later'Name ty

unapplyNLater :: Type -> Maybe Type
unapplyNLater (App (App later (unapplyTomorrow -> Just av)) ty)
 | isLater later = Just $ App (App later av) ty
unapplyNLater _ = Nothing
                      
unapplyType :: Name -> Type -> Maybe Type
unapplyType tyName (TConApp _ _ n _ x)
  | n == tyName = Just x
unapplyType _ _ = Nothing

unapplyLazy' :: Type -> Maybe Type
unapplyLazy' (Lazy' lazy' lazyType ty)
  | isLazy' lazy' && isLazyCodata lazyType = Just ty
unapplyLazy' _ = Nothing

normaliseLater :: Type -> Idris Type
normaliseLater (unapplyLater -> Just ty) =
  applyLater' =<< normaliseLater ty
normaliseLater (App (App later now) ty)
  | isLater later && isNow now = return ty
normaliseLater ty = return ty

---- TERM (UN)APPLICATIONS ----
                           
applyApply :: Term -> Type -> Idris Term
applyApply ty tm =
  do apply <- applyRef
     return $ App (App apply ty) tm

unapplyApply :: Term -> Maybe Term
unapplyApply (App (App apply _) tm)
  | isApply apply = Just tm
unapplyApply _ = Nothing

applyCompose :: Type -> Type -> Term -> Term -> Term -> Idris Term
applyCompose a b av f arg =
  do composeF <- composeRef
     return $ App (App (App (App (App composeF a) b) av) f) arg

applyCompose' :: Type -> Type -> Term -> Term -> Idris Term
applyCompose' a b f arg =
  do now <- nowRef
     applyCompose a b now f arg

unapplyCompose :: Term -> Maybe (Type, Type, Term, Term, Term)
unapplyCompose (Compose compose a b av f arg)
  | isCompose compose = Just (a, b, av, f, arg)
unapplyCompose _ = Nothing

unapplyDataConstructor :: Name -> Term -> Maybe Term
unapplyDataConstructor tmName (DConApp _ _ _ name _ x)
  | name == tmName = Just x
unapplyDataConstructor _ _ = Nothing

unapplyDelay :: Term -> Maybe Term
unapplyDelay (Delay delay lazyType _ tm)
  | isDelay delay && isLazyCodata lazyType = Just tm
unapplyDelay _ = Nothing

unapplyForce :: Term -> Maybe Term
unapplyForce (Force force lazyType _ tm)
  | isForce force && isLazyCodata lazyType = Just tm
unapplyForce _ = Nothing

applyLambdaKappa :: Type -> Term -> Idris Term
applyLambdaKappa ty tm =
  do lambdaKappa <- lambdaKappaRef
     return $ App (App lambdaKappa ty) tm

unapplyLambdaKappa :: Term -> Maybe Term
unapplyLambdaKappa (App (App lambdaKappa _) tm)
  | isLambdaKappa lambdaKappa = Just tm
unapplyLambdaKappa _ = Nothing

applyNext :: Type -> Term -> Idris Term
applyNext ty tm =
  do next <- nextRef
     return $ App (App next ty) tm

unapplyNext :: Term -> Maybe Term
unapplyNext (App (App next _) tm)
  | isNext next = Just tm
unapplyNext _ = Nothing

unapplyRef :: Name -> Term -> Maybe Term
unapplyRef tmName (App (P Ref name _) x)
  | name == tmName = Just x
unapplyRef _ _ = Nothing

unapplyTomorrow :: Term -> Maybe Term
unapplyTomorrow tm = unapplyDataConstructor tomorrowName tm

---- TERM/TYPE IDENTIFICATION ---

isApply :: Term -> Bool
isApply (P Ref (NS (UN apply) [gr]) _)
  | apply == txt applyStr && gr == txt guardedRecursion = True
isApply _ = False

isNow :: Term -> Bool
isNow (P (DCon _ _ _) (NS (UN now) [gr]) _)
  | now == txt nowStr && gr == txt guardedRecursion = True
isNow _ = False                                                         

isCompose :: Term -> Bool
isCompose (P Ref (NS (UN compose) [gr]) _)
  | compose == txt composeStr && gr == txt guardedRecursion = True
isCompose _ = False

isDelay :: Term -> Bool
isDelay (P _ (UN delay) _) | delay == txt delayStr = True
isDelay _ = False

isForall :: Type -> Bool
isForall (P (TCon _ _) (NS (UN forall) [gr]) _)
  | forall == txt forallStr && gr == txt guardedRecursion = True
isForall _ = False

isForce :: Term -> Bool
isForce (P _ (UN force) _) | force == txt forceStr = True
isForce _ = False

isLambdaKappa :: Term -> Bool
isLambdaKappa (P (DCon _ _ _) (NS (UN lambdaKappa) [gr]) _)
  | lambdaKappa == txt lambdaKappaStr && gr == txt guardedRecursion = True
isLambdaKappa _ = False

isLater :: Type -> Bool
isLater (P Ref (NS (UN later) [gr]) _)
  | later == txt laterStr && gr == txt guardedRecursion = True
isLater _ = False

isLater' :: Type -> Bool
isLater' (P (TCon _ _) ((NS (UN later) [gr])) _)
  | later == txt later'Str && gr == txt guardedRecursion = True
isLater' _ = False

isLazyCodata :: Term -> Bool
isLazyCodata (P _ (UN lazyCodata) _) | lazyCodata == txt lazyCodataStr = True
isLazyCodata _ = False

isLazy' :: Term -> Bool
isLazy' (P _ (UN lazy') _) | lazy' == txt lazy'Str = True
isLazy' _ = False

isNext :: Term -> Bool
isNext (P (DCon _ _ _) (NS (UN next) [gr]) _)
  | next == txt nextStr && gr == txt guardedRecursion = True
isNext _ = False                                                         

---- TYPECHECKING ----

-- | cEq env ty ty' checks if ty and ty' are
-- could be converted to each other.           
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

-- | checkGoal t ty env checks if t has type ty
checkGoal :: Term -> Type -> Env -> Idris Bool
checkGoal tm goal env =
  do tmType' <- typeOfMaybe tm env
     case tmType' of
      Just tmType ->
        do iLOG $ "Conversion checking " ++ show tmType ++ " and " ++ show goal
           cEq env tmType goal
      Nothing ->
        do iLOG $ "Conversion checking : no type"
           iLOG $ "Goal : " ++ show goal
           iLOG $ "env : " ++ intercalate ", " (map show env)
           _ <- typeOf tm env
           return False

-- | typeOf t env attempts to get the type of
-- t. If it could not be determined an error
-- is thrown.      
typeOf :: Term -> Env -> Idris Type
typeOf t env =
  do ctxt <- getContext
     case check ctxt env (forget t) of
      OK (_,t') -> normaliseLater (explicitNames t')
      Error e -> ierror e

-- | typeOf' t env ty gets the type of
-- t, if it fails, ty.
typeOf' :: Term -> Env -> Idris Type -> Idris Type
typeOf' t env err =
  do ty' <- typeOfMaybe t env
     case ty' of
      Just ty -> return ty
      Nothing -> err       

-- | typeOfMaybe t env gets the type of
-- t with an environment env. If the type
-- could not be determined, Nothing.
typeOfMaybe :: Term -> Env -> Idris (Maybe Type)
typeOfMaybe t env = idrisCatch (typeOf t env >>= \t' -> return $ Just t') (\_ -> return Nothing)

---- LATER ----

compareAvailability :: Type -> Type -> Ordering
compareAvailability (unapplyLater -> Just _) (unapplyLater -> Nothing) = LT
compareAvailability (unapplyLater -> Nothing) (unapplyLater -> Just _) = GT
compareAvailability (unapplyLater -> Nothing) (unapplyLater -> Nothing) = EQ
compareAvailability (unapplyLater -> Just a) (unapplyLater -> Just b) = compareAvailability a b

debindFirstArg :: Type -> Maybe Type
debindFirstArg (Bind _ (Pi t _) _) = Just t
debindFirstArg _ = Nothing

delayBy :: Type -> Type -> Idris Type
delayBy (unapplyLater -> Just ty) ty' =
  do delayed <- delayBy ty ty'
     applyLater' delayed
delayBy (unapplyLater -> Nothing) ty' =
  return ty'

-- | Distributes laters over the type,
-- e.g. Later (a -> b) becomes
-- Later a -> Later b                            
distributeLater :: Type -> Idris Type
distributeLater (unapplyLater -> Just b@(Bind _ (Pi _ _) _)) =
  do b' <- applyLaters b
     distributeLater b'
  where
    applyLaters :: Type -> Idris Type
    applyLaters (Bind n (Pi t kind) sc) =
      do laterPiTy <- applyLater' t
         laterSc <- applyLaters sc
         return $ Bind n (Pi laterPiTy kind) laterSc
    applyLaters ty = applyLater' ty
distributeLater ty = return ty     

nowType :: Type -> Type
nowType    (unapplyLater -> Just ty) = nowType ty
nowType ty@(unapplyLater -> Nothing) = ty

termAvailability :: Term -> Idris Availability
termAvailability (P Ref name _)
  | name == nowName = return Now
termAvailability (App (P Ref name _) arg)
  | name == tomorrowName = liftM Tomorrow (termAvailability arg)
termAvailability tm = ifail $ "Term " ++ show tm ++ " is not an Availability term."

availabilityTerm :: Availability -> Idris Term
availabilityTerm Now = nowRef
availabilityTerm (Tomorrow n) =
  liftM2 App tomorrowRef (availabilityTerm n)
  
-- |Checks if a type constructor is simply typed.
-- |Only binders and types are allowed.
guardableTC :: Type -> Bool
guardableTC (Bind _ b t) = guardableTC (binderTy b) && guardableTC t
guardableTC (TType _) = True
guardableTC _ = False

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

-- |Same as guardedTT, but ignoring names in the given list.
guardedTTIgnore :: [Name] -> Term -> Idris Term
guardedTTIgnore is t = do let fn = is \\ (freeNames t)
                          i <- getIState
                          let gns = mapMaybe (\y -> lookup y (guarded_renames i)) fn
                          ctxt <- getContext
                          let ps = concat $ map (\n -> lookupP n ctxt) gns
                          return $ substNames (zip gns ps) t          

removeLaziness :: Term -> Term
removeLaziness t = mapTT withoutLazyOps t
  where
    withoutLazyOps :: Term -> Term
    withoutLazyOps (unapplyDelay -> Just tm) = tm
    withoutLazyOps (unapplyForce -> Just tm) = tm
    withoutLazyOps (unapplyLazy' -> Just ty) = ty
    withoutLazyOps tm = tm    

to :: Type -> Type -> Env -> Idris Type
to a b env = do aK <- typeOfMaybe a env
                bK <- typeOfMaybe b env
                case (aK, bK) of
                  (Just(akind), Just(bkind)) -> do c <- cEq env akind bkind
                                                   if c
                                                     then return $ Bind (sUN "__pi_arg") (Pi a akind) b
                                                     else do iLOG $ "kind of " ++ show a ++ " and " ++ show b ++ " were not equal."
                                                             translateError Undefined
                  _ -> do iLOG $ "Couldn't get kind of " ++ show a
                          translateError Undefined

----------------------------------------
----------------- MISC -----------------
----------------------------------------

---- GENERAL FUNCTIONS ----
    
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
    

---- PRETTY PRINT ----

-- | Shows a TT Name similar to the abstract syntax.
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

---- PATTERN SYNONYMS ----

pattern Compose compose a b av f arg = App (App (App (App (App compose a) b) av) f) arg

pattern TConApp tag arity name pty x =
  App (P (TCon tag arity) name pty) x
pattern DConApp tag arity unique name pty x =
  App (P (DCon tag arity unique) name pty) x

pattern Lazy' lazy' lazyType ty = App (App lazy' lazyType) ty

pattern Delay delay lazyType delayType t = App (App (App delay lazyType) delayType) t

pattern Force force lazyType forceType tm = App (App (App force lazyType) forceType) tm

---- CLOCKS ----

-- | Chcecks if the input is a clocked type
clockedType :: Type -> Idris Bool
clockedType (Bind _ _ sc) = clockedType sc
clockedType (unApply -> (P _ n _, _)) =
  do i <- get
     return $ n `elem` (map snd (guarded_renames i))
clockedType _ = return False     

isOpen :: Clock -> Bool
isOpen Open = True
isOpen _ = False

---- TOTALITY ----

-- | Merges two totalities. If one is
-- not total it is chosen.
mergeTotal :: Totality -> Totality -> Totality
mergeTotal (Total _) t = t
mergeTotal t (Total _) = t
mergeTotal t _ = t


----------------------------------------------
------- Recursive references -----------------
----------------------------------------------


fixRecursiveRef :: Modality -> Env -> [Term] -> Name -> Term -> Idris Term
fixRecursiveRef modality lhsEnv params recName t = fixRecRef modality t
  where
    fixRecRef :: Modality -> Term -> Idris Term
    fixRecRef Causal (unapplyRecRef recName -> Just (p@(P Ref n (unapplyForall -> Just recTy)), args)) =
      do appliedRec <- applyApply recTy p
         iLOG $ "appliedRec : " ++ show appliedRec
         let withParams = mkApp appliedRec params
         iLOG $ "withParams : " ++ show withParams
         iLOG $ "params : " ++ show params
         iLOG $ "args : " ++ show args
         nextTy' <- typeOfMaybe withParams lhsEnv
         nextTy <- case nextTy' of
                    Just ty -> return ty
                    Nothing -> ifail "Applying parameters on causal recursive reference makes it ill-typed."
         recRef <- applyNext nextTy withParams
         return $ mkApp recRef (drop (length params) args)
    fixRecRef NonCausal (unapplyRecRef recName -> Just (p@(P Ref n recTy), args)) =
      do let withParams = mkApp p params
         nextTy' <- typeOfMaybe withParams lhsEnv
         nextTy <- case nextTy' of
                    Just ty -> return ty
                    Nothing -> ifail "Applying parameters on causal recursive reference makes it ill-typed."         
         recRef <- applyNext nextTy withParams
         return $ mkApp recRef (drop (length params) args)
    fixRecRef modality p@(P nt n ty) = return p
    fixRecRef modality (Bind n binder ty) =
      -- Recursive ref is never in type, so no recursion there
      liftM (\b -> Bind n b ty) (Tr.forM binder (fixRecRef modality))
    fixRecRef modality (App f x) =
      liftM2 App (fixRecRef modality f) (fixRecRef modality x)
    fixRecRef modality (Proj tm i) =
      liftM (\t -> Proj t i) (fixRecRef modality tm)
    fixRecRef _ tm = return tm
    

-- fixRecursiveRef modality lhsEnv params recName t = flip mapMTT t $ fixRecRef modality
--   where
--     fixRecRef :: Modality -> Term -> Idris Term
--     fixRecRef Causal (unapplyRecRef recName -> Just (p@(P Ref n (unapplyForall -> Just recTy)), args)) =
--       do     
-- --    fixRecRef Causal p@(P Ref n recTy) | n == recName =
--          -- appliedRecTy <- case unapplyForall recTy of
--          --                  Just ty -> return ty
--          --                  Nothing -> ifail "Recursive reference of causal function does not have Forall type"
--          appliedRec <- applyApply recTy p
--          iLOG $ "appliedRec : " ++ show appliedRec
--          let withParams = mkApp appliedRec params
--          iLOG $ "withParams : " ++ show withParams
--          let withArgs = mkApp withParams (drop (length params) args)
--          iLOG $ "params : " ++ show params
--          iLOG $ "args : " ++ show args
--          iLOG $ "withArgs : " ++ show withArgs
--          nextTy' <- typeOfMaybe withArgs lhsEnv
--          nextTy <- case nextTy' of
--                     Just ty -> return ty
--                     Nothing -> ifail "Applying parameters on causal recursive reference makes it ill-typed."
--          applyNext nextTy withArgs
--     fixRecRef NonCausal (unapplyRecRef recName -> Just (p@(P Ref n recTy), args)) =
--       do let withParams = mkApp p params
--          let withArgs = mkApp withParams (drop (length params) args)
--          nextTy' <- typeOfMaybe withArgs lhsEnv
--          nextTy <- case nextTy' of
--                     Just ty -> return ty
--                     Nothing -> ifail "Applying parameters on causal recursive reference makes it ill-typed."         
--          applyNext nextTy withArgs
--     fixRecRef _ tm = return tm

unapplyRecRef :: Name -> Term -> Maybe (Term, [Term])
unapplyRecRef recName (unApply -> unapp@((P Ref n _), _)) | n == recName = Just unapp
unapplyRecRef _ _ = Nothing

-- parameters :: Name -> Context -> [(Int, Name)]
-- parameters n ctxt
--   | isDConName n ctxt,
--     Just ty <- lookupTyExact n ctxt = findParameterIndices ty 0 [] []
--   | isFnName n ctxt = []
--   | otherwise = []
--   where
--     findParameterIndices :: Type -> Int -> [(Int, Name)] -> [(Int, Name)]-> [(Int, Name)]
--     findParameterIndices (Bind n (Pi piTy kind) sc) i constrArgs params =
--       findParameterIndices sc (i+1) ((i, n):constrArgs) params
--     findParameterIndices (App t (P Bound pn _)) i constrArgs params
--       | Just (i',pn') <- find (\(_,m) -> m == pn) constrArgs =
--           findParameterIndices t i constrArgs ((i',pn'):params)
--     findParameterIndices (App t _) i constrArgs params = findParameterIndices t i constrArgs params
--     findParameterIndices (P (TCon _ _) n' _) i constrArgs params = params
--     findParameterIndices _ _ _ params = params

-- parameters :: Type -> [(Int, Name)]
-- parameters ty = (reverse . (nubBy (\(i,_) (j,_) -> i == j))) $ params ty False 0 []
--   where
--     params :: Type -> Bool -> Int -> [(Int,Name)] -> [(Int,Name)]
--     params (Bind n (
--     params (App f x) False i ps = let fParams = params f True i ps
--                                       xParams = params x True i ps
--                                   in fParams ++ xParams
--     params False i ps (App t t') = params True ps (App t t')
--     params True i ps (P Bound n ty) = 

-- pa

-- foldTT :: (TT n -> b -> b) -> b -> TT n -> b
-- foldTT f z (P nt n ty) = f (P nt n ty) (foldTT f z ty)
-- foldTT f z (Bind n binder sc) = f (Bind n binder sc) (F.foldr' f (foldTT f z sc) binder)
-- foldTT f z (App t t') = foldTT f (foldTT f z t') t
-- foldTT f z (Proj tm i) = f (Proj tm i) (foldTT f z tm)
-- foldTT f z tm = f tm z

foldTT :: (TT n -> b -> b) -> b -> TT n -> b
foldTT f z (P nt n ty) = f (P nt n ty) (foldTT f z ty)
foldTT f z (Bind n binder sc) = f (Bind n binder sc) (F.foldr' f (foldTT f z sc) binder)
foldTT f z (App t t') = f (App t t') (foldTT f (foldTT f z t') t)
foldTT f z (Proj tm i) = f (Proj tm i) (foldTT f z tm)
foldTT f z tm = f tm z

boundVars :: TT n -> [(TT n, Int)]
boundVars tm = boundVars' tm 0 [] -- foldTT boundVars' [] tm
  where
    boundVars' :: TT n -> Int -> [(TT n, Int)] -> [(TT n, Int)]
    boundVars' p@(P Bound _ _) i vars = (p,i) : vars
    boundVars' (P nt _ ty) i vars | nt /= Bound = boundVars' ty i vars
    boundVars' (Bind n binder sc) i vars =
      (F.foldr' (\t acc -> boundVars' t i acc) (boundVars' sc (i+1) vars) binder)
    boundVars' (App t t') i vars = boundVars' t i (boundVars' t' i vars)
    boundVars' (Proj tm _) i vars = boundVars' tm i vars
    boundVars' _ _ vars = vars

parameters :: Type -> [(Int, Name)]
parameters ty = let pBounds = boundVars ty
                    argNames = map fst $ getArgTys ty
                    pNames = mapMaybe boundName pBounds
                    paramIndices = mapMaybe (\(pn, i) -> lastIndexOf pn (take i argNames)) pNames --findIndices (\n -> n `elem` pNames)argNames
                    params = filter (\(i, _) -> i `elem` paramIndices) (zip [0..] argNames)
                in  nubBy (\(i,_) (j,_) -> i == j) params
  where
    boundName :: (Term, Int) -> Maybe (Name, Int)
    boundName ((P Bound n _), i) = Just (n, i)
    boundName _ = Nothing

    lastIndexOf :: Eq a => a -> [a] -> Maybe Int
    lastIndexOf a xs = lastIndexOf' a xs 0 Nothing
      where
        lastIndexOf' :: Eq a => a -> [a] -> Int -> Maybe Int -> Maybe Int
        lastIndexOf' a (x:xs) p i = if a == x
                                    then lastIndexOf' a xs (p+1) (Just p)
                                    else lastIndexOf' a xs (p+1) i
        lastIndexOf' a [] _ i = i

parameterArgs :: Term -> Type -> [Term]
parameterArgs lhs ty = let paramIndices = map fst $ parameters ty
                           lhsArgs = snd $ unApply lhs
                       in  map (lhsArgs !!) paramIndices


----------------------------------------------
----------------- NOT IN USE -----------------
----------------------------------------------
{-
collectLater :: Type -> Idris Type
collectLater b@(Bind _ (Pi (unapplyLater -> Just ty) _) sc) =
  do sc' <- idrisCatch (collectLater' sc) (\_ -> return b)
     applyLater' =<< collectLater sc'
  where
    collectLater' :: Type -> Idris Type
    collectLater' (Bind n (Pi (unapplyLater -> Just ty) kind) sc) =
      do sc' <- collectLater' sc
         return $ Bind n (Pi ty kind) sc
    collectLater' (unapplyLater -> Just ty) = return ty
    collectLater' (unapplyLater -> Nothing) = ifail "Unable to collect later from argument."
collectLater ty = return ty

availability :: Type -> Idris Availability
availability ty = liftM snd (unapplyLater ty)

delayBy :: Availability -> Availability -> Availability
delayBy Now a = a
delayBy (Tomorrow a) b = delayBy a (Tomorrow b)

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

parameters :: Name -> Context -> [(Int, Name)]
parameters n ctxt
  | isDConName n ctxt,
    Just ty <- lookupTyExact n ctxt = findParameterIndices ty 0 [] []
  | isFnName n ctxt = []
  | otherwise = []
  where
    findParameterIndices :: Type -> Int -> [(Int, Name)] -> [(Int, Name)]-> [(Int, Name)]
    findParameterIndices (Bind n (Pi piTy kind) sc) i constrArgs params =
      findParameterIndices sc (i+1) ((i, n):constrArgs) params
    findParameterIndices (App t (P Bound pn _)) i constrArgs params
      | Just (i',pn') <- find (\(_,m) -> m == pn) constrArgs =
          findParameterIndices t i constrArgs ((i',pn'):params)
    findParameterIndices (App t _) i constrArgs params = findParameterIndices t i constrArgs params
    findParameterIndices (P (TCon _ _) n' _) i constrArgs params = params
    findParameterIndices _ _ _ params = params

guardedTerm :: Term -> Idris Term
guardedTerm p@(P Bound _ _)       = return p
guardedTerm (P Ref n _)           = guardedRef n
guardedTerm (P (DCon _ _ _) n _)  = guardedDataConstructor n
guardedTerm p@(P (TCon _ _) _ _)  = return p
guardedTerm (Bind _ _ sc)         = guardedTerm sc
guardedTerm (App f x)             = liftM2 App (guardedTerm f) (guardedTerm x)
guardedTerm tm                    = return tm

guardedRef :: Name -> Idris Term
guardedRef = undefined

guardedDataConstructor :: Name -> Idris Term
guardedDataConstructor = undefined
-}
