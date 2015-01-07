{-# LANGUAGE PatternGuards #-}
module Idris.Delaborate (bugaddr, delab, delab', delabMV, delabTy, delabTy', fancifyAnnots, pprintDelab, pprintDelabTy, pprintErr) where

-- Convert core TT back into high level syntax, primarily for display
-- purposes.

import Util.Pretty

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Docstrings (overview, renderDocstring, renderDocTerm)
import Idris.ErrReverse

import Data.List (intersperse, nub)
import qualified Data.Text as T
import Control.Monad.State

import Debug.Trace

bugaddr = "https://github.com/idris-lang/Idris-dev/issues"

delab :: IState -> Term -> PTerm
delab i tm = delab' i tm False False

delabMV :: IState -> Term -> PTerm
delabMV i tm = delab' i tm False True

delabTy :: IState -> Name -> PTerm
delabTy i n
    = case lookupTy n (tt_ctxt i) of
           (ty:_) -> case lookupCtxt n (idris_implicits i) of
                         (imps:_) -> delabTy' i imps ty False False
                         _ -> delabTy' i [] ty False False

delab' :: IState -> Term -> Bool -> Bool -> PTerm
delab' i t f mvs = delabTy' i [] t f mvs

delabTy' :: IState -> [PArg] -- ^ implicit arguments to type, if any
          -> Term
          -> Bool -- ^ use full names
          -> Bool -- ^ Don't treat metavariables specially
          -> PTerm
delabTy' ist imps tm fullname mvs = de [] imps tm
  where
    un = fileFC "(val)"

    de env _ (App f a) = deFn env f [a]
    de env _ (V i)     | i < length env = PRef un (snd (env!!i))
                       | otherwise = PRef un (sUN ("v" ++ show i ++ ""))
    de env _ (P _ n _) | n == unitTy = PTrue un IsType
                       | n == unitCon = PTrue un IsTerm
                       | Just n' <- lookup n env = PRef un n'
                       | otherwise
                            = case lookup n (idris_metavars ist) of
                                  Just (Just _, mi, _) -> mkMVApp n []
                                  _ -> PRef un n
    de env _ (Bind n (Lam ty) sc)
          = PLam un n (de env [] ty) (de ((n,n):env) [] sc)
    de env ((PImp { argopts = opts }):is) (Bind n (Pi ty _) sc)
          = PPi (Imp opts Dynamic False) n (de env [] ty) (de ((n,n):env) is sc)
    de env (PConstraint _ _ _ _:is) (Bind n (Pi ty _) sc)
          = PPi constraint n (de env [] ty) (de ((n,n):env) is sc)
    de env (PTacImplicit _ _ _ tac _:is) (Bind n (Pi ty _) sc)
          = PPi (tacimpl tac) n (de env [] ty) (de ((n,n):env) is sc)
    de env (plic:is) (Bind n (Pi ty _) sc)
          = PPi (Exp (argopts plic) Dynamic False)
                n
                (de env [] ty)
                (de ((n,n):env) is sc)
    de env [] (Bind n (Pi ty _) sc)
          = PPi expl n (de env [] ty) (de ((n,n):env) [] sc)

    de env imps (Bind n (Let ty val) sc)
          | isCaseApp sc
          , (P _ cOp _, args) <- unApply sc
          , Just caseblock    <- delabCase env imps n val cOp args = caseblock
          | otherwise    =
              PLet un n (de env [] ty) (de env [] val) (de ((n,n):env) [] sc)
    de env _ (Bind n (Hole ty) sc) = de ((n, sUN "[__]"):env) [] sc
    de env _ (Bind n (Guess ty val) sc) = de ((n, sUN "[__]"):env) [] sc
    de env plic (Bind n bb sc) = de ((n,n):env) [] sc
    de env _ (Constant i) = PConstant i
    de env _ Erased = Placeholder
    de env _ Impossible = Placeholder
    de env _ (TType i) = PType
    de env _ (UType u) = PUniverse u

    dens x | fullname = x
    dens ns@(NS n _) = case lookupCtxt n (idris_implicits ist) of
                              [_] -> n -- just one thing
                              [] -> n -- metavariables have no implicits
                              _ -> ns
    dens n = n

    deFn env (App f a) args = deFn env f (a:args)
    deFn env (P _ n _) [l,r]
         | n == pairTy    = PPair un IsType (de env [] l) (de env [] r)
         | n == eqCon     = PRefl un (de env [] r)
         | n == sUN "lazy" = de env [] r
    deFn env (P _ n _) [ty, Bind x (Lam _) r]
         | n == sUN "Sigma"
               = PDPair un IsType (PRef un x) (de env [] ty)
                           (de ((x,x):env) [] (instantiate (P Bound x ty) r))
    deFn env (P _ n _) [lt,rt,l,r]
         | n == pairCon = PPair un IsTerm (de env [] l) (de env [] r)
         | n == eqTy    = PEq un (de env [] lt) (de env [] rt)
                                 (de env [] l) (de env [] r)
         | n == sUN "Sg_intro" = PDPair un IsTerm (de env [] l) Placeholder
                                           (de env [] r)
    deFn env f@(P _ n _) args
         | n `elem` map snd env
              = PApp un (de env [] f) (map pexp (map (de env []) args))
    deFn env (P _ n _) args
         | not mvs = case lookup n (idris_metavars ist) of
                        Just (Just _, mi, _) ->
                            mkMVApp n (drop mi (map (de env []) args))
                        _ -> mkPApp n (map (de env []) args)
         | otherwise = mkPApp n (map (de env []) args)
    deFn env f args = PApp un (de env [] f) (map pexp (map (de env []) args))

    mkMVApp n []
            = PMetavar n
    mkMVApp n args
            = PApp un (PMetavar n) (map pexp args)
    mkPApp n args
        | Just imps <- lookupCtxtExact n (idris_implicits ist)
            = PApp un (PRef un n) (zipWith imp (imps ++ repeat (pexp undefined)) args)
        | otherwise = PApp un (PRef un n) (map pexp args)

    imp (PImp p m l n _) arg = PImp p m l n arg
    imp (PExp p l n _)   arg = PExp p l n arg
    imp (PConstraint p l n _) arg = PConstraint p l n arg
    imp (PTacImplicit p l n sc _) arg = PTacImplicit p l n sc arg

    isCaseApp tm | P _ n _ <- fst (unApply tm) = isCN n
                 | otherwise = False
      where isCN (NS n _) = isCN n
            isCN (SN (CaseN _)) = True
            isCN _ = False

    delabCase :: [(Name, Name)] -> [PArg] -> Name -> Term -> Name -> [Term] -> Maybe PTerm
    delabCase env imps scvar scrutinee caseName caseArgs =
      do cases <- case lookupCtxt caseName (idris_patdefs ist) of
                    [(cases, _)] -> return cases
                    _ -> Nothing
         return $ PCase un (de env imps scrutinee)
                    [ (de (env ++ map (\n -> (n, n)) vars) imps (splitArg lhs),
                       de (env ++ map (\n -> (n, n)) vars) imps rhs)
                    | (vars, lhs, rhs) <- cases
                    ]
      where splitArg tm | (_, args) <- unApply tm = nonVar (reverse args)
                        | otherwise = tm
            nonVar [] = error "Tried to delaborate empty case list"
            nonVar [x] = x
            nonVar (x@(App _ _) : _) = x
            nonVar (x@(P (DCon _ _ _) _ _) : _) = x
            nonVar (x:xs) = nonVar xs
-- | How far to indent sub-errors
errorIndent :: Int
errorIndent = 8

-- | Actually indent a sub-error - no line at end because a newline can end
-- multiple layers of indent
indented :: Doc a -> Doc a
indented = nest errorIndent . (line <>)

-- | Pretty-print a core term using delaboration
pprintDelab :: IState -> Term -> Doc OutputAnnotation
pprintDelab ist tm = annotate (AnnTerm [] tm)
                              (prettyIst ist (delab ist tm))

-- | Pretty-print the type of some name
pprintDelabTy :: IState -> Name -> Doc OutputAnnotation
pprintDelabTy i n
    = case lookupTy n (tt_ctxt i) of
           (ty:_) -> annotate (AnnTerm [] ty) . prettyIst i $
                     case lookupCtxt n (idris_implicits i) of
                         (imps:_) -> delabTy' i imps ty False False
                         _ -> delabTy' i [] ty False False

pprintTerm :: IState -> PTerm -> Doc OutputAnnotation
pprintTerm ist = pprintTerm' ist []

pprintTerm' :: IState -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
pprintTerm' ist bnd tm = pprintPTerm (ppOptionIst ist) bnd [] (idris_infixes ist) tm

pprintErr :: IState -> Err -> Doc OutputAnnotation
pprintErr i err = pprintErr' i (fmap (errReverse i) err)

pprintErr' i (Msg s) = text s
pprintErr' i (InternalMsg s) =
  vsep [ text "INTERNAL ERROR:" <+> text s,
         text "This is probably a bug, or a missing error message.",
         text ("Please consider reporting at " ++ bugaddr)
       ]
pprintErr' i (CantUnify _ x_in y_in e sc s) =
  let (x_ns, y_ns, nms) = renameMNs x_in y_in
      (x, y) = addImplicitDiffs (delab i x_ns) (delab i y_ns) in
    text "Can't unify" <> indented (annTm x_ns
                      (pprintTerm' i (map (\ (n, b) -> (n, False)) sc
                                        ++ zip nms (repeat False)) x)) <$>
    text "with" <> indented (annTm y_ns
                      (pprintTerm' i (map (\ (n, b) -> (n, False)) sc
                                        ++ zip nms (repeat False)) y)) <>
    case e of
      Msg "" -> empty
        -- if the specific error is the same as the one we just printed,
        -- there's no need to print it
      CantUnify _ x_in' y_in' _ _ _ | x_in == x_in' && y_in == y_in' -> empty
      _ -> line <> line <> text "Specifically:" <>
           indented (pprintErr' i e) <>
           if (opt_errContext (idris_options i)) then showSc i sc else empty
pprintErr' i (CantConvert x_in y_in env) =
 let (x_ns, y_ns, nms) = renameMNs x_in y_in
     (x, y) = addImplicitDiffs (delab i (flagUnique x_ns)) 
                               (delab i (flagUnique y_ns)) in
  text "Can't convert" <>
  indented (annTm x_ns (pprintTerm' i (map (\ (n, b) -> (n, False)) env)
               x)) <$>
  text "with" <>
  indented (annTm y_ns (pprintTerm' i (map (\ (n, b) -> (n, False)) env)
               y)) <>
  if (opt_errContext (idris_options i)) then line <> showSc i env else empty
    where flagUnique (Bind n (Pi t k@(UType u)) sc)
              = App (P Ref (sUN (show u)) Erased)
                    (Bind n (Pi (flagUnique t) k) (flagUnique sc))
          flagUnique (App f a) = App (flagUnique f) (flagUnique a)
          flagUnique (Bind n b sc) = Bind n (fmap flagUnique b) (flagUnique sc)
          flagUnique t = t
pprintErr' i (CantSolveGoal x env) =
  text "Can't solve goal " <>
  indented (annTm x (pprintTerm' i (map (\ (n, b) -> (n, False)) env) (delab i x))) <>
  if (opt_errContext (idris_options i)) then line <> showSc i env else empty
pprintErr' i (UnifyScope n out tm env) =
  text "Can't unify" <> indented (annName n) <+>
  text "with" <> indented (annTm tm (pprintTerm' i (map (\ (n, b) -> (n, False)) env) (delab i tm))) <+>
 text "as" <> indented (annName out) <> text "is not in scope" <>
  if (opt_errContext (idris_options i)) then line <> showSc i env else empty
pprintErr' i (CantInferType t) = text "Can't infer type for" <+> text t
pprintErr' i (NonFunctionType f ty) =
  annTm f (pprintTerm i (delab i f)) <+>
  text "does not have a function type" <+>
  parens (pprintTerm i (delab i ty))
pprintErr' i (NotEquality tm ty) =
  annTm tm (pprintTerm i (delab i tm)) <+>
  text "does not have an equality type" <+>
  annTm ty (parens (pprintTerm i (delab i ty)))
pprintErr' i (TooManyArguments f) = text "Too many arguments for" <+> annName f
pprintErr' i (CantIntroduce ty) =
  text "Can't use lambda here: type is" <+> annTm ty (pprintTerm i (delab i ty))
pprintErr' i (InfiniteUnify x tm env) =
  text "Unifying" <+> annName' x (showbasic x) <+> text "and" <+>
  annTm tm (pprintTerm' i (map (\ (n, b) -> (n, False)) env) (delab i tm)) <+>
  text "would lead to infinite value" <>
  if (opt_errContext (idris_options i)) then line <> showSc i env else empty
pprintErr' i (NotInjective p x y) =
  text "Can't verify injectivity of" <+> annTm p (pprintTerm i (delab i p)) <+>
  text " when unifying" <+> annTm x (pprintTerm i (delab i x)) <+> text "and" <+>
  annTm y (pprintTerm i (delab i y))
pprintErr' i (CantResolve c) = text "Can't resolve type class" <+> pprintTerm i (delab i c)
pprintErr' i (CantResolveAlts as) = text "Can't disambiguate name:" <+>
                                    align (cat (punctuate (comma <> space) (map (fmap (fancifyAnnots i) . annName) as)))
pprintErr' i (NoTypeDecl n) = text "No type declaration for" <+> annName n
pprintErr' i (NoSuchVariable n) = text "No such variable" <+> annName n
pprintErr' i (WithFnType ty) =
  text "Can't match on a function: type is" <+> annTm ty (pprintTerm i (delab i ty))
pprintErr' i (CantMatch t) =
  text "Can't match on" <+> annTm t (pprintTerm i (delab i t))
pprintErr' i (IncompleteTerm t) = text "Incomplete term" <+> annTm t (pprintTerm i (delab i t))
pprintErr' i UniverseError = text "Universe inconsistency"
pprintErr' i (UniqueError NullType n)
           = text "Borrowed name" <+> annName' n (showbasic n)
                  <+> text "must not be used on RHS"
pprintErr' i (UniqueError _ n) = text "Unique name" <+> annName' n (showbasic n)
                                  <+> text "is used more than once"
pprintErr' i (UniqueKindError k n) = text "Constructor" <+> annName' n (showbasic n)
                                   <+> text ("has a " ++ show k ++ ",")
                                   <+> text "but the data type does not"
pprintErr' i ProgramLineComment = text "Program line next to comment"
pprintErr' i (Inaccessible n) = annName n <+> text "is not an accessible pattern variable"
pprintErr' i (NonCollapsiblePostulate n) = text "The return type of postulate" <+>
                                           annName n <+> text "is not collapsible"
pprintErr' i (AlreadyDefined n) = annName n<+>
                                  text "is already defined"
pprintErr' i (ProofSearchFail e) = pprintErr' i e
pprintErr' i (NoRewriting tm) = text "rewrite did not change type" <+> annTm tm (pprintTerm i (delab i tm))
pprintErr' i (At f e) = annotate (AnnFC f) (text (show f)) <> colon <> pprintErr' i e
pprintErr' i (Elaborating s n e) = text "When elaborating" <+> text s <>
                                   annName' n (showqual i n) <> colon <$>
                                   pprintErr' i e
pprintErr' i (ElaboratingArg f x _ e)
  | isInternal f = pprintErr' i e
  | isUN x =
     text "When elaborating argument" <+>
     annotate (AnnBoundName x False) (text (showbasic x)) <+> -- TODO check plicity
     -- Issue #1591 on the issue tracker: https://github.com/idris-lang/Idris-dev/issues/1591
     text "to" <+> whatIsName <> annName f <> colon <>
     indented (pprintErr' i e)
  | otherwise =
     text "When elaborating an application of" <+> whatIsName <>
     annName f <> colon <> indented (pprintErr' i e)
  where whatIsName = let ctxt = tt_ctxt i
                     in if isTConName f ctxt
                           then text "type constructor" <> space
                           else if isConName f ctxt
                                   then text "constructor" <> space
                                   else if isFnName f ctxt
                                           then text "function" <> space
                                           else empty
        isInternal (MN _ _) = True
        isInternal (UN n) = T.isPrefixOf (T.pack "__") n
        isInternal (NS n _) = isInternal n
        isInternal _ = True

pprintErr' i (ProviderError msg) = text ("Type provider error: " ++ msg)
pprintErr' i (LoadingFailed fn e) = text "Loading" <+> text fn <+> text "failed:" <+>  pprintErr' i e
pprintErr' i (ReflectionError parts orig) =
  let parts' = map (fillSep . map showPart) parts in
  align (fillSep parts') <>
  if (opt_origerr (idris_options i))
    then line <> line <> text "Original error:" <$> indented (pprintErr' i orig)
    else empty
  where showPart :: ErrorReportPart -> Doc OutputAnnotation
        showPart (TextPart str) = fillSep . map text . words $ str
        showPart (NamePart n)   = annName n
        showPart (TermPart tm)  = pprintTerm i (delab i tm)
        showPart (SubReport rs) = indented . hsep . map showPart $ rs
pprintErr' i (ReflectionFailed msg err) =
  text "When attempting to perform error reflection, the following internal error occurred:" <>
  indented (pprintErr' i err) <>
  text ("This is probably a bug. Please consider reporting it at " ++ bugaddr)

-- Make sure the machine invented names are shown helpfully to the user, so
-- that any names which differ internally also differ visibly

renameMNs :: Term -> Term -> (Term, Term, [Name])
renameMNs x y = let ns = nub $ allTTNames x ++ allTTNames y
                    newnames = evalState (getRenames [] ns) 1 in
                      (rename newnames x, rename newnames y, map snd newnames)
  where
    getRenames :: [(Name, Name)] -> [Name] -> State Int [(Name, Name)]
    getRenames acc [] = return acc
    getRenames acc (n@(MN i x) : xs) | rpt x xs 
         = do idx <- get
              put (idx + 1)
              let x' = sUN (str x ++ show idx)
              getRenames ((n, x') : acc) xs
    getRenames acc (n@(UN x) : xs) | rpt x xs 
         = do idx <- get
              put (idx + 1)
              let x' = sUN (str x ++ show idx)
              getRenames ((n, x') : acc) xs
    getRenames acc (x : xs) = getRenames acc xs

    rpt x [] = False
    rpt x (UN y : xs) | x == y = True
    rpt x (MN i y : xs) | x == y = True
    rpt x (_ : xs) = rpt x xs

    rename :: [(Name, Name)] -> Term -> Term
    rename ns (P nt x t) | Just x' <- lookup x ns = P nt x' t
    rename ns (App f a) = App (rename ns f) (rename ns a)
    rename ns (Bind x b sc)
           = let b' = fmap (rename ns) b
                 sc' = rename ns sc in
                 case lookup x ns of
                      Just x' -> Bind x' b' sc'
                      Nothing -> Bind x b' sc'
    rename ns x = x

-- If the two terms only differ in their implicits, mark the implicits which
-- differ as AlwaysShow so that they appear in errors
addImplicitDiffs :: PTerm -> PTerm -> (PTerm, PTerm)
addImplicitDiffs x y
    = if (x `expLike` y) then addI x y else (x, y)
  where
    addI :: PTerm -> PTerm -> (PTerm, PTerm)
    addI (PApp fc f as) (PApp gc g bs)
         = let (as', bs') = addShows as bs in
               (PApp fc f as', PApp gc g bs')
       where addShows [] [] = ([], [])
             addShows (a:as) (b:bs)
                = let (as', bs') = addShows as bs
                      (a', b') = addI (getTm a) (getTm b) in
                      if (not (a' `expLike` b'))
                         then (a { argopts = AlwaysShow : argopts a,
                                   getTm = a' } : as',
                               b { argopts = AlwaysShow : argopts b,
                                   getTm = b' } : bs')
                         else (a { getTm = a' } : as',
                               b { getTm = b' } : bs')
             addShows xs ys = (xs, ys)
    addI (PLam fc n a b) (PLam fc' n' c d)
         = let (a', c') = addI a c
               (b', d') = addI b d in
               (PLam fc n a' b', PLam fc' n' c' d')
    addI (PPi p n a b) (PPi p' n' c d)
         = let (a', c') = addI a c
               (b', d') = addI b d in
               (PPi p n a' b', PPi p' n' c' d')
    addI (PRefl fc a) (PRefl fc' b)
         = let (a', b') = addI a b in
               (PRefl fc a', PRefl fc' b')
    addI (PEq fc at bt a b) (PEq fc' ct dt c d)
         | trace (show (at,bt)) False = undefined
         | at `expLike` ct && bt `expLike` dt
         = let (a', c') = addI a c
               (b', d') = addI b d in
               (PEq fc at bt a' b', PEq fc' ct dt c' d')
         | otherwise
         = let (at', ct') = addI at ct
               (bt', dt') = addI bt dt
               (a', c') = addI a c
               (b', d') = addI b d
               showa = if at `expLike` ct then [] else [AlwaysShow]
               showb = if bt `expLike` dt then [] else [AlwaysShow] in
               (PApp fc (PRef fc eqTy) [(pimp (sUN "A") at' True)
                                               { argopts = showa },
                                        (pimp (sUN "B") bt' True)
                                               { argopts = showb },
                                        pexp a', pexp b'],
                PApp fc (PRef fc eqTy) [(pimp (sUN "A") ct' True)
                                               { argopts = showa },
                                        (pimp (sUN "B") dt' True)
                                               { argopts = showb },
                                        pexp c', pexp d'])

    addI (PPair fc pi a b) (PPair fc' pi' c d)
         = let (a', c') = addI a c
               (b', d') = addI b d in
               (PPair fc pi a' b', PPair fc' pi' c' d')
    addI (PDPair fc pi a t b) (PDPair fc' pi' c u d)
         = let (a', c') = addI a c
               (t', u') = addI t u
               (b', d') = addI b d in
               (PDPair fc pi a' t' b', PDPair fc' pi' c' u' d')
    addI x y = (x, y)

    -- Just the ones which appear desugared in errors
    expLike (PRef _ n) (PRef _ n') = n == n'
    expLike (PApp _ f as) (PApp _ f' as')
        = expLike f f' && length as == length as' &&
          and (zipWith expLike (getExps as) (getExps as'))
    expLike (PPi _ n s t) (PPi _ n' s' t')
        = n == n' && expLike s s' && expLike t t'
    expLike (PLam _ n s t) (PLam _ n' s' t')
        = n == n' && expLike s s' && expLike t t'
    expLike (PPair _ _ x y) (PPair _ _ x' y') = expLike x x' && expLike y y'
    expLike (PDPair _ _ x _ y) (PDPair _ _ x' _ y') = expLike x x' && expLike y y'
    expLike (PEq _ xt yt x y) (PEq _ xt' yt' x' y')
         = expLike x x' && expLike y y'
    expLike (PRefl _ x) (PRefl _ x') = expLike x x'
    expLike x y = x == y

-- Issue #1589 on the issue tracker
--     https://github.com/idris-lang/Idris-dev/issues/1589
--
-- Figure out why MNs are getting rewritte to UNs for top-level
-- pattern-matching functions
isUN :: Name -> Bool
isUN (UN n) = not $ T.isPrefixOf (T.pack "__") n -- TODO
isUN (NS n _) = isUN n
isUN _ = False

annName :: Name -> Doc OutputAnnotation
annName n = annName' n (showbasic n)

annName' :: Name -> String -> Doc OutputAnnotation
annName' n str = annotate (AnnName n Nothing Nothing Nothing) (text str)

annTm :: Term -> Doc OutputAnnotation -> Doc OutputAnnotation
annTm tm = annotate (AnnTerm [] tm)

fancifyAnnots :: IState -> OutputAnnotation -> OutputAnnotation
fancifyAnnots ist annot@(AnnName n _ _ _) =
  do let ctxt = tt_ctxt ist
         docs = docOverview ist n
         ty   = Just (getTy ist n)
     case () of
       _ | isDConName      n ctxt -> AnnName n (Just DataOutput) docs ty
       _ | isFnName        n ctxt -> AnnName n (Just FunOutput) docs ty
       _ | isTConName      n ctxt -> AnnName n (Just TypeOutput) docs ty
       _ | isMetavarName   n ist  -> AnnName n (Just MetavarOutput) docs ty
       _ | isPostulateName n ist  -> AnnName n (Just PostulateOutput) docs ty
       _ | otherwise            -> annot
  where docOverview :: IState -> Name -> Maybe String -- pretty-print first paragraph of docs
        docOverview ist n = do docs <- lookupCtxtExact n (idris_docstrings ist)
                               let o    = overview (fst docs)
                                   norm = normaliseAll (tt_ctxt ist) []
                                   -- TODO make width configurable
                                   -- Issue #1588 on the Issue Tracker
                                   -- https://github.com/idris-lang/Idris-dev/issues/1588
                                   out  = displayS . renderPretty 1.0 50 $
                                          renderDocstring (renderDocTerm (pprintDelab ist)
                                                                         norm) o
                               return (out "")
        getTy :: IState -> Name -> String -- fails if name not already extant!
        getTy ist n = let theTy = pprintPTerm (ppOptionIst ist) [] [] (idris_infixes ist) $
                                  delabTy ist n
                      in (displayS . renderPretty 1.0 50 $ theTy) ""
fancifyAnnots _ annot = annot

showSc :: IState -> [(Name, Term)] -> Doc OutputAnnotation
showSc i [] = empty
showSc i xs = line <> line <> text "In context:" <>
            indented (vsep (reverse (showSc' [] xs)))
     where showSc' bnd [] = []
           showSc' bnd ((n, ty):ctxt) =
             let this = bindingOf n False <+> colon <+> pprintTerm' i bnd (delab i ty)
             in this : showSc' ((n,False):bnd) ctxt


showqual :: IState -> Name -> String
showqual i n = showName (Just i) [] (ppOptionIst i) { ppopt_impl = False } False (dens n)
  where
    dens ns@(NS n _) = case lookupCtxt n (idris_implicits i) of
                              [_] -> n -- just one thing
                              _ -> ns
    dens n = n

showbasic :: Name -> String
showbasic n@(UN _) = show n
showbasic (MN _ s) = str s
showbasic (NS n s) = showSep "." (map str (reverse s)) ++ "." ++ showbasic n
showbasic (SN s) = show s
showbasic n = show n

