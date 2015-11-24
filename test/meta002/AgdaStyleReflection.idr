||| Implement an Agda-style reflection system as a DSL inside of
||| Idris's reflected elaboration. Requires handling type class
||| resolution and implicit arguments - some of the same features as
||| the Idris elaborator itself.
module AgdaStyleReflection


import Language.Reflection.Utils
import Pruviloj

%default total


||| Function arguments as provided at the application site
record Arg a where
  constructor MkArg
  plicity : Plicity
  argValue : a

instance Functor Arg where
  map f (MkArg plic x) = MkArg plic (f x)

||| Reflected terms, in the tradition of Agda's reflection library
data Term
  = Var Nat (List (Arg Term))
  | Ctor TTName (List (Arg Term))
  | TyCtor TTName (List (Arg Term))
  | Def TTName (List (Arg Term))
  | Lam Term
  | Pi Term Term
  | Constant Const
  | Ty

unApply : Raw -> (Raw, List Raw)
unApply tm = unApply' tm []
  where unApply' : Raw -> List Raw -> (Raw, List Raw)
        unApply' (RApp f x) xs = unApply' f (x::xs)
        unApply' notApp xs = (notApp, xs)

||| Quote a reflected Idris term to a Term in some induced local context
covering
quoteTerm' : List TTName -> Raw -> Elab Term
quoteTerm' env (Var n) =
    case findIndex (==n) env of
      Just i => return (Var i [])
      Nothing =>
        case findIndex (\(n', _) => n == n') !getEnv of
          Just i => return (Var i [])
          Nothing => do [(n', nt, ty)] <- lookupTy n
                          | [] => fail [TextPart "No such variable", NamePart n]
                          | vs => fail ([TextPart "Can't disambiguate"] ++
                                        map (NamePart . fst) vs)
                        case nt of
                          Bound    => fail [TextPart "Bound variable not found"]
                          Ref      => pure $ Def n' []
                          DCon _ _ => pure $ Ctor n' []
                          TCon _ _ => pure $ TyCtor n' []
quoteTerm' env (RBind n (Lam ty) tm) = Lam <$> quoteTerm' (n::env) tm
quoteTerm' env (RBind n (Pi ty kind) tm) = [| Pi (quoteTerm' env ty)
                                                 (quoteTerm' (n::env) tm) |]
quoteTerm' env (RBind n (Let ty val) tm) = fail [TextPart "can't quote let"]
quoteTerm' env (RBind n (Hole ty) tm) = fail [TextPart "can't quote hole"]
quoteTerm' env (RBind n (GHole ty) tm) = fail [TextPart "can't quote deferred hole"]
quoteTerm' env (RBind n (Guess ty val) tm) = fail [TextPart "can't quote guess"]
quoteTerm' env (RBind n (PVar ty) tm) = fail [TextPart "can't quote patvar"]
quoteTerm' env (RBind n (PVTy ty) tm) = fail [TextPart "can't quote pattern type"]
quoteTerm' env (RApp tm tm') =
    do let (f, args) = unApply (RApp tm tm')
       rawArgs <- traverse (quoteTerm' env) args
       case f of
         Var n => doApp n rawArgs
         tm => fail [RawPart tm, TextPart "not normalized first"]

  where
    mkArgs : List Term -> List FunArg -> List (Arg Term)
    mkArgs []  _  = []
    mkArgs tms [] = map (MkArg Explicit) tms
    mkArgs (tm::tms) (ar::ars) = MkArg (plicity ar) tm :: mkArgs tms ars

    doApp : TTName -> List Term -> Elab Term
    doApp fn xs =
        do (fn', nt, ty) <- lookupTyExact fn
           (_, args, res) <- lookupArgsExact fn'
           let rest = mkArgs xs args
           case nt of
             Bound    => fail [TextPart "Bound variable illegal here"]
             Ref      => pure $ Def fn' rest
             DCon _ _ => pure $ Ctor fn' rest
             TCon _ _ => pure $ TyCtor fn' rest

quoteTerm' env RType = pure Ty
quoteTerm' env (RUType x) = fail [TextPart "Uniqueness not supported here"]
quoteTerm' env (RConstant c) = pure (Constant c)

||| Quote a reflected Idris term to a Term
covering
quoteTerm : Raw -> Elab Term
quoteTerm = quoteTerm' []

||| Attempt to resolve a de Bruijn index in a context
resolveVar : Nat -> Elab TTName
resolveVar k =
    do env <- getEnv
       getVar k (map fst env)

  where getVar : Nat -> List TTName -> Elab TTName
        getVar _     []         = fail [TextPart "Variable out of scope"]
        getVar Z     (n :: _  ) = return n -- NB assumes unique names!
        getVar (S k) (_ :: env) = getVar k env

||| Prepare to apply a global by matching its argument plicities to
||| its argument list.
prepareApply : List FunArg -> List (Arg Term) -> Elab (List (Arg (Maybe Term)))
prepareApply [] tms = pure $ map (map Just) tms -- overapplied OK - it may return a function!
prepareApply ars [] = pure [] -- underapplied is ok too
prepareApply (MkFunArg _ _ Constraint _ :: ars) (MkArg Constraint tm :: tms) =
  [| (pure (MkArg Constraint (Just tm))) :: prepareApply ars tms |]
prepareApply (MkFunArg _ _ Constraint _ :: ars) (MkArg plic tm :: tms) =
  [| (pure (MkArg Constraint Nothing)) :: prepareApply ars (MkArg plic tm :: tms) |]
prepareApply (MkFunArg _ _ Implicit _ :: ars) (MkArg Implicit tm :: tms) =
  [| (pure (MkArg Implicit (Just tm))) :: prepareApply ars tms |]
prepareApply (MkFunArg _ _ Implicit _ :: ars) (MkArg plic tm :: tms) =
  [| (pure (MkArg Implicit Nothing)) :: prepareApply ars (MkArg plic tm :: tms) |]
prepareApply (MkFunArg _ _ Explicit _ :: ars) (MkArg Explicit tm :: tms) =
  [| (pure (MkArg Explicit (Just tm))) :: prepareApply ars tms |]
prepareApply (MkFunArg _ _ Explicit _ :: ars) (MkArg plic tm :: tms) =
  fail [TextPart "Expected explicit argument, got something else!"]

||| Should this argument be solved by unification?
toSolve : Arg (Maybe Term) -> Bool
toSolve (MkArg Explicit _) = False
toSolve (MkArg _ (Just _)) = False
toSolve _                  = True

mutual
  covering
  applyGlobal : List TTName -> TTName -> List (Arg Term) -> Elab ()
  applyGlobal locals fn args =
      do (fn', argSpec, _) <- lookupArgsExact fn
         todo <- prepareApply argSpec args
         hs <- apply (Var fn') (map toSolve todo)
         solve
         for_ {b=()} (zip todo hs) $ \(MkArg p tm, h) =>
           case p of
             Constraint => ignore $ inHole h (resolveTC `{applyGlobal})
             _ => case tm of
                    Nothing => skip
                    Just arg => ignore $ inHole h $ spliceTerm' locals arg

  covering
  spliceTerm' : List TTName -> Term -> Elab ()
  spliceTerm' locals (Var k xs) =
      do n <- resolveVar k
         -- local bindings can't have non-explicit args, so just do a normal application
         hs <- apply (Var n) (map (const True) xs)
         solve
         for_ {b = ()} (zip hs xs) $ \(h, MkArg _ x) =>
           ignore $ inHole h (spliceTerm' locals x)
  spliceTerm' locals (Ctor n xs) = applyGlobal locals n xs
  spliceTerm' locals (TyCtor n xs) = applyGlobal locals n xs
  spliceTerm' locals (Def n xs) = applyGlobal locals n xs
  spliceTerm' locals (Lam body) =
      do x <- gensym "x"
         attack
         intro x
         spliceTerm' (x::locals) body
         solve
  spliceTerm' locals (Pi ty body) =
      do arg <- gensym "arg"
         claim arg `(Type)
         x <- gensym "x"
         attack
         forall x (Var arg)
         focus arg; spliceTerm' locals ty
         spliceTerm' (x::locals) body
         solve
  spliceTerm' locals (Constant c) =
      do fill (quote c); solve
  spliceTerm' locals Ty =
      do fill `(Type); solve

covering
spliceTerm : Term -> Elab ()
spliceTerm = spliceTerm' []

||| Lift an Agda-style tactic into an Idris-style tactic
covering
quoteGoalImpl : (Term -> Term) -> Elab ()
quoteGoalImpl f = do compute
                     g <- goalType >>= quoteTerm
                     spliceTerm (f g)

syntax "quoteGoal" {x} "in" [expr] = %runElab (quoteGoalImpl (\x => expr))

syntax "tactic" [expr] = %runElab (quoteGoalImpl expr)





||| A simple proof search tactic with failure
|||
||| @ goal the type to fill out with search
covering
trivial' : (goal : Term) -> Maybe Term
trivial' (TyCtor `{Nat} []) = pure $ Ctor `{Z} []
trivial' (TyCtor `{Unit} []) = pure $ Ctor `{MkUnit} []
trivial' (TyCtor `{Pair} [MkArg Explicit a, MkArg Explicit b]) =
    pure $
    Ctor `{MkPair}
         [ MkArg Explicit !(trivial' a)
         , MkArg Explicit !(trivial' b)
         ]
trivial' (TyCtor `{Either} [MkArg Explicit a, MkArg Explicit b]) =
     (left <$> trivial' a) <|> (right <$> trivial' b)
   where left : Term -> Term
         left x = Ctor `{Left} [MkArg Explicit x]
         right : Term -> Term
         right x = Ctor `{Right} [MkArg Explicit x]
trivial' (Pi _ body) = Lam <$> trivial' body
trivial' _ = empty

||| Attempt proof search, or fake an error message if it fails.
perhaps : Maybe Term -> Term
perhaps = maybe (Ctor (UN "PROOF SEARCH FAILURE") []) id

||| A simple proof search tactic
|||
||| @ goal the type to fill out with search
covering
trivial : (goal : Term) -> Term
trivial = perhaps . trivial'

foo : (Nat, (), Nat, Either (() -> ()) Void)
foo = quoteGoal x in trivial x

bar : (Nat, (), Either Void Nat, Nat -> ())
bar = tactic trivial

--     When checking right hand side of baz:
--     PROOF SEARCH FAILURE is not defined.
baz : (Nat, Void)
baz = tactic trivial

-- Local Variables:
-- idris-load-packages: ("pruviloj")
-- End:
