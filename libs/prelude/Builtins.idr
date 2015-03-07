%unqualified

%access public
%default total

||| The canonical single-element type, also known as the trivially
||| true proposition.
%elim data Unit =
  ||| The trivial constructor for `()`.
  MkUnit

namespace Builtins
  ||| The non-dependent pair type, also known as conjunction.
  ||| @A the type of the left elements in the pair
  ||| @B the type of the left elements in the pair
  %elim data Pair : (A : Type) -> (B : Type) -> Type where
     ||| A pair of elements
     ||| @a the left element of the pair
     ||| @b the right element of the pair
     MkPair : {A, B : Type} -> (a : A) -> (b : B) -> Pair A B

  ||| The non-dependent pair type, also known as conjunction, usable with
  ||| UniqueTypes.
  ||| @A the type of the left elements in the pair
  ||| @B the type of the left elements in the pair
  data UPair : (A : Type*) -> (B : Type*) -> Type where
     ||| A pair of elements
     ||| @a the left element of the pair
     ||| @b the right element of the pair
     MkUPair : {A, B : Type*} -> (a : A) -> (b : B) -> UPair A B

  ||| Dependent pairs
  |||
  ||| Dependent pairs represent existential quantification - they consist of a
  ||| witness for the existential claim and a proof that the property holds for
  ||| it. Another way to see dependent pairs is as just data - for instance, the
  ||| length of a vector paired with that vector.
  |||
  |||  @ a the type of the witness @ P the type of the proof
  data Sigma : (a : Type) -> (P : a -> Type) -> Type where
      MkSigma : .{P : a -> Type} -> (x : a) -> (pf : P x) -> Sigma a P

||| The empty type, also known as the trivially false proposition.
|||
||| Use `void` or `absurd` to prove anything if you have a variable of type `Void` in scope. 
%elim data Void : Type where    
    
||| The eliminator for the `Void` type.
void : Void -> a
void {a} v = elim_for Void (\_ => a) v

||| For 'symbol syntax. 'foo becomes Symbol_ "foo"
data Symbol_ : String -> Type where


infix 5 ~=~

||| Explicit heterogeneous ("John Major") equality. Use this when Idris
||| incorrectly chooses homogeneous equality for `(=)`.
||| @ a the type of the left side
||| @ b the type of the right side
||| @ x the left side
||| @ y the right side
(~=~) : (x : a) -> (y : b) -> Type
(~=~) x y = (=) _ _ x y

||| Perform substitution in a term according to some equality.
|||
||| This is used by the `rewrite` tactic and term.
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
replace Refl prf = prf

||| Symmetry of propositional equality
sym : {l:a} -> {r:a} -> l = r -> r = l
sym Refl = Refl

||| Transitivity of propositional equality
trans : {a:x} -> {b:y} -> {c:z} -> a = b -> b = c -> a = c
trans Refl Refl = Refl

||| There are two types of laziness: that arising from lazy functions, and that
||| arising from codata. They differ in their totality condition.
data LazyType = LazyCodata | LazyEval

||| The underlying implementation of Lazy and Inf.
%error_reverse
data Lazy' : LazyType -> Type -> Type where
     ||| A delayed computation.
     |||
     ||| Delay is inserted automatically by the elaborator where necessary.
     |||
     ||| Note that compiled code gives `Delay` special semantics.
     ||| @ t   whether this is laziness from codata or normal lazy evaluation
     ||| @ a   the type of the eventual value
     ||| @ val a computation that will produce a value
     Delay : {t, a : _} -> (val : a) -> Lazy' t a

||| Compute a value from a delayed computation.
|||
||| Inserted by the elaborator where necessary.
Force : {t, a : _} -> Lazy' t a -> a
Force (Delay x) = x

||| Lazily evaluated values. This has special evaluation semantics.
Lazy : Type -> Type
Lazy t = Lazy' LazyEval t

||| Recursive parameters to codata. Inserted automatically by the elaborator
||| on a "codata" definition but is necessary by hand if mixing inductive and
||| coinductive parameters.
Inf : Type -> Type
Inf t = Lazy' LazyCodata t

namespace GuardedRecursion
  ||| A computation that is available later.
  data Later' : Type -> Type where
    Next : {a : Type} -> a -> Later' a

  data ForallKappa : Type -> Type where
    LambdaKappa : {a : Type} -> a -> ForallKappa a
 
  applyKappa : {a : Type} -> ForallKappa a -> a
  applyKappa (LambdaKappa a) = a 

  data Availability = Now | Tomorrow Availability

  Later : Availability -> Type -> Type
  Later Now a = a
  Later (Tomorrow n) a = Later' (Later n a)
                               
  laterApp : {a, b : Type} -> 
             {n : Availability} -> 
             Later (Tomorrow n) (a -> b) -> 
             Later (Tomorrow n) a -> 
             Later (Tomorrow n) b
  laterApp {n = Now} t u = laterApp' t u
    where
     laterApp' : {a, b : Type} -> Later' (a -> b) -> Later' a -> Later' b
     laterApp' (Next t) (Next u) = Next (t u)
  laterApp {n = Tomorrow n'} (Next t) (Next u) = Next (laterApp {n = n'} t u)
  
  ||| The guarded recursive fixed point
  partial
  fix : (Later' a -> a) -> a
  fix f = f (Next (fix f))
  
  ||| The indexed fixed point (named 'pfix' due to the theory)
  partial
  pfix : ((a -> Later' b) -> (a -> b)) -> (a -> b)
  pfix {b} f = fix (\g: Later' (a -> b) => f (\x: a => laterApp {n = Now} g (Next x)))

  ||| A binary version of the indexed fixed point
  partial
  pfix2 : ((a -> b -> Later' c) -> (a -> b -> c)) -> (a -> b -> c)
  pfix2 {b} {c} f = fix (\g: Later' (a -> b -> c) => f (\x: a, y: b => laterApp {n = Now} (laterApp {n = Now} g (Next x)) (Next y)))
  

namespace Ownership
  ||| A read-only version of a unique value
  data Borrowed : UniqueType -> NullType where
       Read : {a : UniqueType} -> a -> Borrowed a

  ||| Make a read-only version of a unique value, which can be passed to another
  ||| function without the unique value being consumed.
  implicit
  lend : {a : UniqueType} -> a -> Borrowed a
  lend x = Read x

par : Lazy a -> a -- Doesn't actually do anything yet. Maybe a 'Par a' type
                  -- is better in any case?
par (Delay x) = x

||| Assert to the totality checker that y is always structurally smaller than
||| x (which is typically a pattern argument)
||| @ x the larger value (typically a pattern argument)
||| @ y the smaller value (typically an argument to a recursive call)
assert_smaller : (x : a) -> (y : b) -> b
assert_smaller x y = y

||| Assert to the totality checker that the given expression will always
||| terminate.
assert_total : a -> a
assert_total x = x

||| Subvert the type checker. This function is abstract, so it will not reduce in
||| the type checker. Use it with care - it can result in segfaults or worse!
abstract %assert_total -- need to pretend
believe_me : a -> b
believe_me x = prim__believe_me _ _ x

||| Subvert the type checker. This function *will*  reduce in the type checker.
||| Use it with extreme care - it can result in segfaults or worse!
public %assert_total
really_believe_me : a -> b
really_believe_me x = prim__believe_me _ _ x
