||| Core tactics for working with Elab reflection. These will be used
||| by most reasonable scripts, and they may be candidates for
||| eventual Prelude inclusion.
module Pruviloj.Core


import Language.Reflection.Elab
import Language.Reflection.Utils

data Infer : Type where
  MkInfer : (a : Type) -> a -> Infer

||| Run something for effects, throwing away the return value
ignore : Functor f => f a -> f ()
ignore x = map (const ()) x

||| Do nothing
skip : Applicative f => f ()
skip = pure ()

||| Attempt to apply a tactic. If it fails, do nothing.
try : Alternative f => f a -> f ()
try tac = ignore tac <|> pure ()

||| Solve the goal using the most recent applicable hypothesis
hypothesis : Elab ()
hypothesis =
    do hyps <- map fst <$> getEnv
       flip choiceMap hyps $ \n =>
         do fill (Var n)
            solve


||| Generate a unique name (using `gensym`) that looks like some
||| previous name, for ease of debugging code generators.
nameFrom : TTName -> Elab TTName
nameFrom (UN x) =
    gensym $ if length x == 0 || ("_" `isPrefixOf` x)
               then "x"
               else x
nameFrom (NS n ns) =
    nameFrom n -- throw out namespaces here, because we want to
               -- generate bound var names
nameFrom (MN x n) =
    gensym $ if length n == 0 || ("_" `isPrefixOf` n)
               then "n"
               else n
nameFrom (SN x) = gensym "SN"
nameFrom NErased = gensym "wasErased"

||| Get the name at the head of the term, if it exists.
headName : Raw -> Maybe TTName
headName (RApp f _) = headName f
headName (Var n) = Just n
headName x = Nothing

||| Create a new hole with a given type without changing the
||| focus. Return the name of the hole.
|||
||| @ hint the hint to pass to `gensym`
||| @ ty the type of the new hole
newHole : (hint : String) -> (ty : Raw) -> Elab TTName
newHole hint ty =
    do hn <- gensym hint
       claim hn ty
       return hn

||| Use a term to solve a hole
|||
||| @ tm the term that has the right type for the hole
exact : (tm : Raw) -> Elab ()
exact tm = do apply tm []
              solve

||| Introduce as many names as possible, returning them.
intros : Elab (List TTName)
intros = do g <- snd <$> getGoal
            go g
  where go : TT -> Elab (List TTName)
        go (Bind n (Pi _ _) body) =
            do n' <- nameFrom n
               intro n'
               (n' ::) <$> go body
        go _ = return []

||| Run a tactic inside of a particular hole, if it still exists. If
||| it has been solved, do nothing.
inHole : TTName -> Elab () -> Elab ()
inHole h todo =
  when (h `elem` !getHoles) $
    do focus h
       todo

||| Restrict a polymorphic type to () for contexts where it doesn't
||| matter. This is nice for sticking `debug` in a context where
||| Idris can't solve the type.
simple : {m : Type -> Type} -> m () -> m ()
simple x = x

||| Replace the current goal with one that's definitionally
||| equal. Return the name of the new goal, and ensure that it's
||| focused.
|||
||| @ newGoal A type that is equivalent to the current goal
equiv : (newGoal : Raw) -> Elab TTName
equiv newGoal =
    do h <- gensym "goal"
       claim h newGoal
       fill (Var h); solve
       focus h
       return h

||| Remember a term built with elaboration for later use. If the
||| current goal is `h`, then `remember n ty` puts a fresh hole at
||| the front of the queue, with the old goal `h` second. The
||| contents of this hole end up let-bound in the scope of
||| `h`. Return the name of the new hole, in case it will be used
||| later.
|||
||| @ n the name to be used to save the term
||| @ ty the type to inhabit
remember : (n : TTName) -> (ty : Raw) -> Elab TTName
remember n ty =
    do todo <- gensym "rememberThis"
       claim todo ty
       letbind n ty (Var todo)
       focus todo
       return todo

||| Repeat a given tactic until it fails. Fails if the tactic fails on
||| the first attempt; succeeds otherwise.
repeatUntilFail : Elab () -> Elab ()
repeatUntilFail tac =
    do tac
       repeatUntilFail tac <|> return ()

||| If the current goal is a pattern-bound variable, bind it with the
||| expected name. Otherwise fail.
bindPat : Elab ()
bindPat = do compute
             g <- snd <$> getGoal
             case g of
               Bind n (PVTy _) _ => patbind n
               _ => fail [TermPart g, TextPart "isn't looking for a pattern."]
