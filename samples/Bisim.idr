module Bisim

%default total

corecord Stream' : Type -> Type where
  hd : Stream' a -> a
  tl : Stream' a -> Stream' a
  constructor (::) (hd tl)

ssucc : Stream' Nat -> Stream' Nat
ssucc s = (S (hd s)) :: (ssucc (tl s))

zeros : Stream' Nat
zeros = 0 :: zeros

ones : Stream' Nat
ones = 1 :: ones

twos : Stream' Nat
twos = 2 :: twos

codata BisimStream : Stream' a -> Stream' a -> Type where
  MkBisimStream : (phd : (hd s) = (hd s')) -> (ptl : BisimStream (tl s) (tl s')) -> BisimStream s s'

corecord BisimStream' : (a : Type) -> Stream' a -> Stream' a -> Type where
  phd : BisimStream' a s s' -> (hd s) = (hd s')
  ptl : BisimStream' a s s' -> BisimStream' a (tl s) (tl s')
  constructor MkBisimStream'

bisimsucconestwos : BisimStream' Nat (ssucc ones) twos
bisimsucconestwos = MkBisimStream' Refl bisimsucconestwos

bisim_eq : BisimStream' a s s' -> s = s'
bisim_eq = believe_me

repeat : Vect (S n) a -> Stream' a
repeat xs = repeat' xs xs
  where
  repeat' : Vect (S n) a -> Vect (S m) a -> Stream' a
  repeat' xs (x :: []) = x :: (repeat' xs xs)
  repeat' xs (x :: (y :: ys)) = x :: (repeat' xs (y :: ys))
  
zeroone : Vect 2 Nat
zeroone = [0, 1]  

onetwo : Vect 2 Nat
onetwo = [1, 2]

bisim_succ_repeat_zeroone__repeat_onetwo : BisimStream' Nat (ssucc (repeat zeroone)) (repeat onetwo)
bisim_succ_repeat_zeroone__repeat_onetwo = MkBisimStream' Refl help
  where
  help : BisimStream' Nat (tl (ssucc (repeat (zeroone)))) (tl (repeat onetwo))
  help = MkBisimStream' Refl bisim_succ_repeat_zeroone__repeat_onetwo

bisim_succ_repeat_zeroone__repeat_onetwo' : BisimStream (ssucc (repeat zeroone)) (repeat onetwo)
bisim_succ_repeat_zeroone__repeat_onetwo' = MkBisimStream Refl (MkBisimStream Refl bisim_succ_repeat_zeroone__repeat_onetwo') 
