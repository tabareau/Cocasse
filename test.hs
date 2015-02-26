

module Test where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Sum a b =
   Inl a
 | Inr b

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
append :: char list -> char list -> char list
append s1 s2 =
  case s1 of {
   [] -> s2;
   (::) c s1' -> (::) c (append s1' s2)}

type Decidable = Sum () ()

decidable_le_nat :: Nat -> Nat -> Decidable
decidable_le_nat x =
  nat_rec (\y -> Inl __) (\x0 iHx y ->
    nat_rec (Inr __) (\y0 iHy ->
      case iHx y0 of {
       Inl _ -> Inl __;
       Inr _ -> Inr __}) y) x

type Showable a =
  a -> char list
  -- singleton inductive, whose constructor was Build_Showable
  
show :: (Showable a1) -> a1 -> char list
show showable =
  showable

show_nat :: Showable Nat
show_nat n =
  nat_rec ((::)
    ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    False False False False True True False False) []) (\n0 iHn ->
    append ((::)
      ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
      True True False False True False True False) ((::)
      ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
      False False False False False True False False) ((::)
      ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
      False False False True False True False False) [])))
      (append iHn ((::)
        ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
        True False False True False True False False) []))) n

failed_cast :: a1 -> char list -> a1
failed_cast = Prelude.error "Cast has failed"

cast :: (Showable a1) -> (a1 -> Decidable) -> a1 -> a1
cast h dec a =
  case dec a of {
   Inl _ -> a;
   Inr _ -> failed_cast a (show h a)}

g :: Nat -> Nat
g x =
  S O

client :: Nat -> Nat
client x =
  g (cast show_nat (decidable_le_nat (S O)) x)

