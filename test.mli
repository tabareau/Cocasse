

type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

val append : char list -> char list -> char list

type decidable = (__, __) sum

val decidable_le_nat : nat -> nat -> decidable

type 'a showable =
  'a -> char list
  (* singleton inductive, whose constructor was Build_Showable *)

val show : 'a1 showable -> 'a1 -> char list

val show_nat : nat showable

val cast : 'a1 showable -> ('a1 -> decidable) -> 'a1 -> 'a1

val g : nat -> nat

val client : nat -> nat

