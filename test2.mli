

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

val failed_cast : 'a1 -> char list -> 'a1

val cast : 'a1 showable -> ('a1 -> decidable) -> 'a1 -> 'a1

type ilist =
| Nil
| Cons of nat * nat * ilist

val build_list : nat -> ilist

val hide_cast : 'a1 showable -> ('a1 -> decidable) -> 'a1 -> 'a2 -> 'a2

val cast_forall_dom :
  'a1 showable -> ('a1 -> decidable) -> ('a1 -> 'a2) -> 'a1 -> 'a2

val build_pos : nat -> ilist

val build_pos' : nat -> ilist

