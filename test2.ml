type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type decidable = (__, __) sum

(** val decidable_le_nat : nat -> nat -> decidable **)

let rec decidable_le_nat n y =
  match n with
  | O -> Inl __
  | S n0 ->
    (match y with
     | O -> Inr __
     | S n1 ->
       (match decidable_le_nat n0 n1 with
        | Inl _ -> Inl __
        | Inr _ -> Inr __))

type 'a showable =
  'a -> char list
  (* singleton inductive, whose constructor was Build_Showable *)

(** val show : 'a1 showable -> 'a1 -> char list **)

let show showable0 =
  showable0

(** val show_nat : nat showable **)

let rec show_nat = function
| O -> '0'::[]
| S n0 -> append ('S'::(' '::('('::[]))) (append (show_nat n0) (')'::[]))

(** val failed_cast : 'a1 -> char list -> 'a1 **)

let failed_cast = Prelude.error "Cast has failed"

(** val cast : 'a1 showable -> ('a1 -> decidable) -> 'a1 -> 'a1 **)

let cast h dec a =
  match dec a with
  | Inl _ -> a
  | Inr _ -> failed_cast a (show h a)

type ilist =
| Nil
| Cons of nat * nat * ilist

(** val build_list : nat -> ilist **)

let rec build_list = function
| O -> Nil
| S m -> Cons (m, O, (build_list m))

(** val hide_cast :
    'a1 showable -> ('a1 -> decidable) -> 'a1 -> 'a2 -> 'a2 **)

let hide_cast h dec a b =
  b

(** val cast_forall_dom :
    'a1 showable -> ('a1 -> decidable) -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let cast_forall_dom h dec f a =
  hide_cast h dec a (f (cast h dec a))

(** val build_pos : nat -> ilist **)

let build_pos n =
  build_list n

(** val build_pos' : nat -> ilist **)

let build_pos' =
  cast_forall_dom show_nat (decidable_le_nat (S O)) build_pos

