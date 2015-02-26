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

(** val cast : 'a1 showable -> ('a1 -> decidable) -> 'a1 -> 'a1 **)

let cast h dec a =
  match dec a with
  | Inl _ -> a
  | Inr _ ->
    (let f _ s = failwith (String.concat "" (["Cast has failed because of "]@ (List.map (String.make 1) s))) in f)
      a (show h a)

(** val g : nat -> nat **)

let g x =
  S O

(** val client : nat -> nat **)

let client x =
  g (cast show_nat (decidable_le_nat (S O)) x)

