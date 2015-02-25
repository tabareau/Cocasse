Require Export Unicode.Utf8_core.

Require Export DecidableExtns.

Notation "x .1" := (proj1_sig x) (at level 3).
Notation "x .2" := (proj2_sig x) (at level 3).
Notation " ( x ; p ) " := (exist _ x p).

Axiom failed_cast : forall {A:Type} {P : A -> Prop} (a: A) (msg:Prop), {a : A | P a}.
  
Definition cast (A:Type) (P : A -> Prop) 
  (dec : forall a, Decidable (P a)) : A -> {a : A | P a}.
Proof.
  intro a. case (dec a); intro p.
  - exact (a; p).
  - exact (failed_cast a (P a)).
Defined.
Notation "?" := (cast _ _ _).

Definition cast_fun_range (A B : Type) (P : B -> Prop) 
  (dec : forall b, Decidable (P b)) :
    (A -> B) -> A -> {b : B | P b} :=
  fun f a => ? (f a).
Notation "?>" := (cast_fun_range _ _ _ _).

Definition cast_fun_dom (A B : Type) (P: A -> Prop) 
  (dec: forall a, Decidable (P a)) :
    ({a : A | P a} -> B)  -> A -> B :=
  fun f a => f (? a).
Notation "<?" := (cast_fun_dom _ _ _ _).

Definition cast_forall_range (A: Type) (B: A -> Type) 
  (P : forall a:A, B a -> Prop) 
  (dec : forall a (b : B a), Decidable (P a b)) :
    (forall a: A, B a) -> forall a: A, {b : B a | P a b} :=
  fun f a => ? (f a).
Notation "?>>" := (cast_forall_range _ _ _ _).

Axiom failed_cast_type : forall {A:Type} {P : A -> Prop} {a: A} (msg:Prop),
 (failed_cast (P:=P) a msg).1 = a.


Definition hide_cast (A: Type) (P: A -> Prop) (B: A -> Type)
           (dec: forall a, Decidable (P a)) (a:A): B (? a).1 -> B a.
Proof.
  unfold cast. case (dec a); intro p.
  - exact (fun b => b).
  - exact (fun b => eq_rect _ _ b _ (failed_cast_type (P a))).
Defined.
Notation "[?]" := (hide_cast _ _ _ _ _).


Definition cast_forall_dom (A: Type) (P: A -> Prop) 
           (B: A -> Type) (dec: forall a, Decidable (P a)) :
   (forall x: {a : A | P a}, B x.1)  -> (forall a : A, B a) :=
  fun f a => [?] (f (? a)).
Notation "<<?" := (cast_forall_dom _ _ _ _).

Require Import List.
Definition cast_list A (P : A -> Prop) (_ : forall a, Decidable (P a))  : list A -> list {a : A | P a} := map ?.
Notation "?::" := (cast_list _ _). 
