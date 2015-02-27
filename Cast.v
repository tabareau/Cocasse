(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Éric Tanter          *)
(******************************************************)

Add LoadPath "." as Casts.

Require Export Unicode.Utf8_core.
Require Import String Decidable Showable.

Notation "x .1" := (proj1_sig x) (at level 3).
Notation "x .2" := (proj2_sig x) (at level 3).
Notation " ( x ; p ) " := (exist _ x p).


(* Casts for subset types {a : A | P a}, when the property P is decidable *)

(* 
   Errors are represented by the failed cast axiom.

   msg1 is the string representation the (failed) casted value
   msg2 is the violated property

 *)

Axiom failed_cast : 
  forall {A:Type} {P : A -> Prop} (a:A) {msg1:string} (msg2: Prop), {a : A | P a}.

Definition cast (A:Type) `{Show A} (P : A -> Prop) 
  (dec : forall a, Decidable (P a)) : A -> {a : A | P a} :=
fun a: A => 
  match dec a with
    | inl p => (a ; p)
    | inr _ => failed_cast a (msg1 := show a) (P a)
  end.

Notation "?" := (cast _ _ _).

(* Casts for non-dependent functions *)

(* - strengthening the range *)
Definition cast_fun_range (A B : Type) `{Show B} (P : B -> Prop) 
  (dec : forall b, Decidable (P b)) :
    (A -> B) -> A -> {b : B | P b} :=
  fun f a => ? (f a).
Notation "?>" := (cast_fun_range _ _ _ _).

(* - relaxing the domain *)
Definition cast_fun_dom (A B : Type) `{Show A} (P: A -> Prop) 
  (dec: forall a, Decidable (P a)) :
    ({a : A | P a} -> B)  -> A -> B :=
  fun f a => f (? a).
Notation "<?" := (cast_fun_dom _ _ _ _).

(* Casts for dependent functions *)

(* - strengthening the range *)
Definition cast_forall_range (A: Type) (B: A -> Type) `{forall a, Show (B a)}
  (P : forall a:A, B a -> Prop) 
  (dec : forall a (b : B a), Decidable (P a b)) :
    (forall a: A, B a) -> forall a: A, {b : B a | P a b} :=
  fun f a => ? (f a).
Notation "??>" := (cast_forall_range _ _ _ _).


(* - weaking the domain 
   This requires a new axiom to hide the failed cast at the type level
   when the projection is used. *)

Axiom failed_cast_proj1 : 
  forall {A:Type} `{Show A} {P : A -> Prop} {a: A} (msg:Prop),
    (failed_cast (P:=P) a (msg1 := show a) msg).1 = a.

Definition hide_cast (A: Type) (P: A -> Prop) (B: A -> Type) `{Show A}
           (dec: forall a, Decidable (P a)) (a:A): B (? a).1 -> B a.
Proof.
  unfold cast. case (dec a); intro p.
  - exact (fun b => b).
  - exact (fun b => eq_rect _ _ b _ (failed_cast_proj1 (P a))).
Defined.

Notation "[?]" := (hide_cast _ _ _ _ _).

Definition cast_forall_dom (A: Type) (P: A -> Prop) `{Show A}
           (B: A -> Type) (dec: forall a, Decidable (P a)) :
   (forall x: {a : A | P a}, B x.1)  -> (forall a : A, B a) :=
  fun f a => [?] (f (? a)).
Notation "<??" := (cast_forall_dom _ _ _ _).