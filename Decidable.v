(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Eric Tanter          *)
(******************************************************)

Require Import Bool List Le.

(* The Decidable Class, as defined in https://github.com/HoTT/HoTT *)
(* We are defining it here to be independent of the Coq/HoTT library *)

(* We can not use the Decidable class of Coq because its definition *)
(* is in Prop (using \/) instead of Type (using +) *)

Class Decidable (A : Prop) := dec : A + (~ A).

Arguments dec A {_}.

Set Implicit Arguments.

Instance Decidable_bool (t : bool) : Decidable (Is_true t) :=
  match t with
    | true => inl I
    | false => inr id
  end.

(* Connexion to a boolean version of decidable as in *)

Class Decidable_relate (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.

Instance Dec_relate_Decidable P (HP: Decidable_relate P) : 
  Decidable P.
destruct HP as [witness spec]. destruct witness.
- left. exact (proj1 spec eq_refl).
- right. intro p. pose (proj2 spec p). inversion e.
Defined.

Definition Decidable_Dec_relate P (HP: Decidable P) :
  Decidable_relate P.
case HP; intro p.
- refine {| Decidable_witness := true |}.  split; auto.
- refine {| Decidable_witness := false |}. split; auto.
  intro e; inversion e.
Defined.

(* Dedicated class for dealing with decidable equality *)

Class EqDecidable (A : Type) := { 
  eq_dec : forall a b : A, Decidable (a = b) 
}.

Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y).
intros. destruct x, y; try (left ;reflexivity); 
        try (right; intro H; inversion H).
Defined.

Instance EqDecidable_bool : EqDecidable bool := 
  { eq_dec := Decidable_eq_bool }.


Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y).
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (f_equal S H).
    intro H; right. intro e. inversion e. apply (H H1).
Defined.

Instance EqDecidable_nat : EqDecidable nat := 
  { eq_dec := Decidable_eq_nat }.

(* Instances for list *)

Instance Decidable_eq_list : forall A (HA: EqDecidable A) 
  (x y: list A), Decidable (eq x y).
intros A HA. induction x.
- destruct y.
  + left; reflexivity.
  + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (eq_dec a a0); intro H. 
    * case (IHx y); intro Hl.
      left. rewrite H. rewrite Hl. reflexivity.
      right. rewrite H. unfold not in *. 
      intro Hc. inversion Hc. exact (Hl H1).
    * right. unfold not in *. 
      intro Hc. inversion Hc. exact (H H1).
Defined.

Instance EqDecidable_list : 
  forall A (HA: EqDecidable A), EqDecidable (list A) := 
    { eq_dec := Decidable_eq_list HA }.


Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y).
induction x.
- destruct y.
 + left ;reflexivity.
 + left. apply le_S, le_0_n. 
- induction y.
  + right. apply le_Sn_0.
  + case (IHx y). intro H. left. exact (le_n_S _ _ H).
    intro H; right. intro. apply H. exact (le_S_n _ _ H0). 
Defined.


(* Instances for option *)

Instance Decidable_eq_option : forall A (HA: EqDecidable A) 
  (x y: option A), Decidable (eq x y).
intros. destruct x; destruct y.
- case (eq_dec a a0); intro H.
  + left. rewrite H. reflexivity.
  + right. unfold not in *. intro Hc. inversion Hc. 
    exact (H H1).
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. reflexivity.
Defined.

Instance EqDecidable_option :
  forall A (HA: EqDecidable A), EqDecidable (option A) := 
    { eq_dec := Decidable_eq_option HA }.

(* Logical combination instances *)

Instance Decidable_and P Q (HP : Decidable P) 
 (HQ : Decidable Q) : Decidable (P /\ Q).
destruct HP.
- destruct HQ. 
  + exact (inl (conj p q)).
  + apply inr. intro H. exact (n (proj2 H)).
- apply inr. intro H. exact (n (proj1 H)).
Defined.

Instance Decidable_or P Q (HP : Decidable P)
        (HQ : Decidable Q) : Decidable (P \/ Q).
destruct HP.
- exact (inl (or_introl p)).
- destruct HQ. 
  + exact (inl (or_intror q)).
  + apply inr. intro H. case H; auto.
Defined.

Instance Decidable_not P (HP : Decidable P) : 
  Decidable (not P).
case HP; intro H.
- exact (inr (fun X => X H)).
- exact (inl H).
Defined.

Instance Decidable_implies P Q (HP : Decidable P) 
  (HQ : Decidable Q) : Decidable (P -> Q).
destruct HQ.
- exact (inl (fun _ => q)).
- destruct HP. 
  + apply inr. intro H. exact (n (H p)).
  + apply inl. intro p. destruct (n0 p).
Defined.

Instance Decidable_True : Decidable True := inl I.

Instance Decidable_False : Decidable False := inr id.

(* Decidability of proven properties *)

Instance Decidable_proven (P : Prop) (ev :  P):  Decidable P :=
  inl ev.
