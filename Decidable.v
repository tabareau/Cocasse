(** printing {| $\{|$*)
(** printing |} $|\}$*)

(* begin hide *)
Require Import Bool List Le.

Set Implicit Arguments.

(* end hide *)

(** The [Decidable] type class: *)

Class Decidable (A : Prop) := dec : A + (~ A).

Arguments dec A {_}.


(** ** Basic boolean reflection *)

Instance Decidable_bool (t : bool) : Decidable (Is_true t) :=
  match t with
    | true => inl I
    | false => inr id
  end.

(** ** Boolean reflection with proven relation to a proposition 
 %\label{app:bool_refl}%
*)

Class Decidable_relate (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.


Instance Dec_relate_Decidable P (HP: Decidable_relate P) : 
  Decidable P.
(* begin show *)
destruct HP as [witness spec]. destruct witness.
- left. exact (proj1 spec eq_refl).
- right. intro p. pose (proj2 spec p). inversion e.
Defined.
(* end show *)

(*begin hide *)
Definition Decidable_Dec_relate P (HP: Decidable P) :
  Decidable_relate P.
case HP; intro p.
- refine {| Decidable_witness := true |}.  split; auto.
- refine {| Decidable_witness := false |}. split; auto.
  intro e; inversion e.
Defined.
(* end hide *)

(* begin hide *)
(* That instance is good to show the equivalence between the styles of decidability, 
but introduces infinite loops in type class resolution *)
Reset Decidable_Dec_relate.
(* end hide *)

(** ** Decidable equality *)

(** A type class for types with decidable equality: *)

Class EqDecidable (A : Type) := { 
  eq_dec : forall a b : A, Decidable (a = b) 
}.

(** *** Instances for [bool] *)

(* begin show *)
Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y).
intros. destruct x, y; try (left ;reflexivity); 
        try (right; intro H; inversion H).
Defined.
(* end show *)

Instance EqDecidable_bool : EqDecidable bool := 
  { eq_dec := Decidable_eq_bool }.

(** *** Instances for [nat] *)

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



(** *** Instances for [list] *)

Instance Decidable_eq_list : forall A (HA: EqDecidable A) 
  (x y: list A), Decidable (eq x y).
(* begin show *)
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
(* end show *)

Instance EqDecidable_list : 
  forall A (HA: EqDecidable A), EqDecidable (list A) := 
    { eq_dec := Decidable_eq_list HA }.

(** *** Instances for [option] *)

Instance Decidable_eq_option : forall A (HA: EqDecidable A) 
  (x y: option A), Decidable (eq x y).
(* begin show *)
intros. destruct x; destruct y.
- case (eq_dec a a0); intro H.
  + left. rewrite H. reflexivity.
  + right. unfold not in *. intro Hc. inversion Hc. 
    exact (H H1).
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. reflexivity.
Defined.
(* end show *)

Instance EqDecidable_option :
  forall A (HA: EqDecidable A), EqDecidable (option A) := 
    { eq_dec := Decidable_eq_option HA }.

(** ** Logical combination instances *)

Instance Decidable_and P Q (HP : Decidable P) 
 (HQ : Decidable Q) : Decidable (P /\ Q).
(* begin show *)
destruct HP.
- destruct HQ. 
  + exact (inl (conj p q)).
  + apply inr. intro H. exact (n (proj2 H)).
- apply inr. intro H. exact (n (proj1 H)).
Defined.
(* end show *)

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

(** ** Some arithmetic *)

Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y).
(* begin show *)
induction x.
- destruct y.
 + left ;reflexivity.
 + left. apply le_S, le_0_n. 
- induction y.
  + right. apply le_Sn_0.
  + case (IHx y). intro H. left. exact (le_n_S _ _ H).
    intro H; right. intro. apply H. exact (le_S_n _ _ H0). 
Defined.
(* end show *)

(** ** Decidability of proven properties *)

Instance Decidable_proven (P : Prop) (ev :  P):  Decidable P :=
  inl ev.


(* Instance Decidable_and_right (P Q : Prop) *)
(*   (ev: P) (HQ : Decidable Q) : *)
(*     Decidable (P /\ Q). *)
(* case HQ; intro H. *)
(* - left. exact (conj ev H). *)
(* - right. intro. destruct H0. exact (H H1). *)
(* Defined. *)

(* Instance Decidable_and_left (P Q : Prop) *)
(*   (HP : Decidable P) (ev: Q)  : *)
(*     Decidable (P /\ Q). *)
(* case HP; intro H. *)
(* - left. exact (conj H ev). *)
(* - right. intro. destruct H0. exact (H H0). *)
(* Defined. *)
