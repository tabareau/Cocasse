Require Export Unicode.Utf8_core.

Require Import Cast DecidableExtns.
Require Import Nat Arith.
Require Import Eqdep_dec.
Require Import Arith.

(*
The type of rational numbers, with their properties, is defined as: 
*)

Record Rat : Set := mkRat
   {sign : bool;
    top : nat;
    bottom : nat;
    Rat_bottom_cond : 0 <> bottom;
    Rat_irred_cond : forall x y z,
        y * x = top /\ z * x = bottom -> 1 = x}.

(* Cast for rational numbers *)

Axiom failed_cast_Rat : forall (s:bool) (t b: nat), Rat.

Definition cast_Rat (s:bool) (t b: nat)
           {dec_rat_bottom : Decidable _}
           {dec_rat_irred  : (0 <> b) -> Decidable _} : Rat :=
  match dec _ (*Rat_bottom_cond*) with
    | inl Hb => match @dec _ (dec_rat_irred Hb) (*Rat_irred_cond*) with 
                    inl Hi => mkRat s t b Hb Hi
                  | _ => failed_cast_Rat s t b
                end
    | _ => failed_cast_Rat s t b
  end.

(** A decision procedure based on bounded quantification *)

Definition bnat (n:nat) := {m : nat | m <= n}.

Definition bnat_to_nat n : bnat n -> nat := fun x => x.1.

Coercion bnat_to_nat : bnat >-> nat.

Definition bnat_S n : bnat n -> bnat (S n) :=
  fun m => (m.1; le_S _ _ m.2).

(* Adapted from https://coq.inria.fr/files/interval_discr.v *)

Theorem eq_rect_eq_nat :
  forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
intros. apply K_dec_set with (p := h). apply eq_nat_dec. reflexivity.
Qed.

Scheme le_ind' := Induction for le Sort Prop.

Definition le_hprop : forall (n m : nat) (p q : n <= m), p = q.
Proof.
induction p using le_ind'; intro q.
- replace (le_n n) with
  (eq_rect _ (fun n0 => n <= n0) (le_n n) _ eq_refl) by reflexivity.
  generalize (eq_refl n). case q.
  + intro e. rewrite <- eq_rect_eq_nat. reflexivity.
  + intros m l e. contradiction (le_Sn_n m); rewrite <- e; assumption.
- replace (le_S n m p) with
  (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ eq_refl) by reflexivity.
  generalize (eq_refl (S m)). case q.
  + intro Heq. contradiction (le_Sn_n m); rewrite Heq; assumption.
  + intros m0 l HeqS. injection HeqS; intro Heq; generalize l HeqS.
    rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
    rewrite (IHp l0); reflexivity.
Qed.

Fixpoint _Decidable_forall_bounded k (P: bnat k-> Prop)
         (HP : forall n, Decidable (P n)) {struct k}:
  Decidable (forall n : bnat k, P n).
destruct k.
- case (HP (0;Le.le_O_n _)); intro H.
  + left. destruct n. destruct (Le.le_n_0_eq _ l).
    rewrite (le_hprop 0 0 l (Le.le_O_n _)). exact H.
  + right. intro H0. apply (H ([?] (H0 _))).
- case (_Decidable_forall_bounded k (fun n => P (bnat_S k n))
                                   (fun n => HP (bnat_S k n))); intro H.
  + case (HP (S k; Le.le_refl _)). intro HPk.
    * left. intro n. destruct n as [n Hn]. inversion Hn; subst.
      rewrite (le_hprop _ _ Hn (Le.le_refl _)). exact HPk.
      rewrite (le_hprop _ _ Hn (le_S _ _ H1)). exact (H (n;H1)). 
    * right. intro H0. apply n. exact (H0 (S k; Le.le_refl _)).
  + right. intro H0. apply H. intro n. exact (H0 (bnat_S _ n)).
Defined.


Instance Decidable_forall_bounded k (P:bnat k->Prop) (HP : forall n, Decidable (P n)) :
  Decidable (forall n, P n) := _Decidable_forall_bounded _ _ _.

Definition mult_S_le_r n m p : n * m = S p -> n <= S p.
  pose (mult_O_le n m). destruct o. subst. rewrite mult_0_r. intro H; inversion H.
  intro e. now rewrite <- e, mult_comm. 
Defined.

Definition mult_S_le_l n m p : n * m = S p -> m <= S p.
  pose (mult_O_le m n). destruct o. subst. rewrite mult_0_l. intro H; inversion H.
  intro e. now rewrite <- e. 
Defined.


(* Bounded quantification is equivalent to unrestricted quantification *)

Definition Rat_irred_cond_bounded top bottom (H : 0 <> bottom):
  (forall x y z: bnat (max top bottom),
    y * x = top /\ z * x = bottom -> 1 = x)
  <->
  (forall x y z: nat,  y * x = top /\ z * x = bottom -> 1 = x).
  destruct bottom. destruct (H eq_refl).
  split; intros e x y z (H1,H2). 
  - destruct top, x.
    + rewrite mult_0_r in H2. inversion H2.
    + apply (e (S x;mult_S_le_l _ _ _ H2) (0;le_0_n _) (z;mult_S_le_r _ _ _ H2)).
      intuition.
    + rewrite mult_0_r in H2. inversion H2.
    + assert (Hx : S x <= max (S top0) (S bottom0)).
      etransitivity. exact (mult_S_le_l _ _ _ H2). apply Nat.le_max_r.
      assert (Hy : y <= max (S top0) (S bottom0)).
      etransitivity. exact (mult_S_le_r _ _ _ H1). apply Nat.le_max_l.
      assert (Hz : z <= max (S top0) (S bottom0)).
      etransitivity. exact (mult_S_le_r _ _ _ H2). apply Nat.le_max_r.
      apply (e (S x; Hx) (y;Hy) (z;Hz)). intuition.
  - eapply e; eauto.
Defined. 


Instance Rat_irred_cond_dec_bounded top bottom (H : 0 <> bottom)  : Decidable _ :=
Decidable_equivalent (Rat_irred_cond_bounded top bottom H).


(* Example *)

Definition Rat_good := cast_Rat true 5 6.

Eval compute in top Rat_good.

Definition Rat_bad := cast_Rat true 5 10.

Time Eval compute in top Rat_bad.

(* A decision procedure using binary natural numbers *) 

Require Import ZArith_base.
Coercion Z_of_nat : nat >-> Z.

Instance Z_eqdec_ (a b:Z) : Decidable (a = b).
case (Z.eq_dec a b).
- intro e. left. exact e.
- intro ne. right. exact ne. 
Defined.

Instance Z_eqdec : EqDecidable Z := {| eq_dec := Z_eqdec_ |}.

Definition Zmult_mult {a b n} : a * b = n <-> (a*b)%Z = n.
  split; intro e. 
  - rewrite <- Nat2Z.inj_mul. exact (proj2 (Nat2Z.inj_iff _ _) e).
  - rewrite <- Nat2Z.inj_mul in e. exact (Nat2Z.inj _ _ e). 
Defined.

Definition Rat_irred_cond_Z top bottom (H : 0 <> bottom) :
  (forall x y z: bnat (max top bottom),
    Z.mul y x = top /\ Z.mul z x = bottom -> 1 = x) <->
  (forall x y z: nat,
     y * x = top /\ z * x = bottom -> 1 = x).
  etransitivity; try apply Rat_irred_cond_bounded; auto.
  split.
  exact (fun e x y z H => let (H,H0) := H in
                   e x y z (conj (proj1 Zmult_mult H) (proj1 Zmult_mult H0))). 
  exact (fun e x y z H => let (H,H0) := H in
                   e x y z (conj (proj2 Zmult_mult H) (proj2 Zmult_mult H0))). 
Defined. 

Instance Rat_irred_cond_dec top bottom (H : 0 <> bottom) : Decidable _ :=
  Decidable_equivalent (Rat_irred_cond_Z top bottom H).

(* the same example is much faster *)

Definition Rat_bad2 := cast_Rat true 5 10.

Time Eval compute in top Rat_bad2.

(* \paragraph{A decision procedure based on gcd *)

Definition Pos_mult_1 (x y: positive) : 1%positive = (x * y)%positive -> y = 1%positive /\ x = 1%positive.
  intros. split.
  - exact (Pos.mul_eq_1_r _ _ (eq_sym H)). 
  - exact (Pos.mul_eq_1_l _ _ (eq_sym H)).
Defined. 

Definition Zmult_1 : forall (x:Z) (y:nat), 1%Z = (x * y)%Z -> y = 1 /\ x = 1.
  destruct x; intros.
  - inversion H.
  - destruct y. simpl in *.
    + inversion H.
    + simpl in H. inversion H.  apply Pos_mult_1 in H1.
      destruct H1. split. apply (f_equal Zpos) in H0. 
      rewrite Zpos_P_of_succ_nat in H0. rewrite <- Nat2Z.inj_succ in H0.
      exact (Nat2Z.inj _ 1 H0).
      exact (f_equal _ H1).
  - destruct y; inversion H.
Defined. 


Definition Zmult_pos (a b:nat) (c:Z) : a > 0 -> Z_of_nat a = (c * b)%Z -> (0 <= c)%Z.
  destruct a. intro e. inversion e. intro e; clear e. 
  induction c; try (solve [intuition]). 
  destruct b; simpl; intro e; inversion e. 
Defined.


Definition Rat_irred_cond_gcd (top bottom: nat) (Hbot : 0 <> bottom) :
  (Z.gcd top bottom = 1) <->
  (forall x y z, y * x = top /\ z * x = bottom -> 1 = x).
  split. 
  - intros e x y z (H,H0).
    assert (x | top)%Z. exists y. symmetry. exact (proj1 Zmult_mult H).
    assert (x | bottom)%Z. exists z. symmetry. exact (proj1 Zmult_mult H0).
    destruct (Z.gcd_greatest _ _ _ H1 H2).
    rewrite e in H3. symmetry. exact (proj1 (Zmult_1 _ _ H3)).
  - intro e. 
    pose (Z.gcd_divide_l top bottom). 
    pose (Z.gcd_divide_r top bottom).
    pose (Z.gcd_nonneg top bottom).
    pose (Z2Nat.id _ l). 
    destruct d, d0.
    destruct bottom. destruct (Hbot eq_refl).
    rewrite <- e0 in *.
    pose (Zmult_pos _ _ _ (lt_0_Sn _) H0). 
    pose (Hy := H0). rewrite <- (Z2Nat.id _ l0) in Hy.
    rewrite <- Nat2Z.inj_mul in Hy. pose (Hy' := Nat2Z.inj _ _ Hy).
    destruct top.
    + symmetry. specialize (e _ 0 _ (conj eq_refl (eq_sym Hy'))).
      apply (proj2 (Nat2Z.inj_iff _ _) e).
    + pose (Zmult_pos _ _ _ (lt_0_Sn _) H).
      pose (Hx := H). rewrite <- (Z2Nat.id _ l1) in Hx.
      rewrite <- Nat2Z.inj_mul in Hx. pose (Hx' := Nat2Z.inj _ _ Hx).
      symmetry. specialize (e _ _ _ (conj (eq_sym Hx') (eq_sym Hy'))).
      apply (proj2 (Nat2Z.inj_iff _ _) e).
Defined.

Instance Rat_irred_cond_gcd_dec top bottom (H : 0 <> bottom) : Decidable _ :=
  Decidable_equivalent (Rat_irred_cond_gcd top bottom H).

(* Now, computing cast for big rationals is instantaneous. *)

Definition Rat_bad3 := cast_Rat true 75 1235.

Time Eval compute in top Rat_bad3.
