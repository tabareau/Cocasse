(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Eric Tanter          *)
(******************************************************)

Require Export Unicode.Utf8_core.
Add LoadPath "." as Casts.
Require Import Cast Decidable Showable.
Require Import Nat Arith.
Require Import Eqdep_dec.
Require Import Arith.

(* Cast for the record for rational numbers *)

(* The type of bounded integers *)

Definition bnat (n:nat) := {m : nat | m <= n}.

Definition bnat_to_nat n : bnat n -> nat := fun x => x.1.

Coercion bnat_to_nat : bnat >-> nat.

Instance show_bnat k : Show (bnat k) := {| show := fun n => show n.1|}.

Definition bnat_S n : bnat n -> bnat (S n) :=
  fun m => (m.1; le_S _ _ m.2).


(* Record type for rational numbers, as in the Coq documentation, section 2.1 *)

(* The only difference is that we use a bounded quantification to keep *)
(* the property Rat_irred_cond decidable *)

Record Rat : Set := mkRat
   {sign : bool;
    top : nat;
    bottom : nat;
    Rat_bottom_cond : 0 <> bottom;
    Rat_irred_cond : forall x y z: bnat (max top bottom),
        x * y = top /\ x * z = bottom -> 1 = x}.

(* n <= m  is an hProp *) 
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

(* Instance of Decidable for bounded quantification *)

Instance Decidable_forall_bounded k
  (P:bnat k->Prop) (HP : forall n, Decidable (P n)) :
  Decidable (forall n, P n).
exact (_Decidable_forall_bounded _ _ _). Defined.

(* Cast for Rat *)

Axiom failed_cast_Rat : forall (s:bool) (t b: nat), Rat.

Definition cast_Rat (s:bool) (t b: nat) : Rat :=
  match dec _ (*Rat_bottom_cond*), dec _ (*Rat_irred_cond*) with
    | inl Hb , inl Hi => mkRat s t b Hb Hi
    | _ , _ => failed_cast_Rat s t b
  end.

(* Axioms for higher order cast of Rat *)

Axiom failed_cast_sign   : forall s t b, sign (failed_cast_Rat s t b) = s.
Axiom failed_cast_top    : forall s t b, top (failed_cast_Rat s t b) = t.
Axiom failed_cast_bottom : forall s t b, bottom (failed_cast_Rat s t b) = b.

(* Playing with some examples *)

Definition Rat_good := cast_Rat true 5 6.

Eval compute in top Rat_good.

Definition Rat_bad := cast_Rat true 5 10.

Eval compute in top Rat_bad.

