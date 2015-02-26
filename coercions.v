(** printing ?> $\rightarrow?$*)
(** printing <? $?\hspace{-1mm}\rightarrow$*)
(** printing ??> $\forall?$*)
(** printing <?? $?\forall$*)
(** printing EqDecidable $\mathsf{Decidable}_=$*)
(** printing Decidable $\mathsf{Decidable}$*)
(** printing EqDecidable_nat $\mathsf{Decidable}_=^\mathbb{N}$*)
(** printing EqDecidable_bool $\mathsf{Decidable}_=^\mathbb{B}$*)
(** printing < $<$*)
(** printing > $>$*)
(** printing ∀ $\forall$*)
(** printing >-> $\rightarrowtail$*)
(** printing .1 $._1$*)
(** printing .2 $._2$*)
(** printing ).1 $)._1$*)
(** printing ).2 $)._2$*)

(* begin hide *)
Require Export Unicode.Utf8_core.
Add LoadPath "." as Casts.
Require Import Casts.

Require Import Bool List Nat Arith.

Set Implicit Arguments.

Notation "??>" := (cast_forall_range _ _ _ _).
Notation "x .1" := (proj1_sig x) (at level 3).
Notation "x .2" := (proj2_sig x) (at level 3).
Notation " ( x ; p ) " := (exist _ x p).
(* end hide *)

(** The major technical challenge addressed in this work is to provide casts for subset types within Coq. These casts have to be %\emph{explicitly}% placed by programmers, much like in the seminal work of Abadi %\emph{et al.}% on integrating static and dynamic typing%~\cite{abadiAl:toplas1991}%. Gradual typing is however generally associated with a mechanism of %\emph{implicit}% cast insertion: the source language, which may not even feature explicit casts, is translated to an internal language with explicit casts%~\cite{siekTaha:sfp2006}%.

While we have been using the term "gradual certified programming" with a loose interpretation of "gradual", it is indeed possible to achieve some level of implicit cast insertion in Coq, exploiting the %{\em implicit coercion}% mechanism.%\footnote{\url{https://coq.inria.fr/distrib/current/refman/Reference-Manual021.html}}%
*)

(* begin hide *)
Section imp_coerce.
(* end hide *)

  (** %\paragraph{Implicit coercions in a nutshell.}% Let us first briefly illustrate implicit coercions in Coq. Assume a decidable indexed property on [nat], which is used to define a type [rich_nat]: *)

  Variable P : nat -> Prop.
  Variable P_dec : forall n:nat, Decidable (P n).
  Definition rich_nat := {n: nat | P n}.

  (** To define an implicit coercion from values of type [rich_nat] to [nat], we first define a function with the appropriate type, and then declare it as an implicit [Coercion]: *) 

  (* Definition rnat_to_nat : {n: nat | P n} -> nat := *)
  (*   fun n => proj1_sig n. *)
  (* Coercion rnat_to_nat : sig >-> nat. *)
  Definition rnat_to_nat : rich_nat -> nat := fun n => n.1.
  Coercion rnat_to_nat : rich_nat >-> nat.

  (** We can now pass a [rich_nat] to a function that expects a [nat], without having to explicitly apply the coercion function: *)

  Variable f : nat -> nat.
  Variable s : rich_nat.
  Check f s.
  
  (** %\paragraph{Implicit cast insertion.}% In order to implicitly insert casts, it is enough to define a
  standard implicit coercion based on a function that introduces
  casts. For instance, we define an implicit coercion (cast insertion)
  from [nat] to [rich_nat]: *)

  Definition nat_to_rnat : nat -> rich_nat := ?.
  Coercion nat_to_rnat : nat >-> rich_nat.

  (** Calling a function that expects a [rich_nat] with a [nat] argument is now type-correct. Under the hood, the implicit coercion takes care of inserting the cast: *)

  Variable g : rich_nat -> nat.
  Variable n: nat.                                                       
  Check g n.

(* begin hide *)
End imp_coerce.
(* end hide *)

(* Definition cast_nat_sup_10 : nat -> {n : nat | n < 10} := ?. *)
(* Coercion cast_nat_sup_10 : nat >-> sig. *)
(* Definition x : {n : nat | n < 10} := 5. *)

(** Compared to standard gradual typing, the limitation of this approach is that Coq does not support universal coercions, so one needs to explicitly define the specific coercions that are permitted. This is arguably less convenient than a general implicit cast insertion mechanism,  but it is also more controlled. Because types are so central to Coq programming, it is unclear whether general implicit cast insertion would be useful and not an endless source of confusion. Actually, even in gradually-typed languages with much less powerful type systems, it has been argued that a mechanism to control implicit cast insertion is important%~\cite{allendeAl:oopsla2014}%. We believe that the implicit coercion mechanism of Coq combined with casts might be a good tradeoff in practice. *)