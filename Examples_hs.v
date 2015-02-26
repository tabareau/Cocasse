Require Export Unicode.Utf8_core.
Add LoadPath "." as Casts.

Require Import Cast Decidable Showable List Ascii String.

Local Open Scope string_scope.

Definition x_not_ok := 1.
           
Definition x_good : {n:nat | n < 10} := ? 5.

Eval compute in x_good.

Eval compute in x_good.1.

Definition x_bad : {n:nat | n < 10} := ? 15.

Eval compute in x_bad.

Eval compute in x_bad.1.


Definition g (x: {n:nat | n > 0}) := 1.

Eval compute in g (? 0).


Definition client (x: nat) := g (? x).

Extraction Language Haskell.
Extract Constant failed_cast =>
     "\ a s -> Prelude.error (""Cast has failed"" Prelude.++ (Prelude.show s))".
Extraction "test.hs" client.

(** ** A more involved example: casting lists *)

Definition cast_list (A: Type) `{Showable A} (P : A -> Prop) 
  (dec : forall a, Decidable (P a)): 
    list A -> list {a : A | P a} := map ?.

Notation "?::" := (cast_list _ _ _).

Definition list_of_3: list {n:nat | n = 3} := ?:: (3 :: 2 :: 1 :: nil).

Eval compute in list_of_3.


Definition top_succ : nat -> {n:nat | n < 10} := ?> S.


Eval compute in top_succ 6.

Eval compute in top_succ 9.



Definition foo (x: {n:nat | n > 0 }) := x.1.

Extraction foo.

Definition gee := <? foo.
Extraction gee.
