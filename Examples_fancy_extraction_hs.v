Require Export Unicode.Utf8_core.
(* Add LoadPath "." as Casts. *)

Require Import Cast DecidableExtns Showable List Ascii String.

Local Open Scope string_scope.

Extract Inductive bool => "Data.Bool.Bool" [ "Data.Bool.True" "Data.Bool.False" ].

Extract Inductive ascii => "Data.Char.Char"
[
"{- If this appears, you're using Ascii internals. Please don't -}
 (\ b0 b1 b2 b3 b4 b5 b6 b7 ->
  let f b i = if b then 1 Data.Bits.shiftL i else 0 :: Prelude.Int in
  Data.Char.chr (f b0 0 Prelude.+ f b1 1 Prelude.+ f b2 2 Prelude.+ f b3 3 Prelude.+ f b4 4 Prelude.+ f b5 5 Prelude.+ f b6 6 Prelude.+ f b7 7))"
].

Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "\ b c -> Data.Char.chr (((Data.Char.ord c) Data.Bits.shiftL 1) land 255 Prelude.+ if b then 1 else 0)".

Extract Inlined Constant ascii_dec => "(==)".

Extract Inductive string => "[Data.Char.Char]" [ "[]" "(:)" ].


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
     "\ a s -> Prelude.error (""Cast has failed with "" Prelude.++ s)".
Extraction "test.hs" client.

(** ** A more involved example: casting lists *)

Definition cast_list (A: Type) `{Show A} (P : A -> Prop) 
  (dec : forall a, Decidable (P a)): 
    list A -> list {a : A | P a} := map (fun a => ? a).

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
