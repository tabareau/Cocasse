(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Eric Tanter          *)
(******************************************************)

Require Export Unicode.Utf8_core.
Add LoadPath "." as Casts.

Require Import Cast Decidable Showable List Ascii String.

Local Open Scope string_scope.

(* simple examples, with extraction to Haskell code *)
(* The extraction does not make use of Show because of *)
(* some issues with extraction of String to Haskell *)


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

