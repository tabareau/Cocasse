(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Eric Tanter          *)
(******************************************************)

(* Add LoadPath "." as Casts. *)

Require Export Unicode.Utf8_core.
Require Import Cast Decidable Showable List Ascii String.

Local Open Scope string_scope.

(* simple example with extraction to Haskell code *)
(* The extraction does not make use of Show because of *)
(* some issues with extraction of String to Haskell *)

Definition g (x: {n:nat | n > 0}) := 1.

Eval compute in g (? 0).


Definition client (x: nat) := g (? x).

Extraction Language Haskell.
Extract Constant failed_cast =>
     "\ a s -> Prelude.error (""Cast has failed"" Prelude.++ (Prelude.show s))".
Extraction "test.hs" client.