(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Éric Tanter          *)
(******************************************************)

                                                 
Require Import String.

(* The Show class for values convertible to strings, similar to the Haskell Show class  *)

Class Show (A :Type) := { show : A -> string }.

Local Open Scope string_scope.

(* Default Instance *)

Definition not_implemented := "not implemented".

Instance show_default A : Show A := {| show := fun _ => not_implemented|}.

(* Instance for nat *)
Instance show_nat : Show nat :=
  {| show := fix _show_nat n :=
       match n with
         | O => "O"
         | S n0 => "S (" ++ _show_nat n0 ++ ")"
       end
  |}.
