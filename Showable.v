(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Eric Tanter          *)
(******************************************************)

                                                 
Require Import String.

(* The Show Class, similar to Haskell Show Class  *)

Class Show (A :Type) := { show : A -> string }.

Local Open Scope string_scope.

Instance show_nat : Show nat :=
  {| show := fix _show_nat n :=
       match n with
         | 0 => "0"
         | S n0 => "S (" ++ _show_nat n0 ++ ")"
       end
  |}.

Definition not_implemented := "not implemented".
