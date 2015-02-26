Require Import String. 

Class Showable (A :Type) := { show : A -> string }.

Local Open Scope string_scope.

Instance show_nat : Showable nat.
econstructor. intro n ; induction n.
exact "0". exact ("S ("++IHn++")").
Defined.

Definition not_implemented := "not implemented".
