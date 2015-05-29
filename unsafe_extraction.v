Definition segfault_help (f : unit -> bool)
  : if (f tt)
    then (if negb (f tt) then unit else (unit -> bool))
    else (if negb (f tt) then (unit -> bool) else unit).
  remember (negb (f tt)) as x.
  destruct (f tt); destruct x; [ exact tt | exact f | exact f | exact tt ].
  Defined.

Definition segfault (f : unit -> bool) : bool.
  remember (segfault_help f) as f'. unfold segfault_help in Heqf'.
  destruct (f tt); exact (f' tt).
Defined.

Extraction "segfault.ml" segfault.

Definition segfault_help2 (f : bool)
  : if f
    then (if negb f then unit else bool)
    else (if negb f then bool else unit).
  remember (negb f) as f'.
  destruct f; destruct f'; [ exact tt | exact true | exact false | exact tt ].
Defined.

