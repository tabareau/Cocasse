Require Export Unicode.Utf8_core.
Add LoadPath "." as Casts.
Require Import Cast Decidable Showable String.

Require Import Bool List Nat Arith.

Notation "??>" := (cast_forall_range _ _ _ _).

Notation "x .1" := (proj1_sig x) (at level 3).
Notation "x .2" := (proj2_sig x) (at level 3).
Notation " ( x ; p ) " := (exist _ x p).

Inductive binop : Set := Plus | Minus | Times.

(** Expressions are either constants or applications of a binary operation: *)

Inductive exp : Set := 
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp.

(** The semantics of binary operations is as expected: *)

Definition evalBinop (b: binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Minus => sub
    | Times => mult
  end.

(** So is the semantics of evaluating expressions: *)

Fixpoint evalExp (e: exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (evalBinop b) (evalExp e1) (evalExp e2)
  end.


(* begin hide *)
Eval simpl in evalExp (Const 42).
Eval simpl in evalExp (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Instance show_exp : Showable exp := {| show := fun _ => not_implemented|}.

Definition e1 : {e: exp | evalExp e < 10} := ? (Binop Plus (Const 2) (Const 3)).
(* end hide *)

(** ** The stack machine *)

(** We now introduce the intermediate language of instructions for a stack machine: *)

Inductive instr : Set :=
  | iConst : nat -> instr
  | iBinop : binop -> instr.

(** A program is a list of instructions, and a stack is a list of natural numbers: *)

Definition prog := list instr.
Definition stack := list nat.


(** Executing an instruction on a given stack produces either a new stack or [None] if the stack is in an invalid state: *)

Definition runInstr (i: instr) (s: stack): option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b => 
      match s with
      | arg1 :: arg2 :: s' => Some ((evalBinop b) arg1 arg2 :: s')
      | _ => None
      end
  end.

(** %\noindent% Running a program simply executes each instruction, recursively: *)

Fixpoint runProg (p: prog) (s: stack): option stack :=
  match p with
    | nil => Some s
    | i :: p' => match runInstr i s with
                   | None => None
                   | Some s' => runProg p' s'
                 end
  end.

(* begin hide *)
Eval compute in runProg ((iConst 2) :: (iConst 4) :: (iBinop Times) :: nil) nil.
(* end hide *)


(**  ** The compiler 

We can now turn to the compiler, which is a recursive function that produces a program given an expression: *)

Fixpoint compile (e: exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e1 ++ compile e2 ++ iBinop b :: nil
  end. (* bug - compilation is correct only for commutative binops *)

(** %\noindent \emph{Hint: there is a bug!} *) 

(** ** Correct?
%\label{sct:correct}%

Of course, one would like to be sure that [compile] is a %{\em correct}% compiler. The traditional way of certifying the compiler is to state and prove a correctness theorem. In CPDT, the compiler correctness is stated as follows: *)

Theorem compile_correct : forall (e: exp),
  runProg (compile e) nil = Some (evalExp e :: nil).

(* begin hide *)
Abort.
(* end hide *)


(** %\vspace{2mm}% It turns out that the theorem cannot be proven directly by induction on expressions because of the use of [nil] in the statement of the theorem: the induction hypotheses are not useful. Instead, one has to state a generalized version of the theorem, whose proof does go by induction, and then prove [compile_correct] as a corollary%~\cite{cpdt}%. *)

(**
Instead of going into such a burden as soon as the compiler is defined, one may want to assert correctness and have it checked dynamically. With our framework, it is possible to simply cast the compiler to a correct compiler.

Given a definition of [compiler], [compile_correct] is undecidable because it quantifies over all expressions. This being said, it is possible to check that the compiler is "apparently" correct by checking that it produces correct programs whenever it is used. We therefore define what a "correct program" (for a given source expression) is: %\\[2mm]%  *)

(* WHY DO I NEED THE ABOVE HACKERY TO GET A PROPER LAYOUT? MISTERY... *)

Definition correct_prog (e: exp) (p: prog) : Prop := 
  runProg p nil = Some (evalExp e :: nil).

(** To support casting to [correct_prog], Coq must be able to build evidence that the property is decidable. But as mentioned in Section%~\ref{sec:decidable}% and further explained in Section%~\ref{sec:leveraging}%, the evidence is automatically computed by the type class resolution, which allows us to define the (supposedly) correct compiler simply as:
 *)
(* There are different ways to achieve this, which we explore in this and the following sections. A first solution is to define a decision procedure: *) 
(*begin hide *)
Definition b_correct_prog (e: exp) (p: prog) : bool :=
  match runProg p nil with
    | Some (v :: nil) => Nat.eqb v (evalExp e)
    | _ => false
  end.
(*end hide *)

Instance show_prog : Showable prog := {| show := fun _ => not_implemented|}.

Definition correct_compiler :
  forall e:exp, { p: prog | correct_prog e p } := ??> compile.


(* We still need to lift this decision procedure to the property level. The simplest way to do so is to assert compiler correctness based on reflecting [b_correct_prog] directly as a property: *)
(* Definition correct_prog_r (e: exp) (p: prog) : Prop :=  *)
(*   Is_true (b_correct_prog e p). *)
(* %\noindent% We can now define a correct compiler by casting [compile]: *)
(* Definition correct_compiler : *)
  (* forall e:exp, { p: prog | correct_prog_r e p } := ??> compile. *)

(**  We can now exercise [correct_prog]. The following evaluation succeeds: *)

Eval compute in 
  correct_compiler (Binop Plus (Const 2) (Const 2)).

(** 
<<
= (iConst 2 :: iConst 2 :: iBinop Plus :: nil; 
   eq_refl)
: {p : prog | correct_prog ...}
>>
*)

(** However, the cast fails when using a (non-commutative!) subtraction operation: *)

Eval compute in 
  correct_compiler (Binop Minus (Const 2) (Const 1)).
