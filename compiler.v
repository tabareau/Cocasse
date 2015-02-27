(******************************************************)
(*                    Cocasse                         *)
(* A library for Gradual Certified Programming in Coq *)
(* Authors: Nicolas Tabareau and Éric Tanter          *)
(******************************************************)

Require Export Unicode.Utf8_core.
Require Import Cast Decidable Showable String.

Require Import Bool List Nat Arith.

Notation "??>" := (cast_forall_range _ _ _ _).

Notation "x .1" := (proj1_sig x) (at level 3).
Notation "x .2" := (proj2_sig x) (at level 3).
Notation " ( x ; p ) " := (exist _ x p).

(* Example of certified compiler from CPDT, with cast *)

Inductive binop : Set := Plus | Minus | Times.

(* Expressions are either constants or applications of a binary operation: *)

Inductive exp : Set := 
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp.

(* The semantics of binary operations is as expected: *)

Definition evalBinop (b: binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Minus => sub
    | Times => mult
  end.

(* So is the semantics of evaluating expressions: *)

Fixpoint evalExp (e: exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (evalBinop b) (evalExp e1) (evalExp e2)
  end.

Eval simpl in evalExp (Const 42).
Eval simpl in evalExp (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

(* showing expressions [TBD] *)

Instance show_exp : Show exp := {| show := fun _ => not_implemented|}.

(* A simple cast on expressions *)

Definition e1 : {e: exp | evalExp e < 10} := ? (Binop Plus (Const 2) (Const 3)).


(* The stack machine *)

(* Intermediate language of instructions *)

Inductive instr : Set :=
  | iConst : nat -> instr
  | iBinop : binop -> instr.

(* A program is a list of instructions, and a stack is a list of natural numbers *)

Definition prog := list instr.
Definition stack := list nat.


(* Executing an instruction on a given stack produces either a new stack or [None] if the stack is in an invalid state: *)

Definition runInstr (i: instr) (s: stack): option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b => 
      match s with
      | arg1 :: arg2 :: s' => Some ((evalBinop b) arg1 arg2 :: s')
      | _ => None
      end
  end.

(* Running a program simply executes each instruction, recursively: *)

Fixpoint runProg (p: prog) (s: stack): option stack :=
  match p with
    | nil => Some s
    | i :: p' => match runInstr i s with
                   | None => None
                   | Some s' => runProg p' s'
                 end
  end.

Eval compute in runProg ((iConst 2) :: (iConst 4) :: (iBinop Times) :: nil) nil.


(* The (almost correct) compiler *)
Fixpoint compile (e: exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e1 ++ compile e2 ++ iBinop b :: nil
  end. (* bug - compilation is correct only for commutative binops *)


(* Defining what a correct compiler is *)

Definition correct_prog (e: exp) (p: prog) : Prop := 
  runProg p nil = Some (evalExp e :: nil).

(* showing programs [TBD] *)

Instance show_prog : Show prog := {| show := fun _ => not_implemented|}.

(* Casting the compiler to a correct compiler *)

Definition correct_compiler :
  forall e:exp, { p: prog | correct_prog e p } := ??> compile.

(* Cast ok when using a commutative operation: *)

Eval compute in 
  correct_compiler (Binop Plus (Const 2) (Const 2)).

(* Cast fails when using a (non-commutative!) subtraction operation *)

Eval compute in 
  correct_compiler (Binop Minus (Const 2) (Const 1)).
