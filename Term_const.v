Require Import Arith.
Require Import Compare_dec.
Require Import Wf_nat.

Declare ML Module "term_const".

Section Iter.
Variable A : Set.

Fixpoint iter (n : nat) : (A -> A) -> A -> A :=
  fun (fl : A -> A) (def : A) =>
  match n with
  | O => def
  | S m => fl (iter m fl def)
  end.
End Iter.

Theorem SSplus_lt : forall p p' : nat, p < S (S (p + p')).
auto with arith.
Qed.
 
Theorem Splus_lt : forall p p' : nat, p' < S (p + p').
auto with arith.
Qed.
