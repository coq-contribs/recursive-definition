Require Export Arith.
Require Export Wf_nat.
Require Export Compare_dec.

Require Import Term_const.

Parameter div2 : nat -> nat.
Parameter div2_lt : forall x : nat, div2 (S x) < S x.

Recursive Definition log (nat -> nat) lt lt_wf div2_lt
 (forall x : nat,
  log x =
  match x with
  | O => 0
  | S O => 0
  | S (S y) => S (log (div2 (S (S y))))
  end).

Inspect 5.
(* Pour tester pas-à-pas:

Definition log_nat :=
    [log:nat -> nat] [x:nat]
    (Cases x of
        O => (0)
      | (S O) => (O)
      | (S (S y)) => (S (log (div2 (S (S y)))))
     end).

L_Terminate log_nat nat lt lt_wf log_term div2_lt.

Define_from_terminate log nat log_term.

Make_equation log_equation log_nat log log_term
  (x:nat)(log x)=
	(Case (le_gt_dec x (1)) of [h:?] O [h:?] (S (log (div2 x))) end).


 *)