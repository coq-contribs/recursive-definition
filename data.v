Require Export Arith.
Require Export Wf_nat.
Require Export Compare_dec.

Require Import Term_const.

Parameter div2 : nat -> nat.
Parameter div2_gt_lt : forall x : nat, x > 1 -> div2 x < x.

Recursive Definition log (nat -> nat) lt lt_wf div2_gt_lt
 (forall x : nat,
  log x = (if le_gt_dec x 1 then fun h => 0 else fun h => S (log (div2 x)))).

Inspect 5.
(* Pour tester pas-à-pas:

Definition log_nat :=
    [log:nat -> nat] [x:nat]
.    (Case (le_gt_dec x (1)) of [h:?] O [h:?] (S (log (div2 x))) end)

L_Terminate log_nat nat lt lt_wf log_term div2_gt_lt.

Define_from_terminate log nat log_term.

Make_equation log_equation log_nat log log_term
  (x:nat)(log x)=
	(Case (le_gt_dec x (1)) of [h:?] O [h:?] (S (log (div2 x))) end).


 *)