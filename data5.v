Require Export ZArith.
Require Export Zwf.

Require Import Term_const.

Parameter Zwf_minus_one : forall x : Z, (x > 1)%Z -> Zwf 0 (x - 1) x.

Recursive Definition fact (Z -> Z) (Zwf 0) (Zwf_well_founded 0) Zwf_minus_one
 (forall x : Z,
  fact x =
  match Z_le_gt_dec x 1 with
  | left _ => 1%Z
  | right _ => (x * fact (x - 1)%Z)%Z
  end).

Inspect 5.
(* Pour tester pas-à-pas:

Definition fact_F :=
    [fact:Z -> Z] [x:Z]
    (Cases (Z_le_gt_dec x `1`) of
        (left _) => `1`
      | (right _) => `x*(fact x-1)`
     end).

L_Terminate fact_F Z (Zwf `0`) (Zwf_well_founded `0`) fact_term Zwf_minus_one.

Define_from_terminate log Z log_term.

Make_equation log_equation fact_F log log_term
  (x:Z)(log x)=
	(Case (le_gt_dec x (1)) of [h:?] O [h:?] (S (log (div2 x))) end).


 *)