Require Export Arith.
Require Export Wf_nat.

Require Export Term_const.

Lemma le_gt_dec : forall n m : nat, {n <= m} + {n > m}.
Proof.
induction n.
auto with arith.
induction m.
auto with arith.
elim (IHn m); auto with arith.
Defined.

Fixpoint div4 (n : nat) : nat :=
  match n with
  | O => 0
  | S O => 0
  | S (S O) => 0
  | S (S (S O)) => 0
  | S (S (S (S p))) => S (div4 p)
  end.

Fixpoint mod4 (x : nat) : nat :=
  match x with
  | O => 0
  | S O => 1
  | S (S O) => 2
  | S (S (S O)) => 3
  | S (S (S (S q))) => mod4 q
  end.

Parameter le_lt_div4 : forall x : nat, 4 <= x -> div4 x < x.

Definition sqrt4_aux (v : nat * nat) (mod4x : nat) :=
  let (s', r') := v in
  match le_gt_dec (4 * s' + 1) (4 * r' + mod4x) with
  | left h' => (2 * s' + 1, 4 * r' + mod4x - (4 * s' + 1))
  | right h' => (2 * s', 4 * r' + mod4x)
  end.

(* This does not work if we replace y with p *)
Recursive Definition sqrt (nat -> nat * nat) lt lt_wf le_lt_div4
 (forall x : nat,
  sqrt x =
  match le_gt_dec 4 x with
  | left h => sqrt4_aux (sqrt (div4 x)) (mod4 x)
  | right h => match x with
               | O => (0, 0)
               | S y => (1, y)
               end
  end).

Inspect 5.