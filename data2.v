(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export Arith.
Require Export Wf_nat.
Require Export Compare_dec.

Require Import Term_const.

Parameter div2 : nat -> nat.
Parameter div2_lt : forall x : nat, div2 (S x) < S x.

Recursive Definition log (nat -> nat) lt lt_wf div2_lt
 (forall x : nat,
  log x = match x with
          | O => 0
          | S O => 0
          | S (S y) => S (log (div2 x))
          end).

Inspect 5.
(* Pour tester pas-à-pas:

Definition log_nat :=
    [log:nat -> nat] [x:nat]
    (Cases x of
        O => (0)
      | (S O) => (O)
      | (S (S p)) => (S (log (div2 x)))
     end).

L_Terminate log_nat nat lt lt_wf log_term div2_lt.

Define_from_terminate log nat log_term.

Make_equation log_equation log_nat log log_term
  (x:nat)(log x)=
	(Case (le_gt_dec x (1)) of [h:?] O [h:?] (S (log (div2 x))) end).


 *)