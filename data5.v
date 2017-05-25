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