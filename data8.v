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
Require Export Term_const.

Parameter fst_R : Z * Z -> Z * Z -> Prop.
Parameter fst_wf : well_founded fst_R.

Parameter mod_ : forall x y : Z, y <> 0%Z -> Z.
Parameter
  mod_decrease :
    forall (x y : Z) (h : x <> 0%Z), fst_R (mod_ y x h, x) (x, y).

Recursive Definition pgcd (Z * Z -> Z) fst_R fst_wf mod_decrease
 (forall p : Z * Z,
  pgcd p =
  match p with
  | (a, b) =>
      match Z_eq_dec a 0 with
      | left _ => b
      | right h => pgcd (mod_ b a h, a)
      end
  end).