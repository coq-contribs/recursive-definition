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