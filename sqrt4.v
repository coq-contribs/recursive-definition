Require Arith.
Require Compare_dec.
Require Export Wf_nat.
Require Term_const.

Fixpoint div4[n:nat]: nat :=
    Cases n of
        O => O
      |(S O) => O
      |(S (S O)) => O
      |(S (S (S O))) => O
      |(S (S (S (S p)))) => (S (div4 p))
    end.

Fixpoint mod4 [x:nat]:nat :=
      Cases x of
          O => O
       |(S O) => (S O)
       |(S (S O)) => (S (S O))
       |(S (S (S O))) => (S (S (S O)))
       |(S (S (S (S q)))) => (mod4 q)
      end.
Hypothesis lt_div4_x : (x:nat) (lt (div4 (S x)) (S x)).

Definition sqrt4_aux :=
 [v:nat*nat; mod4x:nat] (let (s', r') = v in
	             (Cases (le_gt_dec (plus (mult (4) s') (1)) 
			               (plus (mult (4) r') mod4x)) of
		        (left h') => ((plus (mult (2) s')  (1)), 
			           (minus (plus (mult (4) r') mod4x) 
				          (plus (mult (4) s') (1))))
		      |(right h') => ((mult (2) s'), (plus (mult (4) r') mod4x))
		    end)).

Definition sqrt4_base :=
  [x:nat]Cases x of O => (O,O) | (S p) => ((1),p) end.

Definition sqrt4_F :=
[f: nat -> nat*nat; x:nat ]
 Cases (le_gt_dec (4) x ) of
   (left h) => (sqrt4_aux (f (div4 x)) (mod4 x))
 | (right h) => (Cases x of O => (O, O) |(S p) =>((1), p) end)
 end.

Theorem sqrt_terminates :
 (x:nat){v:nat*nat | (Ex [p:nat] (k:nat)
   (def:nat->nat*nat)(iter (nat -> (nat*nat)) k sqrt4_F def x)=v)}.
Intros x;Elim x using (well_founded_induction nat lt lt_wf).

Recursive Definition sqrt (nat -> nat*nat) lt lt_wf lt_div4_x
 ((x:nat) (sqrt x) =
    (Cases (le_gt_dec (4) x ) of
       (left h) => (sqrt4_aux (sqrt (div4 x)) (mod4 x))
     | (right h) => (sqrt4_base x)
 end)).

(* 
 Local Variables: 
 mode: coq 
 coq-prog-name: "/usr/local/coq-7.0beta/bin/coqtop -byte -I . -emacs"
 compile-command: "make -C <chemin du makefile> <chemin du makefile au fichier>.vo"
 End:
*)
