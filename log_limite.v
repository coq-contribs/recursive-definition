Require Export Arith.
Require Export Compare_dec.
Require Export Wf_nat.

Tactic Definition CaseEq x := Generalize (refl_equal ? x);Pattern -1 x;Case x.

Fixpoint div2[n:nat]: nat :=
   Cases n of
       O => O
      | (S p) => Cases p of
                     O => O
                    | (S q) => (S (div2 q))
                 end
   end.
Parameter thn:(n:nat) (gt n (S O)) ->(lt (div2 n) n).

Definition fl_nat :=
   [f:nat ->nat] [n:nat]
   (Case (le_gt_dec n (1)) of [h:(le n (1))]O [h:(gt n (1))](S (f (div2 n)))
     end).
Section Iter.
Variable A:Set.

Fixpoint iter[n:nat]: (A ->A) -> A ->A :=
   [fl:A ->A] [def:A]
      Cases n of
          O => def
         | (S m) => (fl (iter m fl def))
      end.
End Iter.

Theorem Term:
  (f:nat ->nat) (x:nat)
  {p:nat * nat | (k:nat) (gt k (Snd p)) ->(iter nat ->nat k fl_nat f x)=(Fst p)}.
Intros f n; Elim n using (well_founded_induction nat lt lt_wf); Clear n.
Intros n Hrec.
Generalize (refl_equal ? (le_gt_dec n (1))); Pattern -1 (le_gt_dec n (1));
 Case (le_gt_dec n (1)).
Intros l H'; Try Assumption.
Exists ((0), (0)).
Simpl.
Intros p; Case p.
Intros H''.
Elim (gt_antirefl O); Auto.
Intros n0 H''; Simpl.
Unfold fl_nat.
Rewrite H'.
Auto.
Intros g H'; Try Assumption.
Elim (Hrec (div2 n)).
Intros the_pair; Elim the_pair; Clear the_pair.
Intros rec_res iter_number Hspec.
Exists ((S rec_res), (S iter_number)).
Intros p; Case p.
Intros H'0; Try Assumption.
Elim (lt_n_O <nat, nat> Snd (<nat, nat> ((S rec_res), (S iter_number)))).
Auto.
Intros n0 H'0; Simpl.
Unfold 1 fl_nat.
Rewrite H'.
Rewrite Hspec.
Auto.
Auto with arith.
Apply thn; Auto.
Qed.

Theorem f_terminate:
  (x:nat)
  {v:nat |
    (Ex [p:nat]
    (k:nat) (lt p k) ->(def:nat ->nat)(iter nat ->nat k fl_nat def x)=v)}.
Intros x; (Elim x using (well_founded_induction nat lt lt_wf); Clear x).
(* Apply (well_founded_induction nat lt lt_wf) with a:=x *)
Intros x Hrec; Try Assumption.
Generalize (refl_equal ? (le_gt_dec x (1)));
Change 
(([w:{(le x (1))}+{(gt x (1))}]
  (((le_gt_dec x (1))=w->{v:nat |  
(EX p:nat |
           (k:nat)
            (lt p k)->(def:(nat->nat))(iter nat->nat k fl_nat def x)=v)})))  
(le_gt_dec x (1)));
Case (le_gt_dec x (1)).

(*
Generalize (refl_equal ? (le_gt_dec x (1))); Pattern -1 (le_gt_dec x (1));
 Case (le_gt_dec x (1)).*)
Intros l H'; Try Assumption.
Exists O.
Exists O.
Intros k; Case k.
Intros H'0; Try Assumption.
Elim (gt_antirefl O); Auto.
Intros n H'0 def; Simpl.
Unfold fl_nat.
Rewrite H'.
Auto.
Intros g H'; Try Assumption.
Elim (Hrec (div2 x)); Try Assumption.
Intros rec_res Hspec.
Exists (S rec_res); Try Assumption.
Elim Hspec; Intros p E; Try Exact E.
Exists (S p); Intros k; Case k.
Intros H'0; Try Assumption.
Elim (lt_n_O (S p)); Auto.
Intros n H'0 def.
Simpl.
(*LApply (E n); [Intros H'2; Try Exact H'2 | Idtac]; Auto.*)
(*Cut ((def:(nat->nat))(iter nat->nat n fl_nat def (div2 x))=rec_res ). 
Intros H'2.*)

LApply (E n).
Intros H'2.
Unfold 1 fl_nat.
Rewrite H'.
Generalize (H'2 def).
Intros H'1.
Apply eq_S.
Rewrite <- H'1; Auto.
Apply lt_S_n; Auto.
Apply thn; Auto.
Qed.

(*
Theorem f_terminate_L:
  (x:nat)
  {v:nat |
    (Ex [p:nat]
    (k:nat) (lt p k) ->(def:nat ->nat)(iter nat ->nat k fl_nat def x)=v)}.
Exact [x:nat]
      (well_founded_induction
         nat lt lt_wf
         [n:nat]
         {v:nat |
           (ex
              nat
              [p:nat] (k:nat) (lt p k) ->
              (def:nat ->nat)<nat> (iter nat ->nat k fl_nat def n)=v)}
         [x0:nat]
         [Hrec:(y:nat) (lt y x0) ->
               {v:nat |
                 (ex
                    nat
                    [p:nat] (k:nat) (lt p k) ->
                    (def:nat ->nat)<nat> (iter nat ->nat k fl_nat def y)=v)}]
         (<[s:{(le x0 (S O))}+{(gt x0 (S O))}]
           <{(le x0 (S O))}+{(gt x0 (S O))}> (le_gt_dec x0 (S O))=s ->
           {v:nat |
             (ex
                nat
                [p:nat] (k:nat) (lt p k) ->
                (def:nat ->nat)<nat> (iter nat ->nat k fl_nat def x0)=v)}>
            Cases (le_gt_dec x0 (S O)) of
              (left l) =>
                [H':<{(le x0 (S O))}+{(gt x0 (S O))}>
                      (le_gt_dec x0 (S O))=(left (le x0 (S O)) (gt x0 (S O)) l)]
                (exist
                   nat
                   [v:nat]
                   (ex
                      nat
                      [p:nat] (k:nat) (lt p k) ->
                      (def:nat ->nat)<nat> (iter nat ->nat k fl_nat def x0)=v) O
                   (ex_intro
                      nat
                      [p:nat] (k:nat) (lt p k) ->
                      (def:nat ->nat)<nat> (iter nat ->nat k fl_nat def x0)=O O
                      [k:nat]
                         <[n:nat] (lt O n) ->
                          (def:nat ->nat)
                          <nat> (iter nat ->nat n fl_nat def x0)=O>Cases k of
                             O =>
                               [H'0:(lt O O)]
                               (False_ind
                                  (def:nat ->nat)
                                  <nat> (iter nat ->nat O fl_nat def x0)=O
                                  (gt_antirefl O H'0))
                            | (S n) =>
                                [_:(lt O (S n))] [def:nat ->nat]
                                (eq_ind_r
                                   {(le x0 (S O))}+{(gt x0 (S O))}
                                   (left (le x0 (S O)) (gt x0 (S O)) l)
                                   [s:{(le x0 (S O))}+{(gt x0 (S O))}]
                                   <nat> (Cases s of
                                              (left _) => O
                                             | (right _) =>
                                                 (S
                                                    (iter
                                                       nat ->nat n
                                                       [f:nat ->nat] [n0:nat]
                                                          Cases (le_gt_dec
                                                                   n0 (S O)) of
                                                              (left _) => O
                                                             | (right _) =>
                                                                 (S
                                                                    (f
                                                                       (div2 n0)))
                                                          end def (div2 x0)))
                                          end)=O (refl_equal nat O)
                                   (le_gt_dec x0 (S O)) H')
                         end))
             | (right g) =>
                 [H':<{(le x0 (S O))}+{(gt x0 (S O))}>
                       (le_gt_dec x0 (S O))=
                       (right (le x0 (S O)) (gt x0 (S O)) g)]
                 (sig_rec
                    nat
                    [v:nat]
                    (ex
                       nat
                       [p:nat] (k:nat) (lt p k) ->
                       (def:nat ->nat)
                       <nat> (iter nat ->nat k fl_nat def (div2 x0))=v)
                    [_:{v:nat |
                         (ex
                            nat
                            [p:nat] (k:nat) (lt p k) ->
                            (def:nat ->nat)
                            <nat> (iter nat ->nat k fl_nat def (div2 x0))=v)}]
                    {v:nat |
                      (ex
                         nat
                         [p:nat] (k:nat) (lt p k) ->
                         (def:nat ->nat)<nat> (iter nat ->nat k fl_nat def x0)=v)}
                    [rec_res:nat]
                    [Hspec:(ex
                              nat
                              [p:nat] (k:nat) (lt p k) ->
                              (def:nat ->nat)
                              <nat>
                                (iter nat ->nat k fl_nat def (div2 x0))=rec_res)]
                    (exist
                       nat
                       [v:nat]
                       (ex
                          nat
                          [p:nat] (k:nat) (lt p k) ->
                          (def:nat ->nat)
                          <nat> (iter nat ->nat k fl_nat def x0)=v) (S rec_res)
                       (ex_ind
                          nat
                          [p:nat] (k:nat) (lt p k) ->
                          (def:nat ->nat)
                          <nat> (iter nat ->nat k fl_nat def (div2 x0))=rec_res
                          (ex
                             nat
                             [p:nat] (k:nat) (lt p k) ->
                             (def:nat ->nat)
                             <nat> (iter nat ->nat k fl_nat def x0)=(S rec_res))
                          [p:nat]
                          [E:(k:nat) (lt p k) ->
                             (def:nat ->nat)
                             <nat>
                               (iter nat ->nat k fl_nat def (div2 x0))=rec_res]
                          (ex_intro
                             nat
                             [p0:nat] (k:nat) (lt p0 k) ->
                             (def:nat ->nat)
                             <nat> (iter nat ->nat k fl_nat def x0)=(S rec_res)
                             (S p) [k:nat]
                                      <[n:nat] (lt (S p) n) ->
                                       (def:nat ->nat)
                                       <nat>
                                         (iter nat ->nat n fl_nat def x0)=
                                         (S rec_res)>Cases k of
                                          O =>
                                            [H'0:(lt (S p) O)]
                                            (False_ind
                                               (def:nat ->nat)
                                               <nat>
                                                 (iter
                                                    nat ->nat O fl_nat def x0)=
                                                 (S rec_res) (lt_n_O (S p) H'0))
                                         | (S n) =>
                                             [H'0:(lt (S p) (S n))]
                                             [def:nat ->nat]
                                             (LAPP
                                                (lt p n)
                                                (def0:nat ->nat)
                                                <nat>
                                                  (iter
                                                     nat ->nat n fl_nat def0
                                                     (div2 x0))=rec_res
                                                <nat>
                                                  (fl_nat
                                                     (iter
                                                        nat ->nat n fl_nat def)
                                                     x0)=(S rec_res) (E n)
                                                [H'2:(def:nat ->nat)
                                                     <nat>
                                                       (iter
                                                          nat ->nat n fl_nat def
                                                          (div2 x0))=rec_res]
                                                (eq_ind_r
                                                   {(le x0 (S O))}+
                                                   {(gt x0 (S O))}
                                                   (right
                                                      (le x0 (S O))
                                                      (gt x0 (S O)) g)
                                                   [s:{(le x0 (S O))}+
                                                      {(gt x0 (S O))}]
                                                   <nat> (Cases s of
                                                              (left _) => O
                                                             | (right _) =>
                                                                 (S
                                                                    (iter
                                                                       nat ->nat
                                                                       n fl_nat
                                                                       def
                                                                       (div2 x0)))
                                                          end)=(S rec_res)
                                                   (eq_S
                                                      (iter
                                                         nat ->nat n fl_nat def
                                                         (div2 x0)) rec_res
                                                      (eq_ind
                                                         nat
                                                         (iter
                                                            nat ->nat n fl_nat
                                                            def (div2 x0))
                                                         [n0:nat]
                                                         <nat>
                                                           (iter
                                                              nat ->nat n fl_nat
                                                              def (div2 x0))=n0
                                                         (refl_equal
                                                            nat
                                                            (iter
                                                               nat ->nat n
                                                               fl_nat def
                                                               (div2 x0)))
                                                         rec_res (H'2 def)))
                                                   (le_gt_dec x0 (S O)) H')
                                                (lt_S_n p n H'0))
                                      end) Hspec)) (Hrec (div2 x0) (thn x0 g)))
          end
            (refl_equal {(le x0 (S O))}+{(gt x0 (S O))} (le_gt_dec x0 (S O)))) x).
Qed.
*)
(*
Definition log :=
   [x:nat]
      Cases (f_terminate x) of
          (exist v h) => v
      end.
*)
(*
Theorem fxp_eql: (x:nat)(log x)=(fl_nat log x).
Intros x.
Generalize (refl_equal ? (le_gt_dec x (1))); Pattern -1 (le_gt_dec x (1));
 Case (le_gt_dec x (1)).
Intros l H'; Try Assumption.
Unfold 1 log.
Case (f_terminate x).
Intros v H'0; Try Assumption.
Elim H'0; Intros p E; LApply (E (S p));
 [Intros H'2; Rewrite <- (H'2 log); Clear H'0 | Clear H'0]; Auto.
Simpl.
Unfold fl_nat.
Rewrite H'; Auto.
Intros g H'; Try Assumption.
Unfold 1 log.
Case (f_terminate x).
Intros v H'0; Elim H'0; Intros p E; Try Exact E; Clear H'0.
Unfold fl_nat.
Rewrite H'.
Unfold log.
Case (f_terminate (div2 x)).
Intros x0 H'1; Elim H'1; Intros p0 E0; Try Exact E0; Clear H'1.
Case (le_gt_dec p p0).
Intros G; Try Assumption.
LApply (E (S (S p0))); [Intros H'3; Rewrite <- (H'3 log) | Idtac]; Auto.
LApply (E0 (S p0)); [Intros H'4; Rewrite <- (H'4 log) | Idtac]; Auto.
Simpl.
Unfold 1 fl_nat.
Rewrite H'; Auto.
LApply (gt_S_le p (S p0)); [Intros H'3 | Try Assumption]; Auto with arith.
Intros H'1.
LApply (E (S (S p))); [Intros H'3; Rewrite <- (H'3 log) | Idtac]; Auto.
LApply (E0 (S p)); [Intros H'4; Rewrite <- (H'4 log) | Idtac]; Auto.
Simpl.
Unfold 1 fl_nat.
Rewrite H'; Auto.
Qed.

(* La meme Preuve mais beaucoup plus Simple et plus Constante *)

Theorem log_eq : (x:nat) (log x) = (fl_nat log x).
Intros x.
Unfold log.
Case fl_nat_terminate x.
(CaseEq 'x).                       (* ceci varie d'apres la fonction *)
(* cas de base *)
Intros Heq v Hex.
Unfold fl_nat.
Elim Hex.
Intros p Heq1.
Rewrite <- Heq1 (S p) (lt_n_Sn p) log.
Apply refl_equal.
(* fin du cas de base la preuve est quasi constante: seul log et fl_nat sont
 variables. *)

(* cas recursif *)
Intros n Heq v Hex.
Unfold fl_nat.
Case (f_terminate (div2 (S n))).  (* ici il faut faire varier
                                             f_terminate
                                          et l'argument d'appel recursif. *)
Intros v' Hex'.
Elim Hex.
Intros p Heq1.
Elim Hex'.
Intros p' Heq2.
Rewrite <- Heq1 with S (S (plus p p')) log.  (* faire varier log *)
Rewrite <- Heq2 with S (plus p p') log.      (* faire varier log *)
Auto.

Auto with arith.

Auto with arith.
Qed.



Theorem log_lim: (x:nat)(log x)=(Cases x of
                                     O => O
                                    | (S O) => O
                                    | p => (S (log (div2 p)))
                                 end).
Intros x; Rewrite fxp_eql.
Unfold fl_nat.
Case (le_gt_dec x (1)).
Case x.
Intros H'; Auto.
Intros n; Case n.
Intros H'; Auto.
Intros n0 H'; Inversion H'.
Inversion H0.
Case x.
Intros H'; Inversion H'.
Intros n; Case n.
Intros H'; Inversion H'.
Inversion H0.
Intros n0 H'; Auto.
Qed.
*)

Definition log_F := 
  [log:nat->nat;x:nat]
     Cases x of
        O => O
      | (S O) => O
      | (S (S p)) => (S (log (div2 (S (S p)))))
     end.

Parameter div2_lt : (n:nat)(lt (div2 (S n)) (S n)).

Theorem log_term :
   (x:nat){v:nat|(Ex [p:nat](k:nat)(lt p k)->
        (def : nat -> nat)(iter nat -> nat k log_F def x)=v)}.
Intros x;Elim x using (well_founded_induction nat lt lt_wf).
Clear x;Intros x Hrec.
(CaseEq x).
Exists O;Exists O.
Intros k;Case k.
Intros Hdummy;Elim (lt_n_n O);Auto.
Auto.
Intros n teq;(CaseEq n).
Exists O;Exists O.
Intros k;Case k.
Intros Hdummy;Elim (lt_n_n O);Auto.
Auto.
Intros p teq0.
Elim (Hrec (div2 (S (S p)))).
Intros v' Hex.
Exists (S v').
Elim Hex; Intros p' Heq.
Exists (S p').
Intros k;Case k.
Intros Hdummy;Elim (lt_n_O (S p'));Auto.
Intros k' Hlt def.
LApply (Heq k').
Intros Heq';Rewrite <- (Heq' def).
Auto.
Auto with arith.
Rewrite teq;Rewrite teq0.
Apply div2_lt.
Qed.

Definition log := [x:nat]Cases (log_term x) of (exist v h)=>v end.

Recursive Extraction log.

Theorem aux1 : (n1,n2:nat)(lt n1 (S (S (plus n1 n2)))).
Auto with arith.
Qed.

Theorem aux2 : (n1,n2:nat)(lt n2 (S (plus n1 n2))).
Auto with arith.
Qed.

Theorem log_equation :
  (x:nat)(log x)=(Cases x of
        O => O
      | (S O) => O
      | (S (S p)) => (S (log (div2 (S (S p)))))
     end).
Intros x;Unfold log.
Case (log_term x).
Case x.
Intros v (p Heq); Rewrite <- (Heq (S p) (lt_n_Sn p) log).
Auto.
Intros n;Case n.
Intros v (p Heq); Rewrite <- (Heq (S p) (lt_n_Sn p) log).
Auto.
Intros n'.
Intros v (p Heq).
Case (log_term (div2 (S (S n')))).
Intros v' (p' Heq').
Rewrite <- (Heq (S (S (plus p p'))) (aux1 p p') log).
Rewrite <- (Heq'(S (plus p p')) (aux2 p p') log).
Auto.
Qed.

Fixpoint power [a, x:nat] : nat :=
   Cases x of 
     O => (S O)
   | (S x') => (mult a (power a x'))
   end.

Tactic Definition log_elim x Hrec x'' :=
  Intros x ;Elim x using (well_founded_ind nat lt lt_wf);
  Clear x;Intros x;Case x;
  [Intros Hrec;  Clear Hrec; Rewrite log_equation|
   Intros reserved_name_for_log_elim;(Case reserved_name_for_log_elim;
   Clear reserved_name_for_log_elim);
   [Intros Hrec; Clear Hrec; Rewrite log_equation|
    Intros x'' Hrec;Rewrite log_equation;
    Generalize (Hrec (div2 (S (S x''))) (div2_lt (S x'')));
    Clear Hrec;Intros Hrec]].

Parameter le_mult2_div2 : (x:nat)(le (mult (2) (div2 x)) x);
     le_S_mult2_div2 : (x:nat)(le x (S (mult (2) (div2 x)))).

Theorem log_correct1 : (x:nat)(lt O x)->(le (power (2) (log x)) x).
(log_elim x Hrec x'').
Intros Hlt;Elim (lt_n_n O);Exact Hlt.
Simpl;Auto with arith.
Intros Hlt.
Apply le_trans with (mult (2) (div2 (S (S x'')))).
Replace (power (2)(S (log (div2 (S (S x'')))))) with
        (mult (2) (power (2) (log (div2 (S (S x'')))))).
Apply mult_le.
Apply Hrec.
Simpl;Auto with arith.
Simpl;Auto with arith.
Apply le_mult2_div2.
Qed.

Theorem log_correct2 : (x:nat)(lt x (power (2) (S (log x)))).
(log_elim x Hrec x'').
Simpl;Auto with arith.
Simpl;Auto with arith.

Apply le_lt_trans with (S (mult (2) (div2 (S (S x''))))).
Apply le_S_mult2_div2.
Replace (power (2) (S (S (log (div2 (S (S x''))))))) with
        (mult (2) (power (2) (S (log (div2 (S (S x''))))))).
Unfold lt.
Replace (S (S (mult (2) (div2 (S (S x'')))))) with
   (mult (2) (S (div2 (S (S x''))))).
Apply mult_le.
Change (lt (div2 (S (S x''))) (power (2)(S(log (div2 (S (S x''))))))).
Apply Hrec.
Simpl;Auto with arith.
Simpl;Auto with arith.
Qed.
