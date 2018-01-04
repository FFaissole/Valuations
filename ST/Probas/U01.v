Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.theory.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.dedekind
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod.

Require Export RoundedClosed Opens Valuations LowerIntegrals
               Compactness Riesz1.

Section U01_mes.

Section Unit_int.

Definition btw01 (c : Cut)  := 
              merely (CutZero <= c /\ c <= CutOne).

Definition unit_interval := {c : Cut | btw01 c : hProp}.

Lemma btw01_eq0 : forall a b : unit_interval, 
            proj1_sig a = proj1_sig b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 

Instance unit_interval_isset@{} : IsHSet (unit_interval).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => proj1_sig a = proj1_sig b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply btw01_eq0;apply E.
Qed.

Definition U01 : hSet.
Proof.
exists unit_interval;
apply unit_interval_isset.
Defined.

Definition U01_le : Le U01 := 
          fun x y => proj1_sig x <= proj1_sig y.

Definition U01_is_Q : U01 -> Type :=
         fun x => exists q:Q, QCut q = proj1_sig x.

Notation "[ 0 ; 1 ]" := U01.

Definition open_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p < x < QCut q.

Definition closed_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p <= x /\ x <= QCut q.

Definition os_open_int (p q : Q) : OS [ 0 ; 1 ] := 
              fun x => (semi_decide 
                        ((open_interval p q) (proj1_sig x))).

End Unit_int.

Section Uniform.

Hypothesis Integral : IntPos U01.
Hypothesis Integral_simple : forall a b : Q, 
      rl (Integral (OpenFun U01 (os_open_int a b))) = QRlow (b - a).

Definition Uniform_distr := Riesz1 Integral.

Lemma uniform_open_interval : forall p q, 
               rl (Uniform_distr (os_open_int p q)) = QRlow (q - p).
Proof.
intros p q; unfold Uniform_distr.
simpl; apply Integral_simple.
Qed. 

Lemma uniform_U01 : Uniform_distr (fun x => SierTop) = RlP_1.
Proof.
apply (antisymmetry le).
apply Integral.
assert (H1 : rl (Uniform_distr (os_open_int 0 1)) = Rl1).
rewrite uniform_open_interval.
rewrite rings.negate_0, rings.plus_0_r.
reflexivity.
assert (H2 : Rlle (Integral (OpenFun U01 (os_open_int 0 1))) 
                  ((Integral (OpenFun U01 (λ _ : unit_interval, SierTop))))).
apply Integral.
apply OpenFun_mon.
intros s; apply top_greatest.
rewrite H1 in H2.
trivial.
Qed.

End Uniform.

Section Triangular.

Variable c : Q+.
Hypothesis c_btw01 : 0 < pos c < 1.

Definition Cut_to_Rlow : Cut -> Rlow.
Proof.
intros (lower,upper, cut_iscut). 
destruct cut_iscut.
exists lower.
split; trivial.
Defined.

Definition fun_triang_before_c (x : U01) : RlowPos.
Proof.
destruct x as (cx,Hcx).
assert (Rcx : RlowPos).
exists (Cut_to_Rlow cx).
intros p Hp.
revert Hcx; apply (Trunc_ind _).
intros (Hcx1,Hcx2).
apply Hcx1.
simpl; unfold semi_decide.
destruct (decide (p < 0)).
apply top_greatest.
case (n Hp).
exists (Rlow_mult_q (2/c) Rcx).
apply (Rlow_mult_q (2/c) Rcx).
Defined.

Lemma btw01_cx_aux1 (x : U01) : ∀ p : Q, p < 0 → val (Cut_to_Rlow (1 - proj1_sig x)) p.
Proof. 
intros p Hp.
destruct x as (x,H01x).
unfold Cut_to_Rlow.
simpl.
apply pred_plus_pr.
apply tr.
exists 0,p.
repeat split.
+ unfold semi_decide; destruct (decide (0 < 1)).
  apply top_greatest.
  cut (0 < Qone).
  intros Hc. 
  case (n Hc).
  apply semirings.lt_0_1.
+ SearchAbout upper.
  apply cut_lt_upper.
  assert (Ho : 0 < - p).
  simpl.
 admit.
Admitted. 

Lemma btw01_cx_aux2 : 0 < 2 / (1 - pos c).
Admitted.

Definition fun_triang_after_c (x : U01) : RlowPos.
Proof.
assert (Rcx : RlowPos).
exists (Cut_to_Rlow (1 - proj1_sig x)).
apply btw01_cx_aux1.
assert (overc : Q+).
exists (2 / (1- pos c)).
apply btw01_cx_aux2.
exists (Rlow_mult_q overc Rcx).
apply (Rlow_mult_q overc Rcx).
Defined.

Hypothesis Integral : IntPos U01.
Hypothesis Integral_simple : forall a b : Q, 
      rl (Integral (OpenFun U01 (os_open_int a b))) = QRlow (b - a).
Hypothesis Integral_fun_triang : 
   Integral (λ x : U01,
         (RlPMeet (fun_triang_before_c x) (fun_triang_after_c x))) ≤ RlP_1.

Lemma RlPMeet_fun_pos_plus : forall x (f g V : mf U01),
                  RlPMeet (Rlow_mult_q 2 (fplus f g x)) (V x) = 
                  RlPMeet (Rlow_mult_q 2 (f x)) (V x) + 
                  RlPMeet (Rlow_mult_q 2 (g x)) (V x).
Proof. 
intros x f g V.
apply (antisymmetry le).
+ intros s Hs.
  apply top_le_meet in Hs.
  destruct Hs as (Hs1,Hs2).
  simpl in Hs1, Hs2.
  unfold pred_multQ in Hs1.
  apply pred_plus_pr.
  apply pred_plus_pr in Hs1.
  revert Hs1; apply (Trunc_ind _); 
  intros (r1,(s1,(E1,(E2,E3)))).
  apply tr.
  exists (r1 * / pos 2).
  exists (s1 * / pos 2).
  repeat split.
  apply top_le_meet.
  split.
  simpl; unfold pred_multQ.
  admit. (* OK *)

  admit. (* Ok *) 
  
  apply top_le_meet.
  split.
  simpl; unfold pred_multQ.
  admit. (* OK *)

  admit. (* OK *) 

  admit. (* ok *)

+ intros s Hs.
  apply top_le_meet.
  split; simpl.
  unfold pred_multQ.
  apply pred_plus_pr.
  apply pred_plus_pr in Hs.
  revert Hs; apply (Trunc_ind _); 
  intros (r1,(s1,(E1,(E2,E3)))).
  apply tr.
  apply top_le_meet in E1. 
  apply top_le_meet in E2.
  exists (pos 2 * r1).
  exists (pos 2 * s1).
  destruct E1 as (E11,E12); 
  simpl in E11,E12.
  destruct E2 as (E21,E22); 
  simpl in E21,E22.
  unfold pred_multQ in E11, E21.
  repeat split; trivial.
  admit. (* ok *)
  
  apply pred_plus_pr in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (rv, (sv,(E1,(E2,E3)))).
  apply top_le_meet in E1.
  apply top_le_meet in E2.
  destruct E1 as (E11,E12). 
  destruct E2 as (E21,E22).
Admitted. 


Definition Triangular_distr : IntPos U01.
Proof.
exists (fun f : mf U01 => 
       (Integral (fun x => RlPMeet (Rlow_mult_q 2 (f x)) 
                                      (RlPMeet (fun_triang_before_c x)
                                               (fun_triang_after_c x))))).
+ red;transitivity (Integral (λ x : U01, fzero U01 x)).
  assert (Hx : (λ x : U01,
   RlPMeet (Rlow_mult_q 2 (fzero U01 x))
     (RlPMeet (fun_triang_before_c x) 
              (fun_triang_after_c x))) =
              (λ x : U01, fzero U01 x)).
  apply path_forall; intros x.
  apply (antisymmetry le). 
  assert (Hf : Rlow_mult_q 2 (fzero U01 x) = RlP_0).
  rewrite Rlow_mult_q_RlP_0.
  reflexivity.
  rewrite Rlow_mult_q_RlP_0.
  unfold fzero.
  intros s Hs.
  apply top_le_meet in Hs.
  destruct Hs as (Hs1,Hs2).
  simpl in Hs1, Hs2.
  trivial.
  intros s Hs; simpl in Hs.
  unfold semi_decide in *.
  destruct (decide (s < 0)).
  destruct (RlPMeet (Rlow_mult_q 2 (fzero U01 x))
   (RlPMeet (fun_triang_before_c x) 
            (fun_triang_after_c x))).
  simpl; trivial.
  apply rlpos; trivial.
  case (not_bot Hs).
  rewrite Hx.
  reflexivity.
  apply I_def.
+ red; intros f g.
  rewrite <- I_add.
  apply (antisymmetry le); apply I_mon.
  - intros x q Hq. 
    generalize (RlPMeet_fun_pos_plus x f g 
      (fun x0 => (RlPMeet (fun_triang_before_c x0) 
                          (fun_triang_after_c x0)))).
    intros H3.
    rewrite H3 in Hq.
    clear H3.
    trivial.
  - intros x q Hq. 
    generalize (RlPMeet_fun_pos_plus x f g 
      (fun x0 => (RlPMeet (fun_triang_before_c x0) 
                          (fun_triang_after_c x0)))).
    intros H3.
    rewrite H3.
    clear H3.
    trivial. 
+ red.
  assert (H : Integral
          (λ x : U01,
            RlPMeet (Rlow_mult_q 2 (fone U01 x))
           (RlPMeet (fun_triang_before_c x) 
                    (fun_triang_after_c x)))
          <= 
          Integral (λ x : U01, 
           (RlPMeet (fun_triang_before_c x) 
                    (fun_triang_after_c x)))).
  apply I_mon.
  intros x s Hs.
  apply top_le_meet in Hs.
  simpl in Hs; destruct Hs as (Hs1,Hs2).
  trivial.
  intros s Hs.
  apply H in Hs.
  revert Hs.
  apply Integral_fun_triang.  
+ intros f g Hfg.
  apply I_mon.
  intros x.
  intros s Hs.
  apply top_le_meet in Hs; simpl in Hs.
  destruct Hs as (Hs1,Hs2).
  apply top_le_meet; repeat split; trivial.
  simpl; revert Hs1.
  apply Hfg.
+ intros f.
  generalize (I_cont Integral).
  intros Hcc.
  red in Hcc.
  intros s Hs.
  assert (Hincr : forall n, 
              (λ x : U01,
                 RlPMeet (Rlow_mult_q 2 (f n x))
                (RlPMeet (fun_triang_before_c x) 
                         (fun_triang_after_c x))) <=
              (λ x : U01,
                 RlPMeet (Rlow_mult_q 2 (f (S n) x))
                (RlPMeet (fun_triang_before_c x) 
                         (fun_triang_after_c x)))).
  intros n x q Hx.
  apply top_le_meet. 
  apply top_le_meet in Hx.
  destruct Hx as (H1,H2). 
  split; trivial.
  simpl; simpl in H1.
  unfold pred_multQ in H1; unfold pred_multQ.
  revert H1; apply RC_mon with Qle.
  intros a y; apply (antisymmetry le).
  apply orders.le_or_lt.
  reflexivity.
  simpl.
  apply f.
  specialize (Hcc (Build_IncreasingSequence 
      (λ n : nat,
      (λ x : U01,
       RlPMeet (Rlow_mult_q 2 (f n x))
         (RlPMeet (fun_triang_before_c x) 
                  (fun_triang_after_c x)))) Hincr)).
  apply Hcc.
  clear Hcc. 
  simpl; clear Hincr.
  revert Hs; apply I_mon.
  intros x q Hxq.
  apply top_le_enumerable_sup.
  apply top_le_meet in Hxq.
  destruct Hxq as (H1,H2).
  unfold pred_multQ in H1.
  simpl in H1; unfold pred_multQ in H1.
  unfold semi_decide in H1.
  unfold SDseq_Rlow in H1.
  unfold semi_decide_exists in H1.
  apply top_le_enumerable_sup in H1.
  revert H1; apply (Trunc_ind _).
  intros (N,H1).
  apply tr.
  exists N.
  unfold semi_decide, toRlseq.
  apply top_le_meet.
  split; trivial.
Qed.

End Triangular.
