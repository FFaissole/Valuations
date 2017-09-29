
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
               Compactness.

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

End Unit_int.

Section Covering.

Record Qprod := mkQP{
    fQ : Q ; 
    sQ : Q ; 
}.

Record covering := {
          Cc :> OS U01 -> nat -> Qprod ;
          HCc : Cc ∅ = fun n => mkQP 1 0 ;
          HCm : forall U V, U <= V -> hexists (fun N => 
                    (forall n, n <= N -> Cc U n = Cc V n) /\ 
                    (forall n, N < n -> Cc U n = mkQP 1 0))                         
}.

Definition interval_length (q1 q2 : Q) : RlowPos.
Proof.
destruct (Qle_total q1 q2).
+ destruct (Qdec q1 q2).
  - exists RlP_0.
    intros.
    destruct RlP_0.
    simpl; apply rlpos.
    trivial.
  - exists (QRlow (q2 - q1)).
    intros p Hp.
    simpl; unfold semi_decide.
    destruct (decide (p < q2 - q1)); 
    try (apply top_greatest).
    cut (p < q2 - q1).
    intros Hc.
    case (n0 Hc).
    apply lt_le_trans with 0; trivial.
    cut (q1 < q2).
    intros Hc.
    apply lt_le.
    apply rings.flip_pos_minus in Hc; 
    trivial.
    apply lt_iff_le_apart. 
    split; trivial.
    apply trivial_apart; trivial.
+ exists RlP_0.    
  intros.
  destruct RlP_0.
  simpl; apply rlpos.
  trivial.
Defined.
  
Fixpoint sum_lengths_l (U : OS U01)(K : covering) n := match n with 
   | O => RlP_0
   | S p => RlP_plus (sum_lengths_l U K p) 
         (interval_length (fQ (K U n)) (sQ (K U n)))  
end.

Definition sum_cov (U : OS U01) (K : covering) : RlowPos
                      := RllubPos (fun n => sum_lengths_l U K n).

End Covering.

Section Covering_def. 

Lemma cov_def : forall (K : covering), 
                forall n, sQ ((K ∅) n) < fQ ((K ∅) n).
Proof.
intros K n.
destruct K as (K,HK1,HK2).
simpl.
rewrite HK1.
simpl; apply semirings.lt_0_1.
Qed.


Lemma interv_empty_gen : forall (q1 q2 : Q),
     q2 < q1 -> interval_length q1 q2 = RlP_0.
Proof. 
intros q1 q2 H.
unfold interval_length.
destruct (Qle_total q1 q2).
cut (~ q1 <= q2).
intros Hf. 
case (Hf l). 
apply lt_not_le_flip; trivial.
reflexivity.
Qed.

Lemma interv_empty_0 : forall {U} (K : covering) n,
     sQ ((K U) n) < fQ ((K U) n) ->
     interval_length (fQ ((K U)  n)) (sQ ((K U) n)) = RlP_0.
Proof.
intros U K n H.
apply interv_empty_gen; 
trivial. 
Qed. 

Lemma sum_cov_def : forall (K : covering), 
       sum_cov ∅ K = RlP_0.
Proof.
intros K.
unfold sum_cov.  
cut ((λ n : nat, sum_lengths_l ∅ K n) = (λ _ : nat, RlP_0)).
intros H; rewrite H.
apply (antisymmetry le).
apply RllubPos_le; intro.
intros q; simpl; apply SierLe_imply.
reflexivity.
apply (RllubPos_lub (λ _ : nat, RlP_0) 0).
apply path_forall. 
intros n.
induction n.
simpl; reflexivity.
simpl.
rewrite IHn.
rewrite RlPPlus_left_id.
apply interv_empty_0.
apply cov_def.
Qed.

End Covering_def.
 
Section Covering_mon.

Lemma sum_cov_mon (U V : OS U01) : U <= V -> 
            forall (K : covering), 
         sum_cov U K <= sum_cov V K.
Proof.
intros HUV K s Hs.
simpl in *; unfold semi_decide, 
            SDseq_Rlow, toRlseq in *.
simpl in *.
destruct K as (K,HK1,HK2).
apply top_le_enumerable_sup.
apply top_le_enumerable_sup in Hs.
revert Hs; apply (Trunc_ind _); 
intros (k,Hk).
assert (H : merely (exists N : nat, 
       (forall n, n <= N -> K U n = K V n) /\ 
       (forall n, N < n -> K U n = mkQP 1 0))).
generalize (HK2 U V HUV). 
apply (Trunc_ind _).
intros (N,(HK2a,HK2b)).
apply tr.
exists N; split; 
apply HK2a || apply HK2b; trivial.
revert H; apply (Trunc_ind _). 
intros H. 
apply tr. 
exists k.
unfold semi_decide in *.
destruct H as (N,H).
revert Hk; generalize s.
induction k.
+ simpl; intros; trivial.
+ intros z Hk; simpl; simpl in Hk.
  apply pred_plus_pr.
  apply pred_plus_pr in Hk.
  revert Hk; apply (Trunc_ind _).
  intros (rk,(sk,(Hk1,(Hk2,Hk3)))).
  apply tr.
  exists rk, sk.
  repeat split; try trivial.
  apply IHk; trivial.
  destruct H as (H1,H2).
  destruct (decide ((S k) <= N)).
  - specialize (H1 (S k) l).
    rewrite <- H1.
    trivial.
  - cut (N < S k). 
    intros Hj.
    specialize (H2 (S k) Hj).
    rewrite H2 in Hk2.
    simpl in Hk2.
    simpl in Hk2.
    pose (Hh := interv_empty_gen 
         Qone Qzero semirings.lt_0_1).
    rewrite Hh in Hk2.
    simpl in Hk2. 
    unfold semi_decide in *.
    destruct (decide (sk < 0)).
    apply rlpos.
    trivial.
    apply not_bot in Hk2.
    case Hk2.
    apply not_le_lt_flip; trivial.
Qed.  

End Covering_mon.

Section Covering_mod.   

Lemma sum_cov_mod : forall U V (K : covering) , 
     RlP_plus (sum_cov U K) (sum_cov V K) = 
     RlP_plus (sum_cov (U ∪ V) K) (sum_cov (U ⋂ V) K).
Proof.
intros U V K.
apply (antisymmetry le).
+ admit.
+ admit.  
Admitted.

End Covering_mod.


Section Covering_prob.   

Lemma sum_cov_prob : forall K : covering, 
         sum_cov (fun _ => SierTop) K <= RlP_1.
Proof.
intros K.
intros s Hs.
simpl in Hs; unfold semi_decide, SDseq_Rlow in *.
simpl in Hs.
apply top_le_enumerable_sup in Hs.
revert Hs; apply (Trunc_ind _).
intros (N,HN).
unfold semi_decide, toRlseq in HN.
induction N.
+ simpl in *.
  unfold semi_decide in *.
  destruct (decide (s < 0)).
  destruct (decide (s < 1)). 
  apply top_greatest.
  cut (s < 1).
  intros H.
  case (n H).
  apply lt_le_trans with 0; 
  try trivial.
  apply semirings.le_0_1.
  destruct (decide (s < 1)).
  apply top_greatest.
  trivial.
+ simpl in HN.
Admitted.

End Covering_prob.

Section Covering_cont. 

Lemma sum_lengths_cont : forall K Un n, 
    sum_lengths_l (Cpo.lub Un) K n <= RllubPos (λ n0 : nat, sum_lengths_l (Un n) K n0).
Proof.
intros K Un n s Hs.
apply top_le_enumerable_sup.
apply tr.
simpl in Hs.
exists n.
unfold semi_decide, toRlseq.
revert Hs; generalize s.
induction n.
+ trivial.
+ intros t Ht; apply pred_plus_pr.
  apply pred_plus_pr in Ht.
  revert Ht; apply (Trunc_ind _).
  intros (p,(q,(H1,(H2,H3)))).
  apply tr.
  exists p, q.
  apply IHn in H1.
  repeat split; try trivial.
  simpl.
Admitted.   

Lemma sum_cov_cont : 
     forall (Un : IncreasingSequence (OS U01)) (K : covering),
     sum_cov (Cpo.lub Un) K  ≤ RllubPos (λ n : nat, sum_cov (Un n) K).
Proof.
intros Un K s Hs.
simpl; unfold semi_decide, SDseq_Rlow, toRlseq.
unfold semi_decide_exists.
apply top_le_enumerable_sup.
unfold sum_cov in *.
apply top_le_enumerable_sup in Hs.
revert Hs; apply (Trunc_ind _).
intros (n,Hs).
unfold semi_decide, toRlseq in *.
cut ((sum_lengths_l (Cpo.lub Un) K n) <= 
     (RllubPos (fun x => sum_lengths_l (Un x) K n))).
intros H0.
apply H0 in Hs.
apply top_le_enumerable_sup in Hs.
revert Hs; apply (Trunc_ind _).
intros (x,Hx).
apply tr.
exists x.
apply top_le_enumerable_sup.
apply tr.
exists n.
trivial.
intros k Hk.
clear Hs.
revert Hk; generalize k.
induction n.
+ intros l Hl. simpl in *.
  unfold semi_decide, SDseq_Rlow, 
         semi_decide_exists.
  simpl.
  apply top_le_enumerable_sup.
  apply tr.
  exists O.
  trivial.
+ intros l Hl. 
  apply pred_plus_pr in Hl.
  revert Hl; apply (Trunc_ind _).
  intros (a,(b,(Ha,(Hb,Hc)))).
  apply top_le_enumerable_sup.
  apply IHn in Ha. 
  apply top_le_enumerable_sup in Ha.
  revert Ha; apply (Trunc_ind _).
  intros (v,Hv).
  apply tr.
  assert (Hl : hexists (fun w => forall x, Cpo.lub Un x = Un w x)).
  apply tr. simpl.
  
  admit.
  
  exists v.
  unfold semi_decide, toRlseq.
  apply pred_plus_pr.
  revert Hl; apply (Trunc_ind _); 
  intros (w,Hw).
  apply tr.
  exists a, b.
  repeat split; trivial.
  cut (Cpo.lub Un = Un w).
  intros H0. 
  rewrite H0 in Hb.
  admit.
  apply path_forall;  
  trivial. 

  apply path_forall in Hb.
Admitted.

End Covering_cont.

Hypothesis cano_cov : covering.

Definition Mu01 : Val U01.
Proof.
exists (fun U : OS U01 => sum_cov U (cano_cov)).
+ intros U V.
  apply sum_cov_mod.
+ red; rewrite sum_cov_def; 
  reflexivity.
+ intros U V Hm.
  apply sum_cov_mon; 
  trivial.
+ apply sum_cov_prob.
+ intros Un;
  apply sum_cov_cont.
Defined.

End U01_mes.           
