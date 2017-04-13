
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.interfaces.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric
               HoTTClasses.theory.rings
               HoTTClasses.orders.semirings
               HoTTClasses.orders.rings
               HoTTClasses.theory.dec_fields.

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Giry Cpo
               Interp.
              
Set Implicit Arguments.

(** Random program : Val nat
   fun f: nat -> Sier => (1 / S n) * sum_1^n (f n)
*)

Require Export Spaces.Nat.  
Close Scope nat. 

Definition nat : hSet := default_TruncType 0 nat hset_nat. 

Fixpoint sum_n_moy_aux (p : nat) (f : nat -> RlowPos) : RlowPos := 
       match p with
          |O => RlP_0
          |S p0 => RlP_plus (f (S p0)) (sum_n_moy_aux p0 f)
end.

Lemma sum_n_moy_aux_def (p : nat) : 
      sum_n_moy_aux p (fzero nat) = RlP_0.
Proof.
induction p.
+ simpl; reflexivity.
+ simpl.
  rewrite IHp.
  assert (H0 : (fzero nat (S p)) = RlP_0). 
  reflexivity.
  rewrite H0.
  rewrite RlPPlus_left_id; 
  reflexivity. 
Qed.

Lemma sum_n_moy_aux_mon (p : nat) f g : fle f g ->
      sum_n_moy_aux p f <= sum_n_moy_aux p g.
Proof.
intros Hfg.
induction p.
+ simpl; reflexivity.
+ simpl.
  transitivity (RlP_plus (f (S p)) 
                   (sum_n_moy_aux p g)).
  apply Rllepos_plus_le_preserving; exact IHp.
  rewrite (RlPPlus_comm _ (sum_n_moy_aux p g)).
  rewrite (RlPPlus_comm _ (sum_n_moy_aux p g)).
  apply Rllepos_plus_le_preserving.
  apply Hfg.
Qed.  

Definition QRlow_nat_pos : nat -> RlowPos.
Proof.
intros n.
induction n.
+ exists RlP_0. intros p Hp; simpl.
  unfold semi_decide; destruct (decide (p < 0)).
  apply top_greatest.
  case (n Hp).
+ exists (QRlow (qn (S n))).
  intros p Hp.
  simpl; unfold semi_decide.
  destruct (decide (p < S n)).
  apply top_greatest.
  assert (Hpn : p < (S n)).
  apply lt_le_trans with 0; trivial.
  unfold qn. apply lt_le.
  destruct ((pos_of_nat (S n))).
  apply rationals.is_pos.
  case (n0 Hpn).
Defined.    


Lemma sum_n_moy_aux_prob (n : nat) :
               Rlle (sum_n_moy_aux n (fone nat))
                    (QRlow_nat_pos n).
Proof.
induction n.
+ intros q; trivial. 
+ intros q. simpl in *.
  intros H.
  unfold semi_decide in *.
  apply pred_plus_pr in H.
  destruct (decide (q < S n)).
  apply top_greatest.
  assert (hq : q < S n).
  revert H; apply (Trunc_ind _); 
  intros (a,(b,(E1,(E2,E3)))).
  rewrite E3.
  specialize (IHn b).
  apply IHn in E2.
  induction n.
  - simpl in E2; unfold semi_decide in E2.
    destruct (decide (a < 1)). 
    destruct (decide (b < 0)).
    apply lt_le_trans with (1 + 0)%mc.
    apply plus_lt_compat; trivial.
    rewrite plus_0_r.
    reflexivity.
    apply not_bot in E2; case E2.
    apply not_bot in E1; case E1.
  - simpl in E2; unfold semi_decide in *.
    destruct (decide (a < 1)).
    destruct (decide (b < S n)).
    apply plus_lt_compat; trivial.
    apply not_bot in E2; case E2.
    apply not_bot in E1; case E1.
  - case (n0 hq). 
Qed.    
    
    
Lemma sum_n_moy_aux_add (p : nat) f g : 
      sum_n_moy_aux p (fplus f g) =  RlP_plus (sum_n_moy_aux p f) 
                                             (sum_n_moy_aux p g).
Proof.
induction p.
+ simpl; rewrite RlPPlus_left_id;
  reflexivity.
+ simpl.
  rewrite IHp.
  assert (H0 : (fplus f g (S p)) = 
        RlP_plus (f (S p)) (g (S p))).
  reflexivity.
  rewrite H0.
  rewrite RlPPlus_assoc.
  rewrite RlPPlus_assoc.
  rewrite RlPPlus_comm.
  rewrite RlPPlus_comm.
  rewrite <- (RlPPlus_assoc (f (S p)) (g (S p)) 
             (sum_n_moy_aux p f)).
  rewrite (RlPPlus_comm (g (S p)) 
     (sum_n_moy_aux p f)).
  rewrite RlPPlus_assoc.
  reflexivity.  
Qed.

Definition sum_n_moy (p : nat) (f : nat -> RlowPos) : RlowPos 
             := Rlow_mult_q p (sum_n_moy_aux p f).

Lemma sum_n_moy_def (p : nat) : 
      sum_n_moy p (fzero nat) = RlP_0.
Proof.
unfold sum_n_moy.
rewrite sum_n_moy_aux_def.
apply Rlow_mult_q_RlP_0.
Qed.

Lemma sum_n_moy_prob (n : nat) : 
   Rlle (sum_n_moy n (fone nat)) RlP_1.
Proof.
unfold sum_n_moy.
assert (H : Rlle 
       (Rlow_mult_q n (sum_n_moy_aux n (fone nat))) 
       (Rlow_mult_q n (QRlow_nat_pos n))).
intros q Hq.
unfold Rlow_mult_q in *; simpl in *.
unfold pred_multQ in *; simpl in *.
revert Hq; apply RC_mon with Qle.
intros x y; apply (antisymmetry Qle).
intros x y; apply orders.le_or_lt.
reflexivity.
apply sum_n_moy_aux_prob.     
assert (H2 : Rlle (Rlow_mult_q n (QRlow_nat_pos n)) 
                  RlP_1).
intros q Hq.
simpl in Hq.
unfold pred_multQ in Hq.
induction n.
+ simpl in Hq. simpl.
  unfold semi_decide in *; simpl in *.
  clear H. 
  rewrite mult_1_l in Hq.
  destruct (decide (q < 0)).
  destruct (decide (q < 1)).
  trivial.
  assert (Hf : q < 1).
  transitivity Qzero.
  trivial.
  apply lt_0_1.
  case (n Hf).
  destruct (decide (q < 1)).
  apply top_greatest.
  trivial.         
+ clear IHn. simpl.
  unfold semi_decide in *.
  destruct (decide ((naturals.naturals_to_semiring 
              nat Q (S n) * q)%mc < S n)).
  destruct (decide (q < 1)); trivial.
  apply top_greatest.
  assert (Hf : q < 1). 
  assert (Hu : 
   ((1 / qn (S n))* ((qn (S n))*q))%mc <
    ((1 / qn (S n)) * (qn (S n)))%mc).
  apply pos_mult_lt_l.
  rewrite mult_1_l.
  apply dec_fields.pos_dec_recip_compat.
  apply rationals.is_pos.
  apply l.
  rewrite mult_assoc in Hu.
  rewrite mult_comm in Hu.
  rewrite (mult_comm _ (qn (S n))) in Hu.
  rewrite mult_1_l in Hu.
  assert (Hsn : qn (S n) / qn (S n) = 1). 
  transitivity (1/1).
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : 0 < pos (S n)).
  apply rationals.is_pos.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity. 
  rewrite Hsn in Hu.
  rewrite mult_1_r in Hu; trivial. 
  case (n0 Hf).
  destruct (decide (q < 1)).
  apply top_greatest.
  simpl in Hq.
  unfold semi_decide in Hq.
  destruct (decide ((naturals.naturals_to_semiring 
              nat Q (S n) * q)%mc < S n)).
  case (n0 l).
  destruct (decide
        ((naturals.naturals_to_semiring 
      Datatypes.nat Q (S n) * q)%mc < S n)).
  case (n2 l).
  trivial. 
+ intros q hq; apply H2.
  apply H; trivial.
Qed.   
 
Definition random_aux (N : nat) : M nat. 
Proof.
intros f.
exists (rl (sum_n_moy N f)).
apply (sum_n_moy N). 
Defined. 

Definition random (N : nat) :  IntPos nat.  
Proof. 
exists (random_aux N).
+ unfold Mdef, random_aux.
  apply RCP_eq0.
  rewrite sum_n_moy_def.
  simpl; reflexivity. 
+ intros f g.
  unfold random_aux; simpl.
  apply RCP_eq0; simpl.
  transitivity (pred_multQ (val (RlP_plus (sum_n_moy_aux N f)  
                                 (sum_n_moy_aux N g))) N).
  assert (Hsum : sum_n_moy_aux N (fplus f g) = RlP_plus
             (sum_n_moy_aux N f) (sum_n_moy_aux N g)).
  apply sum_n_moy_aux_add. 
  rewrite Hsum.
  reflexivity.
  apply path_forall.
  intros x. 
  apply (antisymmetry SierLe).
  - apply imply_le.
    intros Hx.
    unfold pred_multQ in Hx.
    apply pred_plus_pr.
    apply pred_plus_pr in Hx.
    revert Hx; apply (Trunc_ind _); 
    intros (a,(b,(E1,(E2,E3)))).
    apply tr.
    exists (a / pos N), (b / pos N).
    repeat split.
    unfold pred_multQ.
    assert (Ha : (pos N * (a / pos N))%mc = a).
    rewrite mult_comm.
    rewrite <- mult_assoc.
    rewrite (mult_comm _ (pos N)).
    assert (Hn : (pos N / pos N) = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos N).
    apply (pos_is_pos).
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hn.
    rewrite mult_1_r.
    reflexivity.
    rewrite Ha; trivial.
    unfold pred_multQ.
    assert (Hb : (pos N * (b / pos N))%mc = b).
    rewrite mult_comm.
    rewrite <- mult_assoc.
    rewrite (mult_comm _ (pos N)).
    assert (Hn : (pos N / pos N) = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos N).
    apply (pos_is_pos).
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hn.
    rewrite mult_1_r.
    reflexivity.
    rewrite Hb; trivial.
    rewrite dec_quotients.
    rewrite (mult_comm a _).
    rewrite (mult_comm b _).
    rewrite <- (semiring_distr Q).
    rewrite <- E3.
    rewrite mult_assoc.
    rewrite (mult_comm _ x).
    rewrite <- mult_assoc.
    assert (H1 : (Qmult (pos N) (pos N))
                / (Qmult (pos N) (pos N)) = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < Qmult (pos N) (pos N)).
    apply pos_mult_compat; apply pos_is_pos.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity. 
    rewrite H1.
    rewrite mult_1_r.
    reflexivity.
    apply lt_ne_flip.
    apply pos_is_pos.
    apply lt_ne_flip.
    apply pos_is_pos.
  - apply imply_le.
    intros Hx.
    unfold pred_multQ.
    apply pred_plus_pr.
    apply pred_plus_pr in Hx.
    revert Hx; apply (Trunc_ind _); 
    intros (a,(b,(E1,(E2,E3)))).
    apply tr.
    exists (Qmult (pos N) a), (Qmult (pos N) b).
    repeat split.
    unfold pred_multQ in E1.
    trivial.
    unfold pred_multQ in E2.
    trivial.
    rewrite E3.
    rewrite (semiring_distr Q).
    reflexivity. 
+ apply sum_n_moy_prob.
+ unfold mon_opens. 
  intros f g Hfg.
  intros q Hq. 
  unfold random_aux in *; simpl in *.
  unfold pred_multQ in *.
  revert Hq. 
  apply RC_mon with Qle.
  intros x y; apply (antisymmetry Qle). 
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply sum_n_moy_aux_mon.
  trivial.
+ intros F q Hq.
  simpl in Hq; unfold pred_multQ in Hq.
  apply top_le_enumerable_sup.
  assert (H : (sum_n_moy_aux N
           (λ x, RllubPos (λ n, F n x))) = 
             RllubPos (fun n => sum_n_moy_aux N 
           (λ x, F n x))).
  apply (antisymmetry Rllepos).
  - clear Hq.
    induction N; 
    intros v Hv.
    apply top_le_enumerable_sup.
    unfold semi_decide, toRlseq.
    * simpl in Hv.
      apply tr.
      exists 0.
      simpl; trivial. 
    * simpl in Hv. 
      unfold semi_decide, toRlseq in *.
      unfold SDseq_Rlow, semi_decide_exists, 
        semi_decide in *.
      apply pred_plus_pr in Hv.
      revert Hv; apply (Trunc_ind _).
      intros (e1,(e2,(E1,(E2,E3)))).
      apply top_le_enumerable_sup in E1.
      apply IHN in E2.
      apply top_le_enumerable_sup in E2.
      unfold semi_decide, toRlseq in E2.
      apply top_le_enumerable_sup.
      unfold semi_decide, toRlseq.
      revert E1; apply (Trunc_ind _); 
      intros (k1,E1).
      revert E2; apply (Trunc_ind _); 
      intros (k2,E2).
      apply tr.
      simpl.  
      destruct (decide (k1 < k2)).
      exists k2.
      apply pred_plus_pr.
      apply tr; exists e1, e2.
      repeat split; trivial.
      revert E1; apply RC_mon with Qle.
      intros x y; apply (antisymmetry Qle). 
      intros x y; apply orders.le_or_lt.
      reflexivity.
      assert (H : F k1 <= F k2).
      apply seq_increasing_le.
      apply lt_le; trivial.
      apply H.
      exists k1.
      apply pred_plus_pr.
      apply tr; exists e1, e2.
      repeat split; trivial.
      revert E2; apply RC_mon with Qle.
      intros x y; apply (antisymmetry Qle). 
      intros x y; apply orders.le_or_lt.
      reflexivity.
      apply sum_n_moy_aux_mon.
      assert (H : F k2 <= F k1).
      apply seq_increasing_le.
      apply not_lt_le_flip in n; trivial.
      apply H.
  - clear Hq.
    induction N; 
    intros v Hv.
    apply top_le_enumerable_sup in Hv.
    unfold semi_decide, toRlseq in *.
    * simpl. 
      revert Hv; apply (Trunc_ind _).
      intros (n,Hn).
      simpl in Hn; trivial.
    * simpl; unfold semi_decide, toRlseq in *.
      unfold SDseq_Rlow, semi_decide_exists, 
             semi_decide in *.
      apply pred_plus_pr.
      apply top_le_enumerable_sup in Hv.
      unfold semi_decide, toRlseq in Hv.
      revert Hv; apply (Trunc_ind _).
      intros (e,E). simpl in E.
      apply pred_plus_pr in E.
      revert E; apply (Trunc_ind _); 
      intros (e1,(e2,(E1,(E2,E3)))).
      apply tr.
      exists e1, e2.
      repeat split. 
      apply top_le_enumerable_sup.
      apply tr; exists e; trivial.
      revert E2; apply RC_mon with Qle.
      intros x y; apply (antisymmetry Qle). 
      intros x y; apply orders.le_or_lt.
      reflexivity.
      apply sum_n_moy_aux_mon.
      intros x.
      apply (RllubPos_lub (fun n => F n x) e).
      trivial.
  - rewrite H in Hq.
    apply top_le_enumerable_sup in Hq.
    unfold semi_decide, toRlseq in Hq.
    unfold semi_decide, toRlseq.
    simpl; unfold pred_multQ; simpl.
    trivial. 
Defined.   