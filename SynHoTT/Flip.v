
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.interfaces.rationals
               partiality
               sierpinsky
               dedekind
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.premetric
               HoTT.Classes.theory.rings
               HoTT.Classes.orders.semirings
               HoTT.Classes.orders.rings
               HoTT.Classes.implementations.assume_rationals
               HoTT.Classes.theory.dec_fields.

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export Rlow Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Giry Cpo
               Interp.
              
Set Implicit Arguments.


(** * Flip coin: IntPos bool
 
   fun f: bool -> RlowPos  => (1/2) (f true) + 
                           (1/2) (f false)
*)

Definition flip : IntPos bool. 
Proof.
exists (fun f => (Rlow_mult_q 2%mc (f true) +
                  Rlow_mult_q 2%mc (f false))).
+ unfold Mdef. 
  assert (ho : forall (A:hSet) x, 
       (fzero A x) = RlP_0).
  intros A x; reflexivity.
  repeat rewrite ho.
  rewrite Rlow_mult_q_RlP_0.
  unfold plus; rewrite RlPPlus_left_id.
  reflexivity. 
+ intros f g.
  assert (Hdistr : forall (A:hSet) p f g (x:A), 
           RlP_plus (Rlow_mult_q p (f x)) 
                    (Rlow_mult_q p (g x)) = 
           Rlow_mult_q p (f x + g x)).
  intros A p ff gg x.
  apply (antisymmetry le).
  - intros s Hs.
    apply pred_plus_pr in Hs.
    simpl.
    apply pred_plus_pr.
    revert Hs; apply (Trunc_ind _).
    intros (rr,(ss,(E1,(E2,E3)))).
    unfold Rlow_mult_q in *; simpl in *; 
    unfold pred_multQ in *; simpl in *.
    apply tr.
    exists (pos p * rr), (pos p * ss).
    repeat split; trivial.
    rewrite E3.
    rewrite (semiring_distr Q).
    reflexivity.
  - intros s Hs.
    simpl in Hs; 
    apply pred_plus_pr in Hs.
    apply pred_plus_pr.
    revert Hs; apply (Trunc_ind _).
    intros (rr,(ss,(E1,(E2,E3)))).
    apply tr.
    exists (rr * / pos p), (ss * / pos p).
    repeat split.
    unfold Rlow_mult_q; simpl; 
    unfold pred_multQ; simpl.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos p)).
    assert (Hp1 : pos p / pos p = 1%mc).
    transitivity (1/1)%mc.
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : Qzero < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hp1.
    rewrite mult_1_r; trivial.
    unfold Rlow_mult_q; simpl; 
    unfold pred_multQ; simpl.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos p)).
    assert (Hp1 : pos p / pos p = 1%mc).
    transitivity (1/1)%mc.
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : Qzero < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hp1.
    rewrite mult_1_r; trivial.
    rewrite dec_quotients.
    rewrite (mult_comm rr _).
    rewrite (mult_comm ss _).
    rewrite <- (semiring_distr Q).
    rewrite <- E3.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    assert (H1: (/ (pos p * pos p) * 
                  pos p * pos p) = 1%mc).
    rewrite <- mult_assoc.
    rewrite mult_comm.
    transitivity (1/1)%mc.
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0%mc < pos p *  pos p).
    apply pos_mult_compat; apply p.
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
    apply p.
    apply lt_ne_flip.
    apply p.
  - rewrite <- Hdistr.
    rewrite <- Hdistr.
    unfold plus. rewrite (RlPPlus_comm 
     (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g true)) 
     (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g false))).
    unfold plus;
    rewrite RlPPlus_assoc.
    rewrite  <- (RlPPlus_assoc (Rlow_mult_q 
                   (Qpos_plus 1%mc 1%mc) (f true))
        (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g true))
        (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (f false))).
    rewrite (RlPPlus_comm 
     (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g false))
     (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g true))).
    rewrite <- RlPPlus_assoc. 
    rewrite (RlPPlus_comm 
     (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g true))
     (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (f false))).
    rewrite RlPPlus_assoc.
    rewrite RlPPlus_assoc.
    rewrite RlPPlus_assoc.
    reflexivity.
+ unfold Mprob.
  assert (H1 : forall (A : hSet) x, 
                fone A x = RlP_1).
  intros A x; reflexivity.
  repeat rewrite H1. 
  intros s Hs.
  apply pred_plus_pr in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (a,(b,(E1,(E2,E3)))).
  unfold Rlow_mult_q in *; simpl in *; 
  unfold pred_multQ in *.
  unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
  destruct (dec (pos 2 * a < Qone)%mc).
  destruct (dec (pos 2 * b < Qone)%mc).
  destruct (dec (s < Qone)).
  apply top_greatest.
  assert (Hs1 : s < Qone).
  rewrite E3.
  apply le_lt_trans with ((1/2)*(pos 2 * a) +
                          (1/2)*(pos 2 * b))%mc.
  apply plus_le_compat.
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite (mult_1_l).
  rewrite (mult_comm (/2)%mc).
  assert (H2 : (pos 2 / 2)%mc = Qone).
  transitivity (1/1)%mc.
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : Qzero < 2%mc).
  apply lt_0_2.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.  
  rewrite H2.
  rewrite mult_1_r; reflexivity.
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite (mult_1_l).
  rewrite (mult_comm (/2)%mc).
  assert (H2 : (pos 2 / 2)%mc = 1%mc).
  transitivity (1/1)%mc.
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : Qzero < 2%mc).
  apply lt_0_2.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.  
  rewrite H2.
  rewrite mult_1_r; reflexivity.
  rewrite <- (semiring_distr Q).
  apply lt_le_trans with (1 / 2 * (1 + 1))%mc.
  apply pos_mult_lt_l.
  rewrite mult_1_l.
  apply dec_fields.pos_dec_recip_compat.
  apply lt_0_2.
  apply plus_lt_compat; trivial.
  rewrite mult_comm.
  rewrite mult_assoc.
  rewrite mult_1_r.
  assert (Hp2 : (2 / 2)%mc = 1%mc).
  transitivity (1/1)%mc.
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : (Qzero < 2)%mc).
  apply lt_0_2.
  case (HF Hp).
  apply lt_ne_flip.
  apply lt_0_1.
  rewrite mult_comm.
  reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.
  rewrite Hp2.
  reflexivity. 
  case (n Hs1).
  apply not_bot in E2; case E2.
  apply not_bot in E1; case E1.
+ intros f g Hfg.
  assert (H : Rlle (Rlow_mult_q 2%mc (f true) + Rlow_mult_q 2%mc (f false))
        (RlP_plus (Rlow_mult_q 2%mc 
              (f true)) (Rlow_mult_q 2%mc (g false)))).
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply Rlow_mon.
  reflexivity.
  apply Hfg.
  assert (H' : Rlle (RlP_plus (Rlow_mult_q 2%mc 
              (f true)) (Rlow_mult_q 2%mc (g false)))
         (Rlow_mult_q 2%mc (g true) + Rlow_mult_q 2%mc (g false))).
  rewrite RlPPlus_comm.
  unfold plus; rewrite (RlPPlus_comm 
       (Rlow_mult_q (Qpos_plus 1%mc 1%mc) (g true))).    
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply Rlow_mon.
  reflexivity.
  apply Hfg.
  unfold Rlle in *; auto.
+ intros F q Hq.
  apply top_le_enumerable_sup in Hq.
  apply top_le_enumerable_sup.
  revert Hq; apply (Trunc_ind _); 
  intros (m,E).
  unfold semi_decide, semi_decide_exists, 
       semi_decide, semi_decide_conj in *.
  apply top_le_enumerable_sup in E.
  revert E; apply (Trunc_ind _); intros (p,Hp).
  unfold semi_decide, semi_decide_sier in Hp.
  apply top_le_meet in Hp.
  destruct Hp as (E1,E2).
  apply top_le_meet in E2. 
  destruct E2 as (E2,E3).
  unfold decidable_semi_decide in *.
  unfold Rlow_mult_q in E1,E2.
  simpl in *.
  unfold pred_multQ in *.
  unfold semi_decide, SDseq_Rlow,
  semi_decide_exists in *.
  apply top_le_enumerable_sup in E1.
  apply top_le_enumerable_sup in E2.
  revert E1; apply (Trunc_ind _); intros (e1,E1).
  revert E2; apply (Trunc_ind _); intros (e2,E2).
  apply tr; unfold toRlseq.
  unfold semi_decide, toRlseq in *.
  destruct (dec (e1 < e2)).
  exists e2.
  apply pred_plus_pr.
  apply tr.
  exists m, p.
  repeat split; trivial.
  revert E1; apply Rlow_mon.
  reflexivity. 
  assert (H : fle (F e1) (F e2)).
  apply seq_increasing_le.
  apply lt_le; trivial.
  apply H.
  destruct (dec (q = m + p)).
  trivial.
  apply not_bot in E3; case E3.
  exists e1.
  apply pred_plus_pr.
  apply tr.
  exists m, p.
  repeat split; trivial.
  revert E2; apply Rlow_mon.
  reflexivity. 
  assert (H : fle (F e2) (F e1)).
  apply seq_increasing_le.
  apply not_lt_le_flip in n; trivial.
  apply H.
  destruct (dec (q = m + p)).
  trivial.
  apply not_bot in E3; case E3. 
Defined.  

Definition ftrue : mf bool := fun x=>match x with
                | true => RlP_1
                | false => RlP_0
end.

Definition ffalse : mf bool := fun x=>match x with
                | true => RlP_0
                | false => RlP_1
end.

Definition otrue : OS bool := fun x=>match x with
                | true => SierTop
                | false => SierBot
end.

Definition ofalse : OS bool := fun x=>match x with
                | true => SierTop
                | false => SierBot
end.


Lemma flip_true : (flip ftrue) = 
                   Rlow_mult_q 2%mc RlP_1.
Proof.
unfold flip; simpl.
rewrite Rlow_mult_q_RlP_0.
unfold plus; 
rewrite RlPPlus_comm.
rewrite RlPPlus_left_id.
reflexivity. 
Qed. 

Lemma flip_false : (flip ffalse) = 
                   Rlow_mult_q 2%mc RlP_1.
Proof.
unfold flip; simpl.
rewrite Rlow_mult_q_RlP_0.
unfold plus; 
rewrite RlPPlus_left_id.
reflexivity. 
Qed. 

Lemma ok_flip : forall f : bool -> RlowPos, 
            ok (Rlow_mult_q 2%mc (f true) + 
                Rlow_mult_q 2%mc (f false)) flip f.
Proof.
intros b. 
unfold ok. 
intros x Hx.
apply pred_plus_pr in Hx.
revert Hx; apply (Trunc_ind _); 
intros (e1,(e2,(E1,(E2,E3)))).
simpl; apply pred_plus_pr.
apply tr.
exists e1, e2.
unfold Rlow_mult_q in *;
simpl in *. 
repeat split; trivial.
Qed.




 


  
