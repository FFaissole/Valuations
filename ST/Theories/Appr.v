Add Rec LoadPath "~/Documents/HoTTClasses/".
Add Rec LoadPath "~/Documents/SyntheticTopology/Spaces".
Add Rec LoadPath "~/Documents/SyntheticTopology/Theories".
Add Rec LoadPath "~/Documents/SyntheticTopology/Models".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.interfaces.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Import D_op OpenFun Valuations. 

Section Approx.

Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n).

Definition qP (n : nat) := ((qnp n) * (1 / qnp (S n))).
Definition qbp (n : nat) (b : Q+) := b * (1 / qnp n). 
Definition qb (n : nat) (b : Q) := (qn n) * b. 
Definition qfc (n : nat) := pos (qP n).


Coercion qn : nat >-> Q.
Coercion qnp : nat >-> Qpos.

Fixpoint appr_aux {A : hSet} (f : mf A) (N : nat)
         (m : Val A):= match N with
             |O => RlP_0
             |S P => m (D_op (qfc P) f) + appr_aux f P m
end.       

Fixpoint appr_os_aux {A : hSet} (f : mf A) (N : nat)
          := match N with
             |O => (fun x:A => RlP_0)
             |S P => fun x:A => (OpenFun A (D_op (qfc P) f) x +
                                 (appr_os_aux f P x))
end. 
                                            
Definition appr {A : hSet} (f : mf A) (N : nat) (m : Val A):=
  Rlow_mult_q (1 / qnp N) (appr_aux f N m).

Definition appr_os {A : hSet} (f : mf A) (N : nat) : mf A :=
           fun x:A => Rlow_mult_q (1 / qnp N) (appr_os_aux f N x).

Lemma appr_aux_0 {A : hSet} : forall N m, 
                    appr_aux (fzero A) N m = RlP_0. 
Proof.
intros N m. 
induction N. 
+ simpl; reflexivity.
+ simpl.
  rewrite IHN.
  unfold plus; rewrite RlPPlus_comm.
  rewrite RlPPlus_left_id.
  unfold D_op; simpl.
  unfold semi_decide. 
  destruct (decide
              (qn (S N) < 0)).
  - unfold qb in l.
    apply orders.lt_flip in l.
    assert (l2 : 0 < qn (S N)).
    apply pos_of_nat.
    case (l l2).
  - destruct (decide (qfc N < 0)).
    unfold qfc in *.
    assert (l' : 0 < pos (qP N)).
    apply (qP N).
    apply orders.lt_not_le_flip in l.
    apply orders.lt_le in l'.
    case (l l').
    rewrite mu_empty_op. 
    reflexivity.
Qed.
  
Lemma appr_0 {A : hSet} : forall N m, 
                  appr (fzero A) N m = RlP_0. 
Proof.
intros N m. 
unfold appr.
rewrite appr_aux_0.
rewrite Rlow_mult_q_RlP_0.
reflexivity.
Qed.

Lemma appr_add {A : hSet} : forall (f g : mf A) m,
  RllubPos (λ n : nat, appr (fplus f g) n m) =
  RllubPos (λ n : nat, appr f n m) + RllubPos (λ n : nat, appr g n m).
Proof.
intros f g mm.
transitivity (RllubPos (fun N => appr f N mm + appr g N mm)).
admit.

apply (antisymmetry le).
  - intros s hs.
    apply top_le_enumerable_sup in hs.
    revert hs; apply (Trunc_ind _); 
    unfold semi_decide, toRlseq.
    intros (m,Hm).
    apply top_le_enumerable_sup.
    apply pred_plus_pr in Hm.
    revert Hm; apply (Trunc_ind _).
    intros (m1,(m2,(Hm1,(Hm2,Hm3)))).
    apply tr.
    exists m1.
    unfold semi_decide,
      semi_decide_exists.
    apply top_le_enumerable_sup.
    apply tr.
    exists m2.
    unfold semi_decide, semi_decide_conj.
    apply top_le_meet.
    repeat split.
    unfold semi_decide, semi_decide_sier.
    apply top_le_enumerable_sup.
    apply tr. unfold semi_decide, toRlseq.
    exists m. trivial.
    unfold semi_decide, semi_decide_sier.
    apply top_le_meet. split.  
    apply top_le_enumerable_sup.
    apply tr. unfold semi_decide, toRlseq.
    exists m. trivial.
    unfold decidable_semi_decide.
    destruct (decide (s = m1 + m2)).
    apply top_greatest.
    case (n Hm3).
  - intros s hs.
    apply pred_plus_pr in hs. 
    apply top_le_enumerable_sup.
    revert hs; apply (Trunc_ind _); 
    unfold semi_decide, toRlseq in *.
    intros (a,(b,(Hab1,(Hab2,Hab3)))).
    apply top_le_enumerable_sup in Hab1.
    apply top_le_enumerable_sup in Hab2.
    revert Hab1; apply (Trunc_ind _).
    intros (a1,Ha1).
    revert Hab2; apply (Trunc_ind _).
    intros (a2,Ha2).
    unfold toRlseq in *.
    unfold semi_decide in *.
    apply tr.
    admit. 
Admitted.

 
Lemma D_op_RlP1_1 {A : hSet} : 
        forall n, D_op (qfc n) (fun x:A => RlP_1) = fun x => SierTop.
Proof.
intros n; unfold D_op.
simpl; unfold semi_decide.
destruct (decide (qfc n < 1)).
reflexivity.
assert (H1 : qfc n < 1).
unfold qfc, qP.
apply orders.le_lt_trans with (pos (qbp n n)).
apply semirings.mult_le_compat.
apply orders.lt_le.
apply (qnp n).
admit.
Admitted. 


Lemma appr_aux_prob {A : hSet} : forall N m,
         appr_aux (fone A) N m <= Rlow_mult_q N RlP_1. 
Proof. 
intros N m.
induction N. 
+ intros q Hq;
  simpl in Hq; unfold semi_decide in *;
  destruct (decide (q < 0)).
  - apply rlpos. 
    apply orders.le_lt_trans with q.
    simpl; rewrite rings.mult_1_l; 
    reflexivity.
    trivial.
  - apply not_bot in Hq; case Hq.
+ unfold appr_aux.
  rewrite D_op_RlP1_1.
  transitivity (RlP_1 + appr_aux (fone A) N m).
  unfold plus; rewrite RlPPlus_comm;
  rewrite (RlPPlus_comm RlP_1).
  apply Rllepos_plus_le_preserving.
  apply mu_prob.
  transitivity (RlP_1 + Rlow_mult_q N RlP_1).
  apply Rllepos_plus_le_preserving; trivial.
  intros z Hz.
  apply pred_plus_pr in Hz.
  revert Hz; apply (Trunc_ind _); 
  intros (a,(b,(H1,(H2,H3)))).
  rewrite H3.
  admit.  
Admitted.



Axiom Rlow_mult_q_distr : forall q r,
    Rlow_mult_q (1 / q) (Rlow_mult_q q r) = r. 


Lemma appr_prob {A : hSet} : forall N m,
         appr (fone A) N m <= RlP_1. 
Proof.
intros N m; unfold appr.
transitivity ((Rlow_mult_q (1 / qnp N))
                 (Rlow_mult_q (qnp N) RlP_1)).
intros s.
unfold Rlow_mult_q; simpl; unfold pred_multQ.
intros hs.
unfold semi_decide.
destruct (decide (pos (qnp N) * 
                 (pos (1 / qnp N) * s) < 1)).
apply top_greatest.
case n.
assert (val (rl (Rlow_mult_q (qnp N) RlP_1))
       ((pos (1 / qnp N) * s))).
revert hs; apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply appr_aux_prob.
simpl in H;
unfold pred_multQ in H;
unfold semi_decide in H; 
destruct (decide (pos (qnp N) * 
                 (' 1 * ' (/ qnp N) * s) < 1)).
trivial.
apply not_bot in H; case H.
rewrite Rlow_mult_q_distr.
reflexivity.
Qed.

Lemma appr_aux_mon_f {A : hSet} : forall n (f g: mf A) mm,
    f <= g -> appr_aux f n mm <= appr_aux g n mm.
Proof.
intros n f g m Hfg.
induction n.  
+ simpl; intros s hs; trivial.
+ simpl; transitivity (m (D_op (qfc n) f) +
                               appr_aux g n m).
  unfold plus; apply Rllepos_plus_le_preserving; 
  trivial.
  unfold plus; rewrite RlPPlus_comm;
  rewrite (RlPPlus_comm (m (D_op (qfc n) g))).
  apply Rllepos_plus_le_preserving; trivial.
  apply mu_mon.
  apply D_op_mon_f; trivial.
Qed.

Lemma appr_mon_f {A : hSet} : forall n (f g: mf A) mm,
    f <= g -> appr f n mm <= appr g n mm.
Proof.
intros n f g m Hfg.
unfold appr.
intros s; unfold Rlow_mult_q;
simpl; unfold pred_multQ.
apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply appr_aux_mon_f; trivial.
Qed.

Axiom appr_mon_n : forall (A : hSet) n m (f: mf A) mm,
    n <= m -> appr f n mm <= appr f m mm.



End Approx. 
