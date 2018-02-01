
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.interfaces.rationals
               partiality
               sierpinsky
               dedekind
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.rings
               HoTT.Classes.theory.dec_fields
               HoTT.Classes.orders.orders
               HoTT.Classes.orders.semirings
               HoTT.Classes.orders.dec_fields
               HoTT.Classes.theory.premetric
               HoTT.Classes.implementations.assume_rationals.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties HIT.quotient.

Require Import Rlow
               Functions
               Valuations
               Cpo.
               
Set Implicit Arguments.

Section Integrals.

(** * Lower Integrals on A: a lower integra is a semi_continuous map 
and defined in mf(A) which is valued in the positive lower reals *)

Definition M (A : hSet) := mf A -> RlowPos. 

Definition Mplus {A} : Plus (M A). 
intros I J f.
specialize (I f).
specialize (J f).
refine (RlP_plus I J).
Defined. 

Definition Mdef {A} (I : M A) :=
              (I (fzero A)) = RlP_0.

Definition Mprob {A} (I : M A) :=
               Rlle (I (fone A)) RlP_1. 

Definition Mstable_add {A} (I : M A) :=
  forall f g: mf A, (I (fplus f g)) = ((I f)+(I g)).

Definition Mpos {A} (I : M A) :=
  forall (f : mf A), (forall x, Rlle RlP_0 (f x)) -> Rlle RlP_0 (I f).

Definition Mmon {A} (I : M A) := 
   forall f g : mf A,  fle f g -> Rlle (I f) (I g).

Definition Mcont {A} : (M A) -> Type := fun I => 
            forall (f : IncreasingSequence (mf A)), 
           Rlle (I (Cpo.lub f)) (RllubPos (fun n => I (f n))).

(** IntPos is a semigroup for plus *)
Global Instance MPos_semi_group {A} : SemiGroup (M A)
                                          (Aop := @Mplus A). 
Proof. 
split. 
+ apply _.   
+ hnf. intros x y z.
  unfold sg_op, plus_is_sg_op.
  apply path_forall; intros q.
  unfold Mplus. 
  rewrite RlPPlus_assoc.
  reflexivity.   
Defined. 

(** Integrals are definite, sigma-additive, monotonic,
associated to probability and continuous *)
Record IntPos (A : hSet) : Type := 
  {I :> mf A -> RlowPos;
   I_def : Mdef I;
   I_add : Mstable_add I;
   I_prob : Mprob I;
   I_mon : Mmon I; 
   I_cont : Mcont I
}.

Hint Resolve I_def I_add I_prob I_mon. 


(** IntPos in hSet *) 

Lemma IntPos_eq0 {A} (J H : IntPos A) :
          I J = I H -> J = H.
Proof. 
intros Hx.
destruct J; destruct H; simpl in Hx;
destruct Hx.
assert (Hdef : I_def0 = I_def1).
apply path_ishprop.
assert (Hadd : I_add0 = I_add1).
apply path_ishprop.
assert (Hmon : I_mon0 = I_mon1).
apply path_ishprop.
assert (Hprob : I_prob0 = I_prob1).
apply path_ishprop.
assert (Hcont : I_cont0 = I_cont1).
apply path_ishprop.
rewrite Hdef, Hadd, Hmon, Hprob, Hcont.
reflexivity. 
Qed. 
 
Instance IntPos_isset {A} : IsHSet (IntPos A).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => I a = I b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply IntPos_eq0;apply E.
Qed.

Definition IntPos_stable_conv {A} (I J : IntPos A) 
             (p q : Q+) (Hpq : Qle (pos (p + q)) Qone) : IntPos A.
Proof.
exists (fun f => Rlow_mult_q (Qpos_one/p) (I f) 
               + Rlow_mult_q (Qpos_one/q) (J f)).
+ red; repeat rewrite I_def.
  repeat (rewrite Rlow_mult_q_RlP_0). 
  unfold plus; 
  rewrite RlPPlus_left_id.
  reflexivity.
+ intros f g.
  repeat rewrite I_add.
  apply (antisymmetry le).
  - intros s Hs.
    apply pred_plus_pr in Hs.
    apply pred_plus_pr.
    revert Hs; apply (Trunc_ind _); 
    intros (e1,(e2,(E1,(E2,E3)))).
    simpl in E1, E2.
    unfold pred_multQ in E1, E2.
    apply pred_plus_pr in E1.
    apply pred_plus_pr in E2.
    revert E1; apply (Trunc_ind _); 
    intros (e11,(e12,(E11,(E12,E13)))).
    revert E2; apply (Trunc_ind _); 
    intros (e21,(e22,(E21,(E22,E23)))).  
    apply tr.
    exists ((pos p * e11) + (pos q * e21)), 
            (pos p * e12 + pos q * e22).
    assert (H1 : forall p e, (pos (1 / p) * (pos p * e) = e)%mc).
    intros z e.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos z)).
    assert (H : pos z * pos (Qpos_one / z) =
            (pos z) / (pos z)).
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos z)).
    rewrite mult_1_l.
    reflexivity.
    rewrite H.  
    assert (Hp1 : pos z / pos z = 1%mc).
    transitivity ((1/1)%mc).
    apply equal_dec_quotients.
    apply orders.not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : Qlt Qzero (pos z)).
    apply z.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    repeat split; trivial.
    repeat split; trivial;
    rewrite Hp1;
    rewrite mult_1_r;
    reflexivity.
    repeat split; trivial.
    apply pred_plus_pr.
    apply tr.
    exists (pos p * e11), (pos q * e21).
    simpl; unfold pred_multQ.
    repeat split; trivial.
    rewrite H1; trivial.
    rewrite H1; trivial.
    apply pred_plus_pr.
    apply tr.
    exists (pos p * e12), (pos q * e22).
    repeat split; trivial;
    simpl; unfold pred_multQ;
    rewrite H1; trivial.
    rewrite E3.
    assert (F1 : e1 = (pos p) * (e11 + e12)).
    apply (left_cancellation_ne_0 mult (1 / pos p)%mc).
    apply apartness.apart_ne.
    apply pseudo_order_lt_apart_flip.
    rewrite mult_1_l.
    apply pos_dec_recip_compat.
    apply p.
    transitivity ((pos p / pos p) * (e11 + e12)).
    rewrite E13.
    assert (Hp1 : pos p / pos p = 1%mc).
    transitivity (1/1)%mc.
    apply equal_dec_quotients.
    apply orders.not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0%mc < (pos p)).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    repeat split; trivial.
    repeat split; trivial;
    rewrite Hp1.
    rewrite mult_1_l; 
    reflexivity.
    rewrite mult_1_l.
    rewrite (mult_assoc (/ pos p) (pos p) (e11 + e12)).
    rewrite mult_comm.
    rewrite (mult_comm (pos p)).
    rewrite mult_comm.
    reflexivity.
    rewrite F1.
    assert (F2 : e2 = (pos q) * (e21 + e22)).
    apply (left_cancellation_ne_0 mult (1 / pos q)%mc).
    apply apartness.apart_ne.
    apply pseudo_order_lt_apart_flip.
    rewrite mult_1_l.
    apply pos_dec_recip_compat.
    apply q.
    transitivity ((pos q / pos q) * (e21 + e22)).
    rewrite E23.
    assert (Hp1 : pos q / pos q = 1%mc).
    transitivity (1/1)%mc.
    apply equal_dec_quotients.
    apply orders.not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : (0 < pos q)%mc).
    apply q.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    repeat split; trivial.
    repeat split; trivial;
    rewrite Hp1.
    rewrite mult_1_l; 
    reflexivity.
    rewrite mult_1_l.
    rewrite (mult_assoc (/ pos q) (pos q) (e21 + e22)).
    rewrite mult_comm.
    rewrite (mult_comm (pos q)).
    rewrite mult_comm.
    reflexivity.
    rewrite F2.
    repeat rewrite (semiring_distr Q).
    rewrite plus_assoc.
    rewrite plus_assoc.
    transitivity (pos p * e11 + 
         (pos q * e21 + pos p * e12) + pos q * e22).
    rewrite (plus_comm (pos q * e21) 
                       (pos p * e12)).   
    rewrite plus_assoc.
    reflexivity.
    rewrite plus_assoc.
    reflexivity.  
  - intros s Hs.
    apply pred_plus_pr in Hs.
    apply pred_plus_pr.
    revert Hs; apply (Trunc_ind _); 
    intros (e1,(e2,(E1,(E2,E3)))).
    simpl in E1, E2.
    unfold pred_multQ in E1, E2.
    apply pred_plus_pr in E1.
    apply pred_plus_pr in E2.
    revert E1; apply (Trunc_ind _); 
    intros (e11,(e12,(E11,(E12,E13)))).
    revert E2; apply (Trunc_ind _); 
    intros (e21,(e22,(E21,(E22,E23)))).  
    apply tr.
    exists (e11 + e21), 
            (e12 + e22).
    (* H1 *)
    repeat split.
    simpl; unfold pred_multQ.
    apply pred_plus_pr.
    apply tr.
    exists (pos (1 / p)%mc * e11), 
            (pos (1 / p)%mc * e21).
    repeat split; trivial.
    repeat rewrite (semiring_distr Q).
    reflexivity.
    simpl; unfold pred_multQ.
    apply pred_plus_pr.
    apply tr.
    exists (pos (1 / q)%mc * e12), 
            (pos (1 / q)%mc * e22).
    repeat split; trivial.
    repeat rewrite (semiring_distr Q).
    reflexivity.    
    rewrite E3, E13, E23.
    transitivity (e11 + (e21 + e12) + e22).
    rewrite (plus_comm e21 e12).
    rewrite plus_assoc. rewrite plus_assoc.
    reflexivity.
    rewrite plus_assoc. rewrite plus_assoc.
    reflexivity.
+ unfold Mprob. 
  assert (Ho : Rlle (Rlow_mult_q (1 / p)%mc RlP_1 
             + Rlow_mult_q (1 / q)%mc RlP_1) RlP_1).
  intros v Hv.
  apply pred_plus_pr in Hv.
  revert Hv; apply (Trunc_ind _).
  intros (a,(b,(E1,(E2,E3)))).
  simpl in *; unfold pred_multQ in *.
  unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
  destruct (dec (pos (1 / p)%mc * a < Qone)).
  destruct (dec (pos (1 / q)%mc * b < Qone)).
  destruct (dec (v < Qone)).
  trivial.
  assert (Hf : v < Qone).
  rewrite E3.
  assert (H1 : pos p * (1 / pos p)%mc * a < pos p).
  apply le_lt_trans with (pos p * (pos (1 / p)%mc * a)).
  rewrite mult_assoc.
  rewrite mult_assoc.
  rewrite mult_assoc.
  reflexivity.
  apply lt_le_trans with (pos p * Qone).
  apply pos_mult_lt_l.
  apply p; trivial.
  trivial.
  rewrite mult_1_r; reflexivity. 
  assert (H2 : pos q * (1 / pos q)%mc * b < pos q).
  apply le_lt_trans with (pos q * (pos (1 / q)%mc * b)).
  rewrite mult_assoc.
  rewrite mult_assoc.
  rewrite mult_assoc.
  reflexivity.
  apply lt_le_trans with (pos q * Qone).
  apply pos_mult_lt_l.
  apply q; trivial.
  trivial.
  rewrite mult_1_r; reflexivity. 
  rewrite mult_assoc in H1, H2.
  rewrite mult_comm in H1, H2.
  rewrite mult_1_r in H1, H2.
  assert (Hp1 : forall r, pos r / pos r = Qone).
  intros r.
  transitivity (1/1)%mc.
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : Qzero < pos r).
  apply r.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.  
  rewrite Hp1 in H1, H2.
  rewrite mult_1_r in H1, H2.
  apply lt_le_trans with (pos p + pos q).
  apply plus_lt_compat; trivial.
  apply Hpq.
  case (n Hf).
  apply not_bot in E2; case E2.
  apply not_bot in E1; case E1. 
  intros v Hv.
  apply Ho.
  apply pred_plus_pr in Hv.
  apply pred_plus_pr.
  revert Hv; apply (Trunc_ind _); 
  intros (a,(b,(E1,(E2,E3)))).
  apply tr. 
  exists a, b.
  repeat split; trivial.
  revert E1; apply Rlow_mon. 
  reflexivity.
  intros w Hw.
  simpl in Hw; 
  unfold pred_multQ in Hw.
  assert (elt RlP_1 (pos (1 / p)%mc * w)).
  revert Hw; apply Rlow_mon.
  reflexivity.
  apply I_prob.
  apply H.
  revert E2; apply Rlow_mon.
  reflexivity.
  intros w Hw.
  simpl in Hw; 
  unfold pred_multQ in Hw.
  assert (elt RlP_1 (pos (1 / q)%mc * w)).
  revert Hw; apply Rlow_mon.
  reflexivity.
  apply I_prob.
  apply H.
+ intros f g Hfg.
  assert (Hh: 
     Rlle (Rlow_mult_q (Qpos_one / p) (I f) 
             + Rlow_mult_q (Qpos_one / q) (J f))
            (RlP_plus (Rlow_mult_q (1 / p)%mc 
      (I f)) (Rlow_mult_q (1 / q)%mc (J g)))). 
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply Rlow_mon. 
  reflexivity.
  apply I_mon;
  apply Hfg.
  assert (Hh2 : Rlle (RlP_plus (Rlow_mult_q (1%mc / p) (I f)) 
                (Rlow_mult_q (1%mc / q) (J g)))
     (Rlow_mult_q (Qpos_one / p) (I g) + Rlow_mult_q (Qpos_one / q) (J g))).
  rewrite RlPPlus_comm. 
  unfold plus; rewrite (RlPPlus_comm _
       (Rlow_mult_q (1 / q)%mc (J g))).    
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply Rlow_mon.
  reflexivity.
  apply I_mon;
  apply Hfg.
  unfold Rlle in *; auto.
+ intros F r Hr.
  apply top_le_enumerable_sup in Hr.
  apply top_le_enumerable_sup.
  revert Hr; apply (Trunc_ind _); 
  intros (m,E).
  unfold semi_decide, semi_decide_exists, 
       semi_decide, semi_decide_conj in *.
  apply top_le_enumerable_sup in E.
  revert E; apply (Trunc_ind _); intros (s,Hs).
  unfold semi_decide, semi_decide_sier in Hs.
  apply top_le_meet in Hs.
  destruct Hs as (E1,E2).
  apply top_le_meet in E2. 
  destruct E2 as (E2,E3).
  unfold decidable_semi_decide in *.
  unfold Rlow_mult_q in E1,E2.
  simpl in *.
  unfold pred_multQ in *.
  unfold semi_decide, SDseq_Rlow,
  semi_decide_exists in *.
  assert (E1' : elt (RllubPos (fun n => I (fun x : A => F n x))) 
    (pos (1 / p)%mc * m)).
  revert E1.
  apply Rlow_mon.
  reflexivity.
  apply I_cont. 
  apply top_le_enumerable_sup in E1'.
  assert (E2' : elt (RllubPos (fun n => J (fun x : A => F n x))) 
    (pos (1 / q)%mc * s)).
  revert E2.
  apply Rlow_mon.
  reflexivity.
  apply I_cont. 
  apply top_le_enumerable_sup in E2'. 
  clear E1 E2.
  revert E1'; apply (Trunc_ind _); intros (e1,E1).
  revert E2'; apply (Trunc_ind _); intros (e2,E2).
  apply tr; unfold toRlseq.
  unfold semi_decide, toRlseq in *.
  destruct (dec (e1 < e2)).
  exists e2.
  apply pred_plus_pr.
  apply tr.
  exists m, s.
  repeat split; trivial.
  revert E1; apply Rlow_mon.
  reflexivity. 
  assert (H : fle (F e1) (F e2)).
  apply seq_increasing_le.
  apply lt_le; trivial.
  apply I_mon.
  apply H.
  destruct (dec (r = m + s)).
  trivial.
  apply not_bot in E3; case E3.
  exists e1.
  apply pred_plus_pr.
  apply tr.
  exists m, s.
  repeat split; trivial.
  revert E2; apply Rlow_mon.
  reflexivity. 
  assert (H : fle (F e2) (F e1)).
  apply seq_increasing_le.
  apply not_lt_le_flip in n; trivial.
  apply I_mon.
  apply H.
  destruct (dec (r = m + s)).
  trivial.
  apply not_bot in E3; case E3. 
Defined.  


Global Instance Le_fun_IntPos {A B:hSet} : Le (A -> IntPos B).
Proof.
intros f g.
refine (forall x u, Rlle ((f x) u) ((g x) u)).
Defined.

Global Instance le_Intpos {A:hSet} : Le (IntPos A) := 
             fun I J => forall f, Rlle (I f) (J f).

Definition IntPos_cpobot  {A:hSet} : IntPos A.
Proof.
exists (fun f => RlP_0).
+ hnf; reflexivity.
+ intros J K.
  transitivity (RlP_plus RlP_0 RlP_0).
  rewrite RlPPlus_left_id.
  reflexivity.
  reflexivity.  
+ hnf.
  intros q Hq; unfold semi_decide in *. 
  simpl in *; unfold semi_decide, Rllt_semi_dec, 
        decidable_semi_decide in *.
  destruct (dec (q < Qzero)%mc).
  destruct (dec (q < Qone)%mc).
  trivial.
  assert (Hnn : q < 1%mc).
  transitivity Qzero.
  trivial.
  apply semirings.lt_0_1.
  case (n Hnn).
  destruct (dec (q < Qone)).
  apply top_greatest.
  trivial.
+ intros a b C.
  unfold Rlle; auto.
+ intros f q Hq.
  simpl in Hq.
  unfold semi_decide, Rllt_semi_dec, 
        decidable_semi_decide in Hq.
  destruct (dec (q < Qzero)).
  apply (RllubPos 
    (fun n : nat => RlP_0)); 
  trivial.
  apply not_bot in Hq; case Hq.
Defined.

Global Instance PO_Intpos {A:hSet} : 
                PartialOrder (@le_Intpos A).
Proof.
split.
+ apply IntPos_isset.
+ intros x y; apply _.
+ constructor.
  - intros x f; unfold Rlle; auto.
  - intros f g h Hfg Hgh z.
    unfold Rlle; intros k Hk.
    assert (elt (g z) k).
    specialize (Hfg z); auto.
    specialize (Hgh z); auto.
+ intros f g Hfg Hgf.
  apply IntPos_eq0.
  apply path_forall.
  intros z; 
  apply (antisymmetry le); 
  trivial.
  specialize (Hfg z).
  auto. 
  specialize (Hgf z).
  auto. 
Defined. 
 

Definition IntPos_cpolub  {A:hSet} : 
         (IncreasingSequence (IntPos A)) -> IntPos A.
Proof.
intros F.
exists (fun f => RllubPos (fun n => F n f)).
+ hnf. 
  apply (antisymmetry Rllepos).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    rewrite I_def.
    intros H; trivial.
  - assert (H0 : RlP_0 = (F O) (fzero A)).
    rewrite I_def; simpl.
    reflexivity.
    rewrite H0.
    apply (RllubPos_lub 
       (fun n => (F n) (fzero A)) 0).
+ intros f g.
  apply (antisymmetry Rllepos).
  intros s Hs.
  apply top_le_enumerable_sup in Hs.
  apply pred_plus_pr.
  revert Hs; apply (Trunc_ind _); 
  intros (n,Hn).
  unfold semi_decide, toRlseq in Hn.
  rewrite I_add in Hn.
  apply pred_plus_pr in Hn.
  revert Hn; apply (Trunc_ind _).
  intros (a,(b,(E1,(E2,E3)))).
  apply tr.
  exists a, b.
  repeat split; trivial.
  apply top_le_enumerable_sup.
  apply tr; exists n; trivial.
  apply top_le_enumerable_sup.
  apply tr; exists n; trivial.
  intros s Hs.
  apply top_le_enumerable_sup.
  apply pred_plus_pr in Hs.
  revert Hs; apply (Trunc_ind _); 
   intros (a,(b,(E1,(E2,E3)))).
  unfold semi_decide, toRlseq.
  apply top_le_enumerable_sup in E1.
  apply top_le_enumerable_sup in E2.
  revert E1; apply (Trunc_ind _); 
  intros (x,Ha).
  revert E2; apply (Trunc_ind _); 
  intros (x',Hb).
  apply tr.
  destruct (dec (x < x')).
  exists x'.
  rewrite I_add.
  apply pred_plus_pr.
  apply tr.
  exists a, b.
  repeat split; trivial.
  unfold semi_decide, toRlseq in Ha.
  revert Ha; apply Rlow_mon. 
  reflexivity.
  assert (HF: le_Intpos (F x) (F x')).
  apply seq_increasing_le.
  apply orders.lt_le; trivial.
  apply HF.
  exists x.
  rewrite I_add.
  apply pred_plus_pr.
  apply tr.
  exists a, b.
  repeat split; trivial.
  unfold semi_decide, toRlseq in Hb.
  revert Hb; apply Rlow_mon.
  reflexivity.
  assert (HF: le_Intpos (F x') (F x)).
  apply seq_increasing_le.
  apply le_iff_not_lt_flip in n; 
  trivial.
  apply HF.
+ hnf.
  intros q Hq.
  apply top_le_enumerable_sup in Hq.
  revert Hq; simpl; apply (Trunc_ind _).
  intros (n,Hn); unfold semi_decide, toRlseq in *.
  assert (Hk : elt RlP_1 q).
  revert Hn; apply Rlow_mon.
  reflexivity.
  apply I_prob.
  simpl in Hk; trivial.
+ intros f g Hfg.
  apply Rllub_mon.
  intros n; unfold toRlseq.
  apply I_mon; trivial.
+ intros f.
  apply Rllub_le.
  intros n.
  unfold toRlseq.
  generalize (I_cont (F n)).
  intros H; unfold Mcont in H.
  assert (H' : Rlle  
   (RllubPos (fun n0 : nat => (F n) (f n0)))
   (RllubPos (fun n0 : nat => RllubPos 
      (fun n1 : nat => (F n1) (f n0))))).
  apply Rllub_mon.
  intros m.
  unfold toRlseq.
  apply (RllubPos_lub (fun k => (F k) (f m)) n).
  intros q Hq.
  apply H'.
  apply H.
  trivial.  
Defined. 


Global Instance Cpo_IntPos {A:hSet} : cpo (IntPos A).
Proof.
exists IntPos_cpobot IntPos_cpolub.
+ intros f n x.
  unfold IntPos_cpolub; simpl.
  apply (RllubPos_lub (fun n => (f n) x) n).
+ intros f n Hfn x.
  unfold IntPos_cpolub; simpl.
  apply RllubPos_le.
  intros m; apply Hfn.
+ intros x; simpl.
  unfold IntPos_cpobot.
  intros z; simpl.
  intros q Hq.
  simpl in Hq; unfold semi_decide, Rllt_semi_dec, 
                  decidable_semi_decide in Hq.
  destruct (dec (q < Qzero)).
  apply rlpos; trivial.
  apply not_bot in Hq; case Hq.   
Defined. 

Definition fun_Increasing_comp {A B:hSet}
       (f : IncreasingSequence 
       (A -> IntPos B)) (x : A) : 
       IncreasingSequence (IntPos B).
Proof.
exists (fun n => f n x).
intros n.
destruct f as (f,Hf).
simpl; red in Hf; 
intros u; apply Hf.
Defined.

Global Instance Cpo_fun_IntPos {A B:hSet} : cpo (A -> IntPos B).
Proof.
pose (ff := (fun f:(IncreasingSequence (A -> IntPos B)) =>
       (fun x:A => lub (fun_Increasing_comp f x)))).
exists (fun x:A => cpobot) ff.
+ intros f n.
  intros x u.
  generalize (@le_lub (IntPos B) le_Intpos Cpo_IntPos
             (fun_Increasing_comp f x)).
  intros XG; apply XG.
+ intros f n.
  intros Hx x u.
  generalize (@lub_le (IntPos B) le_Intpos Cpo_IntPos
             (fun_Increasing_comp f x)).
  intros XG; apply XG.
  intros m.
  specialize (Hx m x).
  trivial.
+ intros X.
  intros f u.
  assert (Hu : le_Intpos cpobot (X f)).
  apply cpobot_bot.
  apply Hu.
Defined.

End Integrals. 