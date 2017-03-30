
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Riesz2.
              
Set Implicit Arguments.

Lemma Riesz_hom1 (A : hSet) : forall (Mu :Val A) U,
    Riesz1 (Riesz2 Mu) U = Mu U.
Proof.
intros Mu U.  
simpl; unfold Riesz2.
apply (antisymmetry le). 
+ apply Rllub_le. 
  intros n; unfold toRlseq.
  induction n. 
  - simpl.
    rewrite Rlow_mult_q'_RlP_0.
    simpl; intros s Hs. 
    simpl in Hs; unfold semi_decide in Hs. 
    destruct (decide (s < 0)).
    apply rlpos; trivial.
    apply not_bot in Hs; case Hs. 
  - unfold appr; rewrite appr_aux_simpl.
    rewrite Rlow_mult_q_distr.
    intros s; trivial.
    apply peano_naturals.S_neq_0. 
+ intros s Hs. 
  apply Rllub_lub with 1. 
  unfold toRlseq.
  unfold appr; rewrite appr_aux_simpl. 
  rewrite Rlow_mult_q_distr; trivial.
  apply peano_naturals.S_neq_0. 
Qed. 


Definition Riesz_hom2 (A : hSet) : forall (It : IntPos A) f,
    Riesz2 (Riesz1 It) f = It f.
Proof.
intros It.
unfold Riesz2; simpl; intros f.
apply (antisymmetry le).
+ apply Rllub_le; intros n. 
  unfold toRlseq.
  assert (H: Rlle (It (appr_os f n)) (It f)).
  apply I_mon.
  apply appr_os_inf.
  assert (H2 : Rlle (appr f n (Riesz1 It))
                    (I It (appr_os f n))).  
  rewrite appr_os_It_inf.
  intros s; trivial. 
  intros s Hs. 
  apply H, H2; trivial. 
+ generalize (I_cont It f). 
  intros Hc.  
  assert (H2 : RllubPosQP
                 (λ q : Q+, I It
                 (λ x : A, RlP_minus_q2 (f x) q)) <=
               RllubPos (λ n : nat,
                               appr f n (Riesz1 It))).
  apply RllubPosQP_le.
  intros q. 
  intros s Hs. 
  apply top_le_enumerable_sup. 
  unfold semi_decide, toRlseq. 
  apply tr.
  assert (H' : ∃ x : nat,
             val (rl (I It (appr_os f x))) s).
  assert (Hs' : exists n:nat, elt Q Qlt (It (λ x : A,
               RlP_minus_q2 (f x) (1 / qnp n))) s).
  apply I_cont_nat.
  exists q; trivial.
  destruct Hs' as (m,Hs').
  exists m. 
  revert Hs'. 
  apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_mon. 
  intros h z. 
  apply Ax2.  
  destruct H' as (n,H').
  exists n.
  revert H'. 
  apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt.
  reflexivity. 
  rewrite appr_os_It_inf. 
  intros k; trivial.    
  intros s Hs. 
  apply H2, Hc; trivial.  
Qed.
