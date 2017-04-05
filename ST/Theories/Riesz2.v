
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

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Appr.
              
Set Implicit Arguments.


Definition Riesz2 (A : hSet): Val A -> IntPos A. 
Proof.
intros mm.
exists (fun f => RllubPos (fun n => 
         appr f n mm)); red.
+ apply (antisymmetry le).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    rewrite appr_0; intros s Hs; trivial.
  - transitivity (appr (fzero A) 0 mm). 
    rewrite appr_0; intros s Hs; trivial.
    generalize (RllubPos_lub (λ n : nat, appr
                    (fzero A) n mm) 0); trivial.
+ intros f g.
  apply appr_add.  
+ apply Rllub_le.
  intros n; unfold toRlseq.
  apply appr_prob.
+ intros f g Hfg. 
  apply Rllub_mon. 
  intros n. 
  unfold toRlseq.
  apply appr_mon_f; trivial.
Defined.  

