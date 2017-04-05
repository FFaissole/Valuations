

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
               ContinuousValuations ContinuousLowerIntegrals
               D_op OpenFun Riesz1_cont Riesz2_cont.
              
Set Implicit Arguments.

Theorem Riesz_hom1 (A : hSet) : forall (Mu :ContVal A) U,
    Riesz1_cont (Riesz2_cont Mu) U = Mu U.
Proof.
intros Mu U.  
simpl; unfold Riesz2.
destruct Mu as (Mu,Hc).
simpl; rewrite Hc.
reflexivity.
Qed.  

Theorem Riesz_hom2 (A : hSet) : forall (It : ContIntPos A) f,
    Riesz2_cont (Riesz1_cont It) f = It f.
Proof.
intros It.
unfold Riesz2_cont; simpl; intros f.
destruct It as (It,Hc); simpl. 
rewrite Hc. 
reflexivity.
Qed.   
