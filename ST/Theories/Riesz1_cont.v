

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
               D_op OpenFun Riesz1.
              
Set Implicit Arguments.


(** * Formal proof of a constructive Riesz Theorem: for 
the detailed pen-and-paper proof, see Coquand-Spitters09, 
Integrals and valuations, or Vickers08, Monad of valuation 
locales *)

(** From Integrals to Valuations: 
  mu_I (U)  = I (1_U) *)
Definition Riesz1_cont (A : hSet) : ContIntPos A -> ContVal A. 
Proof. 
intros J.   
split with (Riesz1 (cI J)). 
intros f.
destruct J as (J,JC); 
simpl.
rewrite JC.
reflexivity.  
Defined.


