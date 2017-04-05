

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
               D_op OpenFun Riesz1 Riesz1_cont Appr Riesz2.
              
Set Implicit Arguments.


Definition Riesz2_cont (A : hSet): ContVal A -> ContIntPos A. 
Proof.
intros mm.
split with (Riesz2 (cmu _ mm)).
destruct mm as (m,Cm).
unfold cont in Cm; simpl; unfold Mcontinuous.
intros f.
assert (Hk : (Riesz1 (Riesz2 m) = m)).
unfold Riesz2, Riesz1.
apply Val_eq0; simpl.
apply path_forall.
intros U.
rewrite Cm.
reflexivity.
rewrite Hk.
reflexivity.
Defined.   



