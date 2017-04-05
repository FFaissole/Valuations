

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
               D_op OpenFun.
              
Set Implicit Arguments.


(** * Formal proof of a constructive Riesz Theorem: for 
the detailed pen-and-paper proof, see Coquand-Spitters09, 
Integrals and valuations, or Vickers08, Monad of valuation 
locales *)

(** From Integrals to Valuations: 
  mu_I (U)  = I (1_U) *)
Definition Riesz1 (A : hSet) : IntPos A -> Val A. 
Proof. 
intros J. 
exists (fun U:OS A => (I J (OpenFun A U))). 
+ red. intros U V.  
  transitivity (I J (OpenFun _ U) + I J (OpenFun _ V)).
  unfold plus; reflexivity. 
  rewrite <- (I_add J (OpenFun _ U) (OpenFun _ V)). 
  transitivity
     ((I J( OpenFun _ (OS_join U V)))+
      (I J (OpenFun _ (OS_meet U V)))); 
  try reflexivity.
  rewrite <- (I_add J (OpenFun _ (OS_join U V))
                    (OpenFun _ (OS_meet U V))).
  rewrite OpenFun_mod, fplus_comm. reflexivity.  
+ red. destruct J. 
  assert (HO : OpenFun A OS_empty = fun x => RlP_0).
  apply path_forall; intros z.
  rewrite OpenFun_def; reflexivity.  
  rewrite HO. simpl. unfold Mdef in I_def. apply I_def. 
+ red. intros U V H. 
  apply I_mon. 
  apply OpenFun_mon; trivial.
+ unfold OS_full; apply I_prob. 
Defined.