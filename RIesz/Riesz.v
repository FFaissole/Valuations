

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
               hit.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals D_op OpenFun Simples. 

Set Implicit Arguments.

Definition Riesz1 (A : hSet) : IntPos A -> D A. 
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


Definition Riesz2 (A : hSet) : D A -> IntPos A.
Proof.
intros Nu. 
refine (I_mu Nu). 
Defined. 


Lemma Riesz_hom1 (A : hSet) : forall (Mu :D A) U,
    mu _ (Riesz1 (Riesz2 Mu)) U = mu _ Mu U.
Proof.
intros Mu U. 
unfold Riesz1. 
simpl. 
unfold Riesz2.
rewrite I_mu_simpl.
apply (antisymmetry le).
+ apply Rllub_le; intros n.
  unfold toRlseq, sum_p_r, sum_prod_sub.
  induction n.
  - rewrite Rlow_mult_q_RlP_0. 
    destruct Mu.
    destruct (mu U). admit.

  - simpl in *. admit.

+ 
Admitted.  

Definition Riesz_hom2 (A : hSet) : forall (It : IntPos A) f,
    I (Riesz2 (Riesz1 It)) f = I It f.
Proof.
intros It. 
unfold Riesz1. 
destruct It; simpl. 
Admitted. 
