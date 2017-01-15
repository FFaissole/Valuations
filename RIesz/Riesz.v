

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

Require Export Spaces.RoundedClosed
               Spaces.Opens Spaces.Functions 
               Theories.Valuations
               Theories.LowerIntegrals
               Riesz.D_op Riesz.OpenFun Riesz.Simples. 

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

(** From Integrals to Valuations : 

 ^        
 |        ** 
 |        ||
 |--------*-*------------------
 |       *|D_2|*
 |----*-*-------*--------------
 |  * |   D_1   |*
 |-*--------------*------------
 |* |     D_0     |  * * *
 ---|-------------|---------------->

I_mu (f) = sup (fun n => sum(i)_0^n (mu (D_op i))
 *)

Definition Riesz2 (A : hSet) : Val A -> IntPos A.
Proof.
intros Nu. 
refine (I_mu Nu). 
Defined. 

(** Homeorphism between integrals and Valuations: 
    - hom1: mu_(I_nu) (U) = nu(U)
    - hom2: I_(mu_J) (f) = J(f) 
 *) 
Lemma Riesz_hom1 (A : hSet) : forall (Mu :Val A) U,
    mu _ (Riesz1 (Riesz2 Mu)) U = mu _ Mu U.
Proof.
intros Mu U.  
simpl. 
rewrite I_mu_simpl.
apply (antisymmetry le).
+ apply Rllub_le; intros n.
  induction n.
  - unfold toRlseq, sum_p_r, sum_prod_sub.
    assert (D_op 0 (OpenFun A U) =  U).  
    generalize (@D_op_correct _ _ A (OpenFun A U) 0).
    intros HGF.
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (U z).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros x. unfold semi_decide.
       destruct (decide (0 < 1)).
       * destruct x; reflexivity.
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * reflexivity.       
    -- intros h HU. 
       admit. 
       
     
    -- rewrite X; unfold Rlle, RCLe_l; auto.    
  - simpl in *. 
    assert (H22 : Rlle ((toRlseq (λ n : nat, sum_p_r n
                 (OpenFun A U) Mu) (S n)))
                       ((toRlseq (λ n0 : nat, sum_p_r n0
                 (OpenFun A U) Mu) n))). 
    apply toRlseq_antimon.
    apply Peano.le_S.
    reflexivity.
    intros s Hs.
    apply IHn.
    apply H22; trivial.
+ unfold sum_p_r.
  transitivity (sum_p_r 0 (OpenFun A U) Mu).
  unfold sum_p_r.  
  unfold sum_prod_sub.
  simpl.
  assert (D_op 0 (OpenFun A U) = U).
  generalize (@D_op_correct _ _ A (OpenFun A U) 0).
  intros HGF.
  unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (U z).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros x. unfold semi_decide.
       destruct (decide (0 < 1)).
       * destruct x; reflexivity.
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * reflexivity.       
    -- simpl. admit.
    -- rewrite X; unfold Rlle, RCLe_l; auto.
    -- simpl. assert (Hu : D_op 0 (OpenFun A U) = U).
       generalize (@D_op_correct _ _ A (OpenFun A U) 0).
       intros HGF.
       unfold D_op, OpenFun, OpenFun_aux.
       apply path_forall; intros z.
       generalize (U z).
       apply (partial_ind0 _ (fun a => _)).
       --- simpl; intros x. unfold semi_decide.
           destruct (decide (0 < 1)).
           * destruct x; reflexivity.
           * assert (Hos : Qzero < Qone).
             apply semirings.lt_0_1.
             case (n Hos).
       --- simpl; unfold semi_decide.
           destruct (decide (0 < 0)).
           * assert (Hj : Qzero <= Qzero). reflexivity.
             generalize (orders.le_not_lt_flip 0 0 Hj).
             intros Hj'; case (Hj' l).          
           * reflexivity.       
       --- simpl. admit.
       --- rewrite Hu. 
       apply (RllubPos_lub (λ n : nat,
       match n with
       | 0 => mu _ Mu U
       | S _ =>
           Rlow_mult_q (1 / qnp (S n))
             (sum_prod_sub n (OpenFun A U) Mu +
              mu _ Mu (D_op (qn (S n)) (OpenFun A U)))
       end) 0).
Admitted.  

Definition Riesz_hom2 (A : hSet) : forall (It : IntPos A) f,
    I (Riesz2 (Riesz1 It)) f = I It f.
Proof.
intros It.
unfold Riesz2.  
rewrite I_mu_simpl.
intros f.
apply (antisymmetry le).
+ unfold sum_p_r. simpl. generalize (I_cont It).
  intros HcI.
  unfold Mcont in *.
  rewrite HcI.
  apply Rllub_le.
  intros n. 
  unfold toRlseq.
   admit.
  
+ rewrite I_cont.
  apply RllubPos_mon.
  intros n. admit. (* ok revoir cont *) 
Admitted. 
