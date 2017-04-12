

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

(** * From Integrals to Valuations *)

(** 1_U preserves lub *)
Lemma OpenFun_lub {A : hSet} : forall (U : IncreasingSequence (OS A)) x, 
         OpenFun A (Cpo.lub U) x = 
                RllubPos (fun n => (OpenFun A (U n)) x).
Proof. 
intros U x.
unfold OpenFun; simpl.
apply (antisymmetry le).
+ intros s Hs. 
  apply top_le_enumerable_sup in Hs. 
  unfold semi_decide, toRlseq in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (m,Hm).
  apply top_le_enumerable_sup.
  apply tr; exists m.  
  revert Hm; apply S_to_RlP_mon.
  apply imply_le.
  intros Hv. 
  apply top_le_joined_seq_n' in Hv.
  revert Hv; apply (Trunc_ind _).
  intros (p,Hp).
  destruct Hp as (Hpm,HUp).
  revert HUp.
  apply SierLe_imply.
  assert (H' : U p <= U m).
  apply seq_increasing_le; trivial.
  apply H'.  
+ intros s Hs.
  apply top_le_enumerable_sup in Hs.
  unfold semi_decide, toRlseq in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (m,Hm).
  revert Hm; apply S_to_RlP_mon.
  apply imply_le. 
  intros H. 
  apply top_le_countable_sup.
  apply tr; exists m; trivial.
Qed. 

(** fun n => U n ---> fun n => 1_(U n) *)
Definition OpenFun_increasing_sequence {A : hSet} : 
   IncreasingSequence (OS A) -> IncreasingSequence (mf A).
Proof.
intros U.
exists (fun n => OpenFun A (U n)).  
intros n x.
apply OpenFun_mon.
apply U.
Defined. 

(**  mu_I (U)  = I (1_U) *)
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
+ intros f.
  transitivity (J (λ x : A, RllubPos (λ n : nat, 
                (OpenFun A (f n) x)))).
  apply I_mon.
  intros x. rewrite OpenFun_lub; reflexivity.
  assert (X : forall x, (λ n : nat, OpenFun A (f n)) x = 
        (OpenFun_increasing_sequence f) x).
  intros x; reflexivity.
  transitivity (J (λ x : A, RllubPos (fun n => 
           seq ((OpenFun_increasing_sequence f)) n x))).
  apply I_mon.
  intros x.
  apply RllubPos_mon;
  intros n q Hn.
  rewrite <- X; trivial. 
  apply J.
Defined.