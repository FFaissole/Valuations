
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.implementations.assume_rationals
               partiality
               sierpinsky
               dedekind
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export Rlow Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun.
              

(** * From Integrals to Valuations *)

(**  mu_I (U)  = I (1_U) *)
Definition Riesz1 (A : hSet) : IntPos A -> Val A. 
Proof. 
intros J. 
exists (fun U:OS A => (I J (OpenFun U))). 
+ red. intros U V.  
  transitivity (I J (OpenFun U) + I J (OpenFun V)).
  unfold plus; reflexivity. 
  rewrite <- (I_add J (OpenFun U) (OpenFun V)). 
  transitivity
     ((I J( OpenFun (OS_join U V)))+
      (I J (OpenFun (OS_meet U V)))); 
  try reflexivity.
  rewrite <- (I_add J (OpenFun  (OS_join U V))
                    (OpenFun  (OS_meet U V))).
  rewrite OpenFun_mod, fplus_comm. reflexivity.  
+ red. destruct J. 
  assert (HO : @OpenFun A OS_empty = fun x => RlP_0).
  apply path_forall; intros z.
  rewrite OpenFun_def; reflexivity.  
  rewrite HO. simpl. unfold Mdef in I_def. apply I_def. 
+ red. intros U V H. 
  apply I_mon. 
  apply OpenFun_mon; trivial.
+ unfold OS_full; apply I_prob.
+ intros f.
  assert (H1 : Rlle (J (OpenFun (Cpo.lub f)))
           (J (fun x : A => RllubPos (fun n : nat => 
                (OpenFun (f n) x))))).
  apply I_mon. 
  intros x. 
  rewrite OpenFun_lub; unfold Rlle; auto.
  assert (H2 : Rlle (J (fun x : A => RllubPos (fun n : nat => OpenFun (f n) x)))
    (RllubPos (fun n : nat => J (OpenFun (f n))))).
  assert (X : forall x, (fun n : nat => OpenFun (f n)) x = 
        (OpenFun_increasing_sequence f) x).
  intros x; reflexivity.
  assert (H3: Rlle  (J (fun x : A => RllubPos (fun n : nat => OpenFun (f n) x)))
      (J (fun x : A => RllubPos (fun n => 
           seq ((OpenFun_increasing_sequence f)) n x)))).
  apply I_mon.
  intros x.
  apply RllubPos_mon;
  intros n q Hn.
  rewrite <- X; trivial.
  assert (X' : (J (fun x : A => RllubPos (fun n : nat => 
                         OpenFun (f n) x))) = 
               (J (fun x : A => RllubPos (fun n : nat => 
                   (OpenFun_increasing_sequence f) n x)))).
  simpl; reflexivity.
  rewrite X'.
  apply J.
  unfold Rlle in *; auto.
Defined.  
