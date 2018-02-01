
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
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
               D_op OpenFun Riesz1.
              
Set Implicit Arguments.

(** * Giry monad on sets *)

(** unit operator *)
Definition unit (A : hSet) (x : A) : IntPos A. 
Proof.
exists (fun f : mf A => f x).    
+ reflexivity.
+ intros f g; reflexivity.
+ unfold Mprob; unfold Rlle; auto.
+ intros f g Hfg; apply Hfg.
+ intros f; unfold Rlle; auto.
Defined.

(** bind operator *)
Definition bind (A B : hSet) : IntPos A -> (A -> IntPos B) -> IntPos B.
Proof.
intros I M.
split with (fun f => I (fun x => (M x) f)).
+ red; assert (H : (fun x : A => (M x) ∅) = (fun x : A => RlP_0)).
  apply path_forall; intros x.  
  rewrite (I_def (M x)); reflexivity.
  rewrite H.
  apply I_def.
+ red; intros f g.
  rewrite <- I_add.
  assert (Hc : fplus (fun x : A => (M x) f) (fun x : A => (M x) g)=
               fun x : A => (M x) (fplus f g)).
  apply path_forall.
  intros x. 
  rewrite I_add.
  reflexivity.
  rewrite Hc; reflexivity. 
+ red. 
  assert (Rlle (I (fun x : A => (M x) (fone B)))
                (I (fun x : A => RlP_1))).
  apply I_mon.
  intros x; apply I_prob.
  assert (Rlle (I (fun _ : A => RlP_1)) RlP_1).
  apply I_prob.
  unfold Rlle; auto.
+ red; intros f g Hfg.
  apply I_mon. intros x; apply I_mon; trivial.
+ intros f.
  pose (ff := fun n : nat =>
            (fun x : A => ((M x) (f n)))).
  assert (Hff : forall n, fle (ff n) (ff (S n))).
  intros n; unfold ff. intros x.
  apply (M x), f.
  pose (F := Build_IncreasingSequence ff Hff).
  generalize (I_cont I F); 
  unfold Mcont; intros HI.
  unfold F in *; simpl in *.
  unfold ff in *.
  assert (H : Rlle (I (fun x : A => (M x) (fun x0 : B => 
             RllubPos (fun n : nat => f n x0))))
               (I (fun x : A => RllubPos 
                      (fun n : nat => (M x) (f n))))).
  apply I_mon; intros x.
  apply (M x).
  assert (X : Rlle (I (fun x : A => RllubPos 
                      (fun n : nat => (M x) (f n))))
        (Rllub (toRlseq (fun n : nat => I (fun x : A => (M x) (f n)))))).
  trivial.
  unfold Rlle in *; auto.
Defined. 

(** Monadic properties *)
Lemma monad1 {A B : hSet} : forall (x : A) (F : A -> IntPos B),
              bind (unit A x) F = F x. 
Proof.
intros x F.
unfold bind; simpl;
apply IntPos_eq0;trivial.  
Qed.

Lemma monad2 {A : hSet} : forall (X : IntPos A),
                 bind X (unit A) = X.
Proof.
intros X; simpl; apply IntPos_eq0;
reflexivity. 
Qed.

Lemma monad3 {A B C: hSet} : forall (X : IntPos A)
                   (F : A -> IntPos B) (G : B -> IntPos C),
     bind (bind X F) G = bind X (fun x:A => bind (F x) G).  
Proof.
intros X F G; apply IntPos_eq0;  
simpl; reflexivity. 
Qed.

Lemma unit_mon {A :hSet} : forall (x:A) (f g : mf A),
    fle f g -> Rlle ((unit A x) f) ((unit A x) g).
Proof. 
intros x U V HUV.
simpl; trivial.
Qed. 

Lemma bind_mon {A B :hSet} : forall (x:A) (X: IntPos A) 
                       (F : A -> IntPos B) (f g : mf B), 
       fle f g -> Rlle ((bind X F) f) ((bind X F) g). 
Proof.
intros x X F f g Hfg. 
unfold bind; 
simpl in *.
apply I_mon.
intros s; apply I_mon; 
trivial.
Qed. 
