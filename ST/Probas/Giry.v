
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
               D_op OpenFun Riesz1.
              
Set Implicit Arguments.

(** * Giry monad on sets *)

(** unit operator *)
Definition unit (A : hSet) (x : A) : IntPos A. 
Proof.
exists (fun f : mf A => f x).    
+ reflexivity.
+ intros f g; reflexivity.
+ unfold Mprob; reflexivity.
+ intros f g Hfg; apply Hfg.
Defined.

(** bind operator *)
Definition bind (A B : hSet) : IntPos A -> (A -> IntPos B) -> IntPos B.
Proof.
intros I M.
split with (fun f => I (fun x => (M x) f)).
+ red; assert (H : (λ x : A, (M x) ∅) = (λ x : A, RlP_0)).
  apply path_forall; intros x.  
  rewrite (I_def (M x)); reflexivity.
  rewrite H.
  apply I_def.
+ red; intros f g.
  rewrite <- I_add.
  assert (Hc : fplus (λ x : A, (M x) f) (λ x : A, (M x) g)=
               λ x : A, (M x) (fplus f g)).
  apply path_forall.
  intros x. 
  rewrite I_add.
  reflexivity.
  rewrite Hc; reflexivity. 
+ red; transitivity (I (λ x : A, RlP_1)).
  apply I_mon.
  intros x; apply I_prob.
  apply I_prob.
+ red; intros f g Hfg.
  apply I_mon. intros x; apply I_mon; trivial.
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
    f <= g -> (unit A x) f <= (unit A x) g.
Proof. 
intros x U V HUV.
simpl; trivial.
Qed. 

Lemma bind_mon {A B :hSet} : forall (x:A) (X: IntPos A) 
                       (F : A -> IntPos B) (f g : mf B), 
       f <= g -> (bind X F) f <= (bind X F) g. 
Proof.
intros x X F f g Hfg. 
unfold bind; 
simpl in *.
apply I_mon.
intros s; apply I_mon; 
trivial.
Qed. 