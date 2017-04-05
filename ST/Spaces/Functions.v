

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe FunextAxiom
               TruncType UnivalenceAxiom Types.Sigma
               HIT.quotient. 

Require Import RoundedClosed.

Set Implicit Arguments.  

(** * Positive integrable functions from A to RlowPos *)


Definition mf (A:hSet) : Type := A -> RlowPos.

Definition ffle {A} : mf A -> mf A -> Type. 
Proof.
intros f g.
unfold mf in f, g.
refine (forall x:A, (f x) <= (g x)).  
Defined.

Definition ffle_hProp {A} : mf A  -> mf A  -> hProp.
Proof.
intros U V.  
refine ((fun x y => BuildhProp (ffle x y)) _  _). 
exact U. exact V. 
Defined.

(** Order on functions *)
Global Instance fle {A} : Le (mf A).  
Proof.
intros x y. 
refine (ffle_hProp x y).   
Defined.  

Global Instance fle_ord {A} : PartialOrder (@fle A). 
Proof. 
split. 
+  apply (@HSet.isset_hrel_subpaths _
       (fun f g => fle f g /\ fle g f)).
  red; intros. split; repeat red; intros; auto.
  apply _.
  intros x y (Hf1,Hf2). 
  apply path_forall. 
  intros s. 
  unfold fle, ffle_hProp in *.   
  simpl in Hf1, Hf2.   
  specialize (Hf1 s). 
  specialize (Hf2 s).
  apply (antisymmetry Rllepos); trivial.
+ intros x y. 
  apply _. 
+ split. 
  - hnf. intros x. repeat red. 
    auto. 
  - hnf. 
    intros x y z Hxy Hyz. 
    intros s. 
    transitivity (y s); auto.
+ hnf. intros x y H' H1. apply path_forall.
  intros s. 
  apply (antisymmetry Rllepos).       
  apply H'. apply H1.
Defined.

(** Operations of functions *)
Global Instance fplus {A} : Plus (mf A) := fun f g => fun x => RlP_plus (f x) (g x).

Global Instance fzero {A} : Zero (mf A) := fun x => RlP_0.
Implicit Arguments fzero [].

Global Instance fone {A} : One (mf A) := fun x => RlP_1.
Implicit Arguments fone [].

(** Properties of fplus  *)
Lemma fplus_comm {A} : Commutative (@fplus A).
Proof.
intros a b; apply fle_ord; 
intros s; unfold fplus;
rewrite (RlPPlus_comm (a s) (b s)); 
reflexivity.
Qed. 

Lemma fplus_assoc {A} : Associative (@fplus A). 
Proof.
intros a b c; apply fle_ord; 
intros s; unfold fplus;
rewrite RlPPlus_assoc; reflexivity.     
Qed. 

Lemma fplus_left_id {A} : LeftIdentity (@fplus A) 0.
Proof.
intros a. 
unfold fplus.
apply path_forall. 
intros s.   
apply RlPPlus_left_id. 
Qed.

Lemma fplus_le_preserving {A} : forall f, OrderPreserving (fun g => fplus f g)
                                      (Ale := fle) (Ble := @fle A). 
Proof.
intros f g h Hgh.
unfold fplus.   
intros q. 
apply RlPlus_le_preserving.
apply Hgh. 
Qed.

(** Semigroup structure on mf with sg_op = plus 
     - sg_op associative
     - mf A is an hset *)
Global Instance mf_semi_group {A} : SemiGroup (mf A). 
Proof. 
split. 
+ apply _.   
+ hnf. intros x y z.
  unfold sg_op, plus_is_sg_op.  
  rewrite fplus_assoc. 
  reflexivity.   
Defined. 


Record mfb (A : hSet) := mk_mfb {
    ff :> A -> RlowPos;
    Hfb : merely (exists b, forall x, Rlle (ff x) (QRlow b))
}.

Definition ffzero (A : hSet) : Zero (mfb A).
Proof.
exists (fzero A).
apply tr; exists 0.
intros x s; trivial.
Qed.

Definition ffone (A : hSet) : One (mfb A).
Proof. 
exists (fone A). 
apply tr; exists 1.
intros x s; trivial. 
Qed. 

Definition ffplus (A : hSet) : Plus (mfb A).
Proof.
intros f g; exists (fun x => (fplus f g) x).
destruct f as (f,Hf).
destruct g as (g,Hg).
revert Hf; apply (Trunc_ind _); intros (bf,Hf).
revert Hg; apply (Trunc_ind _); intros (bg,Hg).
apply tr; exists (bf + bg); intros x.
simpl; intros s Hs.
rewrite RlPlus_Q. 
revert Hs; apply RC_mon with Qle. 
intros u v; apply (antisymmetry le).
intros u v; apply orders.le_or_lt. 
reflexivity.
assert (H2 : Rlle (RlPlus (f x) (g x)) 
                  (RlPlus (f x) (QRlow bg))).
apply RlPlus_le_preserving.
apply Hg.
assert (H3 : Rlle (RlPlus (f x) (QRlow bg)) 
                  (RlPlus (QRlow bf) (QRlow bg))).
rewrite RlPlus_comm.
rewrite (RlPlus_comm (QRlow bf)).
apply RlPlus_le_preserving.
apply Hf.
intros k H4.
apply H3, H2, H4.
Qed.


Global Instance fble {A}: Le (mfb A) := 
                     fun f g => fle f g.

Global Instance Hfb_hprop@{} {A} : forall f, 
       IsHProp (merely (exists b, forall x:A, Rlle (f x) (QRlow b))).
Proof.
apply _. 
Qed.

Lemma fble_eq_ext {A} : forall f g : mfb A, ff f = ff g -> f = g.
Proof.
intros (f,Hf) (g,Hg); simpl; intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 



