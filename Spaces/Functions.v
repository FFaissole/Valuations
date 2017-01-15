

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe FunextAxiom
               TruncType UnivalenceAxiom Types.Sigma
               hit.quotient. 

Require Import Spaces.RoundedClosed.

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
