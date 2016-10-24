
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient. 

Require Import RoundedClosed Valuations.

Set Implicit Arguments.  

(** * Functions *)
Section Meas.
  
Context {A : hSet}.
Context `{Funext} `{Univalence}.
Universe UN. 

Definition mf : Type@{UN} := A -> RlowPos.

Definition ffle : mf -> mf -> Type. 
Proof.
intros f g.
unfold mf in f, g.
refine (forall x:A, (f x) <= (g x)).  
Defined.

Definition ffle_hProp : mf  -> mf  -> hProp.
Proof.
intros U V.  
refine ((fun x y => BuildhProp (ffle x y)) _  _). 
exact U. exact V. 
Defined.

(** Order on functions *)
Global Instance fle : Le mf.  
Proof.
intros x y. 
refine (ffle_hProp x y).   
Defined.  

Global Instance fle_ord : PartialOrder (fle). 
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

(** * Operations on mf *)
Global Instance fplus : Plus mf := fun f g => fun x => RlP_plus (f x) (g x).

Global Instance fzero : Zero mf := fun x => RlP_0.

Implicit Arguments fzero [].

Global Instance fone : One mf := fun x => RlP_1.
Implicit Arguments fone [].

(** Properties of fplus  *)
Lemma fplus_comm : Commutative fplus.
Proof.
intros a b; apply fle_ord; 
intros s; unfold fplus;
rewrite (RlPPlus_comm (a s) (b s)); 
reflexivity.
Qed. 

Lemma fplus_assoc : Associative fplus. 
Proof.
intros a b c; apply fle_ord; 
intros s; unfold fplus;
rewrite RlPPlus_assoc; reflexivity.     
Qed. 

Lemma fplus_left_id : LeftIdentity fplus 0.
Proof.
intros a. 
unfold fplus.
apply path_forall. 
intros s.   
apply RlPPlus_left_id. 
Qed.

Lemma fplus_le_preserving : forall f, OrderPreserving (fun g => fplus f g)
                                      (Ale := fle) (Ble := fle). 
Proof.
intros f g h Hgh.
unfold fplus.   
intros q. 
apply RlPlus_le_preserving.
apply Hgh. 
Qed.

(** Semigroup structure on mf *)
Global Instance mf_semi_group : SemiGroup mf. 
Proof. 
split. 
+ apply _.   
+ hnf. intros x y z.
  unfold sg_op, plus_is_sg_op.  
  rewrite fplus_assoc. 
  reflexivity.   
Defined. 

(** * Lower integrals on set A *)
Section Integrals. 

Definition M := mf -> RlowPos. 

Definition Mplus : Plus M. 
intros I J f.
specialize (I f).
specialize (J f).
refine (RlP_plus I J).
Defined. 

Definition Mdef (I : M) :=
              (I fzero) = RlP_0.

Definition Mprob (I : M) :=
               (I fone) <= RlP_1. 

Definition Mstable_add (I : M) :=
  forall f g: mf, (I (fplus f g)) = ((I f)+(I g)).

Definition Mpos (I : M) :=
  forall (f : mf), (forall x, RlP_0 <= f x) -> RlP_0 <= I f.

Definition Mmon (I : M) := 
   forall f g, fle f g -> (I f) <= (I g).
  
Global Instance MPos_semi_group : SemiGroup M (Aop := Mplus). 
Proof. 
split. 
+ apply _.   
+ hnf. intros x y z.
  unfold sg_op, plus_is_sg_op.
  apply path_forall; intros q.
  unfold Mplus. 
  rewrite RlPPlus_assoc.
  reflexivity.   
Defined. 

(** Integrals are definite, sigma-additive, monotonic and 
associated to probability *)
Record IntPos  : Type := 
  {I : M;
   I_def : Mdef I;
   I_add : Mstable_add I;
   I_prob : Mprob I;
   I_mon : Mmon I
}.

Hint Resolve I_def I_add I_prob. 

Lemma Ieq_ext (f g : mf) (It : IntPos) :
         (forall x, (f x) = (g x)) -> (I It f) = (I It g). 
Proof.
intros HH.
destruct It. simpl. 
assert (Hfg : f = g).
apply path_forall.
intros x; trivial.
rewrite Hfg; reflexivity.
Qed.

End Integrals. 

End Meas. 
