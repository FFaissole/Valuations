
(** Open Subspaces of an hSet A  **)

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom hit.quotient
               Basics.FunextVarieties FunextAxiom.  
Require Import RoundedClosed.

Set Implicit Arguments.

Section OpenSubs.

Context {A : hSet}.
Context `{Funext} `{Univalence}.

Definition OS : Type := A -> Sier. 

(** Order relation on OS *)
Global Instance Osle : Le OS.
Proof.
  intros O1 O2.
  unfold OS in O1, O2.
  refine (forall x:A, SierLe (O1 x) (O2 x)).
Defined.

Global Instance Osle_ord : PartialOrder (Osle). 
Proof. 
split. 
+ apply _. 
+ intros x y. 
  apply _. 
+ split. 
  - hnf. intros x s; reflexivity. 
  - hnf. 
    intros x y z Hxy Hyz. 
    intros s. transitivity (y s); auto. 
+ hnf.
  intros x y H1 H2.
  apply path_forall. 
  red. 
  intros s. 
  apply (antisymmetry le).
  apply H1. apply H2. 
Defined.

(** Join of open subsets *)
Global Instance OS_join : Join OS :=
              fun U V => fun x => SierJoin (U x) (V x).

(** Meet of open subsets *)
Global Instance OS_meet : Meet OS := 
              fun U V => fun x => SierMeet (U x) (V x).

(* Empty space *)
Global Instance OS_empty : Zero OS := fun x : A => ⊥.

(* All the space itself *)
Global Instance OS_full : One OS := fun x : A => ⊤.

(* lub of a sequence of open subspaces *)
Definition OS_lub (f : nat -> OS) : OS.
Proof.
intro x.  
refine (CountableSup (fun n => f n x)).   
Defined.

(* Notations *)
Notation "U ⋂ V" := (OS_meet U V) (at level 80). 
Notation "U ∪ V" := (OS_join U V) (at level 80).
Notation "∅" := (OS_empty).
Notation "'Ω'" := (OS_full).
Notation "U ⊆ V" := (Osle U V) (at level 90).
Notation "∞ Un" := (OS_lub Un) (at level 85). 

(** Lattice properties of the order *)
Lemma os_lattice_order : LatticeOrder Osle.
Proof.
split.
+ split.
  - apply Osle_ord.
  - intros x y s.
    apply SierMeet_is_meet.
  - intros x y s.
    apply SierMeet_is_meet.
  - intros x y z H1 H2 s.  
    apply SierMeet_is_meet.
    apply H1. apply H2.
+ split. 
  - apply Osle_ord.
  - intros x y s. 
    apply SierJoin_is_join. 
  - intros x y s.
    apply SierJoin_is_join.
  - intros x y z H1 H2 s.  
    apply SierJoin_is_join.
    apply H1. apply H2.
Defined.

(** Semigroup structure of OS *)
Global Instance os_semi_group : SemiGroup OS. 
Proof. 
split. 
+ apply _.   
+ hnf. intros x y z. apply path_forall.
  intros s. apply (antisymmetry le); 
  apply SierJoin_is_join.
  transitivity ((x & y) s);
  apply SierJoin_is_join. 
  apply SierJoin_is_join.
  transitivity ((x & y) s);
  apply SierJoin_is_join. 
  apply SierJoin_is_join.
  apply SierJoin_is_join. 
  apply SierJoin_is_join. 
  transitivity ((y & z) s); 
  apply SierJoin_is_join. 
  transitivity ((y & z) s);  
  apply SierJoin_is_join.
Defined. 

(** Lattice structure on OS *)
Global Instance os_jslattice : JoinSemiLattice OS.
Proof.
split.
+ split.
  - apply os_semi_group.
  - red. intros x y. 
    apply path_forall; intro s. 
    apply (antisymmetry le);  
    apply SierJoin_is_join. 
    apply SierJoin_is_join. 
    apply SierJoin_is_join. 
    apply SierJoin_is_join. 
    apply SierJoin_is_join. 
+ red. intros x. 
  red. apply path_forall; intro s.    
  apply (antisymmetry le);  
  apply SierJoin_is_join; reflexivity.
Defined.

Global Instance os_mslattice : MeetSemiLattice OS.
Proof.
split.
+ split.
  - split. 
    apply _.   
    hnf. intros x y z. apply path_forall.
    intros s. apply (antisymmetry le).
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet.
    apply SierMeet_is_meet.
    transitivity ((y ⋂  z) s).    
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet. 
    transitivity ((y ⋂ z) s). 
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet.   
    transitivity ((x ⋂ y) s).       
    apply SierMeet_is_meet.   
    apply SierMeet_is_meet.   
    apply SierMeet_is_meet.   
    transitivity ((x ⋂ y) s).     
    apply SierMeet_is_meet.   
    apply SierMeet_is_meet.   
    apply SierMeet_is_meet.   
  - red. intros x y. 
    apply path_forall; intro s. 
    apply (antisymmetry le);  
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet. 
    apply SierMeet_is_meet. 
+ red. intros x. 
  red. apply path_forall; intro s.    
  apply (antisymmetry le);  
  apply SierMeet_is_meet; reflexivity.
Defined.

Global Instance os_dlattice : DistributiveLattice OS.
Proof.
split.
+ split.
  - apply os_jslattice.
  - apply os_mslattice. 
  - red. intros x y. 
    apply path_forall; intro s. 
    apply (antisymmetry le);  
    apply SierJoin_is_join. 
    reflexivity. 
    apply SierMeet_is_meet. 
  - red. intros x y.  
    apply path_forall; intro s. 
    apply (antisymmetry le);  
    apply SierMeet_is_meet. 
    reflexivity. 
    apply SierJoin_is_join. 
+ repeat red. intros a b c;
  apply path_forall ; intro s.
  generalize Sier_distributive_lattice. 
  intros HG. 
  destruct HG as (_,HG).
  unfold LeftDistribute, LeftHeteroDistribute in *. 
  specialize (HG (a s) (b s) (c s)).
  transitivity ((a s ⊔ b s) ⊓ (a s ⊔ c s)).
  apply HG. reflexivity. 
Defined. 

(** * Valuations on set A *)
Section Valuations.  

(** Space of measures on A *) 
Definition Mes : Type := OS -> RlowPos.

(* Definition of the properties *)
Definition empty_op (m : Mes) := (m ∅) =  RlP_0.

Definition modular (m : Mes) :=
   forall (U V : OS),  (RlP_plus (m U) (m V)) = 
                           (RlP_plus (m (U ∪ V)) (m (U ⋂ V))).

Definition seq_open_mes (m : Mes) :
         (nat -> OS) -> (nat -> RlowPos).
Proof. 
intros L n. 
specialize (L n).
specialize (m L).
refine m.
Defined.

Definition mon_opens (m : Mes) :=
   forall (U V : OS), U ⊆ V -> (m U) <= (m V).

(*Space of valuations on A *)
Record Val : Type :=
  {mu :> Mes;
   mu_modular : modular mu; 
   mu_empty_op : empty_op mu;
   mu_mon : mon_opens mu;
   mu_prob : (mu Ω) <= (RlP_1)
}.

Hint Resolve mu_modular mu_prob mu_empty_op mu_mon.

(** *** Properties of measures *)

(* mu is monotonic *) 
Lemma mu_monotonic : forall (m : Val), mon_opens m.
Proof. auto. Qed.
Hint Resolve mu_monotonic.

(* eq stable *)

Lemma mu_stable_eq : forall (m: Val) (U V : OS),
    U = V -> (mu m U) = (mu m V).
Proof. 
intros m U V H2.
rewrite H2. 
split; auto.   
Qed.

Hint Resolve mu_stable_eq.

End Valuations. 

End OpenSubs.
