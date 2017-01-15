
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import Spaces.RoundedClosed Spaces.Cpo.

(** * Open Subspaces of a hset A *)

(** The continuous maps from A to 
the Sierpinski space Sier forms a classifying topos for the opens 
subsets of A. In Synthetic topology, continuous maps are the 
definissible ones. *)

Definition OS (A : hSet) := A -> Sier. 

Global Instance OS_isset {A} : IsHSet (OS A). 
Proof.
apply _. 
Qed.   

(** Order relation on OS *)
Global Instance Osle {A} : Le (OS A).
Proof.
  intros O1 O2.
  unfold OS in O1, O2.
  refine (forall x:A, SierLe (O1 x) (O2 x)).
Defined.

Global Instance Osle_ord {A} : PartialOrder (@Osle A). 
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
Global Instance OS_join {A} : Join (OS A) :=
              fun U V => fun x => SierJoin (U x) (V x).

(** Meet of open subsets *)
Global Instance OS_meet {A} : Meet (OS A) := 
              fun U V => fun x => SierMeet (U x) (V x).

(** Empty space *)
Global Instance OS_empty {A} : Zero (OS A) := fun x : A => ⊥.

(** The entire space itself *)
Global Instance OS_full {A} : One (OS A) := fun x : A => ⊤.

(** OS A is has a cpo *)
Global Instance OS_cpo {A} : cpo (OS A) Osle. 
Proof.   
exists (fun f : (nat -> OS A) => (fun x =>
                 CountableSup (fun n => f n x))). 
refine OS_empty. 
+ intros f n a. 
  apply (countable_sup_ub (fun n => f n a)). 
+ Search CountableSup.
  intros f x H. assert (HL : forall n a, f n a <= x a).  
  apply H. intros a. 
  apply (countable_sup_least_ub (fun n => f n a)); trivial. 
Defined. 

(** Notations *)
Notation "U ⋂ V" := (OS_meet U V) (at level 80). 
Notation "U ∪ V" := (OS_join U V) (at level 80).
Notation "∅" := (OS_empty).
Notation "'Ω'" := (OS_full).
Notation "U ⊆ V" := (Osle U V) (at level 90).
Notation "∞ Un" := ((lub OS_cpo) Un) (at level 85). 

(** Lattice properties of the order *)
Lemma os_lattice_order  {A} : LatticeOrder (@Osle A).
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

(** Semigroup structure of OS A with sg_op = join (OS A) :
     - associative sg_op
     - OS A is a hSet *)
Global Instance os_semi_group {A} : SemiGroup (OS A). 
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
Global Instance os_jslattice {A} : JoinSemiLattice (OS A).
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

Global Instance os_mslattice {A}: MeetSemiLattice (OS A).
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

Global Instance os_lattice {A} : Lattice (OS A).
split.
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
Defined. 
    
Global Instance os_dlattice {A}: DistributiveLattice (OS A).
Proof.
split.
+ exact os_lattice. 
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
