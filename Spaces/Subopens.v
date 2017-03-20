
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.theory.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.dedekind
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod Types.Sigma. 

Require Export RoundedClosed Opens.

Section OS_OS.


Record OT {A :hSet} (U : OS A) := mkOT{
     value :> A; 
     is_in_U : U value
}.

Global Instance OT_hprop@{} {A :hSet} : 
             forall (U:OS A) x, IsHProp (U x).
Proof.
intros.
apply _.
Qed.

Lemma OT_eq0 {A :hSet} (U : OS A): forall a b : OT U, 
            value U a = value U b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 

Instance OT_isset@{} {A :hSet} (U : OS A) : IsHSet (OT U).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => value U a = value U b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply OT_eq0;apply E.
Qed.

Definition OTs {A :hSet} (U:OS A) : hSet. 
Proof.
exists (OT U).
apply OT_isset.
Qed.

Definition OS_OS {A :hSet} (U : OS A) := OS (OTs U).

End OS_OS. 

Section OS_subspace.

Record subhSet {A : Type} (U : A -> Type) := {
     vals :> A; 
     in_U : U vals /\ forall x, IsHProp (U x) 
}.

Lemma subhSet_eq0 {A :hSet} (U : A -> Type): 
            forall a b : subhSet U, 
            vals U a = vals U b -> a = b. 
Proof.  
intros a b. destruct a, b. simpl; intros E. 
destruct E. apply ap.
destruct in_U0, in_U1.
apply path_ishprop. 
Qed. 

Instance subhSet_isset@{} {A :hSet} (U : A -> Type) : 
                                       IsHSet (subhSet U).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => vals U a = vals U b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E; apply subhSet_eq0;apply E.
Qed.

Definition SSet {A :hSet} (U:A->Type) : hSet. 
Proof.
exists (subhSet U).
apply subhSet_isset.
Qed.

Definition OS_SSet {A :hSet} (U : A -> Type) := OS (SSet U).
