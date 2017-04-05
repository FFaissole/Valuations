
Add Rec LoadPath "~/Documents/HoTTClasses/".
Add Rec LoadPath "~/Documents/SyntheticTopology/Spaces".
Add Rec LoadPath "~/Documents/SyntheticTopology/Theories".
Add Rec LoadPath "~/Documents/SyntheticTopology/Models".

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
               Types.Prod.

Require Export RoundedClosed Opens. 

Definition cover {A : hSet} (U : OS A) (f : nat -> OS A) := 
                    forall x, U x -> exists n, (f n) x. 

Definition finite_cover {A : hSet} (U : OS A) (f : nat -> OS A) := 
                    exists N, forall x, U x -> exists n, n <= N /\ (f n) x.

Definition compactness {A : hSet} (U : OS A) := 
                        hexists (fun f => cover U f) -> 
                        hexists (fun g => finite_cover U g).

Definition below {A : hSet} (U V : OS A) := forall f, cover V f -> 
                exists g, (forall i, exists j:nat, g i = f i) 
                           /\ (finite_cover U g).

Notation "U << V" := (below U V) (at level 50).

Definition local_compactness_weak {A : hSet} (V : OS A) := 
               (forall U, U << V -> (U ⊆ V)) /\ 
               (exists U, U << V /\ U = V).

Section local_compactness_seq.

Context {A : hSet}.

Hypothesis seq_below : forall V : OS A, exists f : nat -> OS A, 
                 forall U, U << V -> exists i, (f i) << V.

Definition sup_below (V : OS A) : OS A.
Proof.
destruct (seq_below V) as (f,Hf).
refine (fun x => CountableSup (fun n => f n x)).
Defined. 

Definition local_compactness := forall V:OS A, V = sup_below V. 

End local_compactness_seq.


 

