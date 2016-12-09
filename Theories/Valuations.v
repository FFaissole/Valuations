
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom hit.quotient
               Basics.FunextVarieties FunextAxiom.

Require Export RoundedClosed Opens Cpo.

Section Val. 

(*Context `{Funext} `{Univalence}.*)

(** Space of valuations on A *) 
Definition Mes (A : hSet) := OS A -> RlowPos.

(* Definition of the properties *)
Definition empty_op {A} (m : Mes A)  := (m ∅) =  RlP_0.

Definition modular  {A} (m : Mes A) :=
   forall (U V : OS A),  (RlP_plus (m U) (m V)) = 
                           (RlP_plus (m (U ∪ V)) (m (U ⋂ V))).

Definition seq_open_mes  {A} (m :Mes A) :
         (nat -> OS A) -> (nat -> RlowPos).
Proof. 
intros L n. 
specialize (L n).
specialize (m L).
refine m.
Defined.

Definition mon_opens  {A} (m : Mes A) :=
   forall (U V : OS A), U ⊆ V -> (m U) <= (m V).

(*Space of distributions*)
Record D  (A : hSet) : Type :=
  {mu :> @Mes A;
   mu_modular : modular mu; 
   mu_empty_op : empty_op mu;
   mu_mon : mon_opens mu;
   mu_prob : (mu Ω) <= (RlP_1)
}.

Hint Resolve mu_modular mu_prob mu_empty_op mu_mon.

(** *** Properties of measures *)

(* mu is monotonic *) 
Lemma mu_monotonic : forall {A} (m : D A), mon_opens m.
Proof.  auto. Qed.
Hint Resolve mu_monotonic.

(* eq stable *)

Lemma mu_stable_eq : forall  {A} (m: D A) (U V : OS A),
    U = V -> (mu A m U) = (mu A m V).
Proof. 
intros A m U V H2.
rewrite H2. 
split; auto.   
Qed.

Hint Resolve mu_stable_eq.

(* mu m (fone A) <= 1%RlPos *)
Lemma mu_one : forall  {A} (m: D A), (mu A m Ω) <=  RlP_1.
Proof. auto. Qed. 

Hint Resolve mu_one.

End Val. 
