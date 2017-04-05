
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.interfaces.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export RoundedClosed Opens OpenFun Valuations Appr.

Section ContVal. 

Definition cont {A} : (Val A) -> Type := fun m => forall U, 
           m U = RllubPos (fun n => appr (OpenFun A U) n m).

Record ContVal (A : hSet) : Type :=
  {cmu :> Val A;
   cmu_cont : cont cmu
}.

Hint Resolve cmu_cont.

(** Deductible properties of valuations *)

(** mu is monotonic *) 
Lemma mucont_monotonic : forall {A} (m : Val A), mon_opens m.
Proof.
intros A m. 
apply mu_monotonic. 
Qed.


Hint Resolve mucont_monotonic.

(** eq stable *)

Lemma mucont_stable_eq : forall {A} (m: ContVal A) (U V : OS A),
    U = V -> m U = m V.
Proof. 
intros A m U V H2.
rewrite H2. 
split; auto.   
Qed.

Hint Resolve mucont_stable_eq.

(** mu m (fone A) <= 1%RlPos *)
Lemma mucont_one : forall  {A} (m: Val A), m Ω <=  RlP_1.
Proof. 
intros A m. 
apply mu_one. 
Qed. 

Hint Resolve mucont_one.

End ContVal. 