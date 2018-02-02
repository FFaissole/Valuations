
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.orders.orders
               HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom.

Require Import HoTTClasses.sierpinsky partiality dedekind.

Require Export Rlow Opens.

Section Val. 

(** * Valuations on A: a valuation is the equivalent of 
measures but on open sets. A valuation is semi_continuous and 
is valued in the positive lower reals *)

(** Carrier for the type of valuations on A *) 
Definition Mes (A : hSet) := OS A -> RlowPos.

(** Definition of the suitable properties *)
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
   forall (U V : OS A), U ⊆ V -> Rlle (m U) (m V).

Definition cont {A} : (Mes A) -> Type := fun m => 
      forall (U : IncreasingSequence (OS A)), 
      Rlle (m (Cpo.lub U)) (RllubPos (fun n => m (U n))).

(** Space of valuations : valuations are definite, 
    modular, monotonic, sub-ptrobabilstic and continuous *)

Record Val (A : hSet) : Type :=
  {mu :> OS A -> RlowPos;
   mu_modular : modular mu; 
   mu_empty_op : empty_op mu;
   mu_mon : mon_opens mu;
   mu_prob : Rlle (mu (fun x => SierTop)) (RlP_1); 
   mu_cont : cont mu
}.


Hint Resolve mu_modular mu_prob mu_empty_op mu_mon.

(** Val in hSet *)



Lemma Val_eq0 {A} (J H : Val A) :
          mu _ J = mu _ H -> J = H.
Proof. 
intros Hx.
destruct J; destruct H; simpl in Hx;
destruct Hx.
assert (Hmod : mu_modular0 = mu_modular1).
apply path_ishprop.
assert (Hempty : mu_empty_op0 = mu_empty_op1).
apply path_ishprop.
assert (Hmon : mu_mon0 = mu_mon1).
apply path_ishprop.
assert (Hprob : mu_prob0 = mu_prob1).
apply path_ishprop.
assert (Hcont : mu_cont0 = mu_cont1).
apply path_ishprop.
rewrite Hmod, Hempty, Hmon, Hprob, Hcont.
reflexivity. 
Qed. 
 
Instance Val_isset {A} : IsHSet (Val A).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => mu _ a = mu _  b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply Val_eq0;apply E.
Qed.

End Val. 