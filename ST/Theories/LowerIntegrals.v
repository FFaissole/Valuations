

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties HIT.quotient.

Require Import RoundedClosed
               Functions
               Valuations. 
               
Set Implicit Arguments.

Section Integrals.

(** * Lower Integrals on A: a lower integra is a semi_continuous map 
and defined in mf(A) which is valued in the positive lower reals *)

Definition M (A : hSet) := mf A -> RlowPos. 

Definition Mplus {A} : Plus (M A). 
intros I J f.
specialize (I f).
specialize (J f).
refine (RlP_plus I J).
Defined. 

Definition Mdef {A} (I : M A) :=
              (I (fzero A)) = RlP_0.

Definition Mprob {A} (I : M A) :=
               (I (fone A)) <= RlP_1. 

Definition Mstable_add {A} (I : M A) :=
  forall f g: mf A, (I (fplus f g)) = ((I f)+(I g)).

Definition Mpos {A} (I : M A) :=
  forall (f : mf A), (forall x, RlP_0 <= f x) -> RlP_0 <= I f.

Definition Mmon {A} (I : M A) := 
   forall f g : mf A,  f <= g -> (I f) <= (I g).

Definition Mcont {A} : (M A) -> Type := fun I => 
            forall (f : IncreasingSequence (mf A)), 
           I (Cpo.lub f) <= RllubPos (fun n => I (f n)).

(** strong version of continuity: not used yet*)
Definition Mcont' {A} (I : M A) :=
  forall f : mf A, (I f <= RllubPosQP (fun q:Q+ =>
                I (fun x => RlP_minus_q2 (f x) q))). 

(** IntPos is a semigroup for plus *)
Global Instance MPos_semi_group {A} : SemiGroup (M A)
                                          (Aop := @Mplus A). 
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

(** Integrals are definite, sigma-additive, monotonic,
associated to probability and continuous *)
Record IntPos (A : hSet) : Type := 
  {I :> mf A -> RlowPos;
   I_def : Mdef I;
   I_add : Mstable_add I;
   I_prob : Mprob I;
   I_mon : Mmon I; 
   I_cont : Mcont I
}.

Hint Resolve I_def I_add I_prob I_mon. 


(** IntPos in hSet *) 

Lemma IntPos_eq0 {A} (J H : IntPos A) :
          I J = I H -> J = H.
Proof. 
intros Hx.
destruct J; destruct H; simpl in Hx;
destruct Hx.
assert (Hdef : I_def0 = I_def1).
apply path_ishprop.
assert (Hadd : I_add0 = I_add1).
apply path_ishprop.
assert (Hmon : I_mon0 = I_mon1).
apply path_ishprop.
assert (Hprob : I_prob0 = I_prob1).
apply path_ishprop.
assert (Hcont : I_cont0 = I_cont1).
apply path_ishprop.
rewrite Hdef, Hadd, Hmon, Hprob, Hcont.
reflexivity. 
Qed. 
 
Instance IntPos_isset@{} {A} : IsHSet (IntPos A).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => I a = I b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply IntPos_eq0;apply E.
Qed.

End Integrals. 