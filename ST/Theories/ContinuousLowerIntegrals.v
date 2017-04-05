

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
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
               Valuations
               LowerIntegrals 
               Appr 
               ContinuousValuations Riesz1. 
               
Set Implicit Arguments.

Section ContIntegrals.


Definition Mcontinuous {A} : (IntPos A) -> Type := fun I => forall f, 
         I f = RllubPos (fun n => appr f n (Riesz1 I)).

(** Integrals are definite, sigma-additive, monotonic and 
associated to probability *)
Record ContIntPos (A : hSet) : Type := 
  {cI :> IntPos A;
   cI_cont : Mcontinuous cI 
}.

Hint Resolve  cI_cont. 

Lemma Iconteq_ext {A} (f g : mf A) (It : ContIntPos A) :
         (forall x, f x = g x) -> It f = It g. 
Proof.
intros HH.
destruct It; simpl.
apply ap; apply path_forall;
trivial.
Qed.

Lemma ContIntPos_eq0 {A} (J H : ContIntPos A) :
          cI J = cI H -> J = H.
Proof. 
intros Hx.
destruct J; destruct H; simpl in Hx;
destruct Hx.
assert (Hcont : cI_cont0 = cI_cont1).
apply path_ishprop.
rewrite Hcont.
reflexivity. 
Qed. 
 
End ContIntegrals. 