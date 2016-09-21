Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.interfaces.rationals
               HoTTClasses.theory.rationals
               HoTTClasses.orders.rings. 
Require Import HoTT.HSet HoTT.Basics.Decidable HoTT.Basics.Trunc
               HProp HSet Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom. 
Require Import Qaxioms. 

Local Set Universe Minimization ToSet.

Definition Rdec  {A : Type} (R : relation A) :=  forall x y, R x y \/ ~ R y x. 

Section GeneralIlq.

Variable A : Type.

Definition APred := A -> Sier. 

Variable Rle : relation A.
Variable Rlt : relation A.
Hypothesis Hdec : Rdec Rle.
Hypothesis Hd : DecidablePaths A. 
Hypothesis Hda : AntiSymmetric Rle.
Hypothesis Hdt : TotalRelation Rle.
Hypothesis HA : Apart A.
Hypothesis ATA : TrivialApart A. 
Hypothesis FR : FullPseudoOrder Rle Rlt. 

Section isGen.

Variable elt : APred.
  
Class IsGen : Type :=
  {
    is_inhab : merely (exists q, elt q);
    is_rounded : forall q, iff@{Set UQ UQ} (elt q)
           (merely (exists r, Rlt q r /\ elt r))
  }.

End isGen.  

Record Gen :=  {
      elt : APred;
      elt_Gen : IsGen elt
}.

Global Existing Instance elt_Gen.

Definition inhab (c : Gen) := is_inhab (elt c).
Definition rounded (c : Gen) := is_rounded (elt c). 

Definition IsGen_conjunction r : IsGen r -> _
  := fun c => (is_inhab r, is_rounded r). 

Global Instance isGen_conj_isequiv {r}
  : IsEquiv (IsGen_conjunction r).
Proof.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- intros E;split; apply E. 
- red;simpl. intros. reflexivity.
- red;simpl. reflexivity.
- simpl. reflexivity.
Defined.

Lemma gen_le : forall a q r, elt a r -> Rle q r -> elt a q. 
Proof.
intros a q r E1 E2.
destruct (Hdec r q) as [E3|E3].
- destruct (antisymmetry Rle _ _ E2 E3). trivial.
- case (E3 E2).  
Qed. 

Section contents.
Context `{Funext} `{Univalence}.

Global Instance GR_hprop@{} : forall r, IsHProp (IsGen r).
Proof.
intros. apply (@trunc_equiv _ _ ((IsGen_conjunction r)^-1) _ _ _).
Qed.

Lemma gen_eq0 : forall a b : Gen, elt a = elt b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E; destruct E; apply ap.
apply path_ishprop. 
Qed. 

Instance gen_isset@{} : IsHSet Gen.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => elt a = elt b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply gen_eq0;apply E.
Qed.

Lemma gen_eq : forall a b : Gen, (forall q, elt a q <-> elt b q) -> a = b.
Proof.
intros a b E; apply gen_eq0; apply path_forall;intros q;apply (antisymmetry le);
apply imply_le;apply E.
Qed.

Lemma gen_orders : forall (c : Gen) (q r : A), elt c q -> ~ elt c r -> Rlt q r.
Proof.
intros c q r E1 E2.
destruct (Hdec r q) as [E|E];trivial.
assert (Hh : elt c r). 
apply gen_le with q; trivial. 
case (E2 Hh).
destruct E2. 
assert (Hh : Rle r q).
destruct (Hdt r q); trivial.
case (E r0). 
apply gen_le with q; trivial. 
Qed.  

Global Instance GenLe_l : Le@{UQ UQ} Gen
  := fun a b => forall q, elt a q -> elt b q.

Global Instance GenLe_r : Le@{UQ UQ} Gen
  := fun a b => GenLe_l b a.

Arguments GenLe_l _ _ /.
Arguments GenLe_r _ _ /.

Instance GenLe_l_partial_order@{} : PartialOrder GenLe_l.
Proof.
repeat split.
- apply _.
- apply _.
- intros a q;trivial.
- intros a b c E1 E2 q E3. auto.
- intros a b E1 E2. apply gen_eq.
  intros;split;(apply E1 || apply E2).
Qed.

Instance GenLe_r_partial_order@{} : PartialOrder GenLe_r.
Proof.
repeat split.
- apply _.
- apply _.
- intros a q;trivial.
- intros a b c E1 E2 q E3. auto.
- intros a b E1 E2. apply gen_eq.
  intros;split;(apply E1 || apply E2).
Qed.

Global Instance GenLt_l : Lt@{UQ UQ} Gen :=
  fun a b => merely (exists q, elt b q /\ ~ elt a q).

Global Instance GenLt_r : Lt@{UQ UQ} Gen :=
  fun a b => GenLt_l b a. 

Arguments GenLt_l _ _ /.
Arguments GenLt_r _ _ /.

Global Instance GenApart : Apart@{UQ UQ} Gen
  := fun a b => a < b \/ b < a.

Instance GenLt_strict_order@{} : StrictOrder GenLt_l.
Proof.
repeat split.
- apply _.
- intros a;hnf;apply (Trunc_ind _);intros [q [E1 E2]].
  case (E2 E1). 
- intros a b c E E';revert E; apply (Trunc_ind _);intros [q [E1 E2]];
  revert E';apply (Trunc_ind _);intros [r [E3 E4]].
  apply tr;exists q. split. 
  + apply gen_le with r;  trivial.
    assert (H' : Rlt q r). apply gen_orders with b; trivial.
    destruct (Hdt q r); trivial. 
    apply FR in r0. case (r0 H'). 
  + trivial.
Qed.

Notation "a <= b" := (GenLe_l a b). 
Notation "a >= b" := (GenLe_r a b). 


Lemma gen_stable : forall r p q, elt r p -> (p=q) -> elt r q.
intros r p q Hp He.
apply gen_le with p; trivial.
rewrite He.
reflexivity.
Save.

Lemma gen_mon : forall (x y : Gen) (p q :A),
    (Rle q p) -> x <= y -> elt x p -> elt y q.
intros x y p q Hpq Hxy Hx.
apply gen_le with p; try assumption. auto. 
Save.


End contents. 

End GeneralIlq.

Section GeneralRelQ. 

Definition QPred := APred Q. 

Variable Qle_g : relation Q.
Variable Qlt_g : relation Q.
Hypothesis Hdec : Rdec Qle_g.
Hypothesis Hda : AntiSymmetric Qle_g.
Hypothesis Hdt : TotalRelation Qle_g.
Hypothesis FR : FullPseudoOrder Qle_g Qlt_g. 
  
Section GeneralDefQ. 

Variable elt : QPred. 

Definition IsGenQ := IsGen Q Qlt_g elt. 

End GeneralDefQ. 

Record GenQ :=  {
      eltQ : QPred;
      elt_GenQ : IsGenQ eltQ
}. 

Global Instance  GenLt_semi_dec : forall r q, SemiDecide (Qlt_g r q). 
Proof. 
intros r q.
apply decidable_semi_decide. 
destruct (Hdt r q). 
destruct (Qdec r q). 
right. 
apply FR. 
rewrite p. 
reflexivity. 
left.
apply trivial_apart in n.
pose (FR' := FR). 
destruct FR' as (_,(_,_,_,_,FR'),_).  
specialize (FR' r q).
apply FR' in n. 
destruct n. 
trivial.
assert (Hh : ~ Qlt_g q r). 
apply FR; trivial. 
case (Hh l). 
destruct (Qdec r q). 
rewrite p. 
right. 
apply (irreflexivity Qlt_g). 
right. apply FR; trivial. 
Defined.


Lemma QIsGenQ : forall q : Q, IsGenQ (fun r => semi_decide (Qlt_g r q)).
Proof.
intros q; split.
+ apply tr; exists (q - 1). admit. 
  

