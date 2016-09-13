Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import LowerR Distr.

Set Implicit Arguments.

Record CutPos := mkCp{
         ct :> Cut;
         Cutpos : (0 <= ct) }.

Definition LeCp : Le CutPos := CutLe. 
                                    
Instance LeCp_partial_order : Transitive LeCp.
Proof.
intros x y z H H'. 
unfold LeCp in *. 
transitivity y; trivial. 
Defined.    

Definition LtCp : Lt CutPos := CutLt. 

Definition PlusCp : Plus CutPos. 
intros a b.
destruct a as (a,Hpa).
destruct b as (b,Hpb). 
exists (a + b). 
transitivity (CutPlus 0 0).  
rewrite CutPlus_left_id. auto. 
generalize cut_plus_le_preserving.
intro HC.
transitivity (CutPlus a 0).
rewrite (CutPlus_comm a 0). 
apply HC; trivial. 
apply HC; trivial. 
Defined.

Lemma LeCp_Plus_mon (A : hSet) : forall x y z t: CutPos,
      LeCp x y -> LeCp z t -> LeCp (PlusCp x z) (PlusCp y t). 
Proof.
intros x y z t Hxy Hzt. 
unfold LeCp in *.
destruct x as (x,xP).
destruct y as (y,yP).
destruct z as (z,zP).
destruct t as (t,tP).
simpl in *.
generalize cut_plus_le_preserving. intro Hcp.
red in Hcp. 
transitivity (y + z).
transitivity (CutPlus x z).
reflexivity.
transitivity (CutPlus y z). 
rewrite (CutPlus_comm x z). 
rewrite (CutPlus_comm y z). 
apply cut_plus_le_preserving.  
trivial. 
reflexivity.
apply cut_plus_le_preserving; trivial. 
Qed.

Definition CutO : Zero CutPos. 
exists CutZero; auto. Defined. 

Lemma zero_le_one : '0 <= '1.
Proof.
red.
assert (CutLe (QCut 0) (QCut 1)).   
unfold QCut. 
unfold CutLe. 
intros q H0.
simpl in *.
unfold semi_decide in *. 
destruct (decide (q < 0)). 
destruct (decide (q < 1)). 
trivial.
assert (H1 : q < 1). 
transitivity 0; trivial.
apply Q00.
case (n H1). 
destruct (decide (q < 1)); try trivial. 
apply top_greatest.
trivial. 
Defined. 

Definition CutI : One CutPos. 
exists CutOne.
transitivity CutZero. auto.
unfold CutZero, CutOne. apply zero_le_one. 
Defined.

Lemma LeCp_0_Left (A : hSet) : LeftIdentity PlusCp CutO.
intros y.
destruct y as (y,Hy). 
destruct CutO as (CO,HPCO).
Admitted.

Lemma LeCp_0_Right (A : hSet) : RightIdentity PlusCp CutO.
Admitted. 