Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import Qaxioms LowerR Distr Dedekind_pos Intpos.

Set Implicit Arguments.  


Definition MF_Open (A : hSet) : MF A -> OpenSub A.
Proof.
intros f x.
specialize (f x).   
refine (dedekind_Sier f). 
Defined.


Lemma MF_Open_Top (A : hSet) : forall (f : MF A) (x:A),
    (CutLt CutO (f x))  -> ((MF_Open f) x). 
Proof. 
intros f x Hx. 
unfold MF_Open. 
unfold dedekind_Sier.
unfold dedek_lt_semi_decide.
destruct (f x). 
simpl in *.
apply cut_lt_lower.
auto. 
Qed.  

Definition Regularity (A : hSet) := forall (O : OpenSub A),
           exists (f : MF A), O = MF_Open f.

Definition Compact (A : hSet) := forall (O : OpenSub A),
           exists (fn : nat -> OpenSub A), forall n, OSLe (fn n) O
                                     /\ (Oslub fn = O).

Definition Cover (A : hSet) : Compact A ->  OpenSub A -> (nat -> OpenSub A). 
intros HC U n.
specialize (HC U).
destruct HC as (fn,HC). 
refine (fn n).  
Defined.

Lemma MF_Top_inv_regular (A : hSet) (Hr : Regularity A) :
      forall (O : OpenSub A), exists (f : MF A), O = MF_Open f 
               /\ (forall x, (CutLt CutO (f x))  -> (O x)).
Proof. 
intros O. 
specialize (Hr O). 
destruct Hr as (f,Hr). 
exists f.
split; trivial. 
intros x.
rewrite Hr. 
apply MF_Open_Top. 
Qed.


Definition LowerPart_aux : CutPos -> Rlow. 
Proof.
intros C. 
generalize (lower_le C).
intro H0.
generalize iscut_lower_rounded.
intro H2.
destruct C as (C,HP). 
destruct C. 
unfold QPred in lower.
exists (fun q:rationals.Q => lower q).
intros x y H H'.
simpl in H0.
specialize (H0 x y H).
apply H0.
auto.
simpl in H0.
intros x Hx.
specialize (H2 lower upper cut_iscut x). 
apply H2 in Hx.
apply Trunc_functor with (∃ r : rationals.Q, x < r ∧ lower r).
intros (r,Hr).
exists r; split; apply Hr.
trivial. 
Defined.

Definition LowerPart : CutPos -> RlowPos. 
intros C.
exists (LowerPart_aux C). 
intros p Hp.
destruct C as (C,HPC). simpl. 
red in HPC.
unfold CutLe in HPC. 
specialize (HPC p). 
apply HPC.
apply cut_lt_lower.
assert (CutLt (QCut p) (QCut 0)).   
unfold QCut. 
unfold CutLt. 
apply tr.
exists (p/2). 
simpl.
unfold semi_decide. 
split.
+ destruct (decide (p < p/2)). 
  apply top_greatest. 
  assert (HH : p < p / 2). 
  apply QA5; trivial.  
  case (n HH). 
+ destruct (decide (p / 2 < 0)). 
  apply top_greatest. 
  assert (HH : p / 2 < 0). 
  apply QA6; trivial. 
  case (n HH). 
+ auto.    
Defined. 

Lemma Le_Cut_LP : forall c d : CutPos, LeCp c d -> Rlle (LowerPart c) (LowerPart d). 
intros c d Hl. 
unfold LowerPart. 
simpl.
intros q Hq.
destruct c as (c,Hc). 
destruct d as (d,Hd).
simpl in *.
unfold LeCp in Hl. 
simpl in Hl. 
unfold CutLe in Hl. 
specialize (Hl q). 
apply Hl; trivial. 
Qed. 
(*
Definition MaxRS_RD : Sier -> CutPos -> CutPos. 
intros s c.
exists (CutJoin c (Sier_RD s)).
transitivity c.
apply c. apply cut_lattice_order. 
Defined.

Lemma MaxRS_RD_mon_l (A : hSet) :  forall (s s' : Sier) (c : CutPos),
              SierLe s s' -> LeCp (MaxRS_RD s c) (MaxRS_RD s' c).
Proof. 
intros s s' c H. 
unfold LeCp. 
unfold MaxRS_RD. 
simpl.
assert (CutLe (Sier_RD s) (Sier_RD s')). 
admit.

apply cut_lattice_order. 
apply cut_lattice_order. 
transitivity (Sier_RD s'). 
trivial.
apply cut_lattice_order. 
Admitted. 
 *)

Lemma CutMeet_Pos : forall a b : CutPos, 0 <= CutMeet a b. 
Admitted.

Lemma CutMeet_Pos_zero_l : forall a : CutPos, CutMeet a CutO = CutO. 
Admitted.

Lemma CutMeet_Pos_zero_r : forall a : CutPos, CutMeet CutO a = CutO.
Admitted. 

Lemma CutMeet_zero_l : forall a : Cut, 0 <= a -> CutMeet a CutZero = CutZero. 
Admitted.

Lemma CutMeet_zero_r : forall a : Cut, 0 <= a -> CutMeet CutZero a = CutZero.
Admitted. 

Definition Ilub (A : hSet) {Hr : Regularity A} {Hc : Compact A} :
         OpenSub A -> IntPos A -> RlowPos.
Proof.
intros U I.
pose (Fn := Cover Hc).   
destruct I.
assert (Hn : forall n, exists (fn : MF A), (Fn U n) = MF_Open fn
               /\ (forall x, (CutLt CutO (fn x))  -> ((Fn U n) x))).  


assert (forall n, Rlle [0] (LowerPart (I0 (Meet_MF_OS HR (Fn n) U)))). 
intros n.
unfold M in I0.
apply RlowPos_pos.
refine (RllubPos (fun n =>
                    ((@Rlow_RlowPos (LowerPart (I0 (Meet_MF_OS HR (Fn n) U)))) (X n)))).
Defined.



Definition Meet_MF_OS (A : hSet) : (Regularity A) -> (MF A) -> (OpenSub A) -> MF A. 
Proof.
intros HR f U x. 
pose (O := MF_Open f). 
pose (X := MeetOpen U O). 
specialize (HR X). 
destruct HR as (g,HR).
refine (g x). 
Defined. 

Variable A : hSet.
Hypothesis HR : Regularity A.

Lemma Meet_MF_OS_mon  : forall (f : MF A) (U V : OpenSub A),
                 OSLe U V -> fLe (Meet_MF_OS HR f U) (Meet_MF_OS HR f V). 
Proof.
intros f U V HUV x.
unfold LeCp.
unfold Meet_MF_OS.   
generalize HR. intro R. 
unfold Regularity in R. 
destruct (R U) as (p1u,p2u).
destruct (R V) as (p1v,p2v). 
rewrite p2u, p2v.
destruct R. 
unfold MF_Open. 
simpl. 
destruct  (R
          (MeetOpen (λ x0 : A, dedekind_Sier (p1v x0))
             (λ x0 : A, dedekind_Sier (f x0)))). 
unfold MF_Open in *.
rewrite <- p2u in proj2_sig.
rewrite <- p2v in proj2_sig0. 
admit. 
Admitted.
(* ATTENTION : soucis dans definition de Regularity *) 


Lemma Meet_MF_OS_Empty  : forall (f : MF A),
          forall x,  ct (Meet_MF_OS HR f (EmptySpaceO A) x) = ct CutO. 
Proof.
intros f x.
generalize HR. intros R.
unfold Meet_MF_OS. 
unfold Regularity in R. 
destruct (R (EmptySpaceO A)) as (R1,R2).
(*unfold MFO_eq in R2.
specialize (R2 x).
unfold EmptySpaceO in R2.
assert (H : R1 x = CutO). 
apply R2. 
reflexivity. 
rewrite H.
apply cut_lattice_order.
simpl. 
destruct (f x). simpl.
assert (H2 : CutMeet ct0 CutZero = CutZero).
simpl. 
apply CutMeet_zero_l; trivial. 
rewrite H2. reflexivity. 
apply CutMeet_Pos. 
Qed.    *)
Admitted. 

Definition Ilub : OpenSub A -> (nat -> MF A) -> IntPos A ->  RlowPos.
Proof.
intros U Fn I.
destruct I.
assert (forall n, Rlle [0] (LowerPart (I0 (Meet_MF_OS HR (Fn n) U)))). 
intros n.
unfold M in I0.
apply RlowPos_pos.
refine (RllubPos (fun n =>
                    ((@Rlow_RlowPos (LowerPart (I0 (Meet_MF_OS HR (Fn n) U)))) (X n)))).
Defined.

Lemma Illub_mon : forall (un : nat -> MF A) (U V : OpenSub A) (I : IntPos A),
                  OSLe U V -> Rlle (Ilub U un I) (Ilub V un I). 
Proof. 
intros un U V I HUV. 
unfold Ilub.
generalize (Rllub_le).
intro HP. 
apply Rllub_mon.
intros n.
apply toRlseq_mon.
apply A. 
simpl.
apply Le_Cut_LP.
apply I_mon.
apply Meet_MF_OS_mon. 
trivial. 
Qed.
(*
Lemma Illub_linear : forall (un : nat -> MF A) (U V : OpenSub A) (I : IntPos A),
    Rleq (RlP_Plus (Ilub U un I) (Ilub V un I))
         (Ilub (U V) un I).     *)
(* need to define a correct Regularity notion *)


Lemma Illub_modular : forall (un : nat -> MF A) (U V : OpenSub A) (I : IntPos A),
    Rleq (RlP_plus (Ilub (JoinOpen U V) un I) (Ilub (MeetOpen U V) un I))
         (RlP_plus (Ilub U un I) (Ilub V un I)).
Proof. 
intros un U V I.
split.   
unfold Ilub. 
Admitted. 

Lemma Ilub_MF_ext : forall (I : IntPos A) (un : nat -> MF A)
                                        (U V : OpenSub A),
           OSEq U V -> Rleq (Ilub U un I) (Ilub V un I). 
Proof.
intros I un U V HUV.
split;
apply Illub_mon; 
apply HUV.
Qed.  

Lemma Ilub_empty : forall (I : IntPos A) (un : nat -> MF A),
           Rleq (Ilub (EmptySpaceO A) un I) RlP_0. 
intros I un.  
unfold Ilub.
split.
apply Rllub_le.
intro n. 
apply toRlseq_le_r. 
apply A.
(*
rewrite Meet_MF_OS_Empty. 
simpl.
rewrite I_def.*)
admit. 

Admitted. 

Definition mu_Radon : (nat -> MF A) -> IntPos A -> D A.
intros Ln I.
exists (fun U : OpenSub A => Ilub U (fun n => Ln n) I).
+ intros U V.
  generalize (Illub_modular Ln U V I).
  intro IM. 
  apply Rleq_sym.
  trivial. 
+ apply Ilub_empty. 
+ intros U V H.
  unfold Ilub. 
  simpl. 
  apply Illub_mon. 
  trivial.
+ admit.
+ admit.   
Admitted. 