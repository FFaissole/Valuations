Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet Types.Universe
               UnivalenceImpliesFunext TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 
Require Import LowerR Dedekind Distr.

Set Implicit Arguments.

Record CutPos := mkCp{
         ct :> Cut;
         Cutpos : (0 <= ct) }.

Definition LeCp : Le CutPos := CutLe. 


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

Definition CutO : Zero CutPos. 
exists CutZero; auto. Defined. 

Lemma zero_le_one : '0 <= '1.
Proof.
generalize (straddle_monotone 1 0).
intro H.
unfold straddle in H.
specialize (H 1). assert (H2 : 0 < 1). 
admit.
Admitted. 

Definition CutI : One CutPos. 
exists CutOne.
transitivity CutZero. auto.
unfold CutZero, CutOne. apply zero_le_one. 
Defined.

Definition MF (A:hSet) : Type := A -> CutPos.

Definition fLe (A : hSet) : Le (MF A). 
Proof.
unfold Le; red; intros f g.
unfold MF in f, g.
refine (forall x:A, LeCp (f x) (g x)).  
Defined.

(* Order properties on f-ops *)
Lemma fle_intro : forall (A:hSet) (f g : MF A), (forall x, LeCp (f x) (g x)) -> (fLe f g).
intros; intro x; trivial.
Save.
Hint Resolve fle_intro.

Lemma fle_intro2 : forall (A : hSet) (f g : MF A), fLe f g -> (forall x, LeCp (f x) (g x)).
intros. auto.
Save.

Lemma feq_intro : forall (A:hSet) (f g : MF A), (forall x, f x = g x) -> f == g.
intros; intro x; trivial.
Qed.
Hint Resolve feq_intro.

(** *** Operations on MF *)
Definition fplus (A:hSet) (f g : MF A) : MF A := 
               fun x => PlusCp (f x) (g x).

Definition fzero (A:hSet) : MF A := 
               fun x => CutO.

Lemma  fplus_simpl : forall (A:hSet)(f g : MF A) (x : A), 
                        fplus f g x = PlusCp (f x) (g x).
trivial.
Save.

Lemma  fplus_def : forall (A:hSet)(f g : MF A), 
                     fplus f g = fun x => PlusCp (f x) (g x).
trivial.
Save.

Implicit Arguments fzero [].

Lemma fzero_simpl : forall (A:hSet)(x : A), fzero A x = CutO.
trivial.
Save.

Lemma fzero_def : forall (A:hSet), fzero A = fun x:A => CutO.
trivial.
Save.

Hint Resolve fplus_simpl fzero_simpl.

Definition fone (A:hSet) : MF A := fun x => CutI.
Implicit Arguments fone [].

Lemma fone_simpl : forall (A:hSet) (x:A), fone A x = CutI.
trivial.
Save.

Lemma fone_def : forall (A:hSet), fone A = fun (x:A) => CutI.
trivial.
Save.


Definition fEq (A : hSet) : MF A -> MF A -> Type. 
Proof.
intros f g.
refine (fLe f g /\ fLe g f).
Defined. 

Lemma fplus_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
          fEq f1 f2 -> fEq g1 g2 -> fEq (fplus f1 g1) (fplus f2 g2).
intros A f1 f2 g1 g2 (H11,H12) (H21,H22).
split;
intro x;
repeat (rewrite fplus_simpl);
simpl. generalize CutLe_rat_preserving.
intros T.
admit. (* monotone dedekind *)
Admitted.

Lemma fplus_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          fLe f1 f2 -> fLe g1 g2 -> fLe (fplus f1 g1) (fplus f2 g2).
intros A f1 f2 g1 g2 H1 H2.
unfold fLe.
intros x.
simpl.
admit (* idem  *). 
Admitted. 

Hint Immediate fplus_le_compat fplus_eq_compat.


(** *** Elementary properties on operations *)


Lemma fle_fplus_left : forall (A:hSet) (f g : MF A),
                           fLe f  (fplus f g).
intros. intro x.
rewrite fplus_simpl. simpl.
(*generalize (Rl_Plus_r_0). intros RG.
specialize (RG (f x)).
destruct RG as (RG1,RG2).
apply Rlle_trans with (Rl_Plus (f x) [0]).
trivial.
apply Rl_Plus_mon. apply Rlle_refl.
red; simpl; intuition. apply Rlpos. trivial.
Save.*)
Admitted. 

Lemma fle_fplus_right : forall (A:hSet) (f g : MF A), 
                           fLe g (fplus f g).
intros. intro x.
rewrite fplus_simpl. simpl.
(*
generalize (Rl_Plus_r_0). intros RG.
specialize (RG (g x)).
destruct RG as (RG1,RG2).
apply Rlle_trans with (Rl_Plus (g x) [0]).
trivial.
generalize (Rl_Plus_comm (f x) (g x)). intros RPC.
destruct RPC as (RPC1,RPC2).
apply Rlle_trans with (Rl_Plus (g x) (f x)).
apply Rl_Plus_mon. apply Rlle_refl. 
red; simpl; intuition. apply Rlpos. trivial.
trivial.
Save.*)
Admitted. 

Hint Resolve fle_fplus_left  fle_fplus_right.



Definition M A := MF A -> CutPos. 

Definition Mplus (A : hSet) : (M A) -> (M A) -> (M A).  
intros I J f.
specialize (I f).
specialize (J f).
refine (PlusCp I J).
Defined. 

Definition Mdef (A : hSet) (I : M A) :=
              (I (fzero A)) = CutO.

Definition Mprob (A : hSet) (I : M A) :=
              LeCp (I (fone A)) CutI. 

Definition Mstable_add (A : hSet) (I : M A) :=
  forall f g:MF A, (I (fplus f g)) = (PlusCp (I f) (I g)).

Record IntPos (A:hSet) : Type := 
  {I : M A;
   I_def : Mdef I;
   I_add : Mstable_add I;
   I_prob : Mprob I 
}.

Hint Resolve I_def I_add I_prob. 

Lemma I_mon (A : hSet) : forall (f g : MF A) (In : IntPos A),
                 fLe f g -> LeCp (I In f) (I In g). 
Proof. 
intros f g In Hle.
  (*
assert (Hmi : I In f = PlusCp (I In (fplus f (fun x => -(g x)))) (I In g)). *)
Admitted.


(* to change *)

Definition MFO_eq : CutPos -> Sier -> Type. 
intros c s. 
refine ((c = CutI -> s = SierTop)  /\
        (c = CutO -> s = SierBot)). 
Defined.

Definition Regularity (A : hSet) := forall (O : OpenSub A),
                     exists (f : MF A), forall x:A, MFO_eq (f x) (O x). 
(*
Definition Sier_RD : Sier -> CutPos. 
intros x.
destruct (Dec_Sier x).
exact CutI.
exact CutO.
Defined.*)

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
Admitted.

Lemma Le_Cut_LP : forall c d : CutPos, LeCp c d -> Rlle (LowerPart c) (LowerPart d). 
intros c d Hl. 
Admitted. 
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

Definition Meet_MF_OS (A : hSet) : (Regularity A) -> (MF A) -> (OpenSub A) -> MF A. 
Proof. 
intros HR f U x.
specialize (HR U).
destruct HR as (g,HR).
exists (CutJoin (f x) (g x)).
transitivity (f x).
destruct f.
simpl; trivial.
apply cut_lattice_order. 
Defined.

Variable A : hSet.
Hypothesis HR : Regularity A.

Lemma Meet_MF_OS_mon  : forall (f : MF A) (U V : OpenSub A),
                 OSLe U V -> fLe (Meet_MF_OS HR f U) (Meet_MF_OS HR f V). 
Proof.
intros f U V HUV. 
admit.

Admitted.

Lemma Meet_MF_OS_Empty  : forall (f : MF A),
            Meet_MF_OS HR f (EmptySpaceO A) = fun x => CutO. 
Proof.
intros f.   
unfold Meet_MF_OS. 
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

Lemma Illub_modular : forall (un : nat -> MF A) (U V : OpenSub A) (I : IntPos A),
    Rleq (RlP_plus (Ilub (MeetOpen U V) un I) (Ilub (JoinOpen U V) un I))
         (RlP_plus (Ilub U un I) (Ilub V un I)).
Proof. 
intros un U V I. 
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
rewrite Meet_MF_OS_Empty. 
simpl.
rewrite I_def.
admit. 

Admitted. 

Definition mu_Radon : (nat -> MF A) -> IntPos A -> D A.
intros Ln I.
exists (fun U : OpenSub A => Ilub U (fun n => Ln n) I).
unfold modular.
intros U V.
admit. 

unfold empty_op.
apply Ilub_empty. 
intros U V H.
unfold mon_opens.
apply Illub_mon. 
trivial. 
Admitted. 