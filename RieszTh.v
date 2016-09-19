
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import Qaxioms LowerR Distr Integral.

Set Implicit Arguments.  

Definition Regularity (A : hSet) := forall (O : OpenSub A),
           exists (f : MF A), OSEq O (MF_Open f).

Definition Compact (A : hSet) := forall (O : OpenSub A),
           exists (fn : nat -> OpenSub A), forall n, OSLe (fn n) O.

Definition Cover (A : hSet) : Compact A ->  OpenSub A -> (nat -> OpenSub A). 
intros HC U n.
specialize (HC U).
destruct HC as (fn,HC). 
refine (fn n).  
Defined.

Lemma MF_Top_inv_regular (A : hSet) (Hr : Regularity A) :
      forall (O : OpenSub A), exists (f : MF A), OSEq O (MF_Open f)
               /\ (forall x, ('0 < (f x))  -> (O x)).
Proof. 
intros O. 
specialize (Hr O). 
destruct Hr as (f,Hr). 
exists f.
split; trivial. 
intros x.
intros LL.
unfold OSEq in Hr.
unfold OSLe in Hr.
destruct Hr as (Hr1,Hr2).
specialize (Hr2 x).
apply SierLe_imply in Hr2.
trivial.
apply MF_Open_Top; trivial.
Qed.


Definition LowerPart : Cut -> Rlow. 
Proof.
intros C. 
generalize (lower_le C).
intro H0.
generalize iscut_lower_rounded.
intro H2.
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

Lemma Le_Cut_LP : forall c d : Cut, CutLe c d -> Rlle (LowerPart c) (LowerPart d). 
intros c d Hl. 
unfold LowerPart. 
simpl.
intros q Hq.
unfold CutLe in Hl. 
specialize (Hl q). 
apply Hl; trivial. 
Qed. 

Definition Seq_nat_Cover_MF (A : hSet) (Hc : Compact A) (Hr : Regularity A)
            : OpenSub A -> (nat -> MF A). 
Proof.
intros U n. 
destruct (Hr U) as (f_U,Hf_U).
intros x. 
refine ((MF_nat_prod n f_U) x).
Defined.

Lemma Seq_nat_Cover_MF_Empty (A : hSet) (Hc : Compact A) (Hr : Regularity A):
       forall n x, (Seq_nat_Cover_MF Hc Hr (EmptySpaceO A) n x) = CutZero.  
Proof. 
intros n x.
unfold Seq_nat_Cover_MF. 
simpl. 
destruct (Hr (EmptySpaceO A)) as (fO,HfO).
unfold MF_nat_prod. 
unfold MF_Open in HfO. 
unfold dedekind_Sier in HfO. 
unfold dedek_lt_semi_decide in HfO. 
unfold EmptySpaceO in *.
assert (Hf' : lower (fO x) 0 = SierBot).
destruct HfO as (Hf1,Hf2).
unfold OSLe in Hf1.
apply semidecidable_bot.
intros F.
unfold OSLe in Hf2.
specialize (Hf2 x).
apply SierLe_imply in Hf2.
apply not_bot in Hf2; trivial.
trivial. 
admit. 

Admitted.  


Definition Ilub (A : hSet) {Hr : Regularity A} {Hc : Compact A} :
         OpenSub A -> IntPos A -> Rlow.
Proof.
intros U I. 
pose (fn := Seq_nat_Cover_MF Hc Hr U). 
assert (u : nat -> Rlow). 
intros n. 
specialize (fn n).
destruct I. 
pose (Ifn := I fn). 
refine (LowerPart Ifn).
refine (Rllub u). 
Defined.

Lemma Rllub_nm_le (A : hSet) (u v : nat -> Rlow) :
            (forall (n : nat), exists (m : nat), u n <= v (m*n))
            -> Rllub u <= Rllub v. 
Proof. 
intros Hn.                                               
apply Rllub_le. 
intros n.
destruct (Hn n) as (m,Hm). 
generalize (Rllub_lub v).
intros HV. 
specialize (HV (m*n)). 
apply Rlle_trans with (v (m*n)); trivial. 
Qed. 

Lemma Illub_mon (A:hSet) (Hr : Regularity A) (Hc : Compact A) :
                  forall (U V : OpenSub A) (J : IntPos A),
                    OSLe U V -> Rlle ((@Ilub _ Hr) Hc U J)
                                     ((@Ilub _ Hr) Hc V J). 
Proof. 
intros U V J HUV.
unfold Ilub. 
apply Rllub_nm_le; trivial.
simpl. 
intros n. 
generalize Le_Cut_LP. 
intros Hclp.
assert (HM : exists m:nat, (I J (Seq_nat_Cover_MF Hc Hr U n)) <=
                            I J (Seq_nat_Cover_MF Hc Hr V (m * n))).
unfold Seq_nat_Cover_MF.
assert (HI : exists m:nat, fLe (λ x : A,
               MF_nat_prod n
                 (let (proj1_sig, _) := Hr U in
                  proj1_sig) x)
                              (λ x : A,
               MF_nat_prod (m * n)
                (let (proj1_sig, _) := Hr V in
                 proj1_sig) x)).  
unfold fLe.
destruct (Hr U) as (fu,(Hfu1,Hfu2)). 
destruct (Hr V) as (fv,(Hfv1,Hfv2)). 
assert (HN : OSLe (MF_Open fu) (MF_Open fv)).
apply OSLe_trans with V; try trivial.  
apply OSLe_trans with U; try trivial. 
apply Nf_Ole in HN.
destruct HN as (m,HN). 
exists m. 
intros x. specialize (HN x). 
unfold MF_nat_prod in *. 
apply nat_cut_prod_scal; trivial.  
destruct HI as (m,HI). 
exists m. 
apply I_mon. 
simpl. 
unfold positive_MF.
intros x.
destruct (Hr U).
simpl in HI. 
destruct (Hr V).
simpl in HI. 
unfold MF_nat_prod.
destruct (Hr U). 
unfold fLe. 
destruct (Hr U) as (fu,Hfu). 
destruct (Hr V) as (fv,Hfv). 
apply HI.
destruct HM as (m,HM). 
exists m. 
apply Hclp.
trivial. 
Defined. 
 
Lemma Ilub_empty (A : hSet) (Hr : Regularity A) (Hc : Compact A)
       : forall (I : IntPos A),
    Rleq ((@Ilub _ Hr) Hc (EmptySpaceO A) I) RlP_0.
Proof. 
intros J.
split.
unfold Ilub. 
apply Rllub_le. 
intros n q Hn. 
simpl in *. 
unfold semi_decide. 
unfold SemiDec. 
unfold decidable_semi_decide. 
destruct (decide (q < 0)). 
apply top_greatest.
assert (X : forall x, (Seq_nat_Cover_MF Hc Hr (EmptySpaceO A) n x) = CutZero).
apply Seq_nat_Cover_MF_Empty.  
simpl in *. 
assert (Hs : lower (CutZero) q). 
assert (Hi :   I J
            (Seq_nat_Cover_MF Hc Hr
                              (EmptySpaceO A) n) = 0).
generalize (Ieq_ext (Seq_nat_Cover_MF Hc Hr
       (EmptySpaceO A) n) (fun x => 0) J X). 
intros HG.  
assert (X0 : I J (λ _ : A, 0) = 0).
apply I_def. 
rewrite X0 in HG.
trivial. 
rewrite Hi in Hn. 
simpl in Hn. 
unfold semi_decide, SemiDec, decidable_semi_decide in *. 
destruct (decide (q < 0)).
case (n0 l).
case (not_bot Hn).
unfold CutZero in Hs. 
simpl in Hs. 
unfold  semi_decide, SemiDec, decidable_semi_decide in *. 
destruct (decide (q < 0)). 
case (n0 l). 
trivial.
 admit. 
Admitted.

Definition mu_Radon (A : hSet) (Hc : Compact A) (Hr : Regularity A):
                           IntPos A -> D A.
intros I.
assert (Hp : forall U, Q_inject 0 <= (@Ilub _ Hr Hc) U I). 
admit.

exists (fun U : OpenSub A => ((@Rlow_RlowPos ((@Ilub _ Hr Hc) U I)) (Hp U))).
+ intros U V. admit. (* modularity *) 
+ apply Ilub_empty. 
+ intros U V H.
  unfold Ilub. 
  simpl. 
  apply Illub_mon; trivial. 
Admitted.

