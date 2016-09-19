

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import Qaxioms LowerR Distr Dedekind_pos.

Set Implicit Arguments.  

Definition MF (A:hSet) : Type := A -> Cut.

Definition fLe (A : hSet) : Le (MF A). 
Proof.
unfold Le; red; intros f g.
unfold MF in f, g.
refine (forall x:A, (f x) <= (g x)).  
Defined.

(* Order properties on f-ops *)
Lemma fle_intro : forall (A:hSet) (f g : MF A), (forall x, (f x) <= (g x)) -> (fLe f g).
intros; intro x; trivial.
Save.
Hint Resolve fle_intro.

Lemma fle_intro2 : forall (A : hSet) (f g : MF A), fLe f g -> (forall x, (f x) <= (g x)).
intros. auto.
Save.

Lemma feq_intro : forall (A:hSet) (f g : MF A), (forall x, f x = g x) -> f == g.
intros; intro x; trivial.
Qed.
Hint Resolve feq_intro.

(** *** Operations on MF *)
Definition fplus (A:hSet) (f g : MF A) : MF A := 
               fun x => CutPlus (f x) (g x).

Definition fzero (A:hSet) : MF A := 
               fun x => CutZero.

Lemma  fplus_simpl : forall (A:hSet)(f g : MF A) (x : A), 
                        fplus f g x = CutPlus (f x) (g x).
trivial.
Save.

Lemma  fplus_def : forall (A:hSet)(f g : MF A), 
                     fplus f g = fun x => CutPlus (f x) (g x).
trivial.
Save.

Implicit Arguments fzero [].

Lemma fzero_simpl : forall (A:hSet)(x : A), fzero A x = '0.
trivial.
Save.

Lemma fzero_def : forall (A:hSet), fzero A = fun x:A => '0.
trivial.
Save.

Hint Resolve fplus_simpl fzero_simpl.

Definition fone (A:hSet) : MF A := fun x => '1.
Implicit Arguments fone [].

Lemma fone_simpl : forall (A:hSet) (x:A), fone A x = '1.
trivial.
Save.

Lemma fone_def : forall (A:hSet), fone A = fun (x:A) => '1.
trivial.
Save.

Definition fminus (A : hSet) (f g : MF A) : MF A. 
Proof. 
refine (fun x => CutPlus (f x) (CutNeg (g x))). 
Defined. 

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
specialize (H11 x).   
specialize (H21 x).
generalize cut_plus_le_preserving. intro Hcp.
red in Hcp. 
transitivity (f2 x + g1 x).
rewrite (CutPlus_comm (f1 x) (g1 x)). 
Admitted.
 
Lemma fplus_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          fLe f1 f2 -> fLe g1 g2 -> fLe (fplus f1 g1) (fplus f2 g2).
intros A f1 f2 g1 g2 H1 H2.
unfold fLe.
intros x.
Admitted.
  

Hint Immediate fplus_le_compat fplus_eq_compat.

(** *** Elementary properties on operations *)

Lemma fle_fplus_left : forall (A:hSet) (f g : MF A),
                           fLe f  (fplus f g).
Admitted.

Lemma fle_fplus_right : forall (A:hSet) (f g : MF A), 
                           fLe g (fplus f g).
Admitted.
 
Hint Resolve fle_fplus_left  fle_fplus_right.


Global Instance dedek_lt_semi_decide : forall x q, SemiDecide (QCut q < x)
  := fun x q => lower x q.

Definition dedekind_Sier : Cut -> Sier. 
intros c. 
refine (dedek_lt_semi_decide c 0).   
Defined. 

Lemma dedekind_Sier_order_pres : forall c d : Cut,
     CutLe c d -> SierLe (dedekind_Sier c) (dedekind_Sier d). 
Proof.
intros c d H. 
unfold CutLe in H. 
unfold dedekind_Sier.
unfold dedek_lt_semi_decide. 
specialize (H 0).
apply imply_le; trivial.   
Qed.

Definition nat_cut_prod (c : Cut) (n : nat) : Cut.
Proof.
destruct c.
pose (qn := pos_of_nat n).
destruct qn as (qn,Qnpos). 
pose (lower_n := fun q => lower (Qmult qn q)).
pose (upper_n := fun q => upper (Qmult qn q)).
simpl in *.
assert (cut_nat_iscut : IsCut lower_n upper_n).
split.
apply tr.
destruct cut_iscut.
Admitted.


Lemma ncp_lower : forall (n : nat) (c : Cut) (q : Q),
                   lower (nat_cut_prod c n) q -> lower c q.   
Admitted.

Lemma nat_cut_prod_scal : forall (n m : nat) a b, 
  a <= nat_cut_prod b m                                          
  -> nat_cut_prod a n ≤ nat_cut_prod b (m * n). 
Proof. Admitted.

Definition MF_Open (A : hSet) : MF A -> OpenSub A.
Proof.
intros f x.
specialize (f x).   
refine (dedekind_Sier f). 
Defined.

Definition MF_nat_prod (A : hSet) (n : nat) : MF A -> MF A.
Proof. 
intros f. 
intros x. 
specialize (f x).   
refine (nat_cut_prod f n). 
Defined. 

Lemma MF_pos_MFnp_pos (A : hSet) : forall (n:nat) (f:MF A),
        forall x, '0 <= (f x) -> '0 <= ((MF_nat_prod n f) x). 
intros n f x H. 
unfold MF_nat_prod. 
Admitted. 

Lemma Nf_Ole (A : hSet) : forall (f g : MF A), OSLe (MF_Open f) (MF_Open g)
      <-> (exists n, fLe f (MF_nat_prod n g)). 
intros f g.
split; intros H.
unfold MF_Open in H. 
unfold dedekind_Sier in H. 
unfold dedek_lt_semi_decide in H. 
unfold fLe. 
unfold CutLe. 
unfold MF_nat_prod. 
admit.

intros x. 
destruct H as (n,Hn). 
unfold MF_nat_prod in Hn.
unfold MF_Open.
unfold dedekind_Sier. 
unfold dedek_lt_semi_decide.
apply imply_le. 
intros H1. 
specialize (Hn x). 
unfold CutLe in Hn. 
apply Hn in H1. 
apply ncp_lower in H1; trivial. 
Admitted. 


Lemma MF_Open_Top (A : hSet) : forall (f : MF A) (x:A),
    ('0 < (f x))  -> ((MF_Open f) x). 
Proof. 
intros f x Hx. 
unfold MF_Open. 
unfold dedekind_Sier.
unfold dedek_lt_semi_decide.
apply cut_lt_lower; trivial.
Qed.  



Definition M A := MF A -> Cut. 

Definition Mplus (A : hSet) : (M A) -> (M A) -> (M A).  
intros I J f.
specialize (I f).
specialize (J f).
refine (CutPlus I J).
Defined. 

Definition Mdef (A : hSet) (I : M A) :=
              (I (fzero A)) = CutZero.

Definition Mprob (A : hSet) (I : M A) :=
              CutLe (I (fone A)) CutOne. 

Definition Mstable_add (A : hSet) (I : M A) :=
  forall f g:MF A, (I (fplus f g)) = (CutPlus (I f) (I g)).

Definition Mpos (A : hSet) (I : M A) :=
  forall (f : MF A), (forall x, 0 <= f x) -> 0 <= I f.

Record IntPos (A:hSet) : Type := 
  {I : M A;
   I_def : Mdef I;
   I_add : Mstable_add I;
   I_prob : Mprob I;
   I_pos : Mpos I 
}.

Hint Resolve I_def I_add I_prob I_pos. 


Definition fSub_pos (A:hSet) (f g: MF A) (H : fLe f g) : MF A.
Proof.
intros x.
specialize (H x).
pose (hx := CutPlus (g x) (CutNeg (f x))).
refine hx.
Defined.   

Definition positive_MF (A : hSet) (f : MF A) := forall x, 0 <= f x. 
  
Lemma I_mon (A : hSet) : forall (f g : MF A) (In : IntPos A),
          (*positive_MF f -> positive_MF g -> *)
          fLe f g -> CutLe (I In f) (I In g). 
Proof. 
intros f g In Hle.
assert (H : I In g = I In (fplus (fSub_pos Hle) f)).
unfold fSub_pos. 
unfold fplus.
assert (H2 : forall x, g x =
         CutPlus (CutPlus (g x) (CutNeg (f x))) (f x)). 
intros x. 
rewrite <- CutPlus_assoc.  
rewrite CutPlus_left_inverse.
rewrite CutPlus_comm. 
rewrite CutPlus_left_id. 
reflexivity. 
destruct In. 
simpl. 
admit. (* Ok *)

rewrite H. 
destruct In. 
simpl in *.
specialize (I_add0 (fSub_pos Hle) f). 
rewrite I_add0.
assert (H3 : I0 f = CutPlus (I0 f) CutZero). 
rewrite CutPlus_comm, CutPlus_left_id. 
reflexivity.
assert (H4 :
          CutLe (CutPlus (I0 f) CutZero)
                (CutPlus (I0 (fSub_pos Hle)) (I0 f))
          -> 
          CutLe (I0 f) (CutPlus (I0 (fSub_pos Hle)) (I0 f))). 
intros HH. 
rewrite <- H3 in HH; trivial. 
apply H4. clear H3 H4 H. 
rewrite <- (CutPlus_comm (I0 f) _). 
apply cut_plus_le_preserving.
specialize (I_pos0 (fSub_pos Hle)). 
apply I_pos0. 
intros x. 
unfold fSub_pos. 
unfold fLe in Hle. 
admit. (* Ok *) 
Admitted.

Lemma Ieq_ext (A : hSet) (f g : MF A) (It : IntPos A) :
         (forall x, (f x) = (g x)) -> (I It f) = (I It g). 
Proof.
intros Hx. 
assert (H1 : (I It f) <= (I It g)). 
apply I_mon.
intros y.
rewrite (Hx y). 
reflexivity. 
assert (H2 : (I It g) <= (I It f)).
apply I_mon; trivial. 
intros y. 
rewrite (Hx y).  
reflexivity.
apply cut_eq. 
split; auto.
split;
unfold LeCp in H1;
unfold LeCp in H2; 
unfold CutLe in *;
generalize (CutLe_upper);
intros S;
apply S; auto.
Qed. 