Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import Qaxioms LowerR Distr Dedekind_pos.

Set Implicit Arguments.  

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
specialize (H11 x).   
specialize (H21 x).
apply LeCp_Plus_mon; trivial. 
apply LeCp_Plus_mon; trivial.
Qed.

Lemma fplus_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          fLe f1 f2 -> fLe g1 g2 -> fLe (fplus f1 g1) (fplus f2 g2).
intros A f1 f2 g1 g2 H1 H2.
unfold fLe.
intros x.
apply LeCp_Plus_mon; trivial.
Qed.  

Hint Immediate fplus_le_compat fplus_eq_compat.

(** *** Elementary properties on operations *)

Lemma fle_fplus_left : forall (A:hSet) (f g : MF A),
                           fLe f  (fplus f g).
intros. intro x.
rewrite fplus_simpl. simpl.
transitivity (PlusCp (f x) CutO).
generalize (LeCp_0_Right A (f x)). intros L.
rewrite L.
unfold LeCp. 
reflexivity.
apply LeCp_Plus_mon; trivial.
unfold LeCp; reflexivity.
apply (g x). 
Qed. 

Lemma fle_fplus_right : forall (A:hSet) (f g : MF A), 
                           fLe g (fplus f g).
intros. intro x.
rewrite fplus_simpl. simpl.
transitivity (PlusCp CutO (g x)).
generalize (LeCp_0_Left A (g x)). intros L.
rewrite L.
unfold LeCp. 
reflexivity.
apply LeCp_Plus_mon; trivial.
apply (f x). 
unfold LeCp; reflexivity.
Qed. 

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




Definition fSub_pos (A:hSet) (f g: MF A) (H : fLe f g) : MF A.
Proof.
intros x.
specialize (H x).
unfold LeCp in H. 
destruct (f x) as (fx,Hfx). 
destruct (g x) as (gx,Hgx). 
simpl in H. 
pose (hx := gx - fx).
assert (0 <= hx).
unfold hx.
apply LeMinus_Pos; trivial. 
refine (mkCp X). 
Defined.   
  
Lemma I_mon (A : hSet) : forall (f g : MF A) (In : IntPos A),
                 fLe f g -> LeCp (I In f) (I In g). 
Proof. 
intros f g In Hle.
unfold LeCp.   
simpl. 
assert (H : I In g = I In (fplus (fSub_pos Hle) f)).
unfold fSub_pos. 
unfold fplus. 
admit.

rewrite H. 
destruct In. 
simpl in *.
specialize (I_add0 (fSub_pos Hle) f). 
rewrite I_add0.
admit. 
Admitted.

Lemma Ieq_ext (A : hSet) (f g : MF A) (It : IntPos A) :
         (forall x, ct (f x) = ct (g x)) -> ct (I It f) = ct (I It g). 
Proof.
intros Hx. 
assert (H1 : LeCp (I It f) (I It g)). 
apply I_mon.
intros y.
unfold LeCp; rewrite (Hx y). 
reflexivity. 
assert (H2 : LeCp (I It g) (I It f)).
apply I_mon.
intros y.
unfold LeCp; rewrite (Hx y).  
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