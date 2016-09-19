

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient. 

Require Import Qaxioms LowerR Distr Dedekind_pos.

Set Implicit Arguments.

Section Meas. 

Context {A : hSet}.
Universe UN. 

Definition mf : Type@{UN} := A -> CutPos.

Definition ffle : Le mf. 
Proof.
unfold Le; red; intros f g.
unfold mf in f, g.
refine (forall x:A, LeCp (f x) (g x)).  
Defined.

Definition equiv_ff : mf -> mf -> Type := fun x y => ffle x y /\ ffle y x.

Definition MF := @quotient _ equiv_ff  _.

Definition MF_rec {T : Type@{i} } {sT : IsHSet T}
  : forall (dclass : mf -> T)
  (dequiv : forall x y, equiv_ff x y -> dclass x = dclass y),
   MF -> T
:= quotient_rec _.

Definition MF_rec2 {T:Type } {sT : IsHSet T}
  : forall (dclass : mf -> mf -> T)
  (dequiv : forall x1 x2, equiv_ff x1 x2 -> forall y1 y2, equiv_ff y1 y2 ->
    dclass x1 y1 = dclass x2 y2),
   MF -> MF -> T.
Proof. 
refine (@quotient_rec2@{UN UN j i Set} _ _ _ _ _ (BuildhSet _)).
intros x. 
split; red; unfold LeCp; reflexivity.  
Defined.   

Lemma Mff_equiv : forall x y x' y', equiv_ff x y -> equiv_ff x' y'
                                  -> ((ffle x x') <~> (ffle y y')). 
intros x y x' y' (X1,X2) (X3,X4).
apply equiv_iff_hprop_uncurried.
red in X1, X2, X3, X4.
split; intros H. 
unfold ffle in *. 
intros z.
transitivity (x' z); try trivial. 
transitivity (x z); try trivial.
unfold ffle in *.
intros z. 
transitivity (y z); try trivial. 
transitivity (y' z); try trivial.
Qed.

Definition ffle_hProp : MF  -> MF  -> TruncType@{UN} -1.
Proof.
intros U V.  
refine (@MF_rec2 _ _ (fun x y => BuildhProp (ffle x y)) _  _ _). 
intros x y Hxy x' y' Hx'y'.
apply path_hprop@{UN Ularge Uhuge}. simpl.
generalize (Mff_equiv Hxy Hx'y'). 
intros S.
apply Mff_equiv; trivial.  
exact U. exact V. 
Defined.  

Global Instance MF_of_mf : Cast mf MF := class_of _.

Definition MF_path {x y} : equiv_ff x y -> MF_of_mf x = MF_of_mf y
  := related_classes_eq _.

Definition MF_rect (P : MF -> Type@{i}) {sP : forall x, IsHSet (P x)}
  (dclass : forall x : mf, P (' x))
  (dequiv : forall x y E, (MF_path E) # (dclass x) = (dclass y))
  : forall q, P q
:= quotient_ind equiv_ff P dclass dequiv.

Definition MF_ind (P : MF -> Type@{i}) {sP : forall x : MF, IsHProp (P x)}
  (dclass : forall x : mf, P (cast mf MF x)) : forall x : MF, P x.
Proof.
pose proof (@trunc_hprop@{i i}) as trunc_hprop.
apply (MF_rect P dclass).
intros;apply path_ishprop@{i}.
Defined.

Definition MF_ind2 (P : MF -> MF -> Type) {sP : forall x y, IsHProp (P x y)}
  (dclass : forall x y : mf, P (' x) (' y)) : forall x y, P x y.
Proof.
apply (MF_ind (fun x => forall y, _));intros x.
apply (MF_ind _);intros y.
apply dclass.
Defined.

Definition MF_ind3 (P : MF -> MF -> MF -> Type@{i})
  {sP : forall x y z : MF, IsHProp (P x y z)}
  (dclass : forall x y z : mf, P (' x) (' y) (' z))
  : forall x y z : MF, P x y z.
Proof.
apply (@MF_ind (fun x => forall y z, _));intros x.
2:apply (MF_ind2 _);auto.
apply (@Forall.trunc_forall@{UN j j} _).
intros. apply Forall.trunc_forall@{UN i j}.
Defined.

Global Instance FLe : Le MF.  
Proof.
intros x y. 
refine (ffle_hProp x y).   
Defined.  
  
Global Instance FLe_ord : PartialOrder (FLe). 
Proof. 
split. 
+ apply _. 
+ intros x y. 
  apply _. 
+ split. 
  - hnf. apply (MF_ind _). intros x.
    change (ffle x x). red; red; reflexivity. 
  - hnf. 
    apply (MF_ind3 (fun _ _ _ => _ -> _ -> _)).
    intros x y z Hxy Hyz. 
    change (ffle x z).
    change (ffle x y) in Hxy. 
    change (ffle y z) in Hyz.
    red in Hxy, Hyz; red.
    intros s. 
    transitivity (y s); auto. 
+ hnf. apply (MF_ind2 (fun _ _ => _ -> _ -> _)).
  intros x y H H'. apply MF_path.
  red. change (ffle x y) in H. 
  change (ffle y x) in H'.
  split; trivial.  
Defined. 






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