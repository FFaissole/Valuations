
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom.
Require Import LowerR.

Set Implicit Arguments.

Definition OpenSub (A : hSet) := A -> Sier. 

Definition JoinOpen (A : hSet) (U V : OpenSub A) : OpenSub A.
Proof.
  intros x.
  specialize (U x).
  specialize (V x).
  refine (SierJoin U V).
Defined.

Definition MeetOpen (A : hSet) (U V : OpenSub A) : OpenSub A.
Proof.
  intros x.
  specialize (U x).
  specialize (V x).
  refine (SierMeet U V).  
Defined.

Definition EmptySpaceO (A : hSet) : (OpenSub _) := fun x : A => SierBot.

Definition FullSpaceO (A : hSet) : (OpenSub _) := fun x : A => SierTop.

Global Instance OSLe (A : hSet) : Le (OpenSub A).
Proof.
  intros O1 O2.
  unfold OpenSub in O1, O2.
  refine (forall x:A, SierLe (O1 x) (O2 x)).
Defined.


Lemma Osle_intro : forall (A:hSet) (f g : OpenSub A), (forall x, SierLe (f x) (g x))
                                                       -> OSLe f g.
intros; intro x; trivial.
Save.
Hint Resolve Osle_intro.

Lemma Osle_intro2 : forall (A : hSet) (f g : OpenSub A), (OSLe f g)
                                     -> (forall x, SierLe (f x) (g x)).
intros. auto.
Save.

Lemma Osle_intro3  : forall (A : hSet) (x:A) (f g : OpenSub A), (OSLe f g)
                                                                -> SierLe (f x) (g x).
auto.
Qed.

Lemma OSLe_trans (A : hSet) : forall U V W : OpenSub A,
           OSLe U V -> OSLe V W -> OSLe U W. 
Proof. 
intros U V W H1 H2. 
intros x. 
specialize (H1 x).
specialize (H2 x). 
transitivity (V x); trivial. 
Qed.

Definition OSEq (A : hSet) : (OpenSub A) -> (OpenSub A) -> Type.
Proof.
intros U V.
refine (OSLe U V /\ OSLe V U).
Defined.

Lemma OSEq_trans (A : hSet) : forall U V W :OpenSub A,  OSEq U V -> OSEq V W -> OSEq U W.
Proof.
intros U V W (H1,H2) (H3,H4).  
unfold OSEq in *.
split.
apply Osle_intro.
intros z.
apply imply_le. intro Hu.
apply (Osle_intro3 z) in H1; try trivial.
apply SierLe_imply in H1; try trivial.
apply (Osle_intro3 z) in H3; try trivial.
apply SierLe_imply in H3; try trivial.
trivial.
apply Osle_intro.
intros z.
apply imply_le. intro Hw.
apply (Osle_intro3 z) in H2; try trivial.
apply SierLe_imply in H2; try trivial.
apply (Osle_intro3 z) in H4; try trivial.
apply SierLe_imply in H4; try trivial.
Qed.


Definition SierEq (A : hSet) : Sier -> Sier -> Type.
intros S S'.
refine (SierLe S S' /\  SierLe S' S).
Defined.

Lemma Oseq_intro : forall (A:hSet) (f g : OpenSub A), (forall x:A, SierEq A (f x) (g x))
                                                      -> OSEq f g.
intros A f g H.
unfold SierEq in H.
split; apply Osle_intro;
intros x.
apply (fst (H x)).
apply (snd (H x)).
Save.
Hint Resolve Oseq_intro.

Definition Oslub (A:hSet) (f : nat -> OpenSub A) : OpenSub A.
Proof.
unfold OpenSub.
intro x.  
refine (CountableSup (fun n => f n x)).   
Defined. 

Lemma Oslub_simpl : forall (A:hSet) (f:nat -> OpenSub A) (x:A), 
                           (Oslub f) x = CountableSup (fun n => f n x).
trivial.
Save.

Lemma Oslub_def : forall (A:hSet)(f:nat -> OpenSub A), 
                           (Oslub f) = fun x => CountableSup (fun n => f n x).
intros.
trivial.
Save.

Definition Mes (A : hSet) : Type := (OpenSub A) -> RlowPos.

Definition empty_op (A : hSet) (m : Mes A) := 
       Rleq (m (EmptySpaceO A)) RlP_0.

Definition modular (A : hSet) (m : Mes A) :=
   forall (U V : OpenSub A), Rleq (RlP_plus (m U) (m V)) 
                                  (RlP_plus (m (JoinOpen U V)) (m (MeetOpen U V))).

Definition seq_open_mes (A : hSet) (m : Mes A) :
        (nat -> OpenSub A) -> (nat -> RlowPos).
intros L n. 
specialize (L n).
specialize (m L).
refine m.
Defined.

Definition scott_continuous (A : hSet) (m : Mes A) :=
   forall (u : nat -> OpenSub A), Rlle (m (Oslub u)) (Rllub (seq_open_mes m u)). 

Definition mon_opens (A : hSet) (m : Mes A) :=
   forall (U V : OpenSub A), OSLe U V -> Rlle (m U) (m V).

Record D (A:hSet) : Type :=
  {mu : Mes A;
   mu_modular : modular mu; 
   mu_empty_op : empty_op mu;
   mu_mon : mon_opens mu;
   mu_prob : Rlle (mu (fun x => SierTop)) (RlP_1)
}.

Hint Resolve mu_modular mu_prob mu_empty_op mu_mon.

(** *** Properties of measures *)

(* mu is monotonic *) 
Lemma mu_monotonic : forall (A : hSet) (m : D A), mon_opens (mu m).
auto.
Save.
Hint Resolve mu_monotonic.
Implicit Arguments mu_monotonic [A].

(* eq stable *) 
Lemma mu_stable_eq : forall (A : hSet) (m: D A) (U V : OpenSub A),
    OSEq U V -> Rleq (mu m U) (mu m V).
intros A m U V (Hl1,Hl2).
split. 
apply mu_monotonic; trivial.
apply mu_monotonic; trivial.
Save.
Hint Resolve mu_stable_eq.
Implicit Arguments mu_stable_eq [A].

(* mu m (fone A) <= 1%RlPos *)
Lemma mu_one : forall (A: hSet) (m: D A), Rlle (mu m (FullSpaceO A))  RlP_1.
auto.
Save.

Hint Resolve mu_one.