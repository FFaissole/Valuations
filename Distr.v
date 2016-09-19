

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom hit.quotient.
Require Import LowerR.

Set Implicit Arguments.


Section OpenSubs. 

Context {A : hSet}.

Universe UN. 

Definition OS : Type@{UN} := A -> Sier. 

Global Instance Osle : Le OS.
Proof.
  intros O1 O2.
  unfold OS in O1, O2.
  refine (forall x:A, SierLe (O1 x) (O2 x)).
Defined.

Definition equiv_OS : OS -> OS -> Type := fun x y => Osle x y /\ Osle y x.  

Definition OpenSub@{} := @quotient _ equiv_OS  _.

Definition OS_rec2 {T:Type } {sT : IsHSet T}
  : forall (dclass : OS -> OS -> T)
  (dequiv : forall x1 x2, equiv_OS x1 x2 -> forall y1 y2, equiv_OS y1 y2 ->
    dclass x1 y1 = dclass x2 y2),
    OpenSub -> OpenSub -> T.
Proof. 
refine (@quotient_rec2@{UN UN j i Set} _ _ _ _ _ (BuildhSet _)).
intros x. 
split.
red; reflexivity. 
red; reflexivity. 
Defined.   

Lemma OSl_equiv : forall x y x' y', equiv_OS x y -> equiv_OS x' y'
                                  -> ((Osle x x') <~> (Osle y y')). 
intros x y x' y' (X1,X2) (X3,X4).
apply equiv_iff_hprop_uncurried.
red in X1, X2, X3, X4.
split; intros H. 
unfold Osle in *. 
intros z.
transitivity (x' z); try trivial. 
transitivity (x z); try trivial.
unfold Osle in *.
intros z. 
transitivity (y z); try trivial. 
transitivity (y' z); try trivial.
Qed.

Definition Osle_hProp : OpenSub -> OpenSub -> TruncType@{UN} -1.
Proof.
intros U V.  
refine (@OS_rec2 _ _ (fun x y => BuildhProp (Osle x y)) _  _ _). 
intros x y Hxy x' y' Hx'y'.
apply path_hprop@{UN Ularge Uhuge}. simpl.
generalize (OSl_equiv Hxy Hx'y'). 
intros S.
apply OSl_equiv; trivial.  
exact U. exact V. 
Defined.  

Global Instance Osub_of_OS : Cast OS OpenSub := class_of _.

Definition OS_path {x y} : equiv_OS x y -> Osub_of_OS x = Osub_of_OS y
  := related_classes_eq _.

Definition OS_rect (P : OpenSub -> Type@{i}) {sP : forall x, IsHSet (P x)}
  (dclass : forall x : OS, P (' x))
  (dequiv : forall x y E, (OS_path E) # (dclass x) = (dclass y))
  : forall q, P q
:= quotient_ind equiv_OS P dclass dequiv.

Definition OS_ind@{i} (P : OpenSub -> Type@{i}) {sP : forall x : OpenSub, IsHProp (P x)}
  (dclass : forall x : OS, P (cast OS OpenSub x)) : forall x : OpenSub, P x.
Proof.
pose proof (@trunc_hprop@{i i}) as trunc_hprop.
apply (OS_rect@{i} P dclass).
intros;apply path_ishprop@{i}.
Defined.

Definition OS_ind2 (P : OpenSub -> OpenSub -> Type) {sP : forall x y, IsHProp (P x y)}
  (dclass : forall x y : OS, P (' x) (' y)) : forall x y, P x y.
Proof.
apply (OS_ind (fun x => forall y, _));intros x.
apply (OS_ind _);intros y.
apply dclass.
Defined.

Definition OS_ind3@{i j} (P : OpenSub -> OpenSub -> OpenSub -> Type@{i})
  {sP : forall x y z : OpenSub, IsHProp (P x y z)}
  (dclass : forall x y z : OS, P (' x) (' y) (' z))
  : forall x y z : OpenSub, P x y z.
Proof.
apply (@OS_ind (fun x => forall y z, _));intros x.
2:apply (OS_ind2@{i j} _);auto.
apply (@Forall.trunc_forall@{UN j j} _).
intros. apply Forall.trunc_forall@{UN i j}.
Defined.

Global Instance OSe : Le OpenSub.  
Proof.
intros x y. 
refine (Osle_hProp x y).   
Defined.  
  
Global Instance Osle_ord : PartialOrder (OSe). 
Proof. 
split. 
+ apply _. 
+ intros x y. 
  apply _. 
+ split. 
  - hnf. apply (OS_ind _). intros x.
    change (Osle x x). red; reflexivity. 
  - hnf. 
    apply (OS_ind3 (fun _ _ _ => _ -> _ -> _)).
    intros x y z Hxy Hyz. 
    change (Osle x z).
    change (Osle x y) in Hxy. 
    change (Osle y z) in Hyz.
    red in Hxy, Hyz; red.
    intros s. 
    transitivity (y s); auto. 
+ hnf. apply (OS_ind2 (fun _ _ => _ -> _ -> _)).
  intros x y H H'. apply OS_path.
  red. change (Osle x y) in H. 
  change (Osle y x) in H'.
  split; trivial.  
Defined. 

Instance os_j : Join OS := fun U V => fun x => SierJoin (U x) (V x).

Lemma os_j_pres : forall x1 x2 x3 x4, equiv_OS x1 x2 -> equiv_OS x3 x4
                 -> equiv_OS (os_j x1 x3) (os_j x2 x4). 
Proof. 
intros x1 x2 x3 x4 (H1,H2) (H3,H4). 
red. red in H1, H2, H3, H4.  
unfold os_j in *. 
split. 
red.
Admitted. 

Global Instance OS_join@{} : Join OpenSub.
Proof.
refine (OS_rec2 (fun x y => '(os_j x y)) _).
intros x1 x2 H12 x3 x4 H34; apply OS_path.
eapply os_j_pres;trivial.
Defined.

Instance os_m : Meet OS := fun U V => fun x => SierMeet (U x) (V x).

Lemma os_m_pres : forall x1 x2 x3 x4, equiv_OS x1 x2 -> equiv_OS x3 x4
                 -> equiv_OS (os_m x1 x3) (os_m x2 x4). 
Proof. 
intros x1 x2 x3 x4 (H1,H2) (H3,H4). 
red. red in H1, H2, H3, H4.
unfold os_m in *. 
split. 
red.
Admitted. 

Global Instance OS_meet@{} : Meet OpenSub.
Proof.
refine (OS_rec2 (fun x y => '(os_m x y)) _).
intros x1 x2 H12 x3 x4 H34; apply OS_path.
eapply os_m_pres;trivial.
Defined.



Definition EmptySpaceO : OpenSub := fun x : A => ⊥.

Definition FullSpaceO : OpenSub := fun x : A => ⊤.




Lemma Osle_intro : forall (f g : OpenSub),
    (forall x, SierLe (f x) (g x)) -> OSLe f g.
Proof. 
intros; intro x; trivial.
Save.
Hint Resolve Osle_intro.

Lemma Osle_intro2 : forall (f g : OpenSub), (OSLe f g)
                                     -> (forall x, SierLe (f x) (g x)).
intros. auto.
Save.

Lemma Osle_intro3  : forall (x:A) (f g : OpenSub), (OSLe f g)
                                               -> SierLe (f x) (g x).
auto.
Qed.

Lemma OSLe_trans : forall U V W : OpenSub,
           OSLe U V -> OSLe V W -> OSLe U W. 
Proof. 
intros U V W H1 H2. 
intros x. 
specialize (H1 x).
specialize (H2 x). 
transitivity (V x); trivial. 
Qed.




Lemma Osle_eq : forall U V, OSLe U V -> U = V. 
Proof. 
intros U V H. 
auto. 

Definition OSEq : OpenSub -> OpenSub -> Type.
Proof.
intros U V.
refine (OSLe U V /\ OSLe V U).
Defined.

Lemma OSEq_trans : forall U V W :OpenSub,  OSEq U V -> OSEq V W -> OSEq U W.
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


Definition SierEq : Sier -> Sier -> Type.
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