

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


Definition OS_rec@{i} {T : Type@{i} } {sT : IsHSet T}
  : forall (dclass : OS -> T)
  (dequiv : forall x y, equiv_OS x y -> dclass x = dclass y),
  OpenSub -> T
:= quotient_rec _.

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
split; red.
intros x.
transitivity ((SierJoin (x1 x) (x4 x))).
apply SierJoin_is_join.
apply SierJoin_is_join.
transitivity (x4 x). 
apply H3. 
apply SierJoin_is_join.
apply SierJoin_preserve_le_l. 
apply H1. 
intros x. 
transitivity ((SierJoin (x1 x) (x4 x))).
apply SierJoin_is_join.
transitivity (x1 x).
apply H2. 
apply SierJoin_is_join. 
apply SierJoin_is_join.
apply SierJoin_is_join.
apply SierJoin_is_join.
transitivity (x3 x). 
apply H4. 
apply SierJoin_is_join.
Qed. 

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

Instance os_zero : Zero OS := fun x : A => ⊥.

Global Instance OS_empty@{} : Zero OpenSub.
Proof.
refine (' os_zero).
Defined.

Instance os_full : One OS := fun x : A => ⊤.

Global Instance OS_full@{} : One OpenSub.
Proof. refine (' os_full). Defined.

Definition os_lub (f : nat -> OS) : OS.
Proof.
intro x.  
refine (CountableSup (fun n => f n x)).   
Defined.
(*
Definition seq_OS_OpenSub : (nat -> OS) -> (nat -> OpenSub) :=
       fun f => (fun n => ' (f n)). 

Definition Os_lub (f : nat -> OpenSub) : OpenSub.
Proof. 
refine ((os_lub f)). 

Lemma Oslub_simpl : forall (A:hSet) (f:nat -> OpenSub A) (x:A), 
                           (Oslub f) x = CountableSup (fun n => f n x).
trivial.
Save.

Lemma Oslub_def : forall (A:hSet)(f:nat -> OpenSub A), 
                           (Oslub f) = fun x => CountableSup (fun n => f n x).
intros.
trivial.
Save.*)

Definition Mes : Type := OpenSub -> RlowPos.

Definition empty_op (m : Mes) := 
       Rleq (m OS_empty) RlP_0.

Definition modular (m : Mes) :=
   forall (U V : OpenSub), Rleq (RlP_plus (m U) (m V)) 
                                  (RlP_plus (m (OS_join U V)) (m (OS_meet U V))).

Definition seq_open_mes (m : Mes) :
        (nat -> OpenSub) -> (nat -> RlowPos).
intros L n. 
specialize (L n).
specialize (m L).
refine m.
Defined.

Definition mon_opens (m : Mes) :=
   forall (U V : OpenSub), OSe U V -> Rlle (m U) (m V).

Record D : Type :=
  {mu : Mes;
   mu_modular : modular mu; 
   mu_empty_op : empty_op mu;
   mu_mon : mon_opens mu;
   mu_prob : Rlle (mu OS_full) (RlP_1)
}.

Hint Resolve mu_modular mu_prob mu_empty_op mu_mon.

(** *** Properties of measures *)

(* mu is monotonic *) 
Lemma mu_monotonic : forall (m : D), mon_opens (mu m).
Proof. auto. Qed.
Hint Resolve mu_monotonic.

(* eq stable *) 
Lemma mu_stable_eq : forall (m: D) (U V : OpenSub),
    U = V -> Rleq (mu m U) (mu m V).
Proof. 
intros m U V H.
rewrite H. 
split; auto.   
Qed.

Hint Resolve mu_stable_eq.

(* mu m (fone A) <= 1%RlPos *)
Lemma mu_one : forall (m: D), Rlle (mu m OS_full)  RlP_1.
Proof. auto. Qed. 

Hint Resolve mu_one.