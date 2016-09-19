Require Export Ccpo.
Require Export Misc.
Set Implicit Arguments.
Require Export QArith.
Open Local Scope Q_scope.
Open Local Scope O_scope.
Require Export QOrderedType.
Require Export Qminmax.
Require Import Qcompl.
Require Export LowerReals.
Require Import Coq.QArith.QArith Coq.QArith.Qring Coq.QArith.Qfield.

(** *** A more general type to deal with arbitrary representation of
   spaces of measurable functions
(** ** Type of spaces equiped with measurable functions *)
Record MFS : Type := mk_MF
   {MFA:Type; MF:>Type; fapp: MF -> MFA -> Rlow;
     fplus : MF -> MF -> MF;
     fmult : U -> MF -> MF;
     fzero : MF;
     flub : (nat -> MF) -> MF;
     fplus_eq : forall (f g : MF) (x : MFA),
                             fapp (fplus f g) x == fapp f x + fapp g x;
     fmult_eq : forall (k:U) (f : MF) (x : MFA),
                             fapp (fmult k f) x == k * fapp f x;
     fzero_eq : forall (x : MFA), fapp fzero x == 0;
     flub_eq : forall (f:nat -> MF) (x:MFA),
                            fapp (flub f) x == lub (fun n => fapp (f n) x)
}.
*)

(** *** Definition MF (A:Type) := A -> U. *)

Definition MF (A:Type) : Type := A -> RlowPos.

(** *** MF A cpo *)
Definition MFcpo (A:Type) : cpo (MF A) := fcpo RlowPoscpo.

(* Order properties on f-ops *)
Lemma fle_intro : forall (A:Type) (f g : MF A), (forall x, f x <= g x) -> f <= g.
intros; intro x; trivial.
Save.
Hint Resolve fle_intro.

Lemma fle_intro2 : forall (A : Type) (f g : MF A), (f <= g) -> (forall x, f x <= g x).
intros. auto.
Save.

Lemma feq_intro : forall (A:Type) (f g : MF A), (forall x, f x == g x) -> f == g.
intros; intro x; trivial.
Save.
Hint Resolve feq_intro.

Open Scope RlP.
(** *** Operations on MF *)
Definition fplus (A:Type) (f g : MF A) : MF A := 
               fun x => (f x) + (g x).

Definition fmult (A:Type) (k:RlowPos) (f : MF A) : MF A := 
               fun x => k * (f x).

Definition fzero (A:Type) : MF A := 
               fun x => RlP_0.

Definition flub (A:Type) (f : nat -m> MF A) : MF A := lub f.

Lemma  fplus_simpl : forall (A:Type)(f g : MF A) (x : A), 
                        fplus f g x = (f x) + (g x).
trivial.
Save.

Lemma  fplus_def : forall (A:Type)(f g : MF A), 
                     fplus f g = fun x => (f x) + (g x).
trivial.
Save.

Lemma  fmult_simpl : forall (A:Type)(k:RlowPos) (f : MF A) (x : A), 
                             fmult k f x =  k *(f x).
trivial.
Save.

Lemma  fmult_def : forall (A:Type)(k:RlowPos) (f : MF A), 
                             fmult k f = fun x => k * (f x).
trivial.
Save.

Implicit Arguments fzero [].

Lemma fzero_simpl : forall (A:Type)(x : A), fzero A x = RlP_0.
trivial.
Save.

Lemma fzero_def : forall (A:Type), fzero A = fun x:A => RlP_0.
trivial.
Save.

Lemma flub_simpl : forall (A:Type)(f:nat -m> MF A) (x:A), 
                           (flub f) x = lub (f <o> x).
trivial.
Save.

Lemma flub_def : forall (A:Type)(f:nat -m> MF A), 
                           (flub f) = fun x => lub (f <o> x).
intros.
trivial.
Save.


Hint Resolve fplus_simpl fmult_simpl fzero_simpl flub_simpl.


Definition fone (A:Type) : MF A := fun x => RlP_1.
Implicit Arguments fone [].

Lemma fone_simpl : forall (A:Type) (x:A), fone A x = RlP_1.
trivial.
Save.

Lemma fone_def : forall (A:Type), fone A = fun (x:A) => RlP_1.
trivial.
Save.

Definition fcte (A:Type) (k:RlowPos): MF A := fun x => k.
Implicit Arguments fcte [].

Lemma fcte_simpl : forall (A:Type) (k:RlowPos) (x:A), fcte A k x = k.
trivial.
Save.

Lemma fcte_def : forall (A:Type) (k:RlowPos), fcte A k = fun (x:A) => k.
trivial.
Save.

Definition fconj (A:Type)(f g:MF A) : MF A := fun x => (f x) * (g x).

Lemma fconj_simpl : forall (A:Type) (f g: MF A) (x:A), fconj f g x = (f x) * (g x).
trivial.
Save.

Lemma fconj_def : forall (A:Type) (f g: MF A), fconj f g = fun x => (f x) * (g x).
trivial.
Save.

(** *** LUB properties on MF *)
Lemma MF_lub_simpl : forall  (A:Type) (f : nat -m> MF A) (x:A), 
             lub f x = lub (f <o>x).
auto.
Save.
Hint Resolve MF_lub_simpl.

Lemma MF_lub_def : forall  (A:Type) (f : nat -m> MF A), 
             lub f = fun x => lub (f <o>x).
auto.
Save.


(** *** Defining morphisms *)

Lemma fplus_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1==f2 -> g1==g2 -> fplus f1 g1 == fplus f2 g2.
intros; intro x.
repeat (rewrite fplus_simpl). simpl; red; firstorder.
Save.

Add Parametric Morphism (A:Type) : (@fplus A)
    with signature Oeq ==> Oeq ==> Oeq 
    as fplus_feq_compat_morph.
intros; exact (fplus_eq_compat H H0); auto.
Save.

Instance fplus_mon2 : forall A, monotonic2 (fplus (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fplus_simpl; simpl; red; firstorder.
Save.
Hint Resolve fplus_mon2.

Lemma fplus_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1<=f2 -> g1<=g2 -> fplus f1 g1 <= fplus f2 g2.
intros; apply fplus_mon2; auto.
Save.

Add Parametric Morphism A : (@fplus A) with signature Ole ++> Ole ++> Ole 
    as fplus_fle_compat_morph.
intros f1 f2 H g1 g2 H1 x. apply fplus_le_compat; trivial.
Save.

Lemma fmult_eq_compat : forall A  k1 k2 (f1 f2:MF A), 
          k1 == k2 -> f1 == f2 -> fmult k1 f1 == fmult k2 f2.
intros A k1 k2 f1 f2 H H1 x.
repeat (rewrite fmult_simpl); simpl; red; firstorder.
Save.

Add Parametric Morphism A : (@fmult A) 
   with signature Oeq ==> Oeq ==> Oeq as fmult_feq_compat_morph.
intros k1 k2 H f1 f2 H1; apply fmult_eq_compat; trivial.
Save.

Instance fmult_mon2 : forall A, monotonic2 (fmult (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fmult_simpl; simpl; red; firstorder.
Save.
Hint Resolve fmult_mon2.

Lemma fmult_le_compat : forall A  k1 k2 (f1 f2:MF A), 
          k1 <= k2 -> f1 <= f2 -> fmult k1 f1 <= fmult k2 f2.
intros; apply fmult_mon2; auto.
Save.

Add Parametric Morphism A : (@fmult A)
    with signature Ole ++> Ole ++> Ole as fmult_fle_compat_morph.
intros k1 k2 H f1 f2 H1 x; apply fmult_le_compat; trivial.
Save.

Lemma fconj_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
           f1==f2 -> g1==g2 -> fconj f1 g1 == fconj f2 g2.
 intros; intro x. 
 repeat (rewrite fconj_simpl); simpl; red; firstorder.
Save.
 
Add Parametric Morphism A : (@fconj A)
with signature Oeq ==> Oeq ==> Oeq as fconj_feq_compat_morph.
intros; exact (fconj_eq_compat H H0); auto.
Save.

Instance fconj_mon2 : forall A, monotonic2 (fconj (A:=A)).
unfold monotonic2. intros; intro a.
repeat rewrite fconj_simpl.
assert (x a <= y a). auto. assert (z a <= t a). auto.
apply Rl_Product_mon; trivial. 
Save.
Hint Resolve fconj_mon2.

Lemma fconj_le_compat : forall A  (f1 f2 g1 g2:MF A), 
           f1 <= f2 -> g1 <= g2 -> fconj f1 g1 <= fconj f2 g2.
intros; apply fconj_mon2; auto.
Save.
 
Add Parametric Morphism A : (@fconj A) with signature Ole  ++> Ole  ++> Ole 
as fconj_fle_compat_morph.
intros.
exact (fconj_le_compat H H0); auto.
Save.

Hint Immediate fplus_le_compat fplus_eq_compat 
fmult_le_compat fmult_eq_compat (*fminus_le_compat fminus_eq_compat*)
fconj_eq_compat.


(** *** Elementary properties on operations *)


Lemma fle_fplus_left : forall (A:Type) (f g : MF A),
                           f <= fplus f g.
intros. intro x.
rewrite fplus_simpl. simpl.
generalize (Rl_Plus_r_0). intros RG.
specialize (RG (f x)).
destruct RG as (RG1,RG2).
apply Rlle_trans with (Rl_Plus (f x) [0]).
trivial.
apply Rl_Plus_mon. apply Rlle_refl.
red; simpl; intuition. apply Rlpos. trivial.
Save.

Lemma fle_fplus_right : forall (A:Type) (f g : MF A), 
                           g <= fplus f g.
intros. intro x.
rewrite fplus_simpl. simpl.
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
Save.

Hint Resolve fle_fplus_left  fle_fplus_right.


(** *** Compatibility of functions *)

Definition Fconj A : MF A -m> MF A -m> MF A := mon2 (fconj (A:=A)).
 
Lemma Fconj_simpl : forall A f g, Fconj A f g = fconj f g.
 trivial.
Save.
 
Lemma fconj_sym : forall A (f g : MF A), fconj f g == fconj g f.
 intros; intro x; unfold fconj. apply Rl_Product_comm. 
Save.
Hint Resolve fconj_sym.

Lemma Fconj_sym : forall A (f g : MF A), Fconj A f g == Fconj A g f.
intros; repeat rewrite Fconj_simpl; auto.
Save.
Hint Resolve Fconj_sym.

Lemma lub_MF_simpl : forall A (h : nat -m> MF A) (x:A), lub h x = lub (h <o> x).
intros; exact (fcpo_lub_simpl h x).
Save.

(** *** Continuity of RlowPos operations *)

Lemma Rl_Product_cont_l : forall (h : nat-m> RlowPos) (p : RlowPos), 
              (lub h) * p == lub (mshift (Rl_Product_pos_m @ h) p).
intros; apply Ole_antisym.
intros; rewrite <- continuous2_left. reflexivity.
apply continuous2_continuous. apply Rl_Product_pos_cont. 
exact (lub_comp_le (mshift Rl_Product_pos_m p) h).
Save.

Lemma Rl_Product_cont_r : forall (p : RlowPos) (h : nat-m> RlowPos) , 
              p * (lub h) == lub (Rl_Product_pos_m p @ h).
intros; apply Ole_antisym. 
rewrite <- continuous2_right. reflexivity.
apply Rl_Product_pos_cont.
exact (lub_comp_le (Rl_Product_pos_m p) h).
Save.

Lemma Rl_Plus_cont2 : forall (f g : nat-m> RlowPos), 
       lub f + lub g == lub ((Rl_Plus_pos_m @2 f) g).
intros. rewrite <- lub_cont2_app2_eq. reflexivity.
apply Rl_Plus_pos_cont.
Save. 

Definition Fmult A : RlowPos -m> MF A -m> MF A := mon2 (fmult (A:=A)).
 
Lemma Fmult_simpl : forall A k f, Fmult A k f = fmult k f.
 trivial.
Save.
 
Lemma Fmult_simpl2 : forall A k f x, Fmult A k f x =  k * (f x).
 trivial.
Save.

(** *** MF A order *)

Instance MFO (A:Type) : ord (MF A) := ford A RlowPos.

(** *** Type of measures on [A] *)

(* Definition of M A *)
Definition M A := MF A -m> RlowPos.

(* M A is an order *)
Instance MO (A:Type) : ord (M A) := fmono (MF A) RlowPos.


(* M A is a cpo *)
Instance Mcpo (A:Type) : cpo (M A) := fmon_cpo (O := MF A) (D := RlowPos).

Instance app_mon (A:Type) (x:A) : monotonic (fun (f:MF A) => f x).
red; auto.
Save.
Hint Resolve app_mon.

(** *** Monadic operators on M A *)

(* UNIT *)
Definition munit (A:Type) (x:A) : M A := mon (fun (f:MF A) => f x).

(* STAR *)
Definition mstar : forall (A B:Type), M A -> (A -> M B) -> M B.
intros A B a F; exists (fun f => a (fun x => F x f)).
red; intros.
apply (fmonotonic a); intro z; simpl.
apply (fmonotonic (F z)); trivial.
Defined.

Lemma star_simpl : forall (A B:Type) (a:M A) (F:A -> M B)(f:MF B),
        mstar a F f =  a (fun x => F x f).
trivial.
Save.

(** *** Properties of monadic operators *)
Lemma law1 : forall (A B:Type) (x:A) (F:A -> M B) (f:MF B), mstar (munit x) F f == F x f.
trivial.
Qed.

Lemma law2 :
 forall (A:Type) (a:M A) (f:MF A), mstar a (fun x:A => munit x) f == a (fun x:A => f x).
trivial.
Qed.

Lemma law3 :
 forall (A B C:Type) (a:M A) (F:A -> M B) (G:B -> M C)
   (f:MF C), mstar (mstar a F) G f == mstar a (fun x:A => mstar (F x) G) f.
trivial.
Qed.

(** ** Properties of distributions *)

(** *** Stability of the operators *)

Definition stable_add (A:Type) (m:M A) : Prop :=
  forall f g:MF A, m (fplus f g) == (m f) + (m g).

Definition stable_mull (A:Type) (m:M A) : Prop :=
  forall (k:RlowPos) (f:MF A), m (fmult k f) == k * (m f).


(** *** Stability properties *)
Section StabilityProperties.

Lemma Mstable_eq A (m : M A) : stable m.
apply monotonic_stable; trivial.
Save.
Hint Resolve Mstable_eq.

Lemma unit_stable_eq : forall (A:Type) (x:A), stable (munit x).
auto.
Qed.

Lemma star_stable_eq : forall (A B:Type) (m:M A) (F:A -> M B), stable (mstar m F).
auto.
Qed.

Lemma star_stable_add : forall (A B:Type) (m:M A) (F:A -> M B),
stable_add m -> (forall a:A, stable_add (F a)) -> stable_add (mstar m F).
unfold stable_add in |- *; intros.
unfold mstar in |- *. simpl. simpl in H.
rewrite <- H. apply (Mstable_eq m).
intro x. apply H0.
Save.

Lemma star_stable_mull : forall (A B:Type) (m:M A) (F:A -> M B),
stable_mull m -> (forall a:A, stable_mull (F a)) -> stable_mull (mstar m F).
unfold stable_mull in |- *; intros.
unfold mstar in |- *; simpl. simpl in H.
rewrite <- H. apply (Mstable_eq m).
intro x. apply H0.
Save.

Lemma unit_monotonic : forall (A:Type) (x:A) (f g : MF A),
 (f <= g)%O -> munit x f <= munit x g.
auto.
Save.

Lemma star_monotonic : forall A B (m:M A) (F:A -> M B) (f g : MF B),
(f <= g)%O -> mstar m F f <= mstar m F g.
auto.
Save.

Lemma star_le_compat : forall A B (m1 m2:M A) (F1 F2:A -> M B),
       (m1 <= m2)%O -> (F1 <= F2)%O -> (mstar m1 F1 <= mstar m2 F2)%O.
intros; intro f; repeat rewrite star_simpl.
transitivity (m1 (fun x  => (F2 x) f)); auto.
apply (fmonotonic m1); intro x.
apply (H0 x f).
Save.

Hint Resolve star_le_compat.

End StabilityProperties.

(** ** Definition of distribution
Finite distributions are monotonic measure functions such that
    - [ mu (f + g) = mu f + mu g]
    - [ mu k * f = k * mu f]
    - [ mu 1 <= 1]
    - continuité de mu
*)

Record distr (A:Type) : Type := 
  {mu : M A;
   mu_stable_add : stable_add mu; 
   mu_stable_mull : stable_mull mu;
   mu_prob : mu (fun x => RlP_1) <= RlP_1;
   mu_continuous : continuous mu
}.

Hint Resolve mu_stable_add mu_prob mu_stable_mull mu_continuous.

(** *** Properties of measures *)

(* mu is monotonic *) 
Lemma mu_monotonic : forall (A : Type) (m : distr A), 
monotonic (mu m).
auto.
Save.
Hint Resolve mu_monotonic.
Implicit Arguments mu_monotonic [A].

(* eq stable *) 
Lemma mu_stable_eq : forall (A : Type) (m: distr A), 
stable (mu m).
auto.
Save.
Hint Resolve mu_stable_eq.
Implicit Arguments mu_stable_eq [A].

(* add stable for unit *) 
Lemma unit_stable_add : forall (A:Type) (x:A), stable_add (munit x).
red in |-*; intros.
unfold munit in *.
auto.
Qed.

(* mull stable for unit *) 
Lemma unit_stable_mull : forall (A:Type) (x:A), stable_mull (munit x).
red in |-*; intros.
unfold munit in *.
auto.
Qed.

(* mu m (fone A) <= 1%RlPos *)
Lemma mu_one : forall (A: Type) (m: distr A), mu m (fone A) <= RlP_1.
auto.
Save.

Hint Resolve mu_one.

(* definitions of constants operations *)
Lemma mu_cte : forall (A : Type) (m:distr A) (r : RlowPos), 
               mu m (fcte A r)== (mu m (fone A)) * r.
intros. transitivity (mu m (fmult r (fone A))).
apply Mstable_eq. intro x. rewrite fcte_def. rewrite fmult_simpl.
unfold fone. simpl; symmetry; apply Rl_Product_r_1.
rewrite (mu_stable_mull m r). apply Rl_Product_comm.
Save.

(** *** Additionnal properties *)
Lemma mu_cte_le : forall (A : Type) (m:distr A) (r : RlowPos), 
               mu m (fcte A r) <= r.
intros. rewrite mu_cte. simpl; rewrite mu_prob. 
assert (Rleq (Rl_Product RlP_1 r) r). simpl.
rewrite Rl_Product_comm.
apply Rl_Product_r_1. destruct H; trivial.
Save.


Lemma mu_one_le : forall (A:Type) (m: distr A) f, 
(forall x, f x <= RlP_1) -> mu m f <= RlP_1.
intros. transitivity (mu m (fone A)). apply mu_monotonic.
auto. auto.
Save.


Hint Immediate mu_one_le.

(** *** Distributions and operations *)

Lemma mu_add : forall (A:Type) (m: distr A) (f g : MF A),
       mu m (fplus f g) == (mu m f) + (mu m g).
apply mu_stable_add.
Save.
Hint Resolve mu_stable_add.

Lemma mu_mull : forall (A:Type) (m: distr A) (k : RlowPos) (f : MF A),
               mu m (fmult k f) == k * (mu m f).
apply mu_stable_mull.    
Save.

Lemma mu_add_zero : forall (A:Type) (m: distr A) f g,
    mu m f == RlP_0 -> mu m g == RlP_0 -> mu m (fplus f g) == RlP_0.
intros. rewrite mu_add. simpl in H. simpl. rewrite H.
simpl in H0; rewrite H0. apply QRl_Plus.
Save.

Hint Resolve mu_add_zero.

Lemma mu_stable_pos : forall (A:Type) (m: distr A) f, (0 <= f)%O -> 0 <= mu m f.
auto.
Save.

(** *** Order relations on distributions *)

Instance Odistr (A:Type) : ord (distr A) := 
    {Ole := fun (f g : distr A) => (mu f <= mu g)%O;
     Oeq := fun (f g : distr A) => Oeq (mu f) (mu g)}.
split; intuition.
intros f g h; transitivity (mu g); auto.
Defined.

(** *** Monadic operators for distributions *)
Definition Munit : forall (A:Type), A -> distr A.
intros.
exists (munit X).
apply unit_stable_add.
apply unit_stable_mull.
auto.
intros fn x.
simpl. trivial.
Defined.

(** *** Operation Let *)
Definition Mlet : forall A B:Type, distr A -> (A -> distr B) -> distr B.
intros A B mA mB.
exists (mstar (mu mA) (fun x => (mu (mB x)))).
apply star_stable_add. auto. 
auto.
apply star_stable_mull; auto.
apply mu_one_le. intros; apply mu_one_le. auto.
intros fn. rewrite star_simpl.  
transitivity (mu mA (fun x:A => (lub (mu (mB x) @ fn)))).
apply mu_monotonic; intro x. apply mu_continuous.
rewrite <- lub_ishift. apply mu_continuous.
Defined.

(** ** Properties of Munit and Mlet *)(** *** Basic properties on distributions and operations *)
Lemma Munit_simpl : forall (A:Type) (q:A -> RlowPos) x, mu (Munit x) q = q x.
trivial.
Save.

Lemma Munit_simpl_eq : forall (A:Type) (q:A -> RlowPos) x, mu (Munit x) q == q x.
trivial.
Save.

Lemma Mlet_simpl : forall (A B:Type) (m:distr A) (M:A -> distr B) (f:B -> RlowPos),
     mu (Mlet m M) f = mu m (fun x => (mu (M x) f)).
trivial.
Save.


Lemma Mlet_simpl_eq : forall (A B:Type) (m:distr A) (M:A -> distr B) (f:B -> RlowPos),
     mu (Mlet m M) f == mu m (fun x => (mu (M x) f)).
trivial.
Save.


Lemma Munit_eq_compat : forall A (x y : A), x = y -> (Munit x) == (Munit y).
intros; subst; auto.
Save.

Lemma Mlet_le_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A -> distr B), 
  (m1 <= m2 -> M1 <= M2 -> Mlet m1 M1 <= Mlet m2 M2)%O.
intros A B m1 m2 M1 M2 Hm HM f.
repeat rewrite Mlet_simpl.
transitivity (mu m2 (fun x => mu (M1 x) f)); auto.
apply (fmonotonic (mu m2)); intro; auto.
apply (HM x f).
Save.

Hint Resolve Mlet_le_compat.

(** *** Morphisms on Mlet *)
Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature Ole ==> Ole ==> Ole 
  as Mlet_le_morphism.
auto.
Save.

Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature  Ole ==> (@pointwise_relation A (distr B) (@Ole _ _)) ==> Ole 
  as Mlet_le_pointwise_morphism.
auto.
Save.


(** *** Monotonicity on Mlet *)
Instance Mlet_mon2 : forall (A B : Type), monotonic2 (@Mlet A B).
red; auto.
Save.

(** *** MLet = monotonic version of Mlet *)
Definition MLet (A B : Type) : distr A -m> (A -> distr B) -m> distr B
               := mon2 (@Mlet A B).

Lemma MLet_simpl0 : forall (A B:Type) (m:distr A) (M:A -> distr B),
     MLet A B m M = Mlet m M.
trivial.
Save.

Lemma MLet_simpl : forall (A B:Type) (m:distr A) (M:A -> distr B)(f:B -> RlowPos),
     mu (MLet A B m M) f = mu m (fun x => mu (M x) f).
trivial.
Save.

Lemma Mlet_eq_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A -> distr B), 
  (m1 == m2 -> M1 == M2 -> Mlet m1 M1 == Mlet m2 M2)%type.
intros. apply (monotonic2_stable2 (@Mlet A B)); trivial.
Save.
Hint Resolve Mlet_eq_compat.

Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature Oeq ==> Oeq ==> Oeq 
  as Mlet_eq_morphism.
auto.
Save.


Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature  Oeq ==> (@pointwise_relation A (distr B) (@Oeq _ _)) ==> Oeq 
  as Mlet_Oeq_pointwise_morphism.
auto.
Save.


(** *** Distributions and order relations *)

Lemma mu_le_compat : forall (A:Type) (m1 m2:distr A),
  (m1 <= m2 -> forall f g : A -> RlowPos,  f <= g -> mu m1 f <= mu m2 g)%O.
intros; transitivity (mu m2 f); auto.
Save.

Lemma mu_eq_compat : forall (A:Type) (m1 m2:distr A),
  (m1 == m2 -> forall f g : A -> RlowPos,  f == g -> mu m1 f == mu m2 g)%type.
intros; transitivity (mu m2 f); auto.
Save. 

Hint Immediate mu_le_compat mu_eq_compat.

Add Parametric Morphism (A : Type) : (mu (A:=A))
  with signature Ole ==> Ole
  as mu_le_morphism.
auto.
Save.

Add Parametric Morphism (A : Type) : (mu (A:=A))
  with signature Oeq ==> Oeq
  as mu_eq_morphism.
auto.
Save.

(*** ** Morphisms and distributions  *)

Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation A RlowPos (@eq _) ==> Oeq) as mu_distr_eq_morphism.
intros f g H1.
auto. replace f with g. trivial. 
red in H1. symmetry. apply FunctionalExtensionality.functional_extensionality.
trivial. 
Save.

Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation A RlowPos (@Oeq _ _) ==> Oeq) as mu_distr_Oeq_morphism.
intros f g H1.
auto.
Save.

Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation _ _ (@Ole _ _) ==> Ole) as mu_distr_le_morphism.
intros x y H. auto.
Save.

Add Parametric Morphism (A B:Type) : (@Mlet A B)
  with signature (Ole ==> @pointwise_relation _ _ (@Ole _ _) ==> Ole) as mlet_distr_le_morphism.
intros x y H F G H2.
apply Mlet_le_compat; auto.
Save.

Add Parametric Morphism (A B:Type) : (@Mlet A B)
  with signature (Oeq ==> @pointwise_relation _ _ (@Oeq _ _) ==> Oeq) as mlet_distr_eq_morphism.
intros x y H F G H2.
apply Mlet_eq_compat; auto.
Save.

(** *** Properties of monadic operators *)
Lemma Mlet_unit : forall A B (x:A) (m:A -> distr B), Mlet (Munit x) m == m x.
intros; intro f; auto.
Save.

Lemma Mlet_ext : forall A (m:distr A), Mlet m (fun x => Munit x) == m.
intros;  intro f.
rewrite Mlet_simpl.
apply (mu_stable_eq m).
intro x. apply Munit_simpl_eq.
Save.

Lemma Mlet_assoc : forall A B C (m1: distr A) (m2:A -> distr B) (m3:B -> distr C),
     Mlet (Mlet m1 m2) m3 == Mlet m1 (fun x:A => Mlet (m2 x) m3).
intros;  intro f.  
auto.
Save.

(** *** Choice operation *)
(** *** The distribution associated to [pchoice p m1 m2] is 
        [ f --> p (m1 f) + (1-p) (m2 f) ] *)

Definition pchoice : forall A, RlowPos -> RlowPos -> M A -> M A -> M A.
intros A p q m1 m2;
     exists (fun f => (p*(m1 f) + q*(m2 f))%RlP).
red; intros; simpl.
apply Rl_Plus_mon. apply Rl_Prod_compat. reflexivity.
apply (fmonotonic m1). trivial.   
apply Rl_Prod_compat. reflexivity. 
apply (fmonotonic m2). trivial.   

Defined.

Lemma pchoice_simpl : forall A p q (m1 m2:M A) f,
      pchoice p q m1 m2 f = (p * m1 f + q * m2 f)%RlP.
trivial.
Save.


(** *** Mchoice : choice distribution *)
Definition Mchoice (A:Type) (p q :RlowPos) (H : p + q <= RlP_1)
                         (m1 m2: distr A) : distr A.
exists (pchoice p q (mu m1) (mu m2)).
(* stable_plus *)
red; intros; repeat (rewrite pchoice_simpl).
rewrite (mu_stable_add m1 f g). rewrite (mu_stable_add m2 f g).
rewrite Rl_Plus_Product_distr.
simpl.
rewrite <- Rl_Plus_assoc2.
generalize (Rl_Plus_Product_distr q ((mu m2) f) ((mu m2) g)).
intros HH.
simpl in HH.
rewrite HH.
apply Rleq_refl.
(* stable_mull *)
red; intros; repeat (rewrite pchoice_simpl).
rewrite (mu_stable_mull m1 k f). rewrite (mu_stable_mull m2 k f).
rewrite Rl_Plus_Product_distr.
rewrite Rl_Product_assoc2. rewrite Rl_Product_assoc2. 
rewrite Rl_Product_assoc2. rewrite Rl_Product_assoc2.
assert (Rl_Product p k == Rl_Product k p); simpl; rewrite Rl_Product_comm.
reflexivity. rewrite H0. rewrite Rl_Product_comm.
assert (Rl_Product k q == Rl_Product q k); rewrite Rl_Product_comm.
reflexivity. rewrite H1. reflexivity.
(* mu_prob *)
repeat (rewrite pchoice_simpl). rewrite (mu_one m1).
rewrite (mu_one m2). repeat (rewrite Rl_Product_r_1).
trivial.
(* continuous *)
red; intros; rewrite pchoice_simpl.
rewrite (mu_continuous m1 h).
rewrite (mu_continuous m2 h).
rewrite Rl_Product_cont_r. 
rewrite Rl_Product_cont_r. 
rewrite Rl_Plus_cont2.
apply lub_le_compat. 
intro x; reflexivity.
Defined.

(** *** Properties of Mchoice *)
Lemma Mchoice_simpl : forall A p q (H : p + q <= RlP_1) (m1 m2:distr A) f,
      mu (Mchoice H m1 m2) f = p * mu m1 f + q * mu m2 f.
trivial.
Save.

Lemma Mchoice_le_compat : forall (A:Type) (p q :RlowPos) (H : p + q <= RlP_1)
                                 (m1 m2 n1 n2: distr A),
    m1<=m2 -> n1<=n2 -> Mchoice H m1 n1 <= Mchoice H m2 n2.
simpl; intros.
apply Rl_Plus_mon; apply Rl_Product_mon. apply Rlle_refl.
trivial. apply Rlle_refl. trivial.
Save.
Hint Resolve Mchoice_le_compat.

Add Parametric Morphism (A:Type) (p q : RlowPos) (H : p + q <= RlP_1) 
                                :  (Mchoice (A:=A) H)
  with signature Oeq ==> Oeq ==> Oeq
as Mchoice_eq_compat.
intros; intro f.
simpl.
rewrite H0; apply Rl_Plus_morph. reflexivity.
rewrite H1; apply Rl_Product_morph. reflexivity.
reflexivity.
Save.
Hint Immediate  Mchoice_eq_compat.


(** *** Properties of Mu for lub, on continuity *)
Definition Mu (A : Type) : distr A -m> M A.
exists (mu (A:=A)). intros x y H f. apply H.
Defined.

Lemma Mu_simpl (A : Type) D : Mu A D = mu D.
trivial. 
Save. 

Lemma M_lub_simpl (A : Type) (h : nat -m> M A) (f : MF A) : 
            (lub h) f == lub (mshift h f).
reflexivity. 
Save.


Definition mu_lub (A : Type) (muf : nat -m> distr A) : distr A. 
exists (lub ((Mu A) @ muf)).
+ intros f g. rewrite M_lub_simpl. rewrite M_lub_simpl. rewrite M_lub_simpl.
  rewrite Rl_Plus_cont2. apply lub_eq_compat. intro x.
  rewrite mshift_simpl, comp_simpl, Mu_simpl.
  rewrite mu_add. simpl. reflexivity.
+ intros f g. repeat (rewrite M_lub_simpl). rewrite Rl_Product_cont_r.
  apply lub_eq_compat. intro x. rewrite mshift_simpl, comp_simpl, Mu_simpl.
  rewrite mu_mull. simpl. reflexivity.
+ rewrite M_lub_simpl. apply lub_le. intro n. simpl. apply mu_one.
+ intros f. apply lub_continuous. intro n. apply (mu_continuous (muf n)).
Defined.

Lemma mu_lub_le (A : Type) (muf : nat -m> distr A): 
         forall  (n : nat), muf n <= (mu_lub muf).
simpl; intros. exact (le_lub (mshift (Mu A @ muf) x) n).
Save.

Lemma mu_lub_sup A (muf : nat -m> distr A) : forall (m : distr A), 
                   (forall n, muf n <= m) -> (mu_lub muf <= m).
intros. apply lub_le. intro n. simpl. apply H.
Save.

Definition distr0 (A : Type) : distr A. 
exists (mon (cte (MF A) RlP_0)). 
intros f g; simpl. symmetry. apply Rl_Plus_r_0.
intros f g. repeat ( rewrite Rl_Product_r_0 ). simpl.
reflexivity.
simpl. apply Qle_Rlle. apply Ole_Qle. auto with qarith.
intro f. apply RlowPos_pos.
Defined. 
 
Instance Distrcpo A : cpo (distr A) := 
  { D0 := distr0 A;
    lub := @mu_lub A}.
intros d f. apply RlowPos_pos.
apply mu_lub_le. 
apply mu_lub_sup.
Defined. 

