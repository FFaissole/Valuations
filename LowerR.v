Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.interfaces.rationals
               HoTTClasses.theory.rationals.
Require Import HoTT.HSet HoTT.Basics.Decidable HoTT.Basics.Trunc
               HProp HSet Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom.


(** Some axioms on Q ---> to move **)
Axiom Qeq_refl : forall x:Q, x = x.

Axiom Qeq_sym : forall x y:Q, x = y -> y = x.

Axiom Qeq_trans : forall x y z :Q, x = y -> y = z -> x = z.

Hint Immediate Qeq_sym : qarith.
Hint Resolve Qeq_refl Qeq_trans : qarith.

Axiom Qeq_dec: forall x y: Q, (x=y)\/(~ x=y).

Axiom Qnot_eq_sym: forall x y : Q, ~(x = y) -> ~(y = x).

Hint Resolve Qnot_eq_sym : qarith.

Axiom Qplus_assoc : forall x y z:Q, x+(y+z)=(x+y)+z.

Axiom Qplus_0_l : forall x:Q, 0+x = x.

Axiom Qplus_0_r : forall x:Q, x+0 = x.

Axiom Qplus_comm : forall x y:Q, x+y = y+x.

Axiom Qopp_involutive : forall q:Q, - -q = q.

Axiom Qplus_opp_r : forall q:Q, q+(-q) = 0.

Axiom Qplus_inj_r : forall (x y z: Q),
  x + z = y + z <-> x = y.

Axiom Qplus_inj_l : forall (x y z: Q),
    z + x = z + y <-> x = y.

Axiom Qmult_assoc : forall n m p:Q, n*(m*p)=(n*m)*p.

Axiom Qmult_0_l : forall x:Q , 0*x = 0.

Axiom Qmult_0_r : forall x:Q , x*0 = 0.

Axiom Qmult_1_l : forall n:Q, 1*n = n.

Axiom Qmult_1_r : forall n:Q, n*1=n.

Axiom Qmult_comm : forall x y:Q, x*y=y*x.

Axiom Qmult_plus_distr_r : forall x y z:Q, x*(y+z)=(x*y)+(x*z).

Axiom Qmult_plus_distr_l : forall x y z:Q, (x+y)*z=(x*z)+(y*z).

Axiom Qmult_integral : forall x y:Q, x*y=0 -> x=0 \/ y=0.

Axiom Qmult_integral_l : forall x y:Q, ~ x = 0 -> x*y = 0 -> y = 0.

Axiom Qinv_involutive : forall q:Q, (/ / q) = q.

Axiom Qmult_inv_r : forall x:Q, ~ x = 0 -> x*(/x) = 1.

Axiom Qinv_mult_distr : forall p q:Q, / (p * q) = /p * /q.

Axiom Qdiv_mult_l : forall x y:Q, ~ y = 0 -> (x*y)/y = x.

Axiom Qmult_div_r : forall x y:Q, ~ y = 0 -> y*(x/y) = x.

Axiom Qmult_inj_r : forall (x y z: Q), ~ z = 0 -> (x * z = y * z <-> x = y).

Axiom Qmult_inj_l : forall (x y z: Q), ~ z = 0 -> (z * x = z * y <-> x = y).

Axiom Qle_refl : forall x, x<=x.

Axiom Qle_antisym : forall x y:Q, x<=y -> y<=x -> x=y.

Axiom Qle_trans : forall x y z:Q, x<=y -> y<=z -> x<=z.

Hint Resolve Qle_trans : qarith.

Axiom Qlt_irrefl : forall x:Q, ~(x<x).

Axiom Qlt_not_eq : forall x y:Q, x<y -> ~ x=y.

Axiom Qle_lteq : forall x y:Q, x<=y <-> x<y \/ x=y.

Axiom Qlt_le_weak : forall x y:Q, x<y -> x<=y.

Axiom Qle_lt_trans : forall x y z:Q, x<=y -> y<z -> x<z.

Axiom Qlt_le_trans : forall x y z:Q, x<y -> y<=z -> x<z.

Axiom Qlt_trans : forall x y z:Q, x<y -> y<z -> x<z.

Axiom Qnot_lt_le : forall x y:Q, ~ x<y -> y<=x.

Axiom Qnot_le_lt : forall x y:Q, ~ x<=y -> y<x.

Axiom Qlt_not_le : forall x y:Q, x<y -> ~ y<=x.

Axiom Qle_not_lt : forall x y:Q, x<=y -> ~ y<x.

Axiom Qle_lt_or_eq : forall x y:Q, x<=y -> x<y \/ x=y.

Hint Resolve Qle_not_lt Qlt_not_le Qnot_le_lt Qnot_lt_le
 Qlt_le_weak Qlt_not_eq Qle_antisym Qle_refl: qarith.

Axiom Q_dec : forall x y:Q, (x<y)\/(y<x)\/(x=y).

Axiom Qlt_le_dec : forall x y:Q, (x<y)\/(y<=x).

Axiom Qopp_le_compat : forall p q:Q, p<=q -> -q <= -p.

Hint Resolve Qopp_le_compat : qarith.

Axiom Qle_minus_iff : forall p q:Q, p <= q <-> 0 <= q+-p.

Axiom Qlt_minus_iff : forall p q:Q, p < q <-> 0 < q+-p.

Axiom Qplus_le_compat :
  forall x y z t:Q, x<=y -> z<=t -> x+z <= y+t.
  
Axiom Qplus_lt_le_compat :
  forall x y z t:Q, x<y -> z<=t -> x+z < y+t.

Axiom Qplus_le_l : forall(x y z: Q), x + z <= y + z <-> x <= y.

Axiom Qplus_le_r : forall (x y z: Q), z + x <= z + y <-> x <= y.

Axiom Qplus_lt_l : forall (x y z: Q), x + z < y + z <-> x < y.

Axiom Qplus_lt_r : forall (x y z: Q), z + x < z + y <-> x < y.

Axiom Qmult_le_compat_r : forall x y z:Q, x <= y -> 0 <= z -> x*z <= y*z.

Axiom Qmult_lt_0_le_reg_r : forall x y z:Q, 0 < z -> x*z <= y*z -> x <= y.

Axiom Qmult_le_r : forall (x y z: Q), 0 < z -> (x*z <= y*z <-> x <= y).

Axiom Qmult_le_l : forall (x y z: Q), 0 < z -> (z*x <= z*y <-> x <= y).

Axiom Qmult_lt_compat_r : forall x y z, 0 < z -> x < y -> x*z < y*z.

Axiom Qmult_lt_r : forall x y z, 0 < z -> (x*z < y*z <-> x < y).

Axiom Qmult_lt_l : forall (x y z: Q), 0 < z -> (z*x < z*y <-> x < y).

Axiom Qmult_le_0_compat : forall a b, 0 <= a -> 0 <= b -> 0 <= a*b.

Axiom Qinv_le_0_compat : forall a:Q, 0 <= a -> 0 <= /a.

Axiom Qle_shift_div_l : forall a b c:Q,
 0 < c -> a*c <= b -> a <= b/c.

Axiom Qle_shift_inv_l : forall a c:Q,
 0 < c -> a*c <= 1 -> a <= /c.

Axiom Qle_shift_div_r : forall a b c:Q,
 0 < b -> a <= c*b -> a/b <= c.

Axiom Qle_shift_inv_r : forall b c:Q,
 0 < b -> 1 <= c*b -> /b <= c.

Axiom Qinv_lt_0_compat : forall a:Q, 0 < a -> 0 < /a.

Axiom Qlt_shift_div_l : forall a b c:Q,
 0 < c -> a*c < b -> a < b/c.

Axiom Qlt_shift_inv_l : forall a c:Q,
 0 < c -> a*c < 1 -> a < /c.

Axiom Qlt_shift_div_r : forall a b c:Q,
 0 < b -> a < c*b -> a/b < c.

Axiom Qlt_shift_inv_r : forall b c:Q,
    0 < b -> 1 < c*b -> /b < c.

Axiom Qmult_le_compat_l:
  forall x y z : Q, (x <= y) -> (0 <= z) -> (z * x <= z * y).

Hint Resolve Qmult_le_compat_l.

Axiom Qmult_lt_compat_l
     : forall x y z : Q, (0 < z) -> (x < y) -> (z*x < z*y).

Hint Resolve Qmult_lt_compat_l.

Axiom Qmult_inv_l : forall x : Q, ~ (x = 0) -> (/ x * x = 1).

Hint Resolve Qmult_inv_l.

Axiom Qplus_le_lt_compat:
  forall x y z t : Q, (x <= y) -> (z < t) -> (x + z < y + t).

Axiom Qplus_lt_compat_r:
  forall x y z : Q, (x < y) -> (x + z < y + z).

Axiom Qplus_lt_compat_l:
  forall x y z : Q, (x < y) -> (z + x < z + y).

Hint Resolve Qplus_lt_compat_r Qplus_lt_compat_l : qarith.

Hint Immediate Qlt_le_weak.

Axiom Qmult_Qdiv_fact :
forall (a b c : Q), ~ (c = 0) -> (a * (b / c) = (a * b) / c).

Axiom Qdiv_1 :
forall a, (a / 1 = a).

Axiom Qplus_le_0 :
forall a b, (0 <= a) -> (0 <= b) -> (0 <= a + b).

Axiom Qplus_lt_0 :
forall a b, (0 < a) -> (0 <= b) -> (0 < a + b).

Axiom Qmult_0 :
forall a b, (0 < a) -> (0 < b) -> (0 < a * b).

Axiom Qgt_0_Qneq_0 :
forall a, (0 < a) -> ~ (a = 0).

Tactic Notation "Qside" "using" constr(lemma) :=
try solve [repeat match goal with
| [ H: _ /\ _ |- _ ] => destruct H
end;
auto using Qplus_le_0, Qmult_le_0_compat, Qmult_0,
Qgt_0_Qneq_0, Qlt_le_weak, Qplus_lt_0, lemma].

Ltac Qside :=
Qside using I.

Axiom Qfracs :
forall a b c d:Q,
   0 < a /\ 0 < b /\ 0 < c /\ 0 < d ->
   (a + c)/(b + d) <= a/b + c/d.


Tactic Notation "multiply" "each" "side" "by"
constr(term) :=
rewrite <- Qmult_le_l with (z := term).

Tactic Notation "cancel" "numerator" "and"
"denominator" :=
rewrite !Qmult_div_r.

Tactic Notation "harmonize" "fractions" :=
rewrite !Qmult_Qdiv_fact.

Tactic Notation "consequence" "of" constr(lemma) := Qside using lemma.

Axiom Qfracs_take_two :
forall a b c d,
(0 < a) /\ (0 < b) /\ (0 < c) /\ (0 < d) ->
((a + c)/(b + d) <= a/b + c/d).
 

Definition mid p q : Q := ((1/2)*(p+q)).

Axiom mid_l : forall p q, (p < q) -> (p < mid p q).

Hint Resolve mid_l.

Axiom mid_r : forall p q, (p < q) -> (mid p q < q).

Hint Resolve mid_r.

Axiom Q11 : (0 < 1 + 1).
Axiom QD : forall x p:Q, Decidable (x < p).
Axiom QA2 : forall x p:Q, x < p → x + p < p * (1 + 1).
Axiom QA22 : forall x p:Q, x < p → x * (1 + 1) < x + p.
Axiom QA3 : forall x p:Q, (x + p) / (1 + 1) < p → x < p.
Axiom QA4 : forall p:Q, p < p + 1.

Local Set Universe Minimization ToSet.

Set Implicit Arguments.

(** Lower Reals in HoTT **) 

Record Rlow := mkRl {
      elt :> Q -> Sier;
      Rlinf : forall x y, elt x -> (y < x) -> elt y;
      Rlsup : forall x, elt x -> merely (exists y, elt y /\ (x < y)) }.

Arguments semi_decide A {_}.
Arguments decidable_semi_decide _ {_} /.
Arguments semi_decide_sier _ /.

Global Instance SemiDec (P : Q -> Type) (x : Q) (H : Decidable (P x)) : SemiDecide (P x).
Proof.                                                   
exact (decidable_semi_decide (P x)).
Defined.

Definition Q_inject (p:Q) : Rlow.
assert (Hd : forall x, Decidable (x < p)).
intros x. apply QD.
exists (fun x:Q => semi_decide (x < p)).
+ intros x y Hxp Hyx.
  unfold semi_decide in *.
  unfold SemiDec in *.
  unfold decidable_semi_decide in *.
  destruct (decide (x < p)).
  destruct (decide (y < p)).
  trivial.
  assert (Ha : y < p).
  apply Qlt_trans with x; trivial.
  red in n. specialize (n Ha).
  case n. 
  destruct (decide (y < p)).
  apply top_greatest.
  trivial.
+ intros x Hx. apply tr.
  exists ((x + p) /(1+1)).
  split.
  * unfold semi_decide in *. unfold SemiDec in *.
    unfold decidable_semi_decide in *.
    destruct (decide (x < p)).
    destruct (decide ((x + p) / (1 + 1) < p)).
    trivial.
    assert (((x + p) / (1 + 1)) < p).
    apply Qlt_shift_div_r. apply Q11. 
    revert l.
    apply QA2. 
    red in n.
    specialize (n X).
    case n. red in Hx.
    destruct (decide ((x + p) / 2 < p)).
    assert (X : Empty).
    apply n.
    revert l.
    apply QA3.
    case X.
    trivial.
  * apply Qlt_shift_div_l. apply Q11.
    unfold semi_decide in Hx.
    unfold SemiDec in Hx.
    unfold decidable_semi_decide in Hx.
    destruct (decide (x < p)).
    revert l. apply QA22. apply not_bot in Hx.
    case Hx. 
Defined.

Notation "[ n ]" := (Q_inject n) : Rl_scope.

Local Open Scope Rl_scope.
Delimit Scope Rl_scope with Rl.
Bind Scope Rl_scope with Rlow.

(** *** Order on Lower Reals *)

(* Order relation "lower than" *)
Definition Rllt (r s : Rlow) := exists p, ~ elt r p /\ elt s p.

(* Order relation "lower or equal" *)
Definition Rlle (r s : Rlow) := forall p, elt r p -> elt s p.

(* Equality between lower reals *)
Definition Rleq r s := Rlle r s /\ Rlle s r.

(** *** Some properties on order relations *) 

Lemma Rlinfe : forall r p q, elt r p -> (q <= p) -> elt r q.
intros r p q Hp He.
destruct (Qdec q p).
rewrite p0. trivial.
assert (He' : q < p). auto with qarith. 
apply Rlinf with p; auto.
Save.

Lemma Rlstable : forall r p q, elt r p -> (p=q) -> elt r q.
intros r p q Hp He.
apply Rlinfe with p; trivial.
rewrite He.
apply Qle_refl.
Save.

Lemma Rl_mon : forall x y p q, (q <= p) -> Rlle x y -> elt x p -> elt y q.
unfold Rlle. intros x y p q Hpq Hxy Hx.
apply Rlinfe with p; try assumption.  
auto. 
Save.

(* Rlle is reflexive, transitive, antisymmetric *)

Lemma Rlle_refl : forall r, Rlle r r.
red; intros; auto.
Save.

Hint Resolve Rlle_refl.

Lemma Rlle_trans : forall r s t, Rlle r s -> Rlle s t -> Rlle r t.
unfold Rlle; intros; auto.
Save.

Hint Resolve Rlle_trans.

Lemma Rlle_antisym : forall r s, Rlle r s -> Rlle s r -> Rleq r s.
red; auto.
Save.

Hint Resolve Rlle_antisym.

(* Rleq is transitive, symmetric and reflexive *)
Lemma Rleq_trans : forall r s t, Rleq r s -> Rleq s t -> Rleq r t.
  unfold Rleq. intros r s t. intros H H2.
  split.
  apply Rlle_trans with s.
  apply H. apply H2.
  apply Rlle_trans with s.
  apply H2. apply H.
Save.

Hint Resolve Rleq_trans.

Lemma Rleq_sym : forall r s, Rleq r s -> Rleq s r. 
  unfold Rleq. intros r s H.
  split; try apply H.  
Save.

Hint Resolve Rleq_sym.

Lemma Rleq_refl : forall r, Rleq r r.
red; intros; auto.
Save.

Hint Resolve Rleq_refl.

(** *** Definitions of elt and Rlle as morphisms *)

Global Instance Rle : Le Rlow. 
Proof.
intros r s.
refine (Rlle r s).
Defined.

(*
Lemma Rleq_Eq : forall x y, Rleq x y -> x = y.
intros x y Hxy.
apply Univalence. 
Admitted.

Instance Rlow_ord : PartialOrder Rle.
Proof.
  split.
  apply (@HSet.isset_hrel_subpaths _ (fun a b => Rleq a b)).
  red. apply Rleq_refl. apply _.
  apply Rleq_Eq. apply _.
  split. 
  unfold Reflexive; apply Rlle_refl.
  unfold Transitive; apply Rlle_trans.
  unfold AntiSymmetric.
  intros x y H H'.
  apply Rleq_Eq.
  apply Rlle_antisym.
  trivial.
  trivial.
Defined.*)
 
(** *** Additional properties on Rlow *)

Lemma elt_nelt_lt : forall x p q, elt x p -> ~ elt x q -> (p<q).
Proof.
intros x p q Hp Hq.
red in Hq.
destruct (Qle_total p q).
destruct (Qdec p q). 
rewrite <- p0 in Hq. 
case (Hq Hp).
auto with qarith.
assert (Heq : x q). 
destruct (Qdec p q).
rewrite <- p0 in Hq. 
case (Hq Hp).
apply Rlinf with p; try trivial.  
auto with qarith.  
case (Hq Heq). 
Qed. 

(* lt --> le *)
Lemma Rllt_le : forall x y, Rllt x y -> Rlle x y.
Proof.
intros x y (p0,(H1,H2)) p Hp. 
apply Rlinf with p0; trivial.
apply elt_nelt_lt with x; trivial.
Save.

(* lt --> ~ le *)
Lemma Rllt_notle : forall x y,  Rllt x y -> ~ (Rlle y  x).
Proof.
intros x y (p0,(H1,H2)) Hyx. 
apply H1.
apply Rl_mon with y p0.
apply Qle_refl. trivial.
trivial.
Save.

(* Transivity properties *) 

Lemma Rllt_le_trans : forall x y z, Rllt x y -> (Rlle y z) -> Rllt x z.
Proof.
intros x y z (p,(Hp1,Hp2)) Hyz. 
red. 
exists p. 
split; trivial.
apply Hyz; trivial.
Save.

Lemma Rlle_lt_trans : forall x y z, Rlle x y -> Rllt y z -> Rllt x z.
Proof.
intros x y z Hxy (q,(Hq1,Hq2)).
exists q. 
split; trivial. 
intro H.
apply Hq1.
apply Hxy; trivial. 
Save. 

Lemma Rllt_trans : forall x y z, Rllt x y -> Rllt y z -> Rllt x z.
Proof.
intros.
apply Rllt_le_trans with y; trivial.
apply Rllt_le. trivial.
Save.


(** *** A sufficent for proving the relation between two reals *)

Lemma Rleq_intro (r s : Rlow) : (forall n, elt r n <-> elt s n) -> Rleq r s.
Proof.
  intros H.
  unfold Rleq.
  apply Rlle_antisym.
+ intros p Hp.  
  apply H; trivial.
+ intros p Hp.  
  apply H; trivial.
Save.

Lemma Qle_Rlle : forall p q, p <= q -> Rlle [p] [q].
Proof.
intros p q Hpq r Hr.
Admitted.

Lemma nelt_elt_rllt (r s : Rlow) : forall r s n,  
             ~ elt r n -> elt s n -> Rllt r s.
Proof.
red; intros.
exists n.
split; assumption.
Save.

Lemma Elt_Q : forall p q, (p < q) <->  elt [q] p.
Proof.
intros p q.
simpl. 
unfold semi_decide.
unfold SemiDec.
unfold decidable_semi_decide.
destruct (decide (p < q)).
split.
intros K.
apply top_greatest.
intros T.
trivial.
split.
red in n.
intros H2.
specialize (n H2).
case n.
intros F.
red in n.
generalize not_bot.
intro F2.
red in F2.
specialize (F2 F).
case F2.
Qed.

Lemma notQltRl_Q : forall p q, (q <= p) <-> ~ elt [q] p.
Proof.
intros; simpl.
split.
intros Hh.
intro F.
unfold semi_decide in F.
unfold SemiDec in F.
unfold decidable_semi_decide in F.
destruct (decide (p < q)).
assert (HF :  ~ (p < q)). 
auto with qarith.
red in HF.
apply HF; trivial.
apply not_bot in F; trivial. 
intros Hh. 
unfold semi_decide in Hh.
unfold SemiDec in Hh. 
unfold decidable_semi_decide in Hh. 
red in Hh. 
destruct (decide (p < q)). 
case (Hh (top_greatest SierTop)).
auto with qarith. 
Qed.

Lemma Qlt_Rllt : forall p q, (p < q) -> Rllt [p] [q].
Proof.
intros.
exists p.
simpl. 
split; try trivial.
unfold semi_decide. unfold SemiDec. unfold decidable_semi_decide.
destruct (decide (p < p)).
apply Qlt_irrefl in l.
intro F.
trivial.
intro F.
generalize not_bot; intro HN.
specialize (HN F); trivial.
unfold semi_decide. unfold SemiDec. unfold decidable_semi_decide.
destruct (decide (p< q)).
apply top_greatest.
specialize (n X).
case n.
Qed.

Lemma Rllt_Qlt : forall p q, Rllt [p] [q] -> (p < q).
Proof.
intros p q (r,(H1,H2)).
apply Qle_lt_trans with r. 
simpl in *.
apply Qnot_lt_le; trivial. 
unfold semi_decide in *. 
unfold SemiDec in *. 
unfold decidable_semi_decide in *. 
destruct (decide (r < p)). 
red in H1.
case (H1 (top_greatest SierTop)).
trivial. 
red in H1. 
destruct (Qle_total r q). 
destruct (Q_dec r q). 
trivial. 
destruct s.
assert (HF : ~ q < r).  
auto with qarith. 
case (HF l0). 
Admitted.

Lemma Rlle_Qle : forall p q, Rlle [p] [q] -> (p <= q).
Proof.
unfold Rlle.
intros p q H.
simpl in *.
unfold semi_decide, SemiDec, decidable_semi_decide in *.
specialize (H q). 
destruct (decide (q < p)). 
destruct (decide (q < q)).
apply Qlt_irrefl in l0. 
case l0.
specialize (H (top_greatest SierTop)). 
apply not_bot in H; case H.
auto with qarith. 
Qed.

Hint Resolve Qle_Rlle Qlt_Rllt.
Hint Immediate Rlle_Qle Rllt_Qlt.

Lemma Qeq_Rleq : forall p q : Q, p = q -> Rleq [p] [q].
Proof.
intros p q H; apply Rlle_antisym; apply Qle_Rlle; rewrite H;
apply Qle_refl.
Save.

Lemma Rleq_Qeq : forall p q, Rleq [p] [q] -> (p = q).
  intros p q H; apply Qle_antisym.  apply Rlle_Qle. apply H.
  apply Rlle_Qle. apply H.
Qed. 

Hint Resolve Qeq_Rleq.
Hint Immediate Rleq_Qeq.

Lemma Elt_Rllt : forall r p, elt r p -> Rllt [p] r.
Proof.
intros.
exists p.
split; trivial.
intro F. 
simpl in F.
unfold semi_decide, SemiDec, decidable_semi_decide in F. 
destruct (decide (p < p)).
apply Qlt_irrefl in l; trivial. 
apply (not_bot F). 
Qed. 

Lemma Rllt_Elt : forall r p, Rllt [p] r -> elt r p.
Proof.
intros r p (q,(Hq1,Hq2)).
apply Rlinfe with q. 
trivial.
simpl in Hq1.
unfold semi_decide in Hq1.
unfold SemiDec in Hq1.
unfold decidable_semi_decide in Hq1.
red in Hq1.
destruct (decide (q < p)).
specialize (Hq1 (top_greatest ⊤)).
case Hq1.
auto with qarith.
Qed.

Lemma QRlle (p:Q) (r:Rlow) : forall k, elt r k -> (p <= k) ->  (Rlle [p] r).
Proof.
intros.
apply Rlle_trans with [k]. 
auto. 
apply Rllt_le; apply Elt_Rllt; trivial. 
Save.


(** *** IV. Bounded lower reals *)
(* Minus infinite : empty space *)
Definition minf : Rlow.
exists (fun q => SierBot).
intros x y H H'. trivial.
intros x H. apply tr. 
exists (x + 1).
split; try trivial.
apply QA4.
Defined.

(* Plus infinite : Q *)
Definition pinf : Rlow.
exists (fun q => SierTop).
intros x y H H2.
trivial.
intros x H. apply tr. 
exists (x+1). 
split; auto. apply QA4. 
Defined. 

(* Some trivial properties *)
Lemma Minf_nelt : forall q, ~ elt minf q.
Proof.
intros q. 
simpl. apply not_bot.
Save.

Lemma Pinf_elt : forall q, elt pinf q.
Proof.
intros q; apply top_greatest.
Save.

Hint Resolve Minf_nelt Pinf_elt.

(* Any lower real is between minf and pinf *)

Lemma Rlle_Pinf : forall r, Rlle r  pinf.
Proof.
intros r p Hp; auto.
Save. 

Lemma Minf_Rlle : forall r, Rlle minf r.
Proof.
intros r p Hp.
red in Hp.  
simpl in Hp.
apply not_bot in Hp.
case Hp.
Save.

Hint Resolve Rlle_Pinf Minf_Rlle.
(*
Global Instance semi_decide_exists (A : Type) {H' : Enumerable A}
  (B : A -> Type) {H : forall x, SemiDecide (B x)}
  : SemiDecide (exists x, B x)
  := EnumerableSup A (fun x => semi_decide (B x)).*)

Global Instance semi_decide_exists (A : Type) {H' : Enumerable A}
  (B : A -> Type) {H : forall x, SemiDecide@{j} (B x)}
  : SemiDecide (merely (exists x, B x))
  := EnumerableSup A (fun x => semi_decide (B x)).
Arguments semi_decide_exists A {_} B {_} /.

Definition Rl_Plus : Plus Rlow. 
Proof.
intros a b.
exists (fun p:Q => semi_decide (merely (exists (q:Q), 
          merely (exists (r:Q), elt a q /\ elt b r /\ p = q + r)))).
+intros x y H Hyx.
 red. red in H.
 unfold semi_decide in *.
 unfold decidable_semi_decide in *.
 unfold semi_decide_exists in *.
 assert (H1 : forall q, SierLe (semi_decide
            (merely
               (∃ r : Q, a q ∧ b r ∧ x = q + r)))
          (semi_decide
            (merely
              (∃ r : Q, a q ∧ b r ∧ y = q + r)))).
 * intros q.
   unfold semi_decide, semi_decide_exists, semi_decide,
          semi_decide_conj, semi_decide, SemiDec.
   admit.
   
 * (*apply SierLe_imply in H1. 

   revert H1.
   generalize enumerable_sup_least_ub. intro Hk.
   specialize (Hk nat NatEnum (fun n => (S n) x)
               (EnumerableSup nat (λ x0 : nat, (S x0) y)) H2).
trivial.



   apply (enumerable_sup_ub' _ (fun q => (semi_decide
            (merely
               (∃ r : Q, a q ∧ b r ∧ y = q + r))))). 
 
 
         
                 ((@EnumerableSup _ _ _ QEnum) (λ x0 : nat, (S x0) y))). 
 intros n.
 specialize (H1 n).
 transitivity ((S n) y). 
 trivial. 
 apply (enumerable_sup_ub' _ (fun n => (S n) y) n).
 revert H.
 apply SierLe_imply.
 generalize enumerable_sup_least_ub. intro Hk.
 specialize (Hk nat NatEnum (fun n => (S n) x)
               (EnumerableSup nat (λ x0 : nat, (S x0) y)) H2).
trivial.*)

 
 admit. 
+admit. (*
 destruct (decide (∃ q r : Q, a q ∧ b r ∧ x = q + r)).
 destruct (decide (∃ q r : Q, a q ∧ b r ∧ y = q + r)).
 trivial.
 assert (Hf : ∃ q r : Q, a q ∧ b r ∧ y = q + r).
 destruct s as (q,(r,(S1,(S2,S3)))).
 exists (q + (y - x)). exists r.
 split.
 apply Rlinf with q.
 trivial. admit. 
 split. 
 trivial.
 admit.

 specialize (n Hf).*)
 
Admitted.


Definition SeqRlow : (nat -> Sier) -> (nat -> Rlow). 
Proof.
intros L n.
specialize (L n).
exists (fun q => L).
intros x y r H.
trivial.
intros x r. apply tr. 
exists (x + 1).
split; try trivial.
apply QA4.
Defined.

Lemma NatEnum : Enumerable nat. 
exists (fun n => n).
apply _.
Qed.

Global Instance SDseq_Rlow (S : nat -> Rlow) (q : Q) :
                                 SemiDecide (exists n, (elt (S n) q)). 
Proof.
apply (@semi_decide_exists nat NatEnum (fun n => elt (S n) q)).
intros n.   
unfold SemiDecide.
specialize (S n).
refine (S q).
Defined.

Definition Rllub : (nat -> Rlow) -> Rlow. 
intros S.
exists (fun q => semi_decide (exists n, (elt (S n) q))).  
intros x y H H0.
unfold semi_decide in *.
unfold SDseq_Rlow in *.
unfold semi_decide_exists in *.
unfold semi_decide in *.
assert (H1 : forall n, SierLe ((S n) x) ((S n) y)).
intros n.
apply imply_le.
intros Hx.
apply Rlinf with x; trivial.
assert (H2 : forall n, SierLe ((S n) x)
                 ((@EnumerableSup _ _ _ NatEnum) (λ x0 : nat, (S x0) y))). 
intros n.
specialize (H1 n).
transitivity ((S n) y). 
trivial. 
apply (enumerable_sup_ub' _ (fun n => (S n) y) n).
revert H.
apply SierLe_imply.
generalize enumerable_sup_least_ub. intro Hk.
specialize (Hk nat NatEnum (fun n => (S n) x)
               (EnumerableSup nat (λ x0 : nat, (S x0) y)) H2).
trivial.
intros x Hx. 
unfold semi_decide in *. 
unfold SDseq_Rlow in *. 
unfold semi_decide_exists in * . 
admit. 
(*apply enumerable_sup_least_ub in H2.
trivial. 
Unfold EnumerableSup in *.
admit. admit. *)
Admitted.

Lemma Rllub_case 
  : forall (fr : nat -> Rlow) n p, elt (fr n) p -> elt (Rllub fr) p.
Proof.
intros fr n p H.
red.
Admitted.

Lemma Rllub_lub : forall (fr : nat -> Rlow) n, Rlle (fr n) (Rllub fr).
Proof.
exact Rllub_case.
Save.

Lemma Rllub_le 
  : forall (fr : nat -> Rlow) r, (forall n, Rlle (fr n)  r) -> Rlle (Rllub fr) r.
Proof.
  intros fr r.
  intros Hp.
Admitted.

Lemma Rllub_mon : forall (fr fk : nat -> Rlow), (forall n, Rlle (fr n) (fk n))
                               -> Rlle (Rllub fr) (Rllub fk). 
Proof. 
intros fr fk. 
intros Hle. 
assert (Hx : forall n, Rlle (fr n) (Rllub fk)). 
intros n.
specialize (Hle n). 
apply Rlle_trans with (fk n). 
auto.
apply Rllub_lub. 
apply Rllub_le. auto.
Defined. 

Record RlowPos := mkRlP {
      val :> Rlow;
      Rlpos : forall p : Q, (p < 0) -> elt val p
}.

Axiom Qnega : exists q : Q,  q < 0. 

Lemma RlowPos_pos : forall (r : RlowPos), Rlle [0] r.
intros r. unfold Rlle.
intros p Hp.
simpl in Hp.
unfold semi_decide, SemiDec in Hp.
unfold decidable_semi_decide in Hp.
Admitted.

Definition toRL : RlowPos -> Rlow.
intros (p,Hpos). exists p; apply p.
Defined.

Definition toRlseq : (nat -> RlowPos) -> (nat -> Rlow). 
Proof.
intros L n.
specialize (L n).
exists (val L).
intros x y HL Hxy.
apply Rlinf with x; trivial.
apply Rlsup.
Defined.

Lemma toRlseq_mon (A : hSet) (l m : nat -> RlowPos) :
        forall n, Rlle (l n) (m n) -> Rlle ((toRlseq l) n) ((toRlseq m) n). 
Proof. auto. Qed. 

Hint Resolve RlowPos_pos toRL. 

Lemma toRlseq_le_r (A : hSet) (l : nat -> RlowPos) (r : RlowPos) :
  forall n, Rlle (l n) r -> Rlle ((toRlseq l) n) r.
Proof. auto. Qed. 
  
Global Instance Rl_pos_Le : Le (RlowPos).
Proof.
intros x y.
refine (Rlle x y).
Defined.

Definition MaxRl : Rlow -> Rlow -> Rlow. 
Proof. 
intros r s.   
exists (fun q:Q => semi_decide (elt r q /\ elt s q)). 
intros x y H H'. 
unfold semi_decide in *.
unfold semi_decide_conj in *.
unfold semi_decide in *.
unfold semi_decide_sier in *.
apply top_le_meet.
apply top_le_meet in H.
destruct H as (Hrx,Hsx).
split; apply Rlinf with x; trivial.
intros x H. 
unfold semi_decide in *.
unfold semi_decide_conj in *.
unfold semi_decide in *.
unfold semi_decide_sier in *.
apply top_le_meet in H.
destruct H as (Hrx,Hsx).
admit. 
Admitted.

Lemma MaxRl_Max : forall a b : Rlow, (Rlle a (MaxRl a b)) /\ (Rlle b (MaxRl a b)).
Admitted. 

Lemma MaxRl_mon : forall a b c d : Rlow,
    Rlle a b -> Rlle c d -> Rlle (MaxRl a c) (MaxRl b d).
Admitted. 

Definition Rl_plus : Plus Rlow. Admitted.
  
Lemma QRl_Plus : forall (p q : Q), Rl_Plus [p] [q] == [(p+q)].
Proof.
Admitted.

(* r + 0 = r *)
Lemma Rl_Plus_r_0 : forall (r : Rlow), Rleq (Rl_Plus r [0]) r.
Proof.
Admitted.

Hint Resolve Rl_Plus_r_0.

(* Addition is commutative *)
Lemma Rl_Plus_comm_le : forall r s, Rlle (Rl_Plus r s) (Rl_Plus s r). 
intros r s k.
intros H.
Admitted. 

Lemma Rl_Plus_comm : forall r s, Rleq (Rl_Plus r s) (Rl_Plus s r).
Proof. 
split; apply Rl_Plus_comm_le. 
Save. 

(* Addition is associative *)
Lemma Rl_Plus_assoc : forall r s t, Rleq (Rl_Plus (Rl_Plus r s) t) 
                                         (Rl_Plus r (Rl_Plus s t)).
Proof.
intros; split; red; simpl.
Admitted. 
     
Hint Resolve Rl_Plus_comm Rl_Plus_r_0 Rl_Plus_assoc. 

Lemma Rl_Plus_assoc2 : forall r s t z, Rleq (Rl_Plus (Rl_Plus r s) (Rl_Plus t z)) 
                                         (Rl_Plus (Rl_Plus r t) (Rl_Plus s z)).
Proof.
intros r s t z.
Admitted.

Lemma Rl_Plus_mon : forall r s t u, Rlle r s -> Rlle t u -> Rlle (Rl_Plus r t) (Rl_Plus s u). 
Admitted.

Definition RllubPos (fr : nat -> RlowPos) : RlowPos.
exists (Rllub (toRlseq fr)).
intros p Hp.
assert (H : elt (fr 0%nat) p).
apply Rlpos. trivial.
apply Rllub_case with O.
apply H.
Defined.

Definition Rlow_RlowPos (r : Rlow) : (Rlle [0]  r)-> RlowPos.
  exists r. unfold Rlle in X.
  intros p Hp.
  specialize (X p).
  apply  Elt_Q in Hp.
  apply X; trivial.
Defined. 

Lemma O_simpl : Rlle [0] [0].
Proof. apply Rlle_refl. Qed. 

(** *** [0] for RlowPos *)
Definition RlP_0 : RlowPos.
refine ((@Rlow_RlowPos [0]) O_simpl).
Defined.

Lemma Rlle_O_I : Rlle [0] [1].
Proof.
red.
intros p HO.
apply Elt_Q in HO.
apply Elt_Q.
auto.
Admitted.

(** *** [1] for RlowPos *)
Definition RlP_1 : RlowPos. 
apply ((@Rlow_RlowPos [1]) Rlle_O_I).
Defined.

Definition RlP_plus : Plus RlowPos.
intros r s.
assert (Hpo : Rlle [0] (Rl_Plus r s)).
unfold Rlle.
intros p Hp.
apply Elt_Q in Hp.
apply Rl_mon with (Rl_Plus [0] [0]) p.
apply Qle_refl.
apply Rl_Plus_mon.
apply (RlowPos_pos r).
apply (RlowPos_pos s).
generalize (Rl_Plus_r_0 [0]).
intros (GRL1,GRL2).
unfold Rlle in GRL2.
apply Elt_Q in Hp.
specialize (GRL2 p Hp).
trivial. 
refine ((@Rlow_RlowPos (Rl_Plus r s)) Hpo).
Defined.

Definition MaxRlP : RlowPos -> RlowPos -> RlowPos. 
intros r s. 
assert (Hpo : Rlle [0] (MaxRl r s)).
unfold Rlle.
intros p Hp.
apply Elt_Q in Hp.
apply Rl_mon with (MaxRl [0] [0]) p.
apply Qle_refl.
apply MaxRl_mon.
apply (RlowPos_pos r).
apply (RlowPos_pos s).
apply Rl_mon with [0] p.
apply Qle_refl.
apply MaxRl_Max.
apply Elt_Q; trivial.
refine ((@Rlow_RlowPos (MaxRl r s)) Hpo).
Defined. 