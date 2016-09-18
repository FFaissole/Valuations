Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.interfaces.rationals
               HoTTClasses.theory.rationals.
Require Import HoTT.HSet HoTT.Basics.Decidable HoTT.Basics.Trunc
               HProp HSet Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom.

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
Axiom Q00 : 0 < 1. 
Axiom Q11 : (0 < 1 + 1).
Axiom QD : forall x p:Q, Decidable (x < p).
Axiom QA2 : forall x p:Q, x < p → x + p < p * (1 + 1).
Axiom QA22 : forall x p:Q, x < p → x * (1 + 1) < x + p.
Axiom QA3 : forall x p:Q, (x + p) / (1 + 1) < p → x < p.
Axiom QA4 : forall p:Q, p < p + 1.

Axiom QA5 : forall p:Q, p < 0 -> p < (p/2).
Axiom QA6 : forall p:Q, p < 0 -> (p / 2) < 0. 

Definition n_Q_m : nat -> Q -> Q.
intros n q. 
refine (Qmult (pos (pos_of_nat n)) q). 
Defined. 

Definition on : Q -> nat -> Q.
intros n q. 
Admitted. 