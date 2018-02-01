
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.interfaces.rationals
               HoTT.Classes.theory.rings
               HoTT.Classes.orders.rings
               HoTT.Classes.interfaces.integers
               HoTT.Classes.interfaces.naturals
               HoTT.Classes.interfaces.orders
               HoTT.Classes.implementations.natpair_integers
               HoTT.Classes.implementations.assume_rationals
               HoTT.Classes.theory.rings
               HoTT.Classes.theory.integers
               HoTT.Classes.theory.dec_fields
               HoTT.Classes.orders.dec_fields
               HoTT.Classes.theory.lattices
               HoTT.Classes.orders.lattices
               HoTT.Classes.theory.additional_operations
               HoTT.Classes.theory.premetric
               HoTT.Classes.theory.rationals
               HoTT.HSet HoTT.Basics.Decidable HoTT.Basics.Trunc
               HProp HSet Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom. 

Require Import sierpinsky partiality dedekind.


(** * Constructive Lower Reals *)

Local Set Universe Minimization ToSet.

Section Rlow_def_aux.

Definition QPred := Q -> Sier.

Variable elt : QPred.

Class IsRlow : Type := {
    is_inhab : hexists (fun q => elt q); 
    is_rounded : forall q, elt q <-> 
                 hexists (fun r => q < r /\ elt r)
}.

End Rlow_def_aux. 

Record Rlow := {
    elt :> QPred; 
    elt_Rlow : IsRlow elt
}.

Global Existing Instance elt_Rlow.

Definition inhab (c : Rlow) := is_inhab (elt c).
Definition rounded (c : Rlow) := is_rounded (elt c). 

Definition IsRlow_conjunction r : IsRlow r -> _
  := fun c => (is_inhab r, is_rounded r). 

Global Instance IsRlow_conj_isequiv {r}
  : IsEquiv (IsRlow_conjunction r).
Proof.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- intros E;split; apply E. 
- red;simpl. 
  intros. reflexivity.
- red;simpl. reflexivity.
- simpl. reflexivity.
Defined.

Section contents.
Context `{Funext} `{Univalence}.

Global Instance IsRlow_hprop : forall r, IsHProp (IsRlow r).
Proof.
intros. apply (@trunc_equiv _ _ ((IsRlow_conjunction r)^-1) _ _ _).
Qed.

Lemma Rlow_eq0 : forall a b : Rlow, elt a = elt b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); 
simpl; intros E. destruct E.
apply ap.
apply path_ishprop. 
Qed. 

Instance Rlow_isset : IsHSet Rlow.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => elt a = elt b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;
  apply Rlow_eq0;apply E.
Qed.

Lemma Rlow_eq : forall a b : Rlow, (forall q, elt a q <-> elt b q) -> a = b.
Proof.
intros a b E; 
apply Rlow_eq0;
apply path_forall;
intros q;apply (antisymmetry le);
apply imply_le;
apply E.
Qed.

Lemma Rlow_le : forall a q r, elt a r -> (q <= r)%mc -> elt a q. 
Proof.
intros a q r E1 E2.
destruct (le_or_lt r q) as [E3|E3].
- destruct (antisymmetry Qle r q); trivial.
- apply rounded. 
  apply tr. 
  exists r; auto.
Qed. 

Lemma Rlow_ord_lt : forall (c : Rlow) (q r : Q), elt c q -> ~ elt c r -> q < r.
Proof.
intros c q r E1 E2.
destruct (le_or_lt r q) as [E|E];trivial.
assert (Hh : elt c r). 
apply Rlow_le with q; trivial.
case (E2 Hh).
Qed.  

Global Instance Rlle : Le Rlow
  := fun a b => forall q, elt a q -> elt b q.

Arguments Rlle _ _ /.

Instance Rlle_partial_order : PartialOrder Rlle.
Proof.
repeat split.
- apply _.
- apply _.
- intros a q;trivial.
- intros a b c E1 E2 q E3. auto.
- intros a b E1 E2. 
  apply Rlow_eq.
  intros;split;(apply E1 || apply E2).
Qed.


Global Instance Rllt : Lt Rlow :=
  fun a b => merely (exists q, elt b q /\ ~ elt a q).

Arguments Rllt _ _ /.

Global Instance RCApart : Apart Rlow
  := fun a b => a < b \/ b < a.

Lemma Fpo_Qle_Qlt : FullPseudoOrder Qle Qlt. 
Proof.
split; try apply _. 
split; try apply _.
apply rationals_order. 
apply rationals_order.
Qed. 

Instance Rllt_strict_order : StrictOrder Rllt.
Proof.
repeat split.
- apply _.
- intros a;hnf;
  apply (Trunc_ind _);intros [q [E1 E2]].
  case (E2 E1). 
- intros a b c E E';revert E; 
  apply (Trunc_ind _);intros [q [E1 E2]];
  revert E';apply (Trunc_ind _);
  intros [r [E3 E4]].
  apply tr;exists q. split. 
  + apply Rlow_le with r;  trivial.
    assert (H' : q < r). 
    apply Rlow_ord_lt with b; trivial.
    destruct (Qdec q r); trivial.
    rewrite p; reflexivity.
    apply lt_iff_le_ne; trivial. 
  + trivial. 
Qed.

Notation "a ⊆ b" := (Rlle a b) (at level 60). 

Lemma Rlow_stable : forall r p q, elt r p -> (p=q) -> elt r q.
Proof.
intros r p q Hp He.
rewrite <- He; trivial.
Qed.

(** Monotonicity property : if (p<=q)%Q and (x<=y)%RC then 
    (if p is in x then q is in y *)

Lemma Rlow_mon : forall (x y : Rlow) (p q :Q),
    Qle q p -> x ⊆ y -> elt x p -> elt y q.
Proof.
intros x y p q Hpq Hxy Hx.
destruct (Qdec p q).
rewrite <- p0.
auto.
apply Rlow_le with p; try assumption; auto.
Qed. 

(** Qlt is semi_decidable *)
Global Instance  Rllt_semi_dec : forall r q : Q, SemiDecide (r < q). 
Proof. 
intros r q.
apply decidable_semi_decide. 
destruct (Qle_total r q). 
destruct (Qdec r q). 
right. 
apply Fpo_Qle_Qlt. 
rewrite p. 
reflexivity. 
left.
apply trivial_apart in n.
pose (FR' := Fpo_Qle_Qlt). 
destruct FR' as (_,(_,_,_,_,FR'),_).  
specialize (FR' r q).
apply FR' in n. 
destruct n. 
trivial.
assert (Hh : ~ Qlt q r). 
apply Fpo_Qle_Qlt; trivial. 
case (Hh l0). 
destruct (Qdec r q). 
rewrite p. 
right. 
apply (irreflexivity Qlt). 
right. 
apply Fpo_Qle_Qlt; trivial. 
Defined.


(** Case rational ---> lower real *) 
Lemma QIsRlow : forall q : Q, IsRlow (fun r => semi_decide (r < q)).
Proof.
intros q; split.
+ apply tr; exists (q - Qone).
  apply (snd semi_decidable).
  apply flip_lt_minus_l.
  apply pos_plus_lt_compat_r. 
  apply lt_0_1. 
+ intros p;split.
  - intros Hh;apply semi_decidable in Hh.
    apply tr;econstructor;
    split;[|apply (snd semi_decidable)];
    apply Q_average_between;trivial.
  - apply (Trunc_ind _);
    intros [r [H1 H2]];
    apply (snd semi_decidable);
    apply semi_decidable in H2.
    transitivity r;trivial.
Qed. 

Global Instance QRlow : Cast Q Rlow. 
Proof.
intros q. 
exists (fun r => semi_decide (r < q)%mc).
apply QIsRlow.
Defined. 

Arguments QRlow _ /.

(** Zero on Rlow *)
Global Instance Rl0 : Zero Rlow := QRlow Qzero.
Arguments Rl0 /.

(** One on Rlow *)
Global Instance Rl1 : One Rlow := QRlow Qone.
Arguments Rl1 /.


(** Properties of QRlow *)
Lemma Rllt_Q_preserving : StrictlyOrderPreserving (cast Q Rlow).
Proof.
intros q r E. apply tr.
exists ((q + r) / (Qone + Qone)). 
split. 
apply (snd semi_decidable);
apply Q_average_between; auto. 
intros K. 
apply (snd semi_decidable) in K. 
unfold semi_decide, semi_decide_sier in K. 
simpl in K. 
unfold semi_decide in K. 
destruct (dec ((q + r) / (Qone + Qone) < q)). 
assert (Hj : q < (q + r) / (Qone + Qone)). 
apply Q_average_between; auto.
assert (Hf2 : ~ ((q + r) / (Qone + Qone)) < q).
intros S.
apply lt_flip in S.
case (S Hj).
case (Hf2 l).
unfold Rllt_semi_dec in K.
simpl in K.
destruct (dec ((q + r) / (Qone + Qone) < q)).
case (n l).
apply not_bot in K; case K. 
Qed.

Lemma Rllt_Q_reflecting : StrictlyOrderReflecting (cast Q Rlow).
Proof.
intros q r;apply (Trunc_ind _);intros [s [H1 H2]].
apply (@semi_decidable (_ < _) _ _) in H1.
simpl in H2; unfold semi_decide in H2.
unfold Rllt_semi_dec in H2; simpl in H2.
destruct (dec (s < q)). 
case (H2 (top_greatest SierTop)). 
destruct (le_or_lt q r).
destruct (Qdec q r). 
rewrite p in n. 
case (n H1). 
generalize (le_equiv_lt q r).
intros [].
trivial.
intros p.
case (n0 p).
trivial.
assert (Hf : s < q).
transitivity r; trivial.
case (n Hf).
Qed.

Global Instance Rllt_Q_embedding : StrictOrderEmbedding (cast Q Rlow).
Proof.
split.
- apply Rllt_Q_preserving.
- apply Rllt_Q_reflecting.
Qed.

(** Sum of two lower reals *)
Global Instance pred_plus_l : Plus QPred.
Proof.
intros x y q.
exact (semi_decide (merely (exists r : Q, merely (exists s : Q,
  x r /\ y s /\ q = r + s)))).
Defined.

Arguments pred_plus _ _ / _.

Lemma rlow_pred_plus_pr : forall a b : Rlow, forall q,
  (pred_plus (elt a) (elt b)) q <->
  merely (exists r s, elt a r /\ elt b s /\ q < r + s).
Proof.
intros a b q;split.
+ intros Hh;
  apply pred_plus_pr in Hh;
  revert Hh;apply (Trunc_ind _);
  intros [p [t [H1 [H2 H3]]]].
  apply rounded in H1.
  revert H1;
  apply (Trunc_ind _);
  intros [p' [Er E1]].
  apply tr;exists p',t;
  repeat split;trivial.
  rewrite H3.
  apply (strictly_order_preserving (+ _)). trivial.
+ apply (Trunc_ind _);
  intros [p [t [H1 [H2 H3]]]].
  apply pred_plus_pr.
  apply tr;exists p, (t - (p + t - q));
  repeat split.
  - trivial.
  - apply Rlow_le with t;trivial.
    apply lt_le.
    apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply flip_lt_minus_l.
    rewrite involutive, plus_0_l.
    trivial.
  - abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma plus_isRlow : forall a b : Rlow, 
            IsRlow (pred_plus (elt a) (elt b)).
Proof.
intros a b;split.
+ generalize (inhab a).
  apply (Trunc_ind _);
  intros [p H1].
  generalize (inhab b).
  apply (Trunc_ind _);
  intros [q H2].
  apply tr;exists (p+q).
  apply pred_plus_pr.
  apply tr;exists p,q;auto.
+ intros q;split.
  - intros Hh.
    apply pred_plus_pr in Hh.
    revert Hh;
    apply (Trunc_ind _);
    intros [p [t [H1 [H2 H3]]]].
    apply (rounded a) in H1.
    apply (rounded b) in H2.
    revert H1;apply (Trunc_ind _);
    intros [k [K1 K2]];
    revert H2;apply (Trunc_ind _);
    intros [z [Z1 Z2]].
    apply tr;exists (k + z). split.
    * rewrite H3. 
      apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  - apply (Trunc_ind _);
    intros [q' [E1 E2]].
    apply pred_plus_pr in E2.
    revert E2.
    apply (Trunc_ind _);
    intros [r' [s' [E2 [E3 E4]]]].
    assert (Hq : q = (r' - (q' - q)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hq.
    apply pred_plus_pr.
    apply tr;econstructor;econstructor;split;
    [|split;[|reflexivity]];trivial.
    apply Rlow_le with r';trivial.
    apply flip_le_minus_l.
    apply nonneg_plus_le_compat_r.
    apply (snd (flip_nonneg_minus _ _)).
    apply lt_le;trivial.
Qed. 

Global Instance RlPlus : Plus Rlow.
Proof.
intros a b. 
exists (pred_plus (elt a) (elt b)). 
apply plus_isRlow. 
Defined.   

Arguments RlPlus _ _ /.

(** Properties of RlPlus : 
     - commutativity 
     - associativity 
     - left/right identity with 0
     - compatibility with QRlow *)

Lemma RlPlus_eq_pr : forall a b : Rlow, forall q,
  elt (a + b) q <->
  merely (exists r s, elt a r /\ elt b s /\ q = r + s).
Proof.
intros a b q;apply pred_plus_pr.
Qed.


Lemma RlPlus_lt_pr : forall a b : Rlow, forall q,
  elt (a + b) q <->
  merely (exists r s, elt a r /\ elt b s /\ q < r + s).
Proof.
exact rlow_pred_plus_pr.
Qed.

Lemma RlPlus_comm : Commutative RlPlus.
Proof.
intros a b;
apply Rlow_eq;
auto;
simpl;
intros q;
split;
intros E;
apply pred_plus_pr in E;
apply pred_plus_pr;
revert E;
apply (Trunc_ind _);
intros [r [s [E1 [E2 E3]]]];
apply tr;
exists s,r;
repeat split;trivial;
rewrite E3; apply commutativity.
Qed. 

Lemma RlPlus_assoc : Associative RlPlus.
Proof.
intros a b c;
apply (antisymmetry Rlle);
red;simpl;intros q E;
simpl in *;
apply pred_plus_pr in E;
revert E;apply (Trunc_ind _); 
[intros [r [s [E1 [E2 E3]]]] | intros [r [s [E2 [E1 E3]]]]];
apply pred_plus_pr in E2;
revert E2;apply (Trunc_ind _);
intros [l [u [E2 [E4 E5]]]];
rewrite E3,E5;
[rewrite plus_assoc | rewrite <-plus_assoc];
(apply pred_plus_pr;apply tr;
do 2 econstructor;split;
[|split;[|reflexivity]]);
trivial;
apply pred_plus_pr;apply tr;eauto.
Qed.

Lemma RlPlus_left_id : LeftIdentity RlPlus Rl0.
Proof.
intros a;
apply (antisymmetry le);
red;simpl;intros q E;
simpl in *. 
- apply pred_plus_pr in E;
  revert E;
  apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  apply semi_decidable in E1.
  rewrite E3.
  apply Rlow_le with s;trivial.
  set (S:=s) at 2;rewrite <-(plus_0_l S).
  apply (order_preserving (+ _)). 
  apply lt_le;trivial.
- apply pred_plus_pr.
  apply rounded in E;revert E;
  apply (Trunc_ind _);
  intros [s [E1 E2]].
  apply tr;exists (q - s),s;
  repeat split.
  + apply (snd semi_decidable).
    destruct (dec (q-s < Qzero)).
    apply top_greatest.
    apply flip_neg_minus in E1.
    case (n E1). 
  + trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma RlPlus_Q : forall q r : Q, QRlow (q + r)
                                 = QRlow q + QRlow r :> Rlow.
Proof.
intros;apply (antisymmetry le).
- intros s E.
  change (IsTop (semi_decide (s < q + r))) in E.
  apply (fst semi_decidable) in E.
  change (IsTop ((elt (QRlow q) + elt (QRlow r)) s)).
  apply pred_plus_pr.
  apply tr.
  exists (q - (q + r - s) / 2)%mc, (r - (q + r - s) / 2)%mc.
  repeat split.
  + apply (snd semi_decidable).
    apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;
    [|solve_propholds].
    red. apply flip_pos_minus in E.
    trivial.
  + apply (snd semi_decidable).
    apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;
    [|solve_propholds].
    red.
    apply flip_pos_minus in E.
    trivial.
  + set (QRS := q + r - s).
    path_via (q + r - QRS * (2 / 2))%mc;
    [|abstract ring_tac.ring_with_integers (NatPair.Z nat)].
    rewrite dec_recip_inverse;
    [|apply lt_ne_flip;solve_propholds].
    rewrite mult_1_r;unfold QRS;clear QRS.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
- intros s E.
  simpl. apply (snd semi_decidable).
  simpl in E.
  apply pred_plus_pr in E.
  revert E;apply (Trunc_ind _);
  intros [r' [s' [E1 [E2 E3]]]].
  apply semi_decidable in E1;
  apply semi_decidable in E2.
  rewrite E3.
  apply plus_lt_compat;trivial.
Qed.


(** Join of two lower reals *)
Lemma RlJoin_isRlow : forall a b : Rlow,
  IsRlow (fun q => semi_decide (hor (elt a q) (elt b q))).
Proof.
intros a b;split.
+ generalize (inhab a);
  apply (Trunc_ind _);intros [q E].
  apply tr.
  exists q.
  apply top_le_join, tr,inl,E.
+ intros q;split.
  - intros E.
    apply top_le_join in E.
    revert E;apply (Trunc_ind _).
    intros [E|E];
    apply rounded in E;
    revert E;apply (Trunc_ind _);
    intros [r [E1 E2]];
    apply tr;
    exists r; split;trivial;
    apply top_le_join,tr;auto.
  - apply (Trunc_ind _);
    intros [r [E1 E2]];
    apply top_le_join in E2;
    revert E2.
    apply (Trunc_ind _);intros [E2|E2];
    apply top_le_join,tr;
    [left|right];
    apply rounded,tr;
    eauto.
Qed.

Global Instance RlJoin : Join Rlow. 
Proof. 
intros a b. 
exists (fun q => semi_decide (hor (elt a q) (elt b q))). 
apply RlJoin_isRlow. 
Defined.   

Arguments RlJoin _ _ /.

(** Meet of two lower reals *)

Lemma RlMeet_isRlow : forall a b : Rlow,
  IsRlow (fun q => semi_decide (meet (elt a q) (elt b q))).
Proof.
intros a b;split.
+ generalize (inhab a);
  apply (Trunc_ind _);intros [qa Ea].
  generalize (inhab b);
  apply (Trunc_ind _);intros [qb Eb].
  apply tr.
  destruct (Qle_total qa qb).
  - exists qa.
    apply top_le_meet. 
    split.
    * trivial.
    * apply Rlow_le with qb; try trivial.
  - exists qb. 
    apply top_le_meet. 
    split.
    * apply Rlow_le with qa; try trivial.
    * trivial.
+ intros q;split.
  - intros E.
    apply top_le_meet in E.
    revert E.
    intros (E1,E2).
    apply rounded in E1.
    apply rounded in E2.
    revert E1; apply (Trunc_ind _).
    intros (q1,(E1,E1')).
    revert E2; apply (Trunc_ind _).
    intros (q2,(E2,E2')).
    apply tr.
    destruct (Qle_total q1 q2).
    * exists q1. 
      split; trivial.
      apply top_le_meet.
      split. 
      -- trivial.
      -- apply Rlow_le with q2; try trivial.
    * exists q2. 
      split; trivial. 
      apply top_le_meet.
      split. 
      -- apply Rlow_le with q1; try trivial.
      -- trivial.
   - apply (Trunc_ind _).
     intros (r,(Hr1,Hr2)).
     apply top_le_meet.     
     apply top_le_meet in Hr2.
     destruct Hr2 as (Hr21,Hr22).
     split.     
     -- apply Rlow_le with r.
        trivial.
        apply lt_le; trivial.
     -- apply Rlow_le with r.
        trivial.
        apply lt_le; trivial.
Qed.

Global Instance RlMeet : Meet Rlow. 
Proof. 
intros a b. 
exists (fun q => semi_decide (meet (elt a q) (elt b q))). 
apply RlMeet_isRlow. 
Defined.   

Arguments RlMeet _ _ /.

(** Orders Rlle and operations on lower reals *)

Lemma Rlle_Q_preserving : OrderPreserving (cast Q Rlow).
Proof.
intros y q Hh t Hty. 
simpl in *.
unfold semi_decide in *.
unfold Rllt_semi_dec, decidable_semi_decide in *. 
destruct (dec (t < y)). 
destruct (dec (t < q)). 
trivial. 
assert (Hf : t < q). 
apply lt_le_trans with y; try trivial.
case (n Hf). 
destruct (dec (t < q)). 
apply top_greatest. 
trivial.
Qed.


Lemma RlPlus_le_preserving : forall a : Rlow, OrderPreserving (a +).
Proof.
intros a b c E q E1.
apply RlPlus_eq_pr in E1.
revert E1.
apply (Trunc_ind _).
intros [r [s [E1 [E2 E3]]]].
apply (RlPlus_eq_pr a c).
apply tr.
exists r,s.
split;trivial.
split; trivial.
apply E.
trivial.
Qed.


(** Auxiliary definitions of sequences of lower reals *)

Lemma NatEnum : Enumerable nat. 
Proof.
exists (fun n => n).
apply _.
Qed.


Global Instance SDseq_Rlow (S : nat -> Rlow) (q : Q) (H : Funext) :
                                 SemiDecide (exists n, (elt (S n) q)). 
Proof.
apply (@semi_decide_exists H nat NatEnum (fun n => elt (S n) q)).
intros n.   
unfold SemiDecide.
specialize (S n).
refine ((elt S) q).
Defined.


(** Lub of a sequence of lower reals *)
Definition Rllub (f : nat -> Rlow)  : Rlow.
Proof. 
exists (fun q => semi_decide (exists n, (elt (f n) q))). 
+ split. 
  - assert (Hn : forall n, merely (exists qn, elt (f n) qn)). 
    intros n.
    destruct (f n). 
    destruct elt_Rlow0. simpl. trivial.
    specialize (Hn O). 
    revert Hn; apply (Trunc_ind _). 
    intros (q,Hn). 
    assert (Ho : merely (exists n:nat, elt (f n) q)).
    apply tr; exists O; trivial. 
    generalize ((@top_le_enumerable_sup _ _ _ NatEnum) 
                (fun n => elt (f n) q)).
    intros HG. 
    apply HG in Ho.             
    apply tr. exists q. 
    trivial.
 - intros q. 
   split; intros H'.    
   * assert (Hnn : forall n, elt (f n) q
                -> merely (exists r, Qlt q r /\ elt (f n) r)).
     intros n. 
     destruct (f n). 
     destruct elt_Rlow0. 
     simpl. intros Hh. 
     apply is_rounded0 in Hh. trivial.
     apply top_le_enumerable_sup' in H'.
     revert H'; 
     apply (Trunc_ind _); intros (z,H').
     specialize (Hnn z).
     specialize (Hnn H').
     revert Hnn. apply (Trunc_ind _).
     intros (r,(Hr1,Hr2)).
     apply tr.
     exists r.
     split; try trivial.
     revert Hr2.
     unfold semi_decide.
     unfold SDseq_Rlow.
     unfold semi_decide_exists.
     intros H1.
     apply top_le_enumerable_sup.
     apply tr.
     exists z.
     unfold semi_decide, semi_decide_exists.
     trivial.
   * revert H'; apply (Trunc_ind _).      
     intros (rr,(H',H'')). 
     assert (Qle q rr).         
     apply orders.lt_le.
     trivial.
     apply top_le_enumerable_sup.
     apply top_le_enumerable_sup in H''.
     revert H''; apply (Trunc_ind _); intros (s,H'').
     apply tr.
     exists s.
     unfold semi_decide in *.    
     apply Rlow_le with rr; try trivial.
Defined.

(** Properties of Rllub *)
Lemma Rllub_case 
  : forall (fr : nat -> Rlow) n p, elt (fr n) p -> elt (Rllub fr) p.
Proof.
intros fr n p Hp.
apply Rlow_mon with (fr n) p.
reflexivity.
intros q.
apply SierLe_imply. 
generalize enumerable_sup_ub'.
intros HG.
apply (HG _ _ (fun n => elt (fr n) q)).
trivial.
Qed.

Lemma Rllub_lub : forall (fr : nat -> Rlow) n, Rlle (fr n) (Rllub fr).
Proof.
intros fr n q Hq.
revert Hq.
apply SierLe_imply. 
generalize enumerable_sup_ub'.
intros HG.
apply (HG _ _ (fun n => elt (fr n) q) n).
Qed.

Lemma Rllub_le 
  : forall (fr : nat -> Rlow) r, (forall n, Rlle (fr n)  r) -> Rlle (Rllub fr) r.
Proof.
intros fr r Hn.
intros q Hq.  
revert Hq.
apply SierLe_imply.
apply enumerable_sup_least_ub.
intros x.
apply imply_le.
apply Hn.
Qed.

Lemma Rllub_mon : forall (fr fk : nat -> Rlow), (forall n, Rlle (fr n) (fk n))
                                                -> Rlle (Rllub fr) (Rllub fk).
Proof.
intros fr fk Hrk q Hq.
apply top_le_enumerable_sup'.
apply top_le_enumerable_sup' in Hq.
revert Hq. apply (Trunc_ind _).
intros (z,Hq); apply tr.
exists z.
apply Rlow_mon with (fr z) q.
reflexivity.
apply Hrk.
trivial.
Qed.



(** Positive lower reals: a lower real is said to be positive if 
every negative rational number is in the lower real *)

Record RlowPos := mkRlP {
      rl :> Rlow;
      rlpos : forall p : Q, (p < Qzero) -> elt rl p
}.

Global Instance RlowPos_Rlow : Cast RlowPos Rlow := rl.
Arguments RlowPos_Rlow /.

Lemma RlowPos_pos : forall (r : RlowPos), Rlle Rl0 r.
Proof. 
intros r; unfold Rlle.
intros p Hp.
simpl in Hp.
unfold semi_decide, Rllt_semi_dec, 
       decidable_semi_decide in *.
destruct (dec (p < Qzero)). 
destruct r. simpl. 
apply rlpos0; trivial.
case (not_bot Hp). 
Qed.

Lemma RlP_eq : forall a b : RlowPos, (forall q, elt a q
                                    <-> elt b q) -> a = b.
Proof.
intros a b E; apply Rlow_eq in E; auto.
destruct a; 
destruct b; simpl; auto.
simpl in *; 
destruct E; 
apply ap; 
apply path_ishprop.
Qed.
(*
Definition toRL : RlowPos -> Rlow.
Proof.
intros (p,Hpos). refine p; apply p.
Defined.
*)
Global Instance Rllepos : Le RlowPos := fun x y => x ⊆ y.

Global Instance Rlltpos : Lt RlowPos := fun x y => Rllt x y.

Lemma RlP_eq0 : forall a b : RlowPos, elt a = elt b
                                      -> a = b.
Proof.  
intros (a,Ha) (b,Hb); 
simpl; intros E.
apply RlP_eq.
intros q; simpl. 
rewrite E. 
split; trivial.  
Qed. 

Global Instance RlP_isset :  IsHSet RlowPos. 
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => elt (rl a) = elt (rl b))).
- intros a;split;reflexivity.
- apply _. 
- intros a b E;
  apply RlP_eq0;apply E.
Qed.


Global Instance Rllepos_order : PartialOrder Rllepos.
Proof.
split.
+ apply RlP_isset. 
+ apply _. 
+ split.
  - red; intros; apply Rlle_partial_order.     
  - red. intros x y z. 
    apply Rlle_partial_order. 
+ red. intros x y Hx Hy.
  apply RlP_eq.  
  intros q. 
  split; intros Hab.
  * apply Hx; trivial. 
  * apply Hy; trivial. 
Qed.



(** Sequences of RlowPos *)
Definition toRlseq : (nat -> RlowPos) -> (nat -> Rlow). 
Proof.
intros L n.
specialize (L n).
refine L.
Defined.

(*
Definition toRlseqQ : (Q -> RlowPos) -> (Q -> Rlow). 
Proof.
intros L n.
specialize (L n).
refine L.
Defined.

Lemma toRlseq_mon (A : hSet) (l m : nat -> RlowPos) :
  forall n, Rlle (l n) (m n) -> Rlle ((toRlseq l) n)
                                     ((toRlseq m) n). 
Proof. auto. Qed.

Lemma toRlseqQ_mon (A : hSet) (l m :  Q-> RlowPos) :
  forall n, Rlle (l n) (m n) -> Rlle ((toRlseqQ l) n)
                                     ((toRlseqQ m) n). 
Proof. auto. Qed. 

Hint Resolve RlowPos_pos. 

Lemma toRlseq_le_r (A : hSet) (l : nat -> RlowPos) (r : RlowPos) :
  forall n, Rlle (l n) r -> Rlle ((toRlseq l) n) r.
Proof. auto. Qed. 

*)


(** Lub on sequences of RlowPos *)
Definition RllubPos (fr : nat -> RlowPos) : RlowPos.
Proof.
exists (Rllub (toRlseq fr)).
intros p Hp.  
assert (H2 : elt (fr 0%nat) p).
apply rlpos. trivial.
apply Rllub_case with O.
apply H2.
Defined.

Lemma RllubPos_case 
  : forall (fr : nat -> RlowPos) n p, elt (fr n) p -> elt (RllubPos fr) p.
Proof.
intros fr; apply Rllub_case.
Qed.

Lemma RllubPos_lub : forall (fr : nat -> RlowPos) n, Rlle (fr n) (RllubPos fr).
Proof.
intros fr; apply Rllub_lub.
Qed.

Lemma RllubPos_le 
  : forall (fr : nat -> RlowPos) r, (forall n, Rlle (fr n)  r) -> Rlle (RllubPos fr) r.
Proof.
intros fr.
apply Rllub_le.
Qed. 

Lemma RllubPos_mon : forall (fr fk : nat -> RlowPos),
    (forall n, Rlle (fr n) (fk n)) -> Rlle (RllubPos fr) (RllubPos fk).
Proof.
intros fr fk. 
apply Rllub_mon. 
Qed.


(** Any lower real r such that 0%Rlow <= r is positive *)
Definition Rlow_RlowPos (r : Rlow) : (Rlle Rl0  r) -> RlowPos.
Proof.
  exists r. unfold Rlle in X.
  intros p Hp.
  specialize (X p).
  apply X; trivial.
  simpl; destruct (dec (p < Qzero));
  unfold semi_decide, Rllt_semi_dec, decidable_semi_decide;
  destruct (dec (p < Qzero));
  try (apply top_greatest);
  case (n Hp). 
Defined.

(** 0 for RlowPos *)
Definition RlP_0 : RlowPos.
Proof.
exists Rl0.
intros p Hp.
simpl.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide;
destruct (dec (p < Qzero));
try (apply top_greatest);
case (n Hp). 
Defined.

(*
Lemma Rlle_O_I : Rlle (' 0) (' 1).
apply (Rlle_Q_preserving).
apply le_0_1.
Qed.
*)
(** 1 for RlowPos *)
Definition RlP_1 : RlowPos.
Proof.
exists Rl1.
intros p Hp. 
simpl.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide.
destruct (dec (p < Qone)).
apply top_greatest.
assert (Hc : p < Qone).
apply le_lt_trans with Qzero.
apply lt_le.
trivial.
apply lt_0_1.
case (n Hc).
Defined.

(** Sum of two RlowPos *)
Global Instance  RlP_plus : Plus RlowPos.
Proof. 
intros r s.
assert (Hpo : Rlle Rl0 (RlPlus r s)).
transitivity ((RlPlus  Rl0  Rl0)). 
rewrite (RlPlus_left_id). 
reflexivity.
transitivity ((RlPlus r  Rl0)). 
rewrite (RlPlus_comm r  Rl0). 
apply (RlPlus_le_preserving  Rl0). 
apply (RlowPos_pos r).
apply (RlPlus_le_preserving r) . 
apply (RlowPos_pos s).
refine ((@Rlow_RlowPos (RlPlus r s)) Hpo).
Defined.

Lemma RlP_plus_RlPlus : forall a b,
         rl (RlP_plus a b) = RlPlus a b. 
Proof.
intros a b. 
reflexivity.
Qed. 

Lemma RlPPlus_comm : Commutative RlP_plus.
Proof.
intros a b;
apply RlP_eq;
auto;
simpl;
intros q;
split;
intros E;
apply pred_plus_pr in E;
apply pred_plus_pr;
revert E;
apply (Trunc_ind _);
intros [r [s [E1 [E2 E3]]]];
apply tr;
exists s,r;
repeat split;trivial;
rewrite E3; apply commutativity.
Qed.   

Lemma RlPPlus_assoc : Associative RlP_plus.
Proof.
intros a b c;
apply (antisymmetry Rllepos);
red;simpl;intros q E;
simpl in *;
apply pred_plus_pr in E;
revert E;apply (Trunc_ind _); 
[intros [r [s [E1 [E2 E3]]]] | intros [r [s [E2 [E1 E3]]]]];
apply pred_plus_pr in E2;
revert E2;apply (Trunc_ind _);
intros [l [u [E2 [E4 E5]]]];
rewrite E3,E5;
[rewrite plus_assoc | rewrite <-plus_assoc];
(apply pred_plus_pr;apply tr;
do 2 econstructor;split;
[|split;[|reflexivity]]);
trivial;apply pred_plus_pr;apply tr;eauto.
Qed.

Lemma RlPPlus_left_id : LeftIdentity RlP_plus RlP_0.
Proof.
intros a;
apply (antisymmetry le);
red;simpl;intros q E;
simpl in *. 
- apply pred_plus_pr in E;
  revert E;
  apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  apply semi_decidable in E1.
  rewrite E3.
  apply Rlow_le with s; trivial.
  set (S:=s) at 2;rewrite <-(plus_0_l S).
  apply (order_preserving (+ _)). 
  apply lt_le;trivial.
- apply pred_plus_pr.
  apply rounded in E;revert E;
  apply (Trunc_ind _);
  intros [s [E1 E2]].
  apply tr;exists (q - s),s;repeat split.
  + unfold Rllt_semi_dec, decidable_semi_decide.
    destruct (dec (q - s < Qzero)). apply (snd semi_decidable).
    apply top_greatest.
    apply flip_neg_minus in E1. 
    case (n E1). 
  + trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Global Instance RlPApart : Apart@{UQ UQ} RlowPos
  := fun a b => a < b \/ b < a.
Arguments RlPApart _ _ /.

Lemma Rllepos_plus_le_preserving : forall a : RlowPos, OrderPreserving (a +).
Proof.
intros a b c Hh q Hh'. 
apply RlPlus_eq_pr in Hh'.
revert Hh';apply (Trunc_ind _);
intros [p [t [H1 [H2 H3]]]].
apply (RlPlus_eq_pr a c).
apply tr;exists p,t;
repeat split;trivial.
apply Hh; trivial.
Qed.

(** Lower offset on Rlow : a lower real minus a rational *)

Definition pred_minusQ_l (r : QPred) (q : Q) : (r q) -> QPred.
Proof.
intros Hqq. 
assert (fm : (Q -> Q)).    
intros x. 
refine (x + q).
refine (fun m => r (fm m)). 
Defined.   

Lemma minusQ_l_isRlow : forall (a : Rlow) (p : Q) (H : elt a p),
            IsRlow (pred_minusQ_l (elt a) p H).
Proof.
intros a p;split.
+ apply tr. unfold pred_minusQ_l.  
  exists Qzero.
  rewrite rings.plus_0_l; trivial.
+ split.
  - intros Hq.
    unfold pred_minusQ_l in *.
    apply rounded in Hq.
    revert Hq.
    apply (Trunc_ind _).    
    intros Hq.
    apply tr.
    destruct Hq as (r,(Hr1,Hr2)).
    exists (r - p).
    split.
    -- apply flip_lt_minus_r in Hr1.
       trivial.
    -- rewrite <- rings.plus_assoc.
       rewrite (plus_comm _ p). 
       rewrite plus_negate_r.
       rewrite plus_0_r.
       trivial.
   - apply (Trunc_ind _). intros (r,(E1,E2)).
     unfold pred_minusQ_l in *.
     assert ((q + p) < (r + p)).
     apply plus_lt_le_compat; trivial.
     reflexivity.
     apply Rlow_le with (r + p).
     trivial.
     apply orders.lt_le.
     trivial.
Defined.

Global Definition Rl_minus_q (r : Rlow) (q : Q) : (elt r q) -> Rlow.  
Proof.
intros He. 
exists (pred_minusQ_l (elt r) q He). 
apply minusQ_l_isRlow. 
Defined.   

Global Definition RlP_minus_q (r : RlowPos) (q : Q+) : elt r (pos q)
                                                       -> RlowPos.  
Proof.
intros He.
assert (Hpo : Rlle Rl0 (Rl_minus_q r (pos q) He)).
unfold Rl_minus_q. 
unfold pred_minusQ_l. 
intros v Hv.
simpl.
assert (v + pos q < pos q).
apply lt_le_trans with (Qzero + pos q). 
apply plus_lt_le_compat. 
simpl in Hv; unfold semi_decide, 
    Rllt_semi_dec, decidable_semi_decide in Hv.
destruct (dec (v < Qzero)).
trivial.
apply not_bot in Hv.
case Hv.
reflexivity. 
rewrite plus_0_l. 
reflexivity. 
apply Rlow_le with (pos q).
trivial.
apply orders.lt_le.
trivial.
refine ((@Rlow_RlowPos (Rl_minus_q r (pos q) He) Hpo)).
Defined.


Definition pred_minusQ_l2 (r : QPred) (q : Q) : QPred.
Proof.
assert (fm : (Q -> Q)).    
intros x. 
refine (x + q).
refine (fun m => r (fm m)). 
Defined.

Lemma minusQ_l_isRlow2 : forall (a : Rlow) (p : Q),
            IsRlow (fun m => semi_decide (hor ((pred_minusQ_l2 (elt a) p) m) (elt Rl0 m))).
Proof.
intros a p;split.
+ unfold pred_minusQ_l2.  
  destruct a.
  simpl.
  destruct elt_Rlow0.
  revert is_inhab0.  
  apply (Trunc_ind _).
  intros (z,Hz).
  apply tr.
  exists (z-p).
  assert (Hpp : z - p + p = z).
  rewrite <- rings.plus_assoc.
  rewrite (plus_comm _ p). 
  rewrite plus_negate_r.
  rewrite rings.plus_0_r.
  reflexivity.
  rewrite Hpp; trivial.
  revert Hz.
  apply SierLe_imply.
  apply SierJoin_is_join.
+ split.
  - intros Hq.
    unfold pred_minusQ_l2 in *.
    unfold semi_decide,semi_decide_disj in *.  
    unfold semi_decide in *.
    unfold semi_decide_sier in *.
    apply top_le_join in Hq. 
    unfold hor in Hq.
    revert Hq; apply (Trunc_ind _). 
    intros [].
    --  intros i. 
        apply rounded in i.
        revert i; apply (Trunc_ind _).         
        intros (r,(Hr1,Hr2)).
        apply tr; exists (r - p).
        split.
        --- apply flip_lt_minus_r in Hr1.
            trivial.
        --- rewrite <- rings.plus_assoc.
            rewrite (plus_comm _ p). 
            rewrite plus_negate_r.
            rewrite plus_0_r.
            apply top_le_join.
            unfold hor.
            apply tr; left; trivial. 
    -- intros i. 
       apply rounded in i.
       revert i; apply (Trunc_ind _).         
       intros (r,(Hr1,Hr2)).
       apply tr; exists r.
       split; trivial.
       apply top_le_join.
       unfold hor.
       apply tr; right; trivial.
  - apply (Trunc_ind _). intros (r,(E1,E2)).
    unfold pred_minusQ_l2 in *.
    assert ((q + p) < (r + p)).
    apply plus_lt_le_compat; trivial.
    reflexivity.
    apply top_le_join.
    unfold hor.
    apply top_le_join in E2. 
    unfold hor in E2. 
    revert E2; apply (Trunc_ind _). 
    unfold semi_decide, semi_decide_sier.
    intros []; intros i.
    -- apply tr; left.
       apply Rlow_le with (r + p).
       trivial.
       apply orders.lt_le.
       trivial.
    -- apply tr.
       right.
       apply Rlow_le with r.
       trivial. apply orders.lt_le.
       trivial.
Defined.

Global Definition Rl_minus_q2 (r : Rlow) (q : Q) : Rlow.  
Proof. 
exists (fun m => semi_decide (hor ((pred_minusQ_l2 (elt r) q) m) (elt Rl0 m))).
apply minusQ_l_isRlow2.
Defined.   

Global Definition RlP_minus_q2 (r : RlowPos) (q : Q+) : RlowPos.  
Proof.
assert (Hpo : Rlle Rl0 (Rl_minus_q2 r (pos q))).
unfold Rl_minus_q2.
intros v Hv.
simpl.
apply top_le_join. 
unfold hor.
apply tr.
right.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide.
destruct (dec (v < Qzero)).
+ apply top_greatest.
+ simpl in Hv.
  unfold semi_decide, Rllt_semi_dec, 
     decidable_semi_decide in Hv.
  destruct (dec (v < Qzero)).
  case (n l).
  apply not_bot in Hv.
  case Hv.
+ refine ((@Rlow_RlowPos 
    (Rl_minus_q2 r (pos q)) Hpo)).
Defined.

(** Multiplication of a lower real and a positive rational *)

Definition pred_multQ (r : QPred) (q : Q+) : QPred.
Proof.
intros m.
refine (r ((pos q)*m)).  
Defined.  

Lemma multQ_isRlow : forall (a : Rlow) (p : Q+),
            IsRlow (pred_multQ (elt a) p).
Proof.
intros a p;split.
+ unfold pred_multQ.
  destruct a as (a,Ha).
  destruct Ha. simpl in *.  
  revert is_inhab0.
  apply (Trunc_ind _).  
  intros (q,Hq). apply tr.
  exists (q/(pos p)).
  assert (X: pos p * (q / pos p) = q).
  transitivity (q*(pos p / pos p)).
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite (mult_comm (pos p)).
  reflexivity. 
  assert (Hp1 : pos p / pos p = Qone).
  transitivity (Qone/Qone).
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : Qzero < pos p).
  apply p.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.  
  rewrite Hp1.
  rewrite mult_1_r.
  reflexivity.   
  rewrite X.
  trivial.
+ split.
  - intros Hq.
    apply rounded in Hq.
    revert Hq.
    apply (Trunc_ind _).    
    intros Hq.
    apply tr.
    destruct Hq as (r,(Hr1,Hr2)).
    exists (r / (pos p)).
    split.
    assert (H1 : Qlt (pos p *q) 
                (pos p *(r / pos p))).
    rewrite (mult_comm _ (r / pos p)). 
    rewrite <- mult_assoc.
    rewrite (mult_comm _ (pos p)).
    assert (Hp1 : pos p / pos p = Qone).
    transitivity (Qone/Qone).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : Qzero < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hp1.
    assert (HZ : r* Qone = r).
    apply mult_1_r.
    rewrite HZ.
    assert (Hq : q = /pos p * (pos p * q)).
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm (/ pos p)).
    assert (Hp1' : pos p / pos p = Qone).
    transitivity (Qone/Qone).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : Qzero < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hp1.
    rewrite mult_1_r.
    reflexivity.
    trivial.
    apply pos_mult_reflect_l with (pos p).
    apply p.
    apply H1.
    unfold pred_multQ.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos p)).
    assert (Hp1 : pos p / pos p = Qone).
    transitivity (Qone/Qone).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : Qzero < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r.
    reflexivity.
    rewrite Hp1.
    rewrite mult_1_r. 
    trivial. 
  - apply (Trunc_ind _). intros (r,(E1,E2)).
    unfold pred_multQ in *.
    destruct (Qle_total Qzero q).
    destruct (Qdec Qzero q).
    rewrite <- p0.
    rewrite mult_0_r.
    revert E2.
    apply Rlow_mon.
    transitivity (Qzero*Qzero).
    rewrite mult_0_r;reflexivity.  
    apply mult_le_compat; try reflexivity.
    apply lt_le; apply p.
    transitivity q; trivial.
    apply lt_le; trivial.
    reflexivity.
    revert E2.
    apply Rlow_mon.
    apply mult_le_compat; trivial.
    apply lt_le, p.
    reflexivity.
    apply lt_le; trivial.
    reflexivity.
    revert E2.
    apply Rlow_mon.
    apply flip_le_negate.
    rewrite negate_mult_distr_l.
    rewrite negate_mult_distr_l.
    apply flip_nonpos_mult_l.
    apply flip_le_negate.
    rewrite negate_0, negate_involutive.
    apply lt_le, p.
    apply lt_le; trivial.
    reflexivity. 
Qed.

Global Definition Rlow_mult_q' : Q+ -> RlowPos -> Rlow. 
Proof.
intros q r. 
exists (pred_multQ (elt r) q). 
apply multQ_isRlow. 
Defined. 

Definition Rlow_mult_q : Q+ -> RlowPos -> RlowPos. 
Proof.
intros q r.
assert ( Rlle Rl0 (Rlow_mult_q' q r)).
unfold Rlow_mult_q'.
intros v Hv.
simpl.
unfold pred_multQ.
assert ((pos q) * v < Qzero).
simpl in Hv.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
destruct (dec (v < Qzero)).
rewrite mult_comm.
apply (neg_pos_mult v (pos q)); try trivial.
apply q.
apply not_bot in Hv.
case Hv.
apply RlowPos_pos.
simpl.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
destruct (dec (pos q * v < Qzero)).
apply top_greatest.
case (n X).
refine (@Rlow_RlowPos (Rlow_mult_q' q r) X).
Defined.

Lemma Rlow_mult_q1 : forall r, Rlow_mult_q Qpos_one r = r. 
Proof.
intros r.
apply (antisymmetry Rllepos).
unfold Rllepos.
intros q Hq.
unfold Rlow_mult_q in Hq.
simpl in Hq.
unfold pred_multQ in *.
assert (X : pos Qpos_one = Qone).
reflexivity.
rewrite X in Hq; clear X.
rewrite mult_1_l in Hq.
trivial.
intros q Hq.
simpl.
unfold pred_multQ.
assert (X : pos Qpos_one = Qone).
reflexivity.
rewrite X; clear X.
rewrite mult_1_l.
trivial.
Qed.

Lemma Rlow_mult_q_RlP_0 : forall q, Rlow_mult_q q RlP_0 = RlP_0.
Proof.
intros r.
apply (antisymmetry Rllepos).
intros q Hq.
unfold Rlow_mult_q in Hq.
simpl in Hq.
unfold pred_multQ in Hq.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
destruct (dec (pos r * q < Qzero)).
assert (H0q : q < Qzero).
apply neg_mult_decompose in l.
destruct l.
destruct p as (F,_).
assert (Hrp : Qle Qzero (pos r)). 
apply lt_le, r.
apply le_iff_not_lt_flip in Hrp.
case (Hrp F).
destruct p as (_,T). 
trivial.
simpl; unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *; 
destruct (dec (q < Qzero)). 
trivial.
case (n H0q).   
apply not_bot in Hq.
case Hq.  
unfold Rllepos.
intros q Hq.
simpl.
unfold pred_multQ.
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
destruct (dec (pos r * q < Qzero)).
apply top_greatest.
assert (hr : q < Qzero).
simpl in Hq; 
unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
destruct (dec (q < Qzero)); trivial.
apply not_bot in Hq; case Hq.
assert (Hr : pos r * q < Qzero).
apply pos_neg_mult; trivial.
apply r.
case (n Hr).  
Qed. 


(** Join of two RlowPos *)
Global Instance RlPJoin : Join RlowPos. 
Proof. 
intros a b.
destruct a as (a,PA).  
destruct b as (b,PB).
exists (RlJoin a b). 
intros p Hp.
specialize (PA p Hp).
specialize (PB p Hp).
simpl.
apply top_le_join.
apply tr.
left; trivial.
Defined.   

Arguments RlPJoin _ _ /.

(** Meet of two RlowPos *)
Global Instance RlPMeet : Meet RlowPos. 
Proof. 
intros a b.
destruct a as (a,PA).  
destruct b as (b,PB).
exists (RlMeet a b). 
intros p Hp.
specialize (PA p Hp).
specialize (PB p Hp).
simpl.
apply top_le_meet.
split; trivial.
Defined.   

Arguments RlPMeet _ _ /.

(** RlowPos is a semigroup for plus *)
Global Instance RlPSemiGroup_plus : @CommutativeSemiGroup 
                                 RlowPos RlP_plus.
Proof.
constructor.
+ constructor. 
  - apply _.
  - intros x y z.
    unfold sg_op.
    rewrite RlPPlus_assoc.
    reflexivity.
+ unfold sg_op; 
  apply RlPPlus_comm.
Defined.

(** RlowPos is a semigroup for join *)
Global Instance RlPSemiGroup_join : @CommutativeSemiGroup 
                                     RlowPos RlPJoin.
Proof.
constructor.
+ constructor. 
  - apply _.
  - intros x y z.
    unfold sg_op, join_is_sg_op.
    apply (antisymmetry Rllepos).
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y, z.
      apply top_le_join in Hq.
      apply top_le_join.
      unfold hor in *.
      simpl in *.
      revert Hq; apply (Trunc_ind _).
      intros []. intros i.
      apply tr; left; apply top_le_join; unfold hor.
      apply tr; left; trivial.
      intros i; apply top_le_join in i.
      revert i; apply (Trunc_ind _); intros [];
      intros i; apply tr.
      left.
      apply top_le_join; unfold hor.
      apply tr; right; trivial.
      right; trivial.
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y, z.
      apply top_le_join in Hq.
      apply top_le_join.
      unfold hor in *.
      simpl in *.
      revert Hq; apply (Trunc_ind _).
      intros []. intros i.
      apply top_le_join in i;
      revert i; apply (Trunc_ind _); 
      intros []. intros i.
      apply tr; left; trivial.
      intros i.
      apply tr; right.
      apply top_le_join; unfold hor.
      apply tr; left; trivial.
      intros i.
      apply tr; right.
      apply top_le_join; unfold hor.
      apply tr; right; trivial.
+ unfold sg_op, join_is_sg_op.
  intros x y.
  apply (antisymmetry Rllepos).
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y.
      apply top_le_join in Hq.
      apply top_le_join.
      revert Hq; apply (Trunc_ind _).
      intros [].
      intros i.
      apply tr.
      right; trivial.
      intros i.      
      apply tr. 
      left; trivial.
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y.
      apply top_le_join in Hq.
      apply top_le_join.
      revert Hq; apply (Trunc_ind _).
      intros [].
      intros i.
      apply tr.
      right; trivial.
      intros i. 
      apply tr. 
      left; trivial.
Defined.

(** RlowPos is a semigroup for meet *)
Global Instance RlPSemiGroup_meet : @CommutativeSemiGroup 
                                     RlowPos RlPMeet.
Proof.
constructor.
+ constructor. 
  - apply _.
  - intros x y z.
    unfold sg_op, join_is_sg_op.
    apply (antisymmetry Rllepos).
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y, z.
      apply top_le_meet in Hq.
      apply top_le_meet.
      simpl in *.
      split.
      apply top_le_meet.
      destruct Hq as (E1,E2).
      apply top_le_meet in E2.
      destruct E2 as (E2,E3).
      split; trivial.
      destruct Hq as (E1,E2).
      apply top_le_meet in E2.
      destruct E2 as (E2,E3).
      trivial.
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y, z.
      apply top_le_meet in Hq.
      apply top_le_meet.
      simpl in *.
      split.
      destruct Hq as (E1,E2).
      apply top_le_meet in E1.
      destruct E1 as (E1,E3).
      trivial.
      destruct Hq as (E1,E2).
      apply top_le_meet in E1.
      destruct E1 as (E1,E3).
      apply top_le_meet; split; trivial.
+ unfold sg_op, join_is_sg_op.
  intros x y.
  apply (antisymmetry Rllepos).
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y.
      apply top_le_meet in Hq.
      apply top_le_meet.
      destruct Hq; split; trivial. 
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y.
      apply top_le_meet in Hq.
      apply top_le_meet.
      destruct Hq; split; trivial. 
Defined.

(** RlowPos is a distributive lattice *)
Global Instance RlPDLattice : DistributiveLattice RlowPos.
Proof.
constructor.
+ constructor.
  - constructor.
    * apply RlPSemiGroup_join.
    * intros x; red.
      unfold sg_op, join_is_sg_op.
      apply (antisymmetry le).
      ** intros q Hq.
         simpl in Hq.        
         destruct x; simpl in *.
         apply top_le_join in Hq; 
         revert Hq; apply (Trunc_ind _).
         intros Hq.
         destruct Hq; trivial.
      ** intros q Hq.
         simpl in Hq.
         destruct x; simpl.
         apply top_le_join; 
         simpl in Hq.
         apply tr.
         left; trivial.
  - constructor.
    * apply RlPSemiGroup_meet.
    * intros x; red.
      unfold sg_op, join_is_sg_op.
      apply (antisymmetry le).
      ** intros q Hq.
         simpl in Hq.
         destruct x; simpl in *.
         apply top_le_meet in Hq; 
         destruct Hq; trivial.
      ** intros q Hq.
         simpl in *.
         destruct x; simpl in *.
         apply top_le_meet; 
         split; trivial.
  - intros x y.
    apply (antisymmetry le).
    * intros q Hq.
      simpl in Hq.
      destruct x, y; simpl in *.
      apply top_le_join in Hq.
      revert Hq; apply (Trunc_ind _).
      intros [].
      trivial.
      intros i.
      apply top_le_meet in i; destruct i; 
      trivial.
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y; simpl in *.
      apply top_le_join. 
      apply tr; left; trivial. 
  - intros x y.
    apply (antisymmetry le).
    * intros q Hq.
      simpl in Hq; unfold semi_decide in Hq.
      destruct x, y; simpl in *.
      apply top_le_meet in Hq.
      destruct Hq; trivial.
    * intros q Hq.
      simpl in *; unfold semi_decide in *.
      destruct x, y; simpl in *.
      apply top_le_meet.
      split; trivial.
      apply top_le_join; unfold hor; 
      apply tr; left; trivial.
+ intros x y z.
  apply (antisymmetry le).
  * intros q Hq.
    simpl in *; unfold semi_decide in *.
    destruct x, y, z; simpl in *.
    apply top_le_join in Hq; unfold hor in Hq.
    apply top_le_meet.
    split.
    revert Hq; apply (Trunc_ind _). 
    intros []. intros i.
    apply top_le_join; unfold hor; 
    apply tr; left; trivial.
    intros i.
    apply top_le_meet in i.
    destruct i as (E1,E2). 
    apply top_le_join; unfold hor; 
    apply tr; right; trivial.
    apply top_le_join; unfold hor.
    revert Hq; apply (Trunc_ind _); 
    intros []. intros i.
    apply tr; left; trivial.
    intros i.
    apply top_le_meet in i; 
    destruct i as (E1,E2).
    apply tr; right; trivial.
  * intros q Hq.
    simpl in *; unfold semi_decide in *.
    destruct x, y, z; simpl in *.
    apply top_le_join; unfold hor.
    apply top_le_meet in Hq.
    destruct Hq as (E1,E2).
    apply top_le_join in E1; unfold hor in E1; 
    revert E1; apply (Trunc_ind _); intros E1.
    apply top_le_join in E2; unfold hor in E2; 
    revert E2; apply (Trunc_ind _); intros E2.
    apply tr.
    destruct E1.
    destruct E2.
    left; trivial.
    left; trivial.
    destruct E2.
    left; trivial.
    right. 
    apply top_le_meet; split; 
    trivial.
Defined.

End contents.

Notation "a ++ b" := (RlPlus a b).
Notation "a -- q" := (Rl_minus_q2 a q) (at level 60).



