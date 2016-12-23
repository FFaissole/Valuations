Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.interfaces.rationals
               HoTTClasses.theory.rationals
               HoTTClasses.theory.rings
               HoTTClasses.orders.rings
               HoTTClasses.interfaces.integers
               HoTTClasses.interfaces.naturals
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.natpair_integers
               HoTTClasses.theory.rings
               HoTTClasses.theory.integers
               HoTTClasses.theory.dec_fields
               HoTTClasses.orders.dec_fields
               HoTTClasses.theory.lattices
               HoTTClasses.orders.lattices
               HoTTClasses.theory.additional_operations
               HoTTClasses.theory.premetric
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky.
Require Import HoTT.HSet HoTT.Basics.Decidable HoTT.Basics.Trunc
               HProp HSet Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom. 


(** * General construction for rounded down/up-closed 
subset on a type *)

Local Set Universe Minimization ToSet.

Section GeneralIlq.
  
(** Very general construction : A is any type, 
APred is the predicate of any subspace of A *)
  
Variable A : Type.

Definition APred := A -> Sier. 

Variable Rle : relation A.
Variable Rlt : relation A.
Hypothesis Hd : DecidablePaths A. 
Hypothesis Hda : AntiSymmetric Rle.
Hypothesis Hdt : TotalRelation Rle.
Hypothesis HA : Apart A. 
Hypothesis ATA : TrivialApart A (Aap := Rlt). 
Hypothesis FR : FullPseudoOrder Rle Rlt. 
Hypothesis RC_le_or_lt : forall x y : A, Rle x y ∨ Rlt y x. 

Section isRoundedClosed.

Variable elt : APred.
  
Class IsRC : Type :=
  {
    is_inhab : merely (exists q, elt q);
    is_rounded : forall q, iff@{Set UQ UQ} (elt q)
           (merely (exists r, Rlt q r /\ elt r))
  }.

End isRoundedClosed.  

Record RC :=  {
      elt : APred;
      elt_RC : IsRC elt
}.

Global Existing Instance elt_RC.

Definition inhab (c : RC) := is_inhab (elt c).
Definition rounded (c : RC) := is_rounded (elt c). 

Definition IsRC_conjunction r : IsRC r -> _
  := fun c => (is_inhab r, is_rounded r). 

Global Instance isRC_conj_isequiv {r}
  : IsEquiv (IsRC_conjunction r).
Proof.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- intros E;split; apply E. 
- red;simpl. intros. reflexivity.
- red;simpl. reflexivity.
- simpl. reflexivity.
Defined.

Section contents.
Context `{Funext} `{Univalence}.

Global Instance RC_hprop@{} : forall r, IsHProp (IsRC r).
Proof.
intros. apply (@trunc_equiv _ _ ((IsRC_conjunction r)^-1) _ _ _).
Qed.

Lemma RC_eq0 : forall a b : RC, elt a = elt b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 

Instance RC_isset@{} : IsHSet RC.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => elt a = elt b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply RC_eq0;apply E.
Qed.

Lemma RC_eq : forall a b : RC, (forall q, elt a q <-> elt b q) -> a = b.
Proof.
intros a b E; apply RC_eq0; apply path_forall;intros q;apply (antisymmetry le);
apply imply_le;apply E.
Qed.

Lemma RC_le : forall a q r, elt a r -> Rle q r -> elt a q. 
Proof.
intros a q r E1 E2.
destruct (RC_le_or_lt r q) as [E3|E3].
- destruct (antisymmetry Rle _ _ E2 E3). trivial.
- apply rounded. apply tr. exists r; auto.
Qed. 

Lemma RC_ordlt : forall (c : RC) (q r : A), elt c q -> ~ elt c r -> Rlt q r.
Proof.
intros c q r E1 E2.
destruct (RC_le_or_lt r q) as [E|E];trivial.
assert (Hh : elt c r). 
apply RC_le with q; trivial. 
case (E2 Hh).
Qed.  

Global Instance RCLe_l : Le@{UQ UQ} RC
  := fun a b => forall q, elt a q -> elt b q.

Arguments RCLe_l _ _ /.

Instance RCLe_l_partial_order@{} : PartialOrder RCLe_l.
Proof.
repeat split.
- apply _.
- apply _.
- intros a q;trivial.
- intros a b c E1 E2 q E3. auto.
- intros a b E1 E2. apply RC_eq.
  intros;split;(apply E1 || apply E2).
Qed.

Global Instance RCLt_l : Lt@{UQ UQ} RC :=
  fun a b => merely (exists q, elt b q /\ ~ elt a q).

Arguments RCLt_l _ _ /.

Global Instance RCApart : Apart@{UQ UQ} RC
  := fun a b => a < b \/ b < a.

Instance GenLt_strict_order@{} : StrictOrder RCLt_l.
Proof.
repeat split.
- apply _.
- intros a;hnf;apply (Trunc_ind _);intros [q [E1 E2]].
  case (E2 E1). 
- intros a b c E E';revert E; apply (Trunc_ind _);intros [q [E1 E2]];
  revert E';apply (Trunc_ind _);intros [r [E3 E4]].
  apply tr;exists q. split. 
  + apply RC_le with r;  trivial.
    assert (H' : Rlt q r). apply RC_ordlt with b; trivial.
    destruct (Hdt q r); trivial. 
    apply FR in r0. case (r0 H'). 
  + trivial.
Qed.

Notation "a <= b" := (RCLe_l a b). 

Lemma RC_stable : forall r p q, elt r p -> (p=q) -> elt r q.
intros r p q Hp He;
apply RC_le with p; trivial;
rewrite He; reflexivity.
Save.

Lemma RC_mon : forall (x y : RC) (p q :A),
    (Rle q p) -> x <= y -> elt x p -> elt y q.
intros x y p q Hpq Hxy Hx;
apply RC_le with p; try assumption; auto. 
Save.

End contents. 

End GeneralIlq.

Section GeneralRelQ. 

(** Special case of A = Q, QPred the predicate of any 
subset of Q *)
    
Definition QPred := APred Q. 

Variable Qle_g : relation Q.
Variable Qlt_g : relation Q.
Hypothesis Hdec : DecidablePaths Q.
Hypothesis Hda : AntiSymmetric Qle_g.
Hypothesis Hdt : TotalRelation Qle_g.
Hypothesis FR : FullPseudoOrder Qle_g Qlt_g. 
  
Section GeneralDefQ. 

Variable elt : QPred. 

Definition IsRCQ := IsRC Q Qlt_g elt. 

End GeneralDefQ. 

Record RCQ :=  {
      eltQ : QPred;
      elt_RCQ : IsRCQ eltQ
}. 

Global Instance  RCLt_semi_dec : forall r q, SemiDecide (Qlt_g r q). 
Proof. 
intros r q.
apply decidable_semi_decide. 
destruct (Hdt r q). 
destruct (Qdec r q). 
right. 
apply FR. 
rewrite p. 
reflexivity. 
left.
apply trivial_apart in n.
pose (FR' := FR). 
destruct FR' as (_,(_,_,_,_,FR'),_).  
specialize (FR' r q).
apply FR' in n. 
destruct n. 
trivial.
assert (Hh : ~ Qlt_g q r). 
apply FR; trivial. 
case (Hh l). 
destruct (Qdec r q). 
rewrite p. 
right. 
apply (irreflexivity Qlt_g). 
right. apply FR; trivial. 
Defined.

End GeneralRelQ. 

Section LowerReals. 
(** Lower Reals, QPred is the set of all the 
rationals less than the represented real numbers, 
i.e. half a dedekind cut. *)
  
Section LowerReals_def.

Variable elt : QPred. 
Definition IsRlow := IsRCQ Qlt elt.
  
End LowerReals_def. 

Context `{Funext} `{Univalence}.

Definition Rlow := RC Q Qlt. 

(** Order relations on Rlow *)
Global Instance Rlle : Le Rlow := RCLe_l Q Qlt.

Instance Rlle_order@{} : PartialOrder Rlle.
Proof.
apply RCLe_l_partial_order; trivial.
Defined. 

Global Instance Rllt : Lt Rlow := RCLt_l Q Qlt. 

Lemma Fpo_Qle_Qlt : FullPseudoOrder Qle Qlt. 
Proof.
split; try apply _. 
split; try apply _.
apply rationals_order. 
apply rationals_order.
Qed. 

Global Instance RlApart : Apart@{UQ UQ} Rlow
  := fun a b => a < b \/ b < a.
Arguments RlApart _ _ /.

Instance Rllt_strict_order@{} : StrictOrder Rllt.
Proof.
repeat split.
- apply _.
- intros a;hnf. apply (Trunc_ind _);intros [q [Hh Hh']].
  case (Hh' Hh).
- intros a b c Hh Hh';revert Hh; apply (Trunc_ind _);intros [q [H1 H2]];
  revert Hh';apply (Trunc_ind _);intros [r [H3 H4]].
  apply tr;exists q. split.
  + apply RC_le with Qle r. red.
    intros x y Hxy Hyx.
    apply (antisymmetry le); trivial.
    apply le_or_lt. trivial.
    assert (Hlt : Qlt q r). 
    apply RC_ordlt with Qle b; try trivial.
    intros s s2; apply (antisymmetry le).
    apply le_or_lt. 
    apply Fpo_Qle_Qlt. 
    apply rationals_order.
    generalize (le_or_lt q r).
    intros HH. destruct HH. trivial.    
    apply lt_flip in l. case (l Hlt).
  + trivial.
Qed.

Definition val := elt Q Qlt.

(** Any rational is a lower real *) 
Lemma QIsRlow : forall q : Q, IsRlow (fun r => semi_decide (r < q)).
Proof.
intros q; split.
+ apply tr; exists (q - 1).
  apply (snd semi_decidable).
  apply flip_lt_minus_l.
  apply pos_plus_lt_compat_r;solve_propholds.
+ intros p;split.
  - intros Hh;apply semi_decidable in Hh.
    apply tr;econstructor;split;[|apply (snd semi_decidable)];
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
exists (fun r => semi_decide (r < q)).
apply QIsRlow.
Defined. 

Arguments QRlow _ /.

(** Zero on Rlow *)
Global Instance Rl0 : Zero Rlow := QRlow 0.
Arguments Rl0 /.

(** One on Rlow *)
Global Instance Rl1 : One Rlow := QRlow 1.
Arguments Rl1 /.

(** Properties of QRlow *)
Lemma Rllt_Q_preserving : StrictlyOrderPreserving (cast Q Rlow).
Proof.
intros q r E. apply tr.
exists ((q + r) / 2). 
split. 
apply (snd semi_decidable);
apply Q_average_between; auto. 
intros K. 
apply (snd semi_decidable) in K. 
unfold semi_decide, semi_decide_sier in K. 
simpl in K. 
unfold semi_decide in K. 
destruct (decide ((q + r) / 2 < q)). 
assert (Hj : q < (q + r) / 2). 
apply Q_average_between; auto.
assert (Hf2 : ~ ((q + r) / 2 < q)).
intros S.
apply lt_flip in S.
case (S Hj).
case (Hf2 l). 
apply not_bot in K; case K. 
Qed.

Lemma Rllt_Q_reflecting : StrictlyOrderReflecting (cast Q Rlow).
Proof.
intros q r;apply (Trunc_ind _);intros [s [H1 H2]].
apply (@semi_decidable (_ < _) _ _) in H1.
simpl in H2; unfold semi_decide in H2. 
destruct (decide (s < q)). 
case (H2 (top_greatest SierTop)). 
destruct (le_or_lt q r).
destruct (Qdec q r). 
rewrite p in n. 
case (n H1). generalize (le_equiv_lt q r).
intros HS. destruct HS. 
trivial.
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

(* Addition of lower reals : like in dedekind cuts in HoTTClasses*)
Definition pred_plus_l : Plus QPred.
Proof.
intros x y q.
exact (semi_decide@{UQ} (merely (exists r : Q, merely (exists s : Q,
  x r /\ y s /\ q = r + s)))).
Defined.

Arguments pred_plus_l _ _ / _.
Existing Instance pred_plus_l.

Lemma rlow_pred_plus_pr : forall a b : Rlow, forall q,
  (val a + val b) q <->
  merely (exists r s, val a r /\ val b s /\ q < r + s).
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
+ apply (Trunc_ind _);intros [p [t [H1 [H2 H3]]]].
  apply pred_plus_pr.
  apply tr;exists p, (t - (p + t - q));repeat split.
  - trivial.
  - apply RC_le with Qle t;trivial.
    intros ss sh;
    apply (antisymmetry le).
    apply le_or_lt. 
    apply lt_le ;red.
    apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply flip_lt_minus_l.
    rewrite involutive, plus_0_l.
    trivial.
  - abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma plus_isRlow : forall a b : Rlow, IsRlow (val a + val b).
Proof.
intros a b;split.
+ generalize (inhab Q Qlt a).
  apply (Trunc_ind _);
  intros [p H1].
  generalize (inhab Q Qlt b).
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
    apply (rounded Q Qlt a) in H1.
    apply (rounded Q Qlt b) in H2.
    revert H1;apply (Trunc_ind _);
    intros [k [K1 K2]];
    revert H2;apply (Trunc_ind _);
    intros [z [Z1 Z2]].
    apply tr;exists (k + z). split.
    * rewrite H3. apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  - apply (Trunc_ind _);intros [q' [E1 E2]].
    apply pred_plus_pr in E2.
    revert E2.
    apply (Trunc_ind _);intros [r' [s' [E2 [E3 E4]]]].
    assert (Hq : q = (r' - (q' - q)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hq.
    apply pred_plus_pr.
    apply tr;econstructor;econstructor;split;
    [|split;[|reflexivity]];trivial.
    apply RC_le with Qle r';trivial.
    intros ss sh; apply (antisymmetry le).
    apply le_or_lt. 
    apply flip_le_minus_l.
    apply nonneg_plus_le_compat_r.
    apply (snd (flip_nonneg_minus _ _)).
    apply lt_le;trivial.
Qed. 

Global Instance RlPlus : Plus Rlow.
Proof.
intros a b. 
exists (val a + val b). 
apply plus_isRlow. 
Defined.   

Arguments RlPlus _ _ /.

Lemma Rlplus_eq_pr : forall a b : Rlow, forall q,
  val (a + b) q <->
  merely (exists r s, val a r /\ val b s /\ q = r + s).
Proof.
intros a b q;apply pred_plus_pr.
Qed.


Lemma rlow_plus_lt_pr : forall a b : Rlow, forall q,
  val (a + b) q <->
  merely (exists r s, val a r /\ val b s /\ q < r + s).
Proof.
exact rlow_pred_plus_pr.
Qed.

(** Properties of the addition of lower reals *)

Lemma RlPlus_comm : Commutative RlPlus.
Proof.
intros a b;
apply RC_eq;
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

Lemma RlPlus_left_id : LeftIdentity RlPlus 0.
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
  apply RC_le with Qle s;trivial.
  intros ss sh; apply (antisymmetry le).
  apply le_or_lt. 
  set (S:=s) at 2;rewrite <-(plus_0_l S).
  apply (order_preserving (+ _)). apply lt_le;trivial.
- apply pred_plus_pr.
  apply rounded in E;revert E;
  apply (Trunc_ind _);
  intros [s [E1 E2]].
  apply tr;exists (q - s),s;repeat split.
  + apply (snd semi_decidable).
    apply flip_neg_minus in E1. trivial.
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
  change (IsTop ((val (QRlow q) + val (QRlow r)) s)).
  apply pred_plus_pr.
  apply tr.
  exists (q - (q + r - s) / 2), (r - (q + r - s) / 2).
  repeat split.
  + apply (snd semi_decidable).
    apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;[|solve_propholds].
    red. apply flip_pos_minus in E.
    trivial.
  + apply (snd semi_decidable).
    apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;[|solve_propholds].
    red.
    apply flip_pos_minus in E.
    trivial.
  + set (QRS := q + r - s).
    path_via (q + r - QRS * (2 / 2));
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

Lemma RlJoin_isRlow : forall a b : Rlow,
  IsRlow (fun q => semi_decide (hor (val a q) (val b q))).
Proof.
intros a b;split.
+ generalize (inhab Q Qlt a);apply (Trunc_ind _);intros [q E].
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
exists (fun q => semi_decide (hor (val a q) (val b q))). 
apply RlJoin_isRlow. 
Defined.   

Arguments RlJoin _ _ /.


Lemma RlMeet_isRlow : forall a b : Rlow,
  IsRlow (fun q => semi_decide (meet (val a q) (val b q))).
Proof.
intros a b;split.
+ generalize (inhab Q Qlt a);apply (Trunc_ind _);intros [qa Ea].
  generalize (inhab Q Qlt b);apply (Trunc_ind _);intros [qb Eb].
  apply tr. SearchAbout Q.
  destruct (Qle_total qa qb).
  - exists qa. unfold semi_decide, semi_decide_sier.
    apply top_le_meet. split.
    * trivial.
    * apply RC_le with Qle qb; try trivial.
      intros x y; apply (antisymmetry le).
      intros x y; apply le_or_lt.
  - exists qb. unfold semi_decide, semi_decide_sier.
    apply top_le_meet. split.
    * apply RC_le with Qle qa; try trivial.
      intros x y; apply (antisymmetry le).
      intros x y; apply le_or_lt.
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
    * exists q1. unfold semi_decide, semi_decide_sier.
      split; trivial. apply top_le_meet.
      split. 
      -- trivial.
      -- apply RC_le with Qle q2; try trivial.
         intros x y; apply (antisymmetry le).
         intros x y; apply le_or_lt.
    * exists q2. unfold semi_decide, semi_decide_sier.
      split; trivial. apply top_le_meet.
      split. 
      -- apply RC_le with Qle q1; try trivial.
         intros x y; apply (antisymmetry le).
         intros x y; apply le_or_lt.
      -- trivial.
   - apply (Trunc_ind _).
     intros (r,(Hr1,Hr2)).
     unfold semi_decide, semi_decide_sier in *.
     apply top_le_meet.     
     apply top_le_meet in Hr2.
     destruct Hr2 as (Hr21,Hr22).
     split.     
     -- apply RC_le with Qle r.
        intros x y; apply (antisymmetry le).
        intros x y; apply le_or_lt.
        trivial.
        apply lt_le; trivial.
     -- apply RC_le with Qle r.
        intros x y; apply (antisymmetry le).
        intros x y; apply le_or_lt.
        trivial.
        apply lt_le; trivial.
Qed.

Global Instance RlMeet : Meet Rlow. 
Proof. 
intros a b. 
exists (fun q => semi_decide (meet (val a q) (val b q))). 
apply RlMeet_isRlow. 
Defined.   

Arguments RlMeet _ _ /.


Lemma Rlle_Q_preserving : OrderPreserving (cast Q Rlow).
Proof.
intros y q Hh.
red; unfold Rlle, RCLe_l, cast, QRlow in *. 
intros t Hty. 
simpl in *.
unfold semi_decide in *. 
destruct (decide (t < y)). 
destruct (decide (t < q)). 
trivial. 
assert (Hf : t < q). 
apply lt_le_trans with y; try trivial.
case (n Hf). 
destruct (decide (t < q)). 
apply top_greatest. 
trivial.
Qed.


Lemma RlPlus_le_preserving : forall a : Rlow, OrderPreserving (a +).
Proof.
intros a b c E q E1.
apply Rlplus_eq_pr in E1.
revert E1.
apply (Trunc_ind _).
intros [r [s [E1 [E2 E3]]]].
apply (Rlplus_eq_pr a c).
apply tr.
exists r,s.
split;trivial.
split; trivial.
apply E.
trivial.
Qed.


Lemma NatEnum : Enumerable nat. 
exists (fun n => n).
apply _.
Qed.

Global Instance SDseq_Rlow (S : nat -> Rlow) (q : Q) (H : Funext) :
                                 SemiDecide (exists n, (val (S n) q)). 
Proof.
apply (@semi_decide_exists H nat NatEnum (fun n => val (S n) q)).
intros n.   
unfold SemiDecide.
specialize (S n).
red in S.  
refine ((val S) q).
Defined.

Definition Rllub (f : nat -> Rlow)  : Rlow. 
exists (fun q => semi_decide (exists n, (val (f n) q))). 
+ split. 
  - unfold semi_decide in *.
    unfold SDseq_Rlow in *.
    unfold semi_decide_exists in *.
    unfold semi_decide in *.
    assert (Hn : forall n, merely (exists qn, val (f n) qn)). 
    intros n.
    destruct (f n). 
    destruct elt_RC0. simpl. trivial.
    specialize (Hn 0). revert Hn; apply (Trunc_ind _). 
    intros (q,Hn). 
    assert (Ho : merely (exists n:nat, val (f n) q)).
    apply tr; exists 0; trivial. 
    generalize ((@top_le_enumerable_sup _ _ _ NatEnum) (fun n => val (f n) q)).
    intros HG. 
    apply HG in Ho.             
    apply tr. exists q. 
    trivial.
 - intros q. 
   split; intros H'.    
   * apply tr. 
     unfold semi_decide, SDseq_Rlow in *. 
     unfold semi_decide_exists in *.
     unfold semi_decide in *. 
     assert (Hnn : forall n, val (f n) q -> merely (exists r, Qlt q r 
                                                      ∧  val (f n) r)).
     intros n. 
     destruct (f n). 
     destruct elt_RC0. 
     simpl. intros Hh. 
     apply is_rounded0 in Hh. trivial.
     
     specialize (Hnn 0). 
     (*revert Hnn; apply (Trunc_ind _). 
     intros (q,Hn). 
     assert (Ho : merely (exists n:nat, val (f n) q)).
     apply tr; exists 0; trivial. 
     generalize ((@top_le_enumerable_sup _ _ _ NatEnum) (fun n => val (f n) q)).
     intros HG. 
     apply HG in Ho.             
     apply tr. exists q. 
     trivial.*)
     admit. 
   * unfold semi_decide in *. 
     unfold SDseq_Rlow in *. 
     unfold semi_decide_exists in *. 
     revert H'; apply (Trunc_ind _).      
     intros (rr,(H',H'')). 
     assert (Qle q rr).         
     admit. 
Admitted.

Lemma Rllub_case 
  : forall (fr : nat -> Rlow) n p, val (fr n) p -> val (Rllub fr) p.
Proof.
Admitted. 

Lemma Rllub_lub : forall (fr : nat -> Rlow) n, Rlle (fr n) (Rllub fr).
Proof.
Admitted.


Lemma Rllub_le 
  : forall (fr : nat -> Rlow) r, (forall n, Rlle (fr n)  r) -> Rlle (Rllub fr) r.
Admitted. 

Lemma Rllub_mon : forall (fr fk : nat -> Rlow), (forall n, Rlle (fr n) (fk n))
                                                -> Rlle (Rllub fr) (Rllub fk).
Admitted. 


Record RlowPos := mkRlP {
      rl :> Rlow;
      rlpos : forall p : Q, (p < 0) -> val rl p
}.

Lemma RlowPos_pos : forall (r : RlowPos), Rlle (' 0) r.
Proof. 
intros r; unfold Rlle.
intros p Hp.
simpl in Hp.
unfold semi_decide in Hp. 
destruct (decide (p < 0)). 
destruct r. simpl. 
apply rlpos0; trivial.
case (not_bot Hp). 
Qed. 

Lemma RlP_eq : forall a b : RlowPos, (forall q, val (rl a) q
                                    <-> val (rl b) q) -> a = b.
Proof.
intros a b E; apply RC_eq in E; auto.
destruct a; destruct b; simpl; auto.
simpl in *; destruct E; apply ap; apply path_ishprop.
Qed.

Definition toRL : RlowPos -> Rlow.
intros (p,Hpos). refine p; apply p.
Defined.

Global Instance Rllepos : Le RlowPos.
Proof.
intros x y. 
refine (Rlle (rl x) (rl y)). 
Defined.

Global Instance Rlltpos : Lt RlowPos. 
Proof. 
intros x y. 
refine (Rllt (rl x) (rl y)).   
Defined. 


Lemma RCP_eq0 : forall a b : RlowPos, val (rl a) = val (rl b) -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E. destruct E.
Admitted. 

Global Instance RCP_isset :  IsHSet RlowPos. 
Admitted. 

Lemma RCP_eq : forall a b : RlowPos,
    (forall q, val (rl a) q <-> val (rl b) q) -> a = b.
Proof.
intros a b E; apply RCP_eq0; apply path_forall;intros q;apply (antisymmetry le);
apply imply_le;apply E.
Qed.

Global Instance Rllepos_order@{} : PartialOrder Rllepos.
Proof.
split.
+ apply RCP_isset. 
+ apply _. 
+ split.
  - red; intros; apply Rlle_order.     
  - red. intros x y z. apply Rlle_order. 
+ red. intros x y Hx Hy.
  apply RCP_eq.  
  intros q. 
  split; intros Hab.
  * apply Hx; trivial. 
  * apply Hy; trivial. 
Qed. 

Definition toRlseq : (nat -> RlowPos) -> (nat -> Rlow). 
Proof.
intros L n.
specialize (L n).
refine (rl L).
Defined.

Lemma toRlseq_mon (A : hSet) (l m : nat -> RlowPos) :
  forall n, Rlle (l n) (m n) -> Rlle ((toRlseq l) n)
                                     ((toRlseq m) n). 
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

Definition RllubPos (fr : nat -> RlowPos) : RlowPos.
exists (Rllub (toRlseq fr)).
intros p Hp.  
assert (H2 : val (rl (fr 0%nat)) p).
apply rlpos. trivial.
apply Rllub_case with O.
apply H2.
Defined.

Lemma RllubPos_case 
  : forall (fr : nat -> RlowPos) n p, val (rl (fr n)) p -> val (rl (RllubPos fr)) p.
Proof.
intros fr.
apply Rllub_case.
Qed.

Lemma RllubPos_lub : forall (fr : nat -> RlowPos) n, Rlle (fr n) (RllubPos fr).
Proof.
intros fr.
apply Rllub_lub.
Qed.

Lemma RllubPos_le 
  : forall (fr : nat -> RlowPos) r, (forall n, Rlle (fr n)  r) -> Rlle (RllubPos fr) r.
intros fr.
apply Rllub_le.
Qed. 

Lemma RllubPos_mon : forall (fr fk : nat -> RlowPos),
    (forall n, Rlle (fr n) (fk n)) -> Rlle (RllubPos fr) (RllubPos fk).
Proof.
intros fr fk. apply Rllub_mon. 
Qed.
 
Definition Rlow_RlowPos (r : Rlow) : (Rlle (' 0)  r)-> RlowPos.
  exists r. unfold Rlle in X.
  intros p Hp.
  specialize (X p).
  apply X; trivial.
  unfold QRlow. 
  simpl. 
  unfold semi_decide.   
  destruct (decide (p < 0)). 
  apply top_greatest.
  case (n Hp). 
Defined.

Lemma O_simpl : Rlle (' 0) (' 0).
Proof. reflexivity. Qed. 

(** *** [0] for RlowPos *)
Definition RlP_0 : RlowPos.
refine ((@Rlow_RlowPos (' 0)) O_simpl).
Defined.

Lemma Rlle_O_I : Rlle (' 0) (' 1).
apply (Rlle_Q_preserving).
apply le_0_1.
Qed. 

Definition RlP_1 : RlowPos. 
apply ((@Rlow_RlowPos (' 1)) Rlle_O_I).
Defined.

Global Instance  RlP_plus : Plus RlowPos.
Proof. 
intros r s.
assert (Hpo : Rlle (' 0) (RlPlus r s)).
transitivity ((RlPlus (' 0) (' 0))). 
rewrite (RlPlus_left_id). 
reflexivity.
transitivity ((RlPlus r (' 0))). 
rewrite (RlPlus_comm r (' 0)). 
apply (RlPlus_le_preserving ('0)). 
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
apply RCP_eq;
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
  apply RC_le with Qle s;trivial.
  intros ss sh; apply (antisymmetry le).
  apply le_or_lt. 
  set (S:=s) at 2;rewrite <-(plus_0_l S).
  apply (order_preserving (+ _)). apply lt_le;trivial.
- apply pred_plus_pr.
  apply rounded in E;revert E;
  apply (Trunc_ind _);
  intros [s [E1 E2]].
  apply tr;exists (q - s),s;repeat split.
  + apply (snd semi_decidable).
    apply flip_neg_minus in E1. trivial.
  + trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Global Instance RlPApart : Apart@{UQ UQ} RlowPos
  := fun a b => a < b \/ b < a.
Arguments RlPApart _ _ /.

Lemma Rllepos_plus_le_preserving : forall a : RlowPos, OrderPreserving (a +).
Proof.
intros a b c Hh q Hh'. apply Rlplus_eq_pr in Hh'.
revert Hh';apply (Trunc_ind _);
intros [p [t [H1 [H2 H3]]]].
apply (Rlplus_eq_pr a c).
apply tr;exists p,t;repeat split;trivial.
apply Hh; trivial.
Qed.

Definition pred_minusQ_l (r : QPred) (q : Q) : (r q) -> QPred.
Proof.
intros Hqq. 
assert (fm : (Q -> Q)).    
intros x. 
refine (x - q).
refine (fun m => r (fm m)). 
Defined.  
Check Rlow. 

Lemma minusQ_l_isRlow : forall (a : Rlow) (p : Q) (H : val a p),
            IsRlow (pred_minusQ_l (val a) p H).
Proof.
intros a p;split.
+ apply tr. unfold pred_minusQ_l.  
  
  exists (p+p).
  assert (Hpp : p + p - p = p).    
  admit. 

  rewrite Hpp; trivial.  
+ split.
  - intros Hq. apply tr. 
    unfold pred_minusQ_l in *.
    admit. 
Admitted.   

Global Definition Rl_minus_q (r : Rlow) (q : Q) : (val r q) -> Rlow.  
Proof.
intros He. 
exists (pred_minusQ_l (val r) q He). 
apply minusQ_l_isRlow. 
Defined.   

Global Definition RlP_minus_q (r : RlowPos) (q : Q+) : (val (rl r) (pos q))
                                                       -> RlowPos.  
Proof.
intros He.
assert (Hpo : Rlle (' 0) (Rl_minus_q (rl r) (pos q) He)).
unfold Rl_minus_q. unfold pred_minusQ_l. 
intros v Hv. 
simpl.
admit. 

refine ((@Rlow_RlowPos (Rl_minus_q r (pos q) He) Hpo)).
Admitted.

Definition Rlow_mult_q : Q -> RlowPos -> RlowPos. 
Admitted.  

Lemma Rlow_mult_q1 : forall r, Rlow_mult_q 1 r = r. 
Admitted. 

Lemma Rlow_mult_q_RlP_0 : forall q, Rlow_mult_q q RlP_0 = RlP_0.
Admitted. 


End LowerReals. 
