(** General type for reals : lower, upper... see Vickers **)
(* I've just changed some definitions, there is some proofs 
to fix *)

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
Require Import Qaxioms. 

Local Set Universe Minimization ToSet.

(** General definitions and properties 
---> general space, general relation 
with suitable properties **)

Section GeneralIlq.

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
Hypothesis gen_le_or_lt : forall x y : A, Rle x y ∨ Rlt y x. 
Section isGen.

Variable elt : APred.
  
Class IsGen : Type :=
  {
    is_inhab : merely (exists q, elt q);
    is_rounded : forall q, iff@{Set UQ UQ} (elt q)
           (merely (exists r, Rlt q r /\ elt r))
  }.

End isGen.  

Record Gen :=  {
      elt : APred;
      elt_Gen : IsGen elt
}.

Global Existing Instance elt_Gen.

Definition inhab (c : Gen) := is_inhab (elt c).
Definition rounded (c : Gen) := is_rounded (elt c). 

Definition IsGen_conjunction r : IsGen r -> _
  := fun c => (is_inhab r, is_rounded r). 

Global Instance isGen_conj_isequiv {r}
  : IsEquiv (IsGen_conjunction r).
Proof.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- intros E;split; apply E. 
- red;simpl. intros. reflexivity.
- red;simpl. reflexivity.
- simpl. reflexivity.
Defined.

Lemma gen_le : forall a q r, elt a r -> Rle q r -> elt a q. 
Proof.
intros a q r E1 E2.
destruct (gen_le_or_lt r q) as [E3|E3].
- destruct (antisymmetry Rle _ _ E2 E3). trivial.
- apply rounded. apply tr. exists r; auto.
Qed. 

Section contents.
Context `{Funext} `{Univalence}.

Global Instance GR_hprop@{} : forall r, IsHProp (IsGen r).
Proof.
intros. apply (@trunc_equiv _ _ ((IsGen_conjunction r)^-1) _ _ _).
Qed.

Lemma gen_eq0 : forall a b : Gen, elt a = elt b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E; destruct E; apply ap.
apply path_ishprop. 
Qed. 

Instance gen_isset@{} : IsHSet Gen.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => elt a = elt b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply gen_eq0;apply E.
Qed.

Lemma gen_eq : forall a b : Gen, (forall q, elt a q <-> elt b q) -> a = b.
Proof.
intros a b E; apply gen_eq0; apply path_forall;intros q;apply (antisymmetry le);
apply imply_le;apply E.
Qed.

Lemma gen_orders : forall (c : Gen) (q r : A), elt c q -> ~ elt c r -> Rlt q r.
Proof.
intros c q r E1 E2.
destruct (gen_le_or_lt r q) as [E|E];trivial.
assert (Hh : elt c r). 
apply gen_le with q; trivial. 
case (E2 Hh).
Qed.  

(* Large order *)
Global Instance GenLe_l : Le@{UQ UQ} Gen
  := fun a b => forall q, elt a q -> elt b q.

Arguments GenLe_l _ _ /.

Instance GenLe_l_partial_order@{} : PartialOrder GenLe_l.
Proof.
repeat split.
- apply _.
- apply _.
- intros a q;trivial.
- intros a b c E1 E2 q E3. auto.
- intros a b E1 E2. apply gen_eq.
  intros;split;(apply E1 || apply E2).
Qed.

(* Strict order *)
Global Instance GenLt_l : Lt@{UQ UQ} Gen :=
  fun a b => merely (exists q, elt b q /\ ~ elt a q).

Arguments GenLt_l _ _ /.
(*Arguments GenLt_r _ _ /.*)

Global Instance GenApart : Apart@{UQ UQ} Gen
  := fun a b => a < b \/ b < a.

Instance GenLt_strict_order@{} : StrictOrder GenLt_l.
Proof.
repeat split.
- apply _.
- intros a;hnf;apply (Trunc_ind _);intros [q [E1 E2]].
  case (E2 E1). 
- intros a b c E E';revert E; apply (Trunc_ind _);intros [q [E1 E2]];
  revert E';apply (Trunc_ind _);intros [r [E3 E4]].
  apply tr;exists q. split. 
  + apply gen_le with r;  trivial.
    assert (H' : Rlt q r). apply gen_orders with b; trivial.
    destruct (Hdt q r); trivial. 
    apply FR in r0. case (r0 H'). 
  + trivial.
Qed.

Notation "a <= b" := (GenLe_l a b). 
(*Notation "a >= b" := (GenLe_r a b).*) 

Lemma gen_stable : forall r p q, elt r p -> (p=q) -> elt r q.
intros r p q Hp He.
apply gen_le with p; trivial.
rewrite He.
reflexivity.
Save.

Lemma gen_mon : forall (x y : Gen) (p q :A),
    (Rle q p) -> x <= y -> elt x p -> elt y q.
intros x y p q Hpq Hxy Hx.
apply gen_le with p; try assumption. auto. 
Save.

End contents. 

End GeneralIlq.

(** A = Q --> general defs for both lower and upper reals **)
Section GeneralRelQ. 

Definition QPred := APred Q. 

Variable Qle_g : relation Q.
Variable Qlt_g : relation Q.
Hypothesis Hdec : DecidablePaths Q.
Hypothesis Hda : AntiSymmetric Qle_g.
Hypothesis Hdt : TotalRelation Qle_g.
Hypothesis FR : FullPseudoOrder Qle_g Qlt_g. 
  
Section GeneralDefQ. 

Variable elt : QPred. 

Definition IsGenQ := IsGen Q Qlt_g elt. 

End GeneralDefQ. 

Record GenQ :=  {
      eltQ : QPred;
      elt_GenQ : IsGenQ eltQ
}. 

Global Instance  GenLt_semi_dec : forall r q, SemiDecide (Qlt_g r q). 
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

Section LowerReals_def.

Variable elt : QPred. 
Definition IsRlow := IsGenQ Qlt elt.
  
End LowerReals_def. 

Context `{Funext} `{Univalence}.

Definition Rlow := Gen Q Qlt. 
Definition val := elt Q Qlt.

Lemma QIsRlow : forall q : Q, IsRlow (fun r => semi_decide (r < q)).
Proof.
intros q; split.
+ apply tr; exists (q - 1). apply (snd semi_decidable).
  apply flip_lt_minus_l. apply pos_plus_lt_compat_r;solve_propholds.
+ intros p;split.
  - intros E;apply semi_decidable in E.
    apply tr;econstructor;split;[|apply (snd semi_decidable)];
    apply Q_average_between;trivial.
  - apply (Trunc_ind _);intros [s [E1 E2]];
    apply (snd semi_decidable);apply semi_decidable in E2.
    transitivity s;trivial.
Qed. 

(* Orders *)
Global Instance Rlle : Le Rlow. 
Proof.
refine (GenLe_l Q Qlt). 
Defined. 

Instance Rlle_order@{} : PartialOrder Rlle.
Proof.
apply GenLe_l_partial_order; trivial.
Defined. 

Global Instance Rllt : Lt Rlow.
Proof.
refine (GenLt_l Q Qlt). 
Defined.

Lemma FPO_Qle_Qlt : FullPseudoOrder Qle Qlt. 
Proof.
split; try apply _. 
split; try apply _. 
auto with qarith. 
auto with qarith. 
Qed. 

Global Instance RlApart : Apart@{UQ UQ} Rlow
  := fun a b => a < b \/ b < a.
Arguments RlApart _ _ /.

Instance Rllt_strict_order@{} : StrictOrder Rllt.
Proof.
repeat split.
- apply _.
- intros a;hnf;apply (Trunc_ind _);intros [q [E1 E2]].
  case (E2 E1).
- intros a b c E E';revert E; apply (Trunc_ind _);intros [q [E1 E2]];
  revert E';apply (Trunc_ind _);intros [r [E3 E4]].
  apply tr;exists q. split.
  + apply gen_le with Qle r. red; auto with qarith.
    apply le_or_lt. trivial.
    assert (H3 : Qlt q r). 
    apply gen_orders with Qle b; try trivial.
    red; auto with qarith.
    apply le_or_lt. 
    apply FPO_Qle_Qlt. 
    auto with qarith. 
  + trivial.
Qed.

(* Operations on Rlow *)
Global Instance QRlow : Cast Q Rlow. 
Proof.
intros q. 
exists (fun r => semi_decide (r < q)).
apply QIsRlow.
Defined. 

Arguments QRlow _ /.

Global Instance Rl0 : Zero Rlow := QRlow 0.
Arguments Rl0 /.

Global Instance Rl1 : One Rlow := QRlow 1.
Arguments Rl1 /.

Definition pred_plus_l : Plus QPred.
Proof.
intros x y q.
exact (semi_decide@{UQ} (merely (exists r : Q, merely (exists s : Q,
  x r /\ y s /\ q = r + s)))).
Defined.

Arguments pred_plus_l _ _ / _.
Existing Instance pred_plus_l.

Lemma pred_plus_pr'_l : forall a b : QPred,
  forall q, (a + b) q <-> merely (exists r s, a r /\ b s /\ q = r + s).
Proof.
unfold plus,pred_plus_l at 1. intros a b q;split.
- intros E. apply semi_decidable in E.
  revert E;apply (Trunc_ind _);intros [r E];
  revert E;apply (Trunc_ind _);intros [s E].
  apply tr;eauto.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply (snd semi_decidable),tr. exists r. apply tr. exists s;auto.
Qed.

Definition pred_plus_pr_l@{} := pred_plus_pr'_l@{UQ UQ UQ UQ}.

Lemma rlow_pred_plus_pr : forall a b : Rlow, forall q,
  (val a + val b) q <->
  merely (exists r s, val a r /\ val b s /\ q < r + s).
Proof.
intros a b q;split.
- intros E;apply pred_plus_pr in E;revert E;apply (Trunc_ind _);
  intros [r [s [E1 [E2 E3]]]].
  apply rounded in E1. revert E1;apply (Trunc_ind _);intros [r' [Er E1]].
  apply tr;exists r',s;repeat split;trivial.
  rewrite E3. apply (strictly_order_preserving (+ _)). trivial.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply pred_plus_pr.
  apply tr;exists r, (s - (r + s - q));repeat split.
  + trivial.
  + apply gen_le with Qle s;trivial.
    red; auto with qarith. apply le_or_lt. 
    apply lt_le ;red.
    apply flip_lt_minus_l. apply pos_plus_lt_compat_r.
    apply flip_lt_minus_l. Locate plus_0_l. rewrite involutive, plus_0_l. trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma plus_isRlow : forall a b : Rlow, IsRlow (val a + val b).
Proof.
intros a b;split.
- generalize (inhab Q Qlt a).
  apply (Trunc_ind _);intros [r Er].
  generalize (inhab Q Qlt b).
  apply (Trunc_ind _);intros [s Es].
  apply tr;exists (r+s). apply pred_plus_pr_l.
  apply tr;exists r,s;auto.
- intros q;split.
  + intros E. apply pred_plus_pr_l in E.
    revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
    apply (rounded Q Qlt a) in E1.
    apply (rounded Q Qlt b) in E2.
    revert E1;apply (Trunc_ind _);intros [r' [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [s' [E2 E2']].
    apply tr;exists (r' + s'). split.
    * rewrite E3. apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  + apply (Trunc_ind _);intros [q' [E1 E2]].
    apply pred_plus_pr in E2. revert E2.
    apply (Trunc_ind _);intros [r' [s' [E2 [E3 E4]]]].
    assert (Hq : q = (r' - (q' - q)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hq. apply pred_plus_pr_l.
    apply tr;econstructor;econstructor;split;[|split;[|reflexivity]];trivial.
    apply gen_le with Qle r';trivial.
    red; auto with qarith. apply le_or_lt. 
    apply flip_le_minus_l. apply nonneg_plus_le_compat_r.
    apply (snd (flip_nonneg_minus _ _)). apply lt_le;trivial.
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


Lemma lower_plus_lt_pr : forall a b : Rlow, forall q,
  val (a + b) q <->
  merely (exists r s, val a r /\ val b s /\ q < r + s).
Proof.
exact rlow_pred_plus_pr.
Qed.

Lemma RlPlus_comm : Commutative RlPlus.
Proof.
intros a b;apply gen_eq; auto; simpl;intros q;split;intros E;
apply pred_plus_pr in E;apply pred_plus_pr;
revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]];
apply tr;exists s,r;repeat split;trivial;
rewrite E3;apply commutativity.
Qed.

Lemma RlPlus_assoc : Associative RlPlus.
Proof.
intros a b c; apply (antisymmetry Rlle);red;simpl;intros q E; simpl in *;
apply pred_plus_pr_l in E;revert E;apply (Trunc_ind _); 
[intros [r [s [E1 [E2 E3]]]] | intros [r [s [E2 [E1 E3]]]]];
apply pred_plus_pr in E2;revert E2;apply (Trunc_ind _);
intros [l [u [E2 [E4 E5]]]];rewrite E3,E5;
[rewrite plus_assoc | rewrite <-plus_assoc];
(apply pred_plus_pr;apply tr;do 2 econstructor;split;[|split;[|reflexivity]]);
trivial;apply pred_plus_pr;apply tr;eauto.
Qed.

Lemma RlPlus_left_id : LeftIdentity RlPlus 0.
Proof.
intros a;apply (antisymmetry le);red;simpl;intros q E; simpl in *. 
- apply pred_plus_pr in E;revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply semi_decidable in E1. rewrite E3. apply gen_le with Qle s;trivial.
  red; auto with qarith. apply le_or_lt. 
  set (S:=s) at 2;rewrite <-(plus_0_l S);unfold S;clear S.
  apply (order_preserving (+ _)). apply lt_le;trivial.
- apply pred_plus_pr.
  apply rounded in E;revert E;apply (Trunc_ind _);intros [s [E1 E2]].
  apply tr;exists (q - s),s;repeat split.
  + apply (snd semi_decidable). apply flip_neg_minus in E1. trivial.
  + trivial.
  + abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.


Lemma RlPlus_rat : forall q r : Q, QRlow (q + r) = QRlow q + QRlow r :> Rlow.
Proof.
intros;apply (antisymmetry le).
- intros s E. change (IsTop (semi_decide (s < q + r))) in E.
  apply (fst semi_decidable) in E.
  change (IsTop ((val (QRlow q) + val (QRlow r)) s)). apply pred_plus_pr.
  apply tr. exists (q - (q + r - s) / 2), (r - (q + r - s) / 2).
  repeat split.
  + apply (snd semi_decidable). apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;[|solve_propholds].
    red. apply flip_pos_minus in E. trivial.
  + apply (snd semi_decidable). apply flip_lt_minus_l.
    apply pos_plus_lt_compat_r.
    apply pos_mult_compat;[|solve_propholds].
    red. apply flip_pos_minus in E. trivial.
  + set (QRS := q + r - s).
    path_via (q + r - QRS * (2 / 2));
    [|abstract ring_tac.ring_with_integers (NatPair.Z nat)].
    rewrite dec_recip_inverse;[|apply lt_ne_flip;solve_propholds].
    rewrite mult_1_r;unfold QRS;clear QRS.
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
- intros s E. simpl. apply (snd semi_decidable).
  simpl in E. apply pred_plus_pr in E.
  revert E;apply (Trunc_ind _);intros [r' [s' [E1 [E2 E3]]]].
  apply semi_decidable in E1;apply semi_decidable in E2.
  rewrite E3. apply plus_lt_compat;trivial.
Qed.

Lemma Rllt_Q_preserving : StrictlyOrderPreserving (cast Q Rlow).
Proof.
intros q r E. apply tr.
exists ((q + r) / 2). 
split. 
apply (snd semi_decidable);  apply Q_average_between; auto. 
intros K. 
apply (snd semi_decidable) in K. 
unfold semi_decide, semi_decide_sier in K. 
simpl in K. 
unfold semi_decide in K. 
destruct (decide ((q + r) / 2 < q)). 
assert (Hj : q < (q + r) / 2). 
apply Q_average_between; auto.
assert (Hf2 : ~ ((q + r) / 2 < q)).
auto with qarith. case (Hf2 l). 
apply not_bot in K; case K. 
Qed.

Lemma Rllt_Q_reflecting : StrictlyOrderReflecting (cast Q Rlow).
Proof.
intros q r;apply (Trunc_ind _);intros [s [E1 E2]].
apply (@semi_decidable (_ < _) _ _) in E1.
simpl in E2. 
unfold semi_decide in E2. 
destruct (decide (s < q)). 
case (E2 (top_greatest SierTop)). 
destruct (le_or_lt q r).
destruct (Qdec q r). 
rewrite p in n. 
case (n E1). 
auto with qarith. 
auto with qarith. 
Qed.

Global Instance Rllt_Q_embedding : StrictOrderEmbedding (cast Q Rlow).
Proof.
split.
- apply Rllt_Q_preserving.
- apply Rllt_Q_reflecting.
Qed.

(* definition has just changed, to fix *)
Lemma Rlow_archimedean : forall a b : Rlow, Rllt a b ->
  merely (exists q : Q,  a < QRlow q < b).
Proof.
intros a b;apply (Trunc_ind _);intros [q [E1 E2]].
apply rounded in E1;revert E1;apply (Trunc_ind _);intros [qa [Ea1 Ea2]].
apply tr;exists qa.
split;apply tr;exists q;split;trivial.
unfold QRlow. 
simpl.
unfold semi_decide. 
destruct (decide (q < qa)). 
apply top_greatest. 
case (n Ea1). 
apply gen_le with Qle qa. 
red; auto with qarith. apply le_or_lt. 
trivial.
apply FPO_Qle_Qlt. 
auto with qarith.
intros HF.
apply E2. 
Admitted. 

Lemma RlJoin_isRlow : forall a b : Rlow,
  IsRlow (fun q => semi_decide (hor (val a q) (val b q))).
Proof.
intros a b;split.
+ generalize (inhab Q Qlt a);apply (Trunc_ind _);intros [q E].
  apply tr;exists q;apply top_le_join,tr,inl,E.
+ intros q;split.
  - intros E;apply top_le_join in E;revert E;apply (Trunc_ind _);intros [E|E];
    apply rounded in E;revert E;apply (Trunc_ind _);intros [r [E1 E2]];
    apply tr;exists r;split;trivial;apply top_le_join,tr;auto.
  - apply (Trunc_ind _);intros [r [E1 E2]];apply top_le_join in E2;revert E2.
    apply (Trunc_ind _);intros [E2|E2];
    apply top_le_join,tr;[left|right];apply rounded,tr;
    eauto.
Qed.

Global Instance RlJoin : Join Rlow. 
Proof. 
intros a b. 
exists (fun q => semi_decide (hor (val a q) (val b q))). 
apply RlJoin_isRlow. 
Defined.   

Arguments RlJoin _ _ /.


Lemma rlow_not_lt_le_flip : forall a b : Rlow, ~ a < b -> b <= a.
Proof.
intros a b E q E1.
apply rounded in E1;revert E1;apply (Trunc_ind _);intros [r [E1 E2]].
apply gen_mon with Qle b r. 
red; auto with qarith. apply le_or_lt. 
apply FPO_Qle_Qlt.
intros HF. apply E.
Admitted. 

Lemma Rllt_cotrans : CoTransitive (@lt Rlow Rllt).
Proof.
intros a b E c;revert E;apply (Trunc_ind _). intros [q [E1 E2]].
(*apply (rounded Q Qlt) in E2;revert E2;apply (Trunc_ind _);intros [s [Es E2]].*)
apply rounded in E1;revert E1;apply (Trunc_ind _);intros [r [Er E1]].
(*generalize (cut_located c _ _ (transitivity Er Es)).*)
unfold hor. 
Admitted. 

Instance Rlow_isapart@{} : IsApart Rlow.
Proof.
split.
- apply _.
- unfold apart;simpl;intros a b;apply Sum.ishprop_sum;try apply _.
  intros E1 E2;apply (lt_antisym a b);split;trivial.
- intros a b [E|E];[right|left];trivial.
- intros a b [E|E] c;generalize (Rllt_cotrans _ _ E c);apply (Trunc_ind _);
  intros [E1|E1];apply tr;unfold apart;simpl;
  unfold GenApart; auto. 
- intros a b;split.
  + intros E. apply (antisymmetry le);apply rlow_not_lt_le_flip;intros E1;
    apply E;unfold apart;simpl;unfold GenApart;auto.
  + intros E;destruct E;intros [E|E];revert E;apply (irreflexivity lt).
Qed.

Global Instance Rlow_fullpseudoorder@{} : FullPseudoOrder Rlle Rllt.
Proof.
repeat (split;try (revert x; fail 1);try apply _).
- apply lt_antisym.
- apply Rllt_cotrans.
- intros a b;split; trivial.
- intros a b;split.
  + intros E1;red;apply (Trunc_ind _);intros [q [E2 E3]].
    apply E3. apply gen_mon with Qle a q.
    red; auto with qarith. apply le_or_lt. 
    reflexivity. auto. trivial. 
  + apply rlow_not_lt_le_flip.
Qed.

Lemma Rlle_rat_preserving : OrderPreserving (cast Q Rlow).
Proof.
apply full_pseudo_order_preserving.
Qed.

Lemma Rlle_rat_reflecting : OrderReflecting (cast Q Rlow).
Proof.
apply full_pseudo_order_reflecting.
Qed.

Instance Rlle_rat_embedding : OrderEmbedding (cast Q Rlow).
Proof.
split.
- apply Rlle_rat_preserving.
- apply Rlle_rat_reflecting.
Qed.

Lemma rlow_plus_le_preserving : forall a : Rlow, OrderPreserving (a +).
Proof.
intros a b c E q E1. apply Rlplus_eq_pr in E1.
revert E1;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
apply (Rlplus_eq_pr a c). apply tr;exists r,s;repeat split;trivial.
apply E. trivial.
Qed.

Lemma rlow_plus_le_reflecting : forall a : Rlow, OrderReflecting (a +).
Proof.
  intros a b c E.
  (*
apply (rlow_plus_le_preserving (- a)) in E.
unfold plus in E.
rewrite !CutPlus_assoc,(CutPlus_left_inverse a),!CutPlus_left_id in E.
trivial.
Qed.*)
Admitted. 
  
Instance rlow_plus_le_embedding@{} : forall a : Rlow, OrderEmbedding (a +).
Proof.
intros;split.
- apply rlow_plus_le_preserving.
- apply rlow_plus_le_reflecting.
Qed.

Definition Rllub (f : nat -> Rlow)  : Rlow. 
intros S.
exists (fun q => semi_decide (exists n, (elt (S n) q))).  
+ intros x y H H0.
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
                 ((@EnumerableSup _ _ NatEnum) (λ x0 : nat, (S x0) y))). 
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
+ intros x Hx.
  apply ch. 
  trivial. 
Defined.

Lemma Rllub_case 
  : forall (fr : nat -> Rlow) n p, val (fr n) p -> val (Rllub fr) p.
Proof.
intros fr n p H.
red.
unfold Rllub.
simpl.
unfold semi_decide. 
unfold SDseq_Rlow. 
unfold semi_decide_exists.
revert H. 
apply SierLe_imply.
transitivity (semi_decide ((fr n) p)). 
unfold semi_decide, semi_decide_sier; reflexivity.
generalize (enumerable_sup_ub'). 
intro HGEn. 
specialize (HGEn nat NatEnum (λ x : nat, semi_decide ((fr x) p)) n). 
simpl in HGEn; trivial.
Defined. 

Lemma Rllub_lub : forall (fr : nat -> Rlow) n, Rlle (fr n) (Rllub fr).
Proof.
exact Rllub_case.
Save.


Lemma Rllub_le 
  : forall (fr : nat -> Rlow) r, (forall n, Rlle (fr n)  r) -> Rlle (Rllub fr) r.
intros fr r Hr.     
red. 
unfold Rllub. 
simpl. 
unfold semi_decide. 
unfold SDseq_Rlow. 
unfold semi_decide_exists.
intros p H. 
Admitted.

Lemma Rllub_mon : forall (fr fk : nat -> Rlow), (forall n, Rlle (fr n) (fk n))
-> Rlle (Rllub fr) (Rllub fk). Admitted. 
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
      rl :> Rlow;
      rlpos : forall p : Q, (p < 0) -> val rl p
}.

Lemma RlowPos_pos : forall (r : RlowPos), Rlle (' 0) r.
Proof. 
intros r. unfold Rlle.
intros p Hp.
simpl in Hp.
unfold semi_decide in Hp. 
destruct (decide (p < 0)). 
destruct r. 
simpl. 
apply rlpos0; trivial.
case (not_bot Hp). 
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

Lemma IHS_RLP:  IsHSet RlowPos. 
Admitted. 

Instance Rllepos_order@{} : PartialOrder Rllepos.
Proof.
split.
+ apply IHS_RLP. 
+ apply _. 
+ split.
  - red; intros; apply Rlle_order.     
  - red. intros x y z. apply Rlle_order. 
+ red. intros x y Hx Hy.
  admit. 
Admitted. 


Definition toRlseq : (nat -> RlowPos) -> (nat -> Rlow). 
Proof.
intros L n.
specialize (L n).
refine (rl L).
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
apply (Rlle_rat_preserving).
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
apply (rlow_plus_le_preserving ('0)). 
apply (RlowPos_pos r).
apply (rlow_plus_le_preserving r) . 
apply (RlowPos_pos s).
refine ((@Rlow_RlowPos (RlPlus r s)) Hpo).
Defined.


Lemma RlPPlus_comm : Commutative RlP_plus.
Proof.
red; intros x y.
apply Rllepos_order.  
red.
unfold Rllepos.
unfold RlP_plus.
simpl.
Admitted. 

Lemma RlPPlus_assoc : Associative RlP_plus.
Proof.
Admitted. 

Lemma RlPPlus_left_id : LeftIdentity RlP_plus RlP_0.
Proof.
Admitted. 

Lemma rlowp_not_lt_le_flip : forall a b : RlowPos, ~ a < b -> b <= a.
Proof.
intros a b E q E1.
apply rounded in E1;revert E1;apply (Trunc_ind _);intros [r [E1 E2]].
Admitted. 

Lemma Rlltpos_cotrans : CoTransitive (@lt RlowPos Rlltpos).
Proof.
intros a b E c;revert E;apply (Trunc_ind _). intros [q [E1 E2]].
(*apply (rounded Q Qlt) in E2;revert E2;apply (Trunc_ind _);intros [s [Es E2]].*)
apply rounded in E1;revert E1;apply (Trunc_ind _);intros [r [Er E1]].
(*generalize (cut_located c _ _ (transitivity Er Es)).*)
unfold hor. 
Admitted. 

Global Instance RlPApart : Apart@{UQ UQ} RlowPos
  := fun a b => a < b \/ b < a.
Arguments RlPApart _ _ /.


Instance RlowPos_isapart@{} : IsApart RlowPos.
Proof.
split.
Admitted. 

Global Instance RlowPos_fullpseudoorder@{} : FullPseudoOrder Rllepos Rlltpos.
Proof.
Admitted. 

Lemma rlowp_plus_le_preserving : forall a : RlowPos, OrderPreserving (a +).
Proof.
intros a b c E q E1. apply Rlplus_eq_pr in E1.
revert E1;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
apply (Rlplus_eq_pr a c). apply tr;exists r,s;repeat split;trivial.
apply E. trivial.
Qed. 

  
Instance rlowp_plus_le_embedding@{} : forall a : RlowPos, OrderEmbedding (a +).
Proof.
intros;split.
- apply rlowp_plus_le_preserving.
- apply rlowp_plus_le_reflecting.
Qed.

End LowerReals. 
