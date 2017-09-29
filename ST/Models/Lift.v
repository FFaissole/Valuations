
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.interfaces.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric
               HoTTClasses.theory.rings
               HoTTClasses.orders.semirings
               HoTTClasses.orders.rings
               HoTTClasses.theory.dec_fields.

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient HIT.unique_choice.

Section lift.

Definition umap : A -> Unit := fun x => tt.

Definition extend : partial A -> Sier := partial_map umap.

Lemma equiv_istop_umap : forall y, IsTop (extend y) -> 
                       hexists (fun w => eta A w = y).
Proof.
apply (partial_ind0 _ (fun a => _ -> _)).
+ intros s Hs.
  apply tr; exists s.
  reflexivity.
+ intros Hk.
  apply not_bot in Hk.
  case Hk.
+ intros f Hf Hn.
  assert (Hnn : hexists (fun n => extend (f n))).
  apply top_le_sup in Hn.
  trivial.
  revert Hnn; apply (Trunc_ind _); 
  intros (m,Hm).
  apply Hf in Hm.
  revert Hm; apply (Trunc_ind _).
  intros (w,Hw).
  apply tr.
  exists w.
  SearchAbout eta.
  symmetry.
  apply eta_is_greatest.
  apply _.
  rewrite Hw.
  apply sup_is_ub.
Qed.
 
Definition map_lift : partial A -> {s : Sier | IsTop s ->  A}.
Proof.  
intros y.
exists (extend y).
intros H.
generalize (equiv_istop_umap y H).
intros Hg.
unfold extend in H.
assert (exists w:A, eta A w = y).
generalize (unique_choice (fun n:Unit => 
     (fun w:A => eta A w = y))).
intros HH. 
unfold hexists.
assert (H1 :(Unit → ∀ y0 : A, IsHProp (eta A y0 = y))).
intros X z.
apply _.
assert (H2 : (Unit → hunique (λ w : A, eta A w = y))).
intros z.
split.
apply Hg.
unfold atmost1P.
intros a b Ha Hb.
rewrite <- Hb in Ha.
apply eta_le_eta.
apply _.
rewrite Ha; reflexivity.
specialize (HH H1 H2).
destruct HH as (f,Hff).
exists (f tt).
apply Hff.
destruct X as (w,HX).
refine w.
Defined.

Lemma map_lift_proj1 : forall y, (map_lift y).1 = extend y.
Proof.
intros y; simpl; reflexivity.
Qed.

Lemma equiv_istop_umap : forall y, IsTop (extend y) -> 
                       hexists (fun w => eta A w = y).
Proof.
apply (partial_ind0 _ (fun a => _ -> _)).
+ intros s Hs.
  apply tr; exists s.
  reflexivity.
+ intros Hk.
  apply not_bot in Hk.
  case Hk.
+ intros f Hf Hn.
  assert (Hnn : hexists (fun n => extend (f n))).
  apply top_le_sup in Hn.
  trivial.
  revert Hnn; apply (Trunc_ind _); 
  intros (m,Hm).
  apply Hf in Hm.
  revert Hm; apply (Trunc_ind _).
  intros (w,Hw).
  apply tr.
  exists w.
  SearchAbout eta.
  symmetry.
  apply eta_is_greatest.
  apply _.
  rewrite Hw.
  apply sup_is_ub.
Qed.
 
Definition map_lift : partial A -> {s : Sier | IsTop s ->  A}.
Proof.  
intros y.
exists (extend y).
intros H.
generalize (equiv_istop_umap y H).
intros Hg.
assert (exists w:A, eta A w = y).
generalize (unique_choice (fun n:Unit => 
     (fun w:A => eta A w = y))).
intros HH. 
unfold hexists.
assert (H1 :(Unit → ∀ y0 : A, IsHProp (eta A y0 = y))).
intros X z.
apply _.
assert (H2 : (Unit → hunique (λ w : A, eta A w = y))).
intros z.
split.
apply Hg.
unfold atmost1P.
intros a b Ha Hb.
rewrite <- Hb in Ha.
apply eta_le_eta.
apply _.
rewrite Ha; reflexivity.
specialize (HH H1 H2).
destruct HH as (f,Hff).
exists (f tt).
apply Hff.
destruct X as (w,HX).
refine w.
Defined. 

End lift.
