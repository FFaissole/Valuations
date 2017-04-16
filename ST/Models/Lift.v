
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

Definition extend : partial A -> Sier.
Proof.
apply (partial_rec A _ le).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
+ intros _. exact SierTop. 
+ exact SierBot. 
+ intros f Hn.
  generalize (Build_IncreasingSequence f Hn).
  intros ff.
  refine (sup Unit ff). 
+ reflexivity.
+ intros x.
  apply imply_le; intros b.
  apply not_bot in b.
  case b. 
+ intros s Hp x Hi n.
  simpl in Hi.
  transitivity (sup Unit (Build_IncreasingSequence s Hp)).
  apply imply_le; intros H.
  apply top_le_sup.
  apply tr; exists n.
  apply H. trivial.
+ intros s Hi x Hn.
  simpl; apply imply_le.
  intros H.
  apply top_le_sup in H.
  revert H.
  apply (Trunc_ind _); intros (m,Hm).
  revert Hm; apply SierLe_imply.
  apply Hn. 
Defined.

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




(*
Record IsEquiv (A B : Type) (f : A → B) : Type := BuildIsEquiv
  { equiv_inv : B → A;
    eisretr : Sect equiv_inv f;
    eissect : Sect f equiv_inv;
    eisadj : ∀ x : A, eisretr (f x) = ap f (eissect x) }*)


Definition map_lift_inv_aux (s : Sier) : 
             forall (f : IsTop s → A), 
                     hunique (fun y => extend y = s /\ 
                       map_lift y = s ↾ f).
Proof.
revert s; apply (partial_ind0 _ (fun a => forall b, _)).
+ intros t Ht.
  split.
  - apply tr.
    assert (H : IsTop (eta Unit t)).
    destruct t; apply top_greatest.
    exists (eta A (Ht H)).
    repeat split.
    * unfold extend.
      transitivity SierTop.
      reflexivity.
      destruct t; reflexivity.
    * unfold map_lift.
     
Admitted.

Definition map_lift_inv : {s : Sier | IsTop s ->  A} -> partial A.
Proof.
intros (s,f).
generalize (unique_choice  (fun _:nat => fun y:partial A => extend y = s /\ 
                       map_lift y =  s  ↾ f)).
intros Huc.
assert (H1 : (nat
       → ∀ y : partial A,
         IsHProp (extend y = s ∧ map_lift y =
                      s  ↾ f))).
intros _ t.
apply _.
assert (H2 : (nat
         → hunique
             (λ y : partial A, extend y = s 
              ∧ map_lift y = s  ↾ f))).
intros _.
apply map_lift_inv_aux.
specialize (Huc H1 H2).
clear H1 H2.
destruct Huc as (F,HF).
refine (F 0).
Defined.

Lemma eta_great : forall x, IsTop (eta Unit x).
Proof.
intros [].
apply top_greatest.
Qed. 

Lemma map_lift_eta : forall b, map_lift 
    (eta A (b (eta_great tt))) = eta Unit tt ↾ b.
Proof.
intros b.
unfold map_lift.
assert (p : extend (eta A (b (eta_great tt))) = 
           eta Unit tt).
unfold extend; reflexivity.
apply path_sigma with p.
apply path_forall.
intros x.
simpl.
Admitted.


Lemma map_lift_bot : forall b, map_lift (bot A) = (bot Unit) ↾ b.
Proof.
intros b.
unfold map_lift.
assert (p : extend (bot A) = bot Unit).
unfold extend; reflexivity.
apply path_sigma with p.
simpl.
apply path_forall.
intros x.
case (not_bot x).
Qed.


Lemma map_lift_inv_eta : forall x f, map_lift_inv 
                      ((eta Unit x) ↾ f) = 
                      eta A (f (eta_great x)).
Proof.
Admitted.

Lemma map_lift_inv_bot : forall f, map_lift_inv 
                        (SierBot ↾ f) = bot A.
Proof.
Admitted.  

Lemma Sect1 : Sect map_lift_inv map_lift.
Proof.
unfold Sect.
intros (s,Hs).
revert s Hs.
apply (partial_ind0 _ (fun a => forall b, _)).
+ intros t b.
  rewrite map_lift_inv_eta.
  destruct t.
  apply map_lift_eta.
+ intros b.
  rewrite map_lift_inv_bot.
  rewrite map_lift_bot with b.
  reflexivity.
+ admit.  
Admitted.

Lemma Sect2 : Sect map_lift map_lift_inv.
Proof.
unfold Sect.
apply (partial_ind0 _ (fun a =>  _)).
+ intros a.
  rewrite map_lift_inv_eta.
  simpl.
  apply eta_is_greatest.
  apply _. 
  admit.
+ rewrite map_lift_inv_bot.
  reflexivity.
+ admit.  
Admitted.
 
Lemma equiv_map_dom : IsEquiv map_lift.
Proof.
split with map_lift_inv Sect1 Sect2.
intros s.
Admitted.

End lift.
