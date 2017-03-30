

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.theory.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.dedekind
               HoTTClasses.orders.orders
               HoTTClasses.interfaces.integers
               HoTTClasses.interfaces.naturals
               HoTTClasses.implementations.natpair_integers
               HoTTClasses.theory.integers.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod HIT.Truncations.


Definition weak_dominance (D : Type0) (is_top : D -> Type) := 
           forall (u:hProp) (s:D),
             hexists (fun z:D => is_top s -> is_top z = u) -> 
             hexists (fun m:D => merely (is_top m) 
                               = merely (u /\ (is_top s))).

Definition dominance (D : Type0) (is_top : D -> Type) := 
           forall (u:hProp) (s:D),
             (is_top s -> hexists (fun z:D => is_top z = u)) -> 
             hexists (fun m:D => merely (is_top m) 
                               = merely (u /\ (is_top s))).

Definition dominance' (D : Type0) (is_top : D -> Type) := 
           forall (u:hProp) (s:D),
             (is_top s -> hexists (fun z:D => is_top z = u)) -> 
             (is_top s -> hexists (fun m:D => merely (is_top m) 
                               = merely (u /\ (is_top s)))).

Lemma weak_dominance_sier : weak_dominance Sier IsTop.
Proof.
intros p u.
revert u.
apply (partial_ind0 _ (fun a => _ -> _)).
+ intros t; destruct t. 
  apply Trunc_functor.
  intros (z,Hz).
  assert (Htrue : IsTop (eta Unit tt)).
  red; apply top_greatest.
  specialize (Hz Htrue).
  exists (meet (eta Unit tt) z).
  unfold meet; rewrite Hz.
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); intros H; apply tr.
  split; trivial.
  apply (Trunc_ind _); intros (H,_); 
  apply tr; trivial.
+ intros Hf; apply tr. 
  exists (bot Unit).
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); intros H; 
  apply not_bot in H; case H.
  apply (Trunc_ind _); intros (_,H); 
  apply tr; trivial.
+ intros f Hn Hf.
  revert Hf; apply (Trunc_ind _).
  intros (z,Hz); apply tr.
  exists (meet z (sup Unit f)).
  apply path_trunctype.
  apply equiv_iff_hprop; 
  apply Trunc_functor.
  intros H1. 
  apply top_le_meet in H1.
  destruct H1 as (H1,H1').
  specialize (Hz H1').
  split; trivial.
  rewrite <- Hz; trivial.
  intros (H1,H1').
  apply top_le_meet.
  split; trivial. 
  specialize (Hz H1').
  rewrite Hz; trivial.
Qed.

Definition Countable_choice := forall (A : Type) (R : nat -> A -> Type), 
                   (forall n, hexists (fun y => R n y)) -> 
                   (hexists (fun f : nat -> A => forall n, R n (f n))).  
               

Lemma dominance_sier (HCC : Countable_choice) 
                       : dominance Sier IsTop.
Proof.
intros p u.
revert u.
apply (partial_ind0 _ (fun a => _ -> _)).
+ intros t Ht; destruct t. 
  assert (Htrue : IsTop (eta Unit tt)).
  red; apply top_greatest.
  specialize (Ht Htrue).
  unfold hexists in *; 
  revert Ht; apply (Trunc_ind _). 
  intros (z,Hz). apply tr. 
  exists (meet (eta Unit tt) z).
  unfold meet; rewrite Hz.
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); intros H; apply tr.
  split; trivial.
  apply (Trunc_ind _); intros (H,_); 
  apply tr; trivial.
+ intros Hf; apply tr. 
  exists (bot Unit).
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); intros H; 
  apply not_bot in H; case H.
  apply (Trunc_ind _); intros (_,H); 
  apply tr; trivial.
+ intros f Hn Hf.
  assert (Hnn : forall n, 
       hexists (λ m : Sier, merely m = 
                  merely (p ∧ IsTop (f n)))).
  intros n.
  specialize (Hn n).
  assert (H : IsTop (f n) -> 
              hexists (λ z : Sier, IsTop z = p)).
  intros Hn'.   
  assert (Ht : IsTop (sup Unit f)).
  apply top_le_sup; apply tr; 
  exists n; trivial.
  specialize (Hf Ht); trivial.
  apply (Hn H). 
  apply HCC in Hnn.
  revert Hnn; apply Trunc_functor.
  intros (ff,Hff). SearchAbout Enumerable.
  assert (NatEnum : Enumerable nat).
  exists (fun n => n); apply _.
  pose (supf := EnumerableSup nat (fun n => ff n)).
  exists supf.
  apply path_trunctype.
  apply equiv_iff_hprop. 
  assert (Hff_eq : ∀ n : nat, merely (ff n) <-> 
                              merely (p ∧ IsTop (f n))).
  intros n; rewrite Hff.
  split; trivial.
  apply (Trunc_ind _); intros HK.
  apply top_le_enumerable_sup in HK.
  revert HK; apply (Trunc_ind _); intros (x,Hx).
  assert (Hx2 : merely (ff x)). 
  apply tr; trivial.
  apply Hff_eq in Hx2.
  revert Hx2; apply (Trunc_ind _); 
  intros (H,H'); apply tr.
  split; trivial.
  apply top_le_sup; apply tr; 
  exists x; trivial.
  assert (Hff_eq : ∀ n : nat, merely (ff n) <-> 
                              merely (p ∧ IsTop (f n))).
  intros n; rewrite Hff.
  split; trivial.
  apply (Trunc_ind _); intros (Hp,HK).
  apply top_le_sup in HK.
  revert HK; apply (Trunc_ind _); intros (x,Hx).
  assert (HU : merely (p /\ IsTop (f x))).
  apply tr; split; trivial.
  apply Hff_eq in HU.
  revert HU; apply (Trunc_ind _); intros HU. 
  apply tr; apply top_le_enumerable_sup.
  apply tr; exists x; trivial.    
Qed.

Lemma dominance_sier' : dominance' Sier IsTop.
Proof.
intros p u.
revert u.
apply (partial_ind0 _ (fun a => _ -> _ -> _)).
+ intros t Ht Ht'; destruct t.
  specialize (Ht Ht'). clear Ht'.  
  unfold hexists in *; 
  revert Ht; apply (Trunc_ind _). 
  intros (z,Hz). apply tr. 
  exists (meet (eta Unit tt) z).
  unfold meet; rewrite Hz.
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); intros H; apply tr.
  split; trivial.
  apply top_greatest.
  apply (Trunc_ind _); intros (H,_); 
  apply tr; trivial.
+ intros Hf Hf'; apply tr. 
  exists (bot Unit).
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); intros H; 
  apply not_bot in H; case H.
  apply (Trunc_ind _); intros (_,H); 
  apply tr; trivial.
+ intros f Hn Hf Hc.
  assert (Hnn : forall n, IsTop (f n) ->
       hexists (λ m : Sier, merely m = 
                  merely (p ∧ IsTop (f n)))).
  intros n.
  specialize (Hn n).
  assert (H : IsTop (f n) -> 
              hexists (λ z : Sier, IsTop z = p)).
  intros Hn'.
  apply Hf; trivial.
  apply Hn; trivial.
  specialize (Hf Hc). clear Hc.
  revert Hf; apply (Trunc_ind _).
  intros (z,Hz); apply tr.  
  exists (meet z (sup Unit f)).
  apply path_trunctype.
  apply equiv_iff_hprop.
  apply (Trunc_ind _); 
  intros HH; apply tr.
  apply top_le_meet in HH.
  destruct HH as (A,B).
  split; trivial.
  rewrite <- Hz; trivial.
  apply (Trunc_ind _); 
  intros (A,B); apply tr.
  apply top_le_meet.
  split; trivial.
  rewrite Hz; trivial.
Qed.  
