
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.theory.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.dedekind
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod.

Require Export RoundedClosed Opens Valuations LowerIntegrals.


Lemma dominance_sier' : forall (u : hProp) (s : Sier), 
            merely (exists z, IsTop s -> IsTop z = u) -> 
            merely (exists m:Sier, merely (IsTop m) 
                                 = merely (u /\ (IsTop s))).
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

Lemma dominance_sier : forall (u : hProp) (s : Sier), 
            (IsTop s -> merely (exists z:Sier, IsTop z = u)) -> 
            merely (exists m:Sier, merely (IsTop m) 
                                 = merely (u /\ (IsTop s))).
Proof.
intros p u Hpu.
revert Hpu.
revert u. 
apply (partial_ind0 _ (fun v => _ -> _)).
+ intros t Ht; destruct t.
  assert (Htrue : IsTop (eta Unit tt)).
  red; apply top_greatest.
  specialize (Ht Htrue).
  revert Ht; apply (Trunc_ind _).
  intros (z,Hz); apply tr. 
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
  assert (Hnn :forall n, IsTop (f n)
          -> merely (∃ z : Sier, IsTop z = p)).
  intros n Hfn.
  assert (H : IsTop (sup Unit f)).
  apply top_le_sup; apply tr. 
  exists n; trivial.
  specialize (Hf H); trivial.    
  assert (Hn2 : forall n, 
     merely (∃ m : Sier, merely m = merely (p ∧ IsTop (f n)))).
  intros m; apply Hn. apply Hnn.
  apply tr.
  revert Hf. 
  generalize (sup Unit f). 
Admitted. 
