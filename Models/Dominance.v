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
               Types.Prod HIT.Truncations.

Definition dominance (D : Type0) (is_top : D -> Type) := 
           forall (u:hProp) (s:D),
             hexists (fun z:D => is_top s -> is_top z = u) -> 
             hexists (fun m:D => merely (is_top m) 
                               = merely (u /\ (is_top s))).

Lemma dominance_sier : dominance Sier IsTop.
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
