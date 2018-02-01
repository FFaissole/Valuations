

Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               sierpinsky
               HoTT.Classes.theory.rationals
               partiality
               dedekind
               HoTT.Classes.orders.orders
               HoTT.Classes.interfaces.integers
               HoTT.Classes.interfaces.naturals
               HoTT.Classes.implementations.natpair_integers
               HoTT.Classes.theory.integers
               HoTT.Classes.implementations.assume_rationals.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod HIT.Truncations HIT.unique_choice. 


(** * Dominance *)

(** Definition of dominance *)
Definition dominance (Σ : Type0) (is_top : Σ -> Type) := 
           forall (u:hProp) (s:Σ),
             (is_top s -> hexists (fun z:Σ => is_top z = u)) -> 
             hexists (fun m:Σ => merely (is_top m) 
                               = merely (u /\ (is_top s))).

Print LoadPath.

(** Sier is a dominance*)
Lemma dominance_sier : dominance Sier IsTop.
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
       hexists (fun m : Sier => merely m = 
                  merely (p /\ IsTop (f n)))).
  intros n.
  specialize (Hn n).
  assert (H : IsTop (f n) -> 
              hexists (fun z: Sier => IsTop z = p)).
  intros Hn'.   
  assert (Ht : IsTop (sup Unit f)).
  apply top_le_sup; apply tr; 
  exists n; trivial.
  specialize (Hf Ht); trivial.
  apply (Hn H). 
  generalize (unique_choice (fun n => 
        (fun m:Sier => merely m = merely (p /\ IsTop (f n))))).
  intros Huc.
  assert (Hp : (forall (x : nat) (y : Sier), 
     IsHProp (merely y = merely (p /\ IsTop (f x))))).
  apply _.
  specialize (Huc Hp).
  assert (Hu : (forall x : nat, hunique (fun m : Sier => merely m = 
                        merely (p /\ IsTop (f x))))).
  intros n; split; try trivial.
  intros s1 s2 Hs1 Hs2.
  apply (antisymmetry le). 
  - apply imply_le; intros H1.
    assert (He1 : merely s1 <-> s1).
    split. apply (Trunc_ind _); trivial.
    intros I; apply tr; trivial.
    assert (He2 : merely s2 <-> s2).
    split. apply (Trunc_ind _); trivial.
    intros I; apply tr; trivial.
    apply He2; apply He1 in H1.
    rewrite Hs2. 
    rewrite Hs1 in H1; trivial.
  - apply imply_le; intros H2.
    assert (He1 : merely s1 <-> s1).
    split. apply (Trunc_ind _); trivial.
    intros I; apply tr; trivial.
    assert (He2 : merely s2 <-> s2).
    split. apply (Trunc_ind _); trivial.
    intros I; apply tr; trivial.
    apply He1; apply He2 in H2.
    rewrite Hs1. 
    rewrite Hs2 in H2; trivial.
  - specialize (Huc Hu).
    destruct Huc as (ff,Hff).
    assert (NatEnum : Enumerable nat).
    exists (fun n => n); apply _.
    pose (supf := EnumerableSup nat (fun n => ff n)).
    apply tr; exists supf.
    apply path_trunctype.
    apply equiv_iff_hprop. 
    assert (Hff_eq : forall n : nat, merely (ff n) <-> 
                              merely (p /\ IsTop (f n))).
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
    assert (Hff_eq : forall n : nat, merely (ff n) <-> 
                              merely (p /\ IsTop (f n))).
    intros n; rewrite Hff.
    split; trivial. clear Hp Hu.
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
