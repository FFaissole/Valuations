
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

Require Export RoundedClosed Opens Valuations.

Section Unit_int.

Definition btw01 (c : Cut) := CutZero <= c /\ c <= CutOne.

Record Unit_interval := mk01{ 
      r01 :> Cut ;
      between01 : btw01 r01
}.

Global Instance btw01_hprop@{} {A :hSet} : 
             forall (r : Cut), IsHProp (btw01 r).
Proof.
intros.
apply _.
Qed.

Lemma btw01_eq0 : forall a b : Unit_interval, 
            r01 a = r01 b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 

Instance Unit_interval_isset@{} : IsHSet (Unit_interval).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => r01 a = r01 b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply btw01_eq0;apply E.
Qed.

Definition U01 : hSet.
Proof.
exists Unit_interval.
apply Unit_interval_isset.
Defined.

End Unit_int.


Definition open_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p < x /\ x < QCut q.

Definition closed_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p <= x /\ x <= QCut q.

Notation "] p ; q [" := (open_interval p q) (at level 50).
Notation "[ p ; q ]" := (closed_interval p q) (at level 50).


Definition covers_open_int : forall U: OS (U01), exists W : nat -> Q*Q, 
                             (forall n, snd (W n) <= snd (W (S n))) /\
                             (forall x, U x -> exists n, 
                                            ] fst (W n) ; snd (W n) [ x). 

Definition fc_open_int (U: OS (U01)) := 
                      exists (W : nat -> Q*Q) (N : nat), 
                             (forall n, snd (W n) <= snd (W (S n))) /\
                             (forall x, U x -> exists n, n<=N /\ 
                                             ] fst (W n) ; snd (W n) [ x). 

Fixpoint sum_lengths (W : nat -> Q*Q) (N : nat) := match N with 
    | O => snd (W O) - fst (W O)
    | S n => sum_lengths W n + snd (W N) - fst (W N)
end.


Definition fc_sum_length (U : OS (U01)) : fc_open_int U -> Q.
Proof.
intros (W,(N,(H1,H2))).
refine (sum_lengths W N).
Defined. 

Definition is_closed_rat (U : OS (U01)) p q := 
                              forall z, U z <-> [ p ; q ] z. 

Theorem sum_length_gt_diff : forall (U : OS (U01)) (HU : fc_open_int U) p q, 
                is_closed_rat U p q -> q - p < (fc_sum_length U HU).
Proof.
intros U HU.
destruct HU as (W,(N,(C1,C2))).
induction N.
+ intros p q Hpq. 
  unfold fc_sum_length; simpl.
  unfold is_closed_rat in Hpq.
  assert (C2' : forall x:U01, U x -> 
           (] fst (W 0) ; snd (W 0) [) x).
  intros x Hux; simpl; specialize (C2 x Hux).
  destruct C2 as (m,(C21,C22)).
  assert (H0 : m = 0).
  induction m.
  reflexivity.
  apply le_iff_not_lt_flip in C21.
  case (C21 (peano_naturals.S_gt_0 m)).
  rewrite H0 in C22; trivial.
  clear C1 C2.
  assert (H1 : ∀ x : U01, ([p; q]) x -> 
                          (] fst (W 0); snd (W 0) [) x).
  intros x Hx; apply Hpq in Hx; 
  apply C2'; trivial.
  unfold open_interval, closed_interval in H1.
  admit.

+ intros p q Hpq.
  assert (C2N : ∀ x : U01, U x → ∃ n : nat, n ≤ N ∧ 
                       (] fst (W n); snd (W n) [) x).
  admit.
 
  specialize (IHN C2N p (fst (W (S N)))).
  assert (C3 :  is_closed_rat U p (fst (W (S N)))).
  admit.
 
  specialize (IHN C3). 
  unfold fc_sum_length in *; simpl;
  clear C3 C2 C2N.
  transitivity ((fst (W (S N)) - p) + 
       (snd (W (S N)) - fst (W (S N)))).
  assert (H : fst (W (S N)) - p + 
              (snd (W (S N)) - fst (W (S N))) = 
              snd (W (S N)) - p).
  admit. 

  rewrite H. clear H.
  assert (H : q < snd (W (S N))).
  admit. admit.

  rewrite rings.plus_comm.
  rewrite <- (rings.plus_assoc (sum_lengths W N)).
  rewrite (rings.plus_comm (sum_lengths W N) 
               (snd (W (S N)) - fst (W (S N)))).
  apply semirings.plus_le_lt_compat.
  reflexivity. 
  trivial.
Admitted. 
              

Definition os_open_int (p q : Q) : OS U01 := 
              fun x => (semi_decide ((open_interval p q) x)).

Notation "] p ; q [" := (os_open_int p q) (at level 50).

Axiom WSO : forall (U : OS U01) x, U x -> exists p q, ] p ; q [ x /\
                                                     (] p ; q [ ⊆ U).

Axiom WSO_strong : forall (U : OS U01), exists (W : nat -> Q*Q), forall x, 
                  (U x -> exists n, (] fst (W n) ; snd (W n) [ x)) /\
                               (forall k, ] fst (W k) ; snd (W k) [ ⊆ U).


Fixpoint W_sum (A B : nat -> Q) (n : nat) : Rlow := match n with 
   | O => match (Qle_total (A 0) (B 0)) with 
               | left _ => QRlow (B 0 - A 0)
               | right _ => 0
          end
   | S p  => W_sum A B p + QRlow (B n - (Qjoin (A n) (B p)))
end.

Lemma W_sum_pos : forall A B n, Rl0 <= W_sum A B n.
Admitted. 

Definition m01 : OS U01 -> RlowPos.
Proof.
intros U; generalize (WSO_strong U); intros (W,H).
pose (A := fun n => fst (W n)).
pose (B := fun n => snd (W n)).  
exists (Rllub (fun n => W_sum A B n)).
intros p Hp.
assert (h0 : val Rl0 p).
unfold Rl0; simpl; unfold semi_decide; 
destruct (decide (p < 0)).
apply top_greatest.
case (n Hp). 
revert h0; apply RC_mon with Qle. 
intros a b; apply (antisymmetry le). 
intros a b; apply orders.le_or_lt. 
reflexivity.
intros k Hk; 
apply Rllub_lub with 0; 
apply W_sum_pos; trivial.
Defined. 

Lemma m01_rat : forall p q, rl (m01 (] p ; q [)) = QRlow (q - p).
Proof.
intros p q; unfold m01; simpl. 
assert (AntiSymmetric Rlle).
admit.

apply (antisymmetry Rlle).
+ apply Rllub_le.
  intros n z Hnq.
  simpl in Hnq.
Admitted.

Lemma m01_mon : forall U V, U ⊆ V -> m01 U <= m01 V. 
Proof.
intros U V HUV q Hq.
unfold m01 in *.
simpl in *; unfold semi_decide, SDseq_Rlow, 
semi_decide_exists in *.
unfold semi_decide in *.
destruct (WSO_strong U) as (WU,HU). 
destruct (WSO_strong V) as (WV,HV).
assert (H' : ∀ x : U01, U x -> (∃ n : nat, 
             (] fst (WV n); snd (WV n) [) x) ∧
             (forall k, ] fst (WV k); snd (WV k) [ ⊆ V)).
intros x Hx. split; apply HV.
revert Hx; apply SierLe_imply. 
apply HUV; trivial. trivial. 
apply top_le_enumerable_sup in Hq; 
apply top_le_enumerable_sup.
revert Hq; apply (Trunc_ind _); 
intros (m,Hq); apply tr.
unfold semi_decide in *; simpl in *.
Admitted.

Lemma m01_def : m01 ∅ = RlP_0.
Proof.
apply (antisymmetry le).
+ intros s Hs.
  simpl; unfold semi_decide;
  destruct (decide (s < 0)).
  apply top_greatest.
  unfold m01 in Hs.
  simpl in Hs.
  unfold semi_decide, SDseq_Rlow, 
         semi_decide_exists, 
         semi_decide in *.
  apply top_le_enumerable_sup in Hs. 
  revert Hs; apply (Trunc_ind _). 
  intros (m,Hm).
  assert (H0 : (W_sum
          (λ n : nat,
           fst ((let (proj1_sig, _) 
             := WSO_strong ∅ in proj1_sig) n))
          (λ n : nat,
           snd ((let (proj1_sig, _) 
             := WSO_strong ∅ in proj1_sig) n)) 
          m) = RlP_0).
  simpl; destruct (WSO_strong ∅) as (W,(HW,Hi)).
  specialize (Hi m).
  assert (Hj : ] fst (W m); snd (W m) [ = ∅).
  apply (antisymmetry le).
  intros r; apply Hi.
  intros r; apply imply_le; intros Hr.
  simpl in Hr; apply not_bot in Hr; 
  case Hr.
  induction m.
  - simpl.
    destruct (Qle_total (fst (W 0)) (snd (W 0))).
    assert (H2 : fst (W 0) = snd (W 0)).
    apply (antisymmetry le); trivial.
    apply le_iff_not_lt_flip.
    intros HF.
    assert (Hj2 : forall x,  ] fst (W 0); snd (W 0) [ x 
                           <-> Empty).
    intros x. rewrite Hj.
    split; intros F. 
    apply not_bot in F; case F. 
    case F. SearchAbout rationals.Q.
    assert (mean : U01).
    exists (QCut (fst (W 0) + snd (W 0)/2)).
    admit.

    apply (Hj2 mean).
    admit.

    rewrite H2.
    admit.
    reflexivity. 
  - simpl; rewrite IHm.
    destruct (WSO_strong ∅).
    simpl in *.
    destruct (Qle_total (fst (W (S m))) 
                        (snd (W m))).
     
     
    

 admit. admit.  
  - rewrite H0 in Hm. clear H0.
    simpl in Hm; unfold semi_decide in Hm; 
    destruct (decide (s < 0)); trivial.
    case (n l).
+ intros s Hs.
  destruct (m01 ∅).
  apply rlpos.
  simpl in Hs; unfold semi_decide in Hs; 
  destruct (decide (s < 0)); trivial.
  apply not_bot in Hs; case Hs.
Admitted. 
 
Lemma m01_mod : forall U V, m01 U + m01 V = m01 (U ∪ V) + m01 (U ⋂ V).
Proof. 
Admitted.

Lemma m01_prob :  m01 (fun x => SierTop) <= RlP_1.
Proof.
intros s Hs.
unfold m01 in Hs.
simpl in Hs.
unfold semi_decide, SDseq_Rlow, 
       semi_decide_exists, 
       semi_decide in Hs. 
simpl in Hs.
apply top_le_enumerable_sup in Hs.
revert Hs; apply (Trunc_ind _); 
intros (m,Hm).
induction m.
+ simpl in Hm.
  admit.
+ clear IHm.
  simpl in Hm.   apply IHm.
      


destruct (WSO_strong 
           (λ _ : U01, SierTop)) as (W,HW).
assert (H : ∀ x : U01, ∃ n : nat,
       (] fst (W n); snd (W n) [) x).
assert (Ht: IsTop SierTop).
apply top_greatest.
intros x; specialize (HW x Ht).
clear Ht.
destruct HW as (n,(Hn,_)).
exists n; trivial.
 


 
apply top_greatest.
specialize (   
(SierTop_is_top))).
 

 



Admitted.   

Definition V01 : Val U01.
Proof.
exists m01.
+ intros U V; apply (m01_mod U V).
+ apply m01_def.
+ intros U V; apply m01_mon.
+ apply m01_prob. 
Defined.  


Definition compact (U : OS U01) := forall (W : nat -> Q*Q),
             (forall x, U x -> exists n, ] fst (W n) ; snd (W n) [ x) 
             -> 
             (exists N, forall x, U x -> exists n, n <= N /\ 
                            ] fst (W n) ; snd (W n) [ x). 
                        
Axiom U01_compact : compact (fun x => SierTop).

Theorem V01_U01_1 : V01 (fun x => SierTop) = RlP_1.                               
Proof.
apply (antisymmetry le).
+ apply V01.
+ intros s Hs.
  unfold V01; simpl.
  unfold semi_decide, SDseq_Rlow, semi_decide_exists.
  unfold semi_decide; simpl.
  apply top_le_enumerable_sup.
  apply tr; simpl.
  generalize U01_compact; intros Hcp.
  unfold compact in Hcp.
  destruct (WSO_strong (fun x => SierTop)) as (W,H).
  specialize (Hcp W).
  assert (H' : ∀ x : U01, (IsTop SierTop) 
        -> ∃ n : nat, (] fst (W n); snd (W n) [) x).
  intros x Ht; specialize (H x Ht).
  destruct H as (m,(H,_)).
  exists m; apply H.
  specialize (Hcp H').
  clear H H'.   
  destruct Hcp as (N,HcN).
  exists N.
  
Admitted.
