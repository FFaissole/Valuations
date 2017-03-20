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
  

Section Open_rats. 

Axiom WSO : forall (U : OS U01) x, U x -> exists p q, ] p , q [ x 
                                                  /\ (] p , q [ ⊆ U).
                                                  
            (* let to define *)                                      
Definition m01 : OS U01 -> RlowPos.
Admitted.
Lemma val_op_rat : forall p q, rl (m01 (op_rat p q)) 
                                 = QRlow (p - q).
Admitted.  
Lemma m01_mon : forall U V, U <= V -> m01 U <= m01 V.
Admitted. 

Definition V01 : Val U01.
Proof.
exists m01.
+ admit. 
+ assert (H0 : forall p q, m01 ∅ <= m01 (op_rat p q)).  
  intros p q; apply m01_mon.
  intros s; apply imply_le; intros Hs; 
  apply not_bot in Hs; case Hs.
  specialize (H0 0 0).
  red in H0; unfold Rllepos, Rl_pos_Le in H0.
  rewrite val_op_rat in H0.
  assert (H1 : Rlle (QRlow (0 - 0)) RlP_0). 
  assert (Hz : (0 - 0) = Qzero).
  apply rings.plus_negate_r.
  rewrite Hz.
  intros s; trivial. 
  apply (antisymmetry le).
  - red; unfold Rl_pos_Le, Rlle, RCLe_l in *.  
    intros q Hq.
    apply H1, H0, Hq.
  - intros s Hs; simpl in Hs; 
    unfold semi_decide in Hs; apply rlpos.
    destruct (decide (s < 0)); try trivial.
    apply not_bot in Hs; case Hs.
+ red; apply m01_mon.
+ admit. 
Admitted.

Theorem V01_U01_1 : V01 Ω = RlP_1.                               
Proof. 
Admitted.

End Open_rats.
