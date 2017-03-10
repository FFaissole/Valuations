Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.theory.rationals
               HoTTClasses.implementations.dedekind
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom.

Require Export RoundedClosed Opens Valuations.

Section Unit_int.

Record Unit_interval := mk01{ 
      r01 :> Cut ;
      H0 : CutZero <= r01 ;
      H1 : r01 <= CutOne
}.

Global Instance IsHSet_Unit_interval : IsHSet Unit_interval.
Proof.
Admitted. 

Definition U01 : hSet.
Proof.
exists Unit_interval.
apply IsHSet_Unit_interval.
Defined.

End Unit_int.

Section Open_rats. 

Definition op_rat (p q : Q) : OS U01. 
Proof.
intros x.
Admitted. 

Definition m01 : OS U01 -> RlowPos.
Admitted.

Lemma val_op_rat : forall p q, rl (m01 (op_rat p q)) 
                                 = QRlow (p - q).
Admitted.  


Axiom WSO : forall (U : OS U01) x, U x -> exists p q, ((op_rat p q) x) /\
                                    (forall y, ((op_rat p q) y) -> U y).

Definition compact (U : OS U01) := (forall x, U x -> exists p q, 
               (op_rat p q) x /\ (forall y, ((op_rat p q) y) -> U y))
             -> 
               (exists N:nat, exists W:nat -> Q*Q, 
                forall x, U x -> exists n, n <= N /\
                                (op_rat (fst (W n)) (snd (W n)) x) /\
                (forall y, (op_rat (fst (W n)) (snd (W n)) y) -> U y)).

Axiom U01_compact : compact Ω.

Lemma U01_finite_cover : exists N:nat, exists W:nat -> Q*Q, 
                forall x : U01, exists n, n <= N /\
                      (op_rat (fst (W n)) (snd (W n)) x).
Proof.
generalize (U01_compact (WSO Ω)).
intros (N,(W,H)).
exists N, W.
intros x; specialize (H x (top_greatest (Ω x))).
destruct H as (n,(H1,(H2,H3))).
exists n.
split; trivial.  
Qed.
       


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

Theorem V01_U01_1 : mu _ V01 Ω = RlP_1.                               
Proof. 
Admitted.

End Open_rats.
