
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
               HIT.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Giry Cpo
               Interp Flip Random.
              
Set Implicit Arguments.

Definition Fiter  : (nat -> IntPos nat) -> (nat -> IntPos nat)
    := (fun f x => Iif flip (f (S x)) (unit nat x)).

Lemma Fiter_mon : forall a b, a <= b -> Fiter a <= Fiter b.
Proof.
intros a b Hab.
unfold Fiter.
intros x u.
unfold Iif.
simpl.
intros q Hq.
apply pred_plus_pr in Hq.
apply pred_plus_pr.
revert Hq; apply (Trunc_ind _); 
intros (v,(w,(E1,(E2,E3)))).
apply tr; 
exists v, w.
repeat split; trivial.
revert E1; apply RC_mon with Qle.
intros s s'; apply (antisymmetry Qle).
intros s s'; apply orders.le_or_lt.
reflexivity.
intros p Hp.
simpl in *.
unfold pred_multQ in *.
revert Hp; apply RC_mon with Qle.
intros s s'; apply (antisymmetry Qle).
intros s s'; apply orders.le_or_lt.
reflexivity.
apply Hab.
Defined.

Definition iterflip : nat -> IntPos nat := 
                            Ifix Fiter Fiter_mon.

