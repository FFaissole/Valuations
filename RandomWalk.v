
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.interfaces.rationals
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.premetric
               HoTT.Classes.theory.rings
               HoTT.Classes.orders.semirings
               HoTT.Classes.orders.rings
               HoTT.Classes.theory.dec_fields
               HoTT.Classes.implementations.assume_rationals
               HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Import HoTTClasses.sierpinsky partiality dedekind.

Require Export Rlow Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Giry Cpo
               Interp Flip Random.


              
Set Implicit Arguments.

Definition Fiter  : (nat -> IntPos nat) -> (nat -> IntPos nat)
    := (fun f x => Iif flip (f (S x)) (unit nat x)).

Lemma Fiter_mon : forall a b, Le_fun_IntPos a b -> 
                              Le_fun_IntPos (Fiter a) (Fiter b).
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
revert E1; apply Rlow_mon.
reflexivity.
intros p Hp.
simpl in *.
unfold pred_multQ in *.
revert Hp; apply Rlow_mon.
reflexivity.
apply Hab.
Defined.

Definition iterflip : nat -> IntPos nat := 
                            Ifix Fiter Fiter_mon.

