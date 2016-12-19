


Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric
               HoTTClasses.orders.orders.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient. 

Require Import RoundedClosed
               Functions
               Valuations. 
               
Set Implicit Arguments. 

Section OpenFun. 
Context `{Funext} `{Univalence}. 

(* Map from Sier to RlowPos *)
Definition OpenFun_aux : forall s : Sier, RlowPos.
Proof.
apply (partial_rec Unit _ le).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
+ intros _. exact RlP_1. 
+ exact RlP_0. 
+ intros f Hn. 
  exact (RllubPos f).
+ reflexivity.
+ intros x.
  apply RlowPos_pos. 
+ intros s Hp x Hi n.
  transitivity ((λ (f0 : nat → RlowPos)
       (_ : ∀ n : nat, f0 n ≤ f0 (S n)), 
       RllubPos f0) s Hp).
  simpl.
  apply RllubPos_lub. 
  trivial.
+ intros s Hi x Hn q Hh.
  assert (Hx : (val (rl (RllubPos s)) q)).
  trivial.
  assert (H2 : RllubPos s <= x).
  apply RllubPos_le. trivial.
  apply RC_mon with Qle (Rllub s) q. 
  intros ss sh; apply (antisymmetry le). apply orders.le_or_lt.
  reflexivity. trivial. trivial.
Defined.

(* Monotonicity of the map from Sier to RlowPos *)
Lemma OpenFun_aux_mon : forall s1 s2, s1 <= s2
                        -> OpenFun_aux s1 <= OpenFun_aux s2.
Proof.
apply (partialLe_ind0 _ _).
+ reflexivity.
+ assert (X : OpenFun_aux (bot Unit) = RlP_0).
  auto. rewrite X.
  intros. apply RlowPos_pos.
+ intros f x H1 H2 n.
  transitivity (OpenFun_aux (sup Unit f)).
  assert (Hr : OpenFun_aux (sup Unit f) = RllubPos
                        (fun n => OpenFun_aux (f n))).
  auto. rewrite Hr.
  apply (Rllub_lub (fun n => OpenFun_aux (f n))); trivial.
  trivial.
+ intros f x H1 H2.
  assert (Hr : OpenFun_aux (sup Unit f) = RllubPos
                        (fun n => OpenFun_aux (f n))).
  auto. rewrite Hr.
  apply Rllub_le.
  intros n.
  apply H2.
Qed.
      
(* Map from Opens to characteristic function *)
Definition OpenFun (A : hSet) : forall (U : A -> Sier),
                                       (A -> RlowPos). 
Proof. 
intros s z. 
specialize (s z).
exact (OpenFun_aux s).
Defined.

Lemma OpenFun_def {A} : forall U:OS A, U = OS_empty
                               -> OpenFun _ U = fun x => RlP_0. 
Proof.
intros U HU.   
apply path_forall. 
intros x. 
rewrite HU. 
auto. 
Qed. 

Lemma OpenFun_prob {A} : forall U:OS A, U = OS_full
                               -> OpenFun _ U <= fun x => RlP_1. 
Proof.
intros U HU x. 
rewrite HU. 
auto. 
Qed. 

(* Monotonicity *)
Lemma OpenFun_mon {A} : forall U V:OS A, U <= V -> OpenFun _ U <= OpenFun _ V.
Proof.
intros U V H1 s.
unfold OpenFun.
apply OpenFun_aux_mon; trivial.
apply (H1 s).
Qed.
(*

Lemma OpenFun_meet_is_meet {A}: forall (U V : OS A) s r,
      (val (rl ((OpenFun _ U) s)) r
    /\ val (rl ((OpenFun _ V) s)) r) <->
       val (rl ((OpenFun_aux ((SierMeet (U s) (V s)))))) r. 
Proof.
intros U V r s.  
split.
+ intros (H1,H2).
  unfold OpenFun in H1.
  revert H1. 
  apply SierLe_imply. unfold val. admit.   
+ intros Hm. 
  
Admitted. *)

Definition OpenFun_meet {A} (U V : OS A) := OpenFun _ (OS_meet U V).

Lemma OpenFun_siermeet_is_meet A : forall (a b : Sier) r s,
      ((val (rl ((OpenFun A (fun x => a)) r)) s)
   /\ (val (rl ((OpenFun A (fun x => b)) r)) s)) <-> 
       (val (rl ((OpenFun A (fun x => SierMeet a b)) r)) s).  
Proof.
split; revert a b.  
apply (partial_ind0 _ (fun a => forall b, _ -> _)).
simpl. unfold semi_decide. destruct (decide (s < 1)).
intros x b (H1,H2).
assert (SierMeet (eta Unit x) b = b). 
reflexivity. 
rewrite X; trivial.
Admitted. 

Lemma OpenFun_meet_is_meet {A}: forall (U V : OS A) s r,
      (val (rl ((OpenFun _ U) s)) r
    /\ val (rl ((OpenFun _ V) s)) r) <->
       val (rl ((OpenFun_meet U V) s)) r. 
Proof.
intros U V r s.  
split.
+ intros (H1,H2).
  unfold OpenFun_meet.
  unfold OS_meet.  
   
  unfold val.  admit.
  
+ intros HH. 
  split.
  - apply RC_mon with Qle (rl (OpenFun_aux ((OS_meet U V) r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierMeet_is_meet.
    apply HH. 
  - apply RC_mon with Qle (rl (OpenFun_aux ((OS_meet U V) r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierMeet_is_meet.
    apply HH. 
Admitted.


Definition OpenFun_join {A} (U V : OS A) := OpenFun _ (OS_join U V). 

Lemma OpenFun_join_is_join {A}: forall (U V : OS A) s r,
      (val (rl ((OpenFun _ U) s)) r
    \/ val (rl ((OpenFun _ V) s)) r) <->
       val (rl ((OpenFun_join U V) s)) r. 
Proof.
intros U V r s.  
split.
+ intros HD. case HD; intros HDO. 
  - unfold OpenFun_meet.
    apply RC_mon with Qle (rl (OpenFun_aux (U r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierJoin_is_join.
    apply HDO.
  - unfold OpenFun_meet.
    apply RC_mon with Qle (rl (OpenFun_aux (V r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierJoin_is_join.
    apply HDO.  
+ intros HH.
  unfold OpenFun_join in HH.
  unfold OS_join in HH.
  admit. 
Admitted. 

  (* new definitions, new proof, to fix soon *)
Lemma OpenFun_mod {A}: forall (U V : OS A), fplus (OpenFun _ U) (OpenFun _ V) =
                                fplus (OpenFun _ (OS_meet U V))
                                      (OpenFun _ (OS_join U V)).
Proof.
intros U V.
apply path_forall; intros z. 
apply (antisymmetry le). 
+ intros q Hs. simpl in *. 
  apply Rlplus_eq_pr in Hs.
  assert (Ho : merely
         (∃ r' s' : Q,
          val (rl (OpenFun _ (OS_meet U V) z)) r'
          ∧ val (rl (OpenFun _ (OS_join U V) z)) s'
          ∧ q = r' + s')).
  revert Hs. apply (Trunc_ind _). 
  intros Hs; apply tr. 
  destruct Hs as (r,(s,(Hr,(Hs,Hq)))). 
  destruct (Qle_total r s).
  - exists r, s. 
    repeat split; try trivial.
    * unfold OS_meet.
      assert (HrV : val (rl (OpenFun A V z)) r). 
      apply RC_le with Qle s. 
      intros ss ss'; apply (antisymmetry le). 
      apply le_or_lt. apply Hs. apply l. 
      apply OpenFun_meet_is_meet.            
       split; trivial.
    * apply RC_mon with Qle (rl (OpenFun_aux (V z))) s. 
      intros ss ss'; apply (antisymmetry le). 
      apply le_or_lt. reflexivity. 
      apply OpenFun_aux_mon. 
      apply SierJoin_is_join.
      apply Hs.  
  - exists s, r. 
    repeat split; try trivial.
    * unfold OS_meet. 
      assert (HrV : val (rl (OpenFun_aux (U z))) s). 
      apply RC_le with Qle r. 
      intros ss ss'; apply (antisymmetry le). 
      apply le_or_lt. apply Hr. apply l.  
      apply OpenFun_meet_is_meet. 
      split; trivial.   
    * apply RC_mon with Qle (rl (OpenFun_aux (U z))) r. 
      intros ss ss'; apply (antisymmetry le). 
      apply le_or_lt. reflexivity. 
      apply OpenFun_aux_mon. 
      apply SierJoin_is_join.
      apply Hr.  
    * rewrite Hq. 
      rewrite rings.plus_comm.  
      reflexivity. 
  - apply pred_plus_pr; trivial.  
+ intros q Hs. simpl in *.
  apply rlow_pred_plus_pr in Hs.
  assert (Ho : merely
         (∃ r' s' : Q,
          val (rl (OpenFun _ U z)) r'
          ∧ val (rl (OpenFun _ V z)) s'
          ∧ q < r' + s')).
  revert Hs. apply (Trunc_ind _). 
  intros Hs; apply tr. 
  destruct Hs as (r,(s,(Hr,(Hs,Hq)))).
  destruct (Qle_total r s).
   - apply OpenFun_join_is_join in Hs.
     destruct Hs. 
     -- exists s, r.               
        repeat split; try trivial. 
        * apply OpenFun_meet_is_meet in Hr. 
          destruct Hr as (Hr1,Hr2). 
          trivial.  
        * rewrite (rings.plus_comm). 
          trivial.
     -- exists r, s. 
        repeat split; try trivial. 
        apply OpenFun_meet_is_meet in Hr. 
        destruct Hr as (Hr1,Hr2). 
        trivial.  
   - exists r, r. 
     repeat split; try trivial.
     * apply RC_mon with Qle (rl (OpenFun _ (OS_meet U V) z)) r. 
       intros ss ss'; apply (antisymmetry le). 
       apply le_or_lt. reflexivity.
       apply OpenFun_aux_mon. 
       apply SierMeet_is_meet.
       apply Hr.  
     * apply RC_mon with Qle (rl (OpenFun _ (OS_meet U V) z)) r. 
       intros ss ss'; apply (antisymmetry le). 
       apply le_or_lt. reflexivity.
       apply OpenFun_aux_mon. 
       apply SierMeet_is_meet.
       apply Hr.
     * apply lt_le_trans with (r + s); trivial.  
       apply semirings.plus_le_compat; try reflexivity; trivial. 
   - apply pred_plus_pr.      
     revert Ho; apply (Trunc_ind _). 
     intros (r,(s,(Ho1,Ho2))); apply tr. 
     exists r.
     exists (q - r). 
     split; try trivial.      
     split. 
     * apply RC_le with Qle s. 
      -- intros x y; apply (antisymmetry le). 
      -- intros x y; apply le_or_lt.       
      -- apply (fst Ho2). 
      -- apply rings.flip_le_minus_l.
         rewrite rings.plus_comm.
         apply lt_le. 
         apply (snd Ho2). 
     * apply rings.plus_conjugate_alt.
Qed.

End OpenFun. 
