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
               D_op OpenFun Riesz1 Giry Cpo.
              
Set Implicit Arguments.


Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n).

Definition qP (n : nat) := ((qnp n) * (1 / qnp (S n))).
Definition qbp (n : nat) (b : Q+) := b * (1 / qnp n). 
Definition qb (n : nat) (b : Q) := (qn n) * b. 
Definition qfc (n : nat) := pos (qP n).


Coercion qn : nat >-> Q.
Coercion qnp : nat >-> Qpos.

(** * Interpretation of probabilistic programs *)
(**
      .  --> [.] ;

      v  --> unit v ;

 let x=a in b --> bind  [a] (fun x => [b]) ;

     f a  -->  bind  [a] (fun x => [f] x) ;

    if b then a1 else a2 --> bind  [b] (fun x:bool => 
    if b then [a1] else [a2]).
**)



(** Image distributions by a function f :  *) 

Definition im_distr {A B : hSet} (f : A -> B) (J : IntPos A) : IntPos B
                                      := bind J (fun a => unit B (f a)).

Lemma im_distr_id {A : hSet}: forall (f : A -> A) (J : IntPos A),
          (forall x, f x = x) -> im_distr f J = J. 
Proof. 
intros f m Hx. 
unfold im_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu. simpl; rewrite monad2; reflexivity. 
Qed.  

Lemma im_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C) (m : IntPos A) : 
   im_distr g (im_distr f m) = im_distr (fun a => g (f a)) m.
Proof.
apply IntPos_eq0; apply path_forall.
intros h; unfold im_distr; simpl; 
reflexivity. 
Qed.


(**  Conditional distribution *)
Definition bool : hSet := default_TruncType 0 bool hset_bool.

Definition Mif (A:hSet) (b: IntPos bool) (m1 m2:IntPos A) : IntPos A. 
Proof.                         
exists (fun X => (bind b (fun x:bool => if x then m1 else m2)) X).
+ hnf; unfold bind; simpl. 
  assert (Hb : (λ y : bool, (if y then m1 else m2) (fzero A)) = 
               λ y : bool, RlP_0).
  apply path_forall; intros y.
  destruct y; rewrite I_def; reflexivity.
  rewrite Hb, I_def; reflexivity.
+ intros f g; unfold bind; simpl.
  rewrite <- I_add.
  assert (H : (λ x : bool, (if x then m1 else m2) (fplus f g)) = 
             (fplus (λ x : bool, (if x then m1 else m2) f)
                    (λ x : bool, (if x then m1 else m2) g))).
  apply path_forall; intros y. unfold fplus. 
  simpl; destruct y;
  apply I_add.
  rewrite H; reflexivity.  
+ intros q Hq.
  unfold bind in Hq.
  simpl in Hq.
  assert (H : val (b (fone bool)) q).
  revert Hq; apply RC_mon with Qle.
  intros x y; apply (antisymmetry le).
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_mon.
  intros y; destruct y;
  apply I_prob.
  revert H; apply RC_mon with Qle.
  intros x y; apply (antisymmetry le).
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_prob.     
+ intros f g Hfg.
  apply I_mon; trivial. 
Defined. 

(** * Correctness judgements *)

(** ok: the measure of F by the program associated 
        to nu is at least p, here p plays the role of 
        the probability.

    ok_up: the measure of F by the program associated 
           to nu is at most p. *)

Definition ok {A} (p : RlowPos) (nu : IntPos A) (F : mf A) :=
                         p <= nu F. 

Definition ok_fun {A B} (f : mf A) (E : A -> IntPos B) (F : A -> mf B) :=
                     forall x:A, ok (f x) (E x) (F x). 

Definition ok_up {A} (p : RlowPos) (nu : IntPos A) (F : mf A) := nu F <= p. 

Definition up_fun {A B} (f : mf A) (E : A -> IntPos B) (F : A -> mf B) :=
                     forall x:A, ok_up (f x) (E x) (F x). 

(** Correctness rules for applications *)

Lemma apply_rule {A B} : forall (J : IntPos A) (f : A -> IntPos B)
                                (r : RlowPos)
                                (F : mf A) (G : OS B),
          ok r J F -> ok_fun F f (fun x => G) ->
          ok r (bind J f) G. 
Proof.
intros nu f r F G H1 H2.
unfold ok_fun, ok in *.
unfold bind.
simpl. transitivity (nu F); trivial.
apply I_mon; trivial.
Qed. 

Lemma apply_rule_up {A B} : forall (J : IntPos A) (f : A -> IntPos B)
                      (r : RlowPos) (F : mf A) (G : mf B),
    ok_up r J F -> up_fun F f (fun x => G) ->
    ok_up r (bind J f) G. 
Proof.
intros nu f r U V H1 H2. 
unfold up_fun, ok_up in *. 
unfold bind; simpl.
transitivity (nu U); trivial.
apply I_mon; trivial.
Qed.


(** Correctness rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> IntPos B) (F : mf A)
                                      (G : A -> mf B),
    (forall x:A, ok (F x) (f x) (G x)) -> ok_fun F f G. 
Proof.
intros f F G HO. 
unfold ok_fun, ok in *; trivial. 
Qed. 

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> IntPos B) (F : mf A) (G : A -> mf B),
       (forall x:A, ok_up (F x) (f x) (G x)) -> up_fun F f G. 
Proof.
intros f F G HO. 
unfold up_fun, ok_up in *; trivial. 
Qed. 


(** * Little examples of probabilistic programs *)

(** Flip program : Val bool
 
   fun f: bool -> Sier  => (1/2) (f true) + 
                           (1/2) (f false)
*)

Definition flip : IntPos bool. 
Proof.
exists (fun f => (Rlow_mult_q 2 (f true) +
                  Rlow_mult_q 2 (f false))).
+ unfold Mdef. 
  assert (ho : forall (A:hSet) x, 
       (fzero A x) = RlP_0).
  intros A x; reflexivity.
  repeat rewrite ho.
  rewrite Rlow_mult_q_RlP_0.
  unfold plus; rewrite RlPPlus_left_id.
  reflexivity. 
+ intros f g.
  assert (Hdistr : forall (A:hSet) p f g (x:A), 
           RlP_plus (Rlow_mult_q p (f x)) 
                    (Rlow_mult_q p (g x)) = 
           Rlow_mult_q p (f x + g x)).
  intros A p ff gg x.
  apply (antisymmetry le).
  - intros s Hs.
    apply pred_plus_pr in Hs.
    unfold Rlow_mult_q. simpl.
    unfold pred_multQ; simpl.
    apply pred_plus_pr.
    revert Hs; apply (Trunc_ind _).
    intros (rr,(ss,(E1,(E2,E3)))).
    unfold Rlow_mult_q in *; simpl in *; 
    unfold pred_multQ in *; simpl in *.
    apply tr.
    exists (pos p * rr), (pos p * ss).
    repeat split; trivial.
    rewrite E3.
    rewrite (semiring_distr Q).
    reflexivity.
  - intros s Hs.
    unfold Rlow_mult_q in Hs; simpl in Hs; 
    unfold pred_multQ in Hs; 
    apply pred_plus_pr in Hs.
    apply pred_plus_pr.
    revert Hs; apply (Trunc_ind _).
    intros (rr,(ss,(E1,(E2,E3)))).
    apply tr.
    exists (rr * / pos p), (ss * / pos p).
    repeat split.
    unfold Rlow_mult_q; simpl; 
    unfold pred_multQ; simpl.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos p)).
    assert (Hp1 : pos p / pos p = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hp1.
    rewrite mult_1_r; trivial.
    unfold Rlow_mult_q; simpl; 
    unfold pred_multQ; simpl.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite (mult_comm _ (pos p)).
    assert (Hp1 : pos p / pos p = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos p).
    apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hp1.
    rewrite mult_1_r; trivial.
    rewrite dec_quotients.
    rewrite (mult_comm rr _).
    rewrite (mult_comm ss _).
    rewrite <- (semiring_distr Q).
    rewrite <- E3.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite mult_comm.
    rewrite mult_assoc.
    rewrite mult_comm.
    assert (H1: (/ (pos p * pos p) * 
                  pos p * pos p) = 1).
    rewrite <- mult_assoc.
    rewrite mult_comm.
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos p *  pos p).
    apply pos_mult_compat; apply p.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity. 
    rewrite H1.
    rewrite mult_1_r.
    reflexivity.
    apply lt_ne_flip.
    apply p.
    apply lt_ne_flip.
    apply p.
  - rewrite <- Hdistr.
    rewrite <- Hdistr.
    unfold plus. rewrite (RlPPlus_comm 
     (Rlow_mult_q (Qpos_plus 1 1) (g true)) 
     (Rlow_mult_q (Qpos_plus 1 1) (g false))).
    unfold plus;
    rewrite RlPPlus_assoc.
    rewrite  <- (RlPPlus_assoc (Rlow_mult_q 
                   (Qpos_plus 1 1) (f true))
        (Rlow_mult_q (Qpos_plus 1 1) (g true))
        (Rlow_mult_q (Qpos_plus 1 1) (f false))).
    rewrite (RlPPlus_comm 
     (Rlow_mult_q (Qpos_plus 1 1) (g false))
     (Rlow_mult_q (Qpos_plus 1 1) (g true))).
    rewrite <- RlPPlus_assoc. 
    rewrite (RlPPlus_comm 
     (Rlow_mult_q (Qpos_plus 1 1) (g true))
     (Rlow_mult_q (Qpos_plus 1 1) (f false))).
    rewrite RlPPlus_assoc.
    rewrite RlPPlus_assoc.
    rewrite RlPPlus_assoc.
    reflexivity.
+ unfold Mprob.
  assert (H1 : forall (A : hSet) x, 
                fone A x = RlP_1).
  intros A x; reflexivity.
  repeat rewrite H1. 
  intros s Hs.
  apply pred_plus_pr in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (a,(b,(E1,(E2,E3)))).
  unfold Rlow_mult_q in *; simpl in *; 
  unfold pred_multQ in *.
  unfold semi_decide in *.
  destruct (decide (pos 2 * a < 1)).
  destruct (decide (pos 2 * b < 1)).
  destruct (decide (s < 1)).
  apply top_greatest.
  assert (Hs1 : s < 1).
  rewrite E3.
  apply le_lt_trans with ((1/2)*(pos 2 * a) +
                          (1/2)*(pos 2 * b)).
  apply plus_le_compat.
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite (mult_1_l).
  rewrite (mult_comm (/2)).
  assert (H2 : (pos 2 / 2) = 1).
  transitivity (1/1).
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : Qzero < 2).
  apply lt_0_2.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.  
  rewrite H2.
  rewrite mult_1_r; reflexivity.
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite (mult_1_l).
  rewrite (mult_comm (/2)).
  assert (H2 : (pos 2 / 2) = 1).
  transitivity (1/1).
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : Qzero < 2).
  apply lt_0_2.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.  
  rewrite H2.
  rewrite mult_1_r; reflexivity.
  rewrite <- (semiring_distr Q).
  apply lt_le_trans with (1 / 2 * (1 + 1)).
  apply pos_mult_lt_l.
  rewrite mult_1_l.
  apply dec_fields.pos_dec_recip_compat.
  apply lt_0_2.
  apply plus_lt_compat; trivial.
  rewrite mult_comm.
  rewrite mult_assoc.
  rewrite mult_1_r.
  assert (Hp2 : 2 / 2 = 1).
  transitivity (1/1).
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : (Qzero < 2)).
  apply lt_0_2.
  case (HF Hp).
  apply lt_ne_flip.
  apply lt_0_1.
  rewrite mult_comm.
  reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity.
  rewrite Hp2.
  reflexivity. 
  case (n Hs1).
  apply not_bot in E2; case E2.
  apply not_bot in E1; case E1.
+ intros f g Hfg.
  transitivity (RlP_plus (Rlow_mult_q 2 
      (f true)) (Rlow_mult_q 2 (g false))). 
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt. 
  reflexivity.
  apply Hfg.
  rewrite RlPPlus_comm.
  unfold plus; rewrite (RlPPlus_comm 
       (Rlow_mult_q (Qpos_plus 1 1) (g true))).    
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt. 
  reflexivity.
  apply Hfg.
Defined.  

Lemma flip_cont : forall F : IncreasingSequence (mf bool), 
                   flip (lub F) <=
                     RllubPos (fun n => flip (F n)).
Proof.
intros F q Hq.
apply top_le_enumerable_sup in Hq.
apply top_le_enumerable_sup.
revert Hq; apply (Trunc_ind _); 
intros (m,E).
unfold semi_decide, semi_decide_exists, 
       semi_decide, semi_decide_conj in *.
apply top_le_enumerable_sup in E.
revert E; apply (Trunc_ind _); intros (p,Hp).
unfold semi_decide, semi_decide_sier in Hp.
apply top_le_meet in Hp.
destruct Hp as (E1,E2).
apply top_le_meet in E2. 
destruct E2 as (E2,E3).
unfold decidable_semi_decide in *.
unfold Rlow_mult_q in E1,E2.
simpl in *.
unfold pred_multQ in *.
unfold semi_decide, SDseq_Rlow,
 semi_decide_exists in *.
apply top_le_enumerable_sup in E1.
apply top_le_enumerable_sup in E2.
revert E1; apply (Trunc_ind _); intros (e1,E1).
revert E2; apply (Trunc_ind _); intros (e2,E2).
apply tr; unfold toRlseq.
unfold semi_decide, toRlseq in *.
destruct (decide (e1 < e2)).
exists e2.
apply pred_plus_pr.
apply tr.
exists m, p.
repeat split; trivial.
revert E1; apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity. 
assert (H : F e1 <= F e2).
apply seq_increasing_le.
apply lt_le; trivial.
apply H.
destruct (decide (q = m + p)).
trivial.
apply not_bot in E3; case E3.
exists e1.
apply pred_plus_pr.
apply tr.
exists m, p.
repeat split; trivial.
revert E2; apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity. 
assert (H : F e2 <= F e1).
apply seq_increasing_le.
apply not_lt_le_flip in n; trivial.
apply H.
destruct (decide (q = m + p)).
trivial.
apply not_bot in E3; case E3.
Qed.


Definition QRlow_qpos (q : Q+)  : RlowPos. 
Proof.
assert (HP : Rlle ('0) (QRlow (rationals.pos q))).
intros p Hp.   
simpl in *. 
unfold semi_decide in *. 
destruct (decide (p < 0)). 
destruct (decide (p < rationals.pos q)). 
trivial. 
assert (p < rationals.pos q). 
apply orders.lt_le_trans with 0; trivial.
destruct q as (q,Hq).
simpl. apply orders.lt_le.
trivial. 
case (n X). 
destruct (decide (p < rationals.pos q)).
apply top_greatest. 
trivial. 
refine (Rlow_RlowPos (QRlow (rationals.pos q)) HP). 
Defined. 


(** Random program : Val nat
   fun f: nat -> Sier => (1 / S n) * sum_1^n (f n)
*)

Require Export Spaces.Nat.  
Close Scope nat. 

Definition nat : hSet := default_TruncType 0 nat hset_nat. 

Fixpoint sum_n_moy_aux (p : nat) (f : nat -> RlowPos) : RlowPos := 
       match p with
          |O => RlP_0
          |S p0 => RlP_plus (f (S p0)) (sum_n_moy_aux p0 f)
end.

Lemma sum_n_moy_aux_def (p : nat) : 
      sum_n_moy_aux p (fzero nat) = RlP_0.
Proof.
induction p.
+ simpl; reflexivity.
+ simpl.
  rewrite IHp.
  assert (H0 : (fzero nat (S p)) = RlP_0). 
  reflexivity.
  rewrite H0.
  rewrite RlPPlus_left_id; 
  reflexivity. 
Qed.

Lemma sum_n_moy_aux_mon (p : nat) f g : fle f g ->
      sum_n_moy_aux p f <= sum_n_moy_aux p g.
Proof.
intros Hfg.
induction p.
+ simpl; reflexivity.
+ simpl.
  transitivity (RlP_plus (f (S p)) 
                   (sum_n_moy_aux p g)).
  apply Rllepos_plus_le_preserving; exact IHp.
  rewrite (RlPPlus_comm _ (sum_n_moy_aux p g)).
  rewrite (RlPPlus_comm _ (sum_n_moy_aux p g)).
  apply Rllepos_plus_le_preserving.
  apply Hfg.
Qed.  

Definition QRlow_nat_pos : nat -> RlowPos.
Proof.
intros n.
induction n.
+ exists RlP_0. intros p Hp; simpl.
  unfold semi_decide; destruct (decide (p < 0)).
  apply top_greatest.
  case (n Hp).
+ exists (QRlow (qn (S n))).
  intros p Hp.
  simpl; unfold semi_decide.
  destruct (decide (p < S n)).
  apply top_greatest.
  assert (Hpn : p < (S n)).
  apply lt_le_trans with 0; trivial.
  unfold qn. apply lt_le.
  destruct ((pos_of_nat (S n))).
  apply rationals.is_pos.
  case (n0 Hpn).
Defined.  
          

Lemma sum_n_moy_aux_prob (n : nat) :
               Rlle (sum_n_moy_aux n (fone nat))
                    (QRlow_nat_pos n).
Proof.
induction n.
+ intros q; trivial.  
+ intros q. simpl in *.
  intros H.
  unfold semi_decide in *.
  apply pred_plus_pr in H.
  destruct (decide (q < S n)).
  apply top_greatest.
  assert (hq : q < S n).
  revert H; apply (Trunc_ind _); 
  intros (a,(b,(E1,(E2,E3)))).
  rewrite E3.
  specialize (IHn b).
  apply IHn in E2.
  induction n.
  - simpl in E2; unfold semi_decide in E2.
    destruct (decide (a < 1)). 
    destruct (decide (b < 0)).
    apply lt_le_trans with (1 + 0)%mc.
    apply plus_lt_compat; trivial.
    rewrite plus_0_r.
    reflexivity.
    apply not_bot in E2; case E2.
    apply not_bot in E1; case E1.
  - simpl in E2; unfold semi_decide in *.
    destruct (decide (a < 1)).
    destruct (decide (b < S n)).
    apply plus_lt_compat; trivial.
    apply not_bot in E2; case E2.
    apply not_bot in E1; case E1.
  - case (n0 hq). 
Qed.    
    
    
Lemma sum_n_moy_aux_add (p : nat) f g : 
      sum_n_moy_aux p (fplus f g) =  RlP_plus (sum_n_moy_aux p f) 
                                             (sum_n_moy_aux p g).
Proof.
induction p.
+ simpl; rewrite RlPPlus_left_id;
  reflexivity.
+ simpl.
  rewrite IHp.
  assert (H0 : (fplus f g (S p)) = 
        RlP_plus (f (S p)) (g (S p))).
  reflexivity.
  rewrite H0.
  rewrite RlPPlus_assoc.
  rewrite RlPPlus_assoc.
  rewrite RlPPlus_comm.
  rewrite RlPPlus_comm.
  rewrite <- (RlPPlus_assoc (f (S p)) (g (S p)) 
             (sum_n_moy_aux p f)).
  rewrite (RlPPlus_comm (g (S p)) 
     (sum_n_moy_aux p f)).
  rewrite RlPPlus_assoc.
  reflexivity.  
Qed.

Definition sum_n_moy (p : nat) (f : nat -> RlowPos) : RlowPos 
             := Rlow_mult_q p (sum_n_moy_aux p f).

Lemma sum_n_moy_def (p : nat) : 
      sum_n_moy p (fzero nat) = RlP_0.
Proof.
unfold sum_n_moy.
rewrite sum_n_moy_aux_def.
apply Rlow_mult_q_RlP_0.
Qed.

Lemma sum_n_moy_prob (n : nat) : 
   Rlle (sum_n_moy n (fone nat)) RlP_1.
Proof.
unfold sum_n_moy.
assert (H : Rlle 
       (Rlow_mult_q n (sum_n_moy_aux n (fone nat))) 
       (Rlow_mult_q n (QRlow_nat_pos n))).
intros q Hq.
unfold Rlow_mult_q in *; simpl in *.
unfold pred_multQ in *; simpl in *.
revert Hq; apply RC_mon with Qle.
intros x y; apply (antisymmetry Qle).
intros x y; apply orders.le_or_lt.
reflexivity.
apply sum_n_moy_aux_prob.     
assert (H2 : Rlle (Rlow_mult_q n (QRlow_nat_pos n)) 
                  RlP_1).
intros q Hq.
simpl in Hq.
unfold pred_multQ in Hq.
induction n.
+ simpl in Hq. simpl.
  unfold semi_decide in *; simpl in *.
  clear H. 
  rewrite mult_1_l in Hq.
  destruct (decide (q < 0)).
  destruct (decide (q < 1)).
  trivial.
  assert (Hf : q < 1).
  transitivity Qzero.
  trivial.
  apply lt_0_1.
  case (n Hf).
  destruct (decide (q < 1)).
  apply top_greatest.
  trivial.         
+ clear IHn. simpl.
  unfold semi_decide in *.
  destruct (decide ((naturals.naturals_to_semiring 
              nat Q (S n) * q)%mc < S n)).
  destruct (decide (q < 1)); trivial.
  apply top_greatest.
  assert (Hf : q < 1). 
  assert (Hu : 
   ((1 / qn (S n))* ((qn (S n))*q))%mc <
    ((1 / qn (S n)) * (qn (S n)))%mc).
  apply pos_mult_lt_l.
  rewrite mult_1_l.
  apply dec_fields.pos_dec_recip_compat.
  apply rationals.is_pos.
  apply l.
  rewrite mult_assoc in Hu.
  rewrite mult_comm in Hu.
  rewrite (mult_comm _ (qn (S n))) in Hu.
  rewrite mult_1_l in Hu.
  assert (Hsn : qn (S n) / qn (S n) = 1). 
  transitivity (1/1).
  apply equal_dec_quotients.
  apply not_le_ne.
  intros HF.
  apply le_iff_not_lt_flip in HF. 
  assert (Hp : 0 < pos (S n)).
  apply rationals.is_pos.
  case (HF Hp).
  generalize rational_1_neq_0.
  apply apartness.apart_ne.
  rewrite mult_comm; reflexivity.
  rewrite dec_recip_1.
  rewrite mult_1_r; reflexivity. 
  rewrite Hsn in Hu.
  rewrite mult_1_r in Hu; trivial. 
  case (n0 Hf).
  destruct (decide (q < 1)).
  apply top_greatest.
  simpl in Hq.
  unfold semi_decide in Hq.
  destruct (decide ((naturals.naturals_to_semiring 
              nat Q (S n) * q)%mc < S n)).
  case (n0 l).
  destruct (decide
        ((naturals.naturals_to_semiring 
      Datatypes.nat Q (S n) * q)%mc < S n)).
  case (n2 l).
  trivial. 
+ intros q hq; apply H2.
  apply H; trivial.
Qed.   
 
Definition random_aux (N : nat) : M nat. 
Proof.
intros f.
exists (rl (sum_n_moy N f)).
apply (sum_n_moy N). 
Defined. 

Definition random (N : nat) :  IntPos nat.  
Proof. 
exists (random_aux N).
+ unfold Mdef, random_aux.
  apply RCP_eq0.
  rewrite sum_n_moy_def.
  simpl; reflexivity. 
+ intros f g.
  unfold random_aux; simpl.
  apply RCP_eq0; simpl.
  transitivity (pred_multQ (val (RlP_plus (sum_n_moy_aux N f)  
                                 (sum_n_moy_aux N g))) N).
  assert (Hsum : sum_n_moy_aux N (fplus f g) = RlP_plus
             (sum_n_moy_aux N f) (sum_n_moy_aux N g)).
  apply sum_n_moy_aux_add. 
  rewrite Hsum.
  reflexivity.
  apply path_forall.
  intros x. 
  apply (antisymmetry SierLe).
  - apply imply_le.
    intros Hx.
    unfold pred_multQ in Hx.
    apply pred_plus_pr.
    apply pred_plus_pr in Hx.
    revert Hx; apply (Trunc_ind _); 
    intros (a,(b,(E1,(E2,E3)))).
    apply tr.
    exists (a / pos N), (b / pos N).
    repeat split.
    unfold pred_multQ.
    assert (Ha : (pos N * (a / pos N))%mc = a).
    rewrite mult_comm.
    rewrite <- mult_assoc.
    rewrite (mult_comm _ (pos N)).
    assert (Hn : (pos N / pos N) = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos N).
    apply (pos_is_pos).
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hn.
    rewrite mult_1_r.
    reflexivity.
    rewrite Ha; trivial.
    unfold pred_multQ.
    assert (Hb : (pos N * (b / pos N))%mc = b).
    rewrite mult_comm.
    rewrite <- mult_assoc.
    rewrite (mult_comm _ (pos N)).
    assert (Hn : (pos N / pos N) = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < pos N).
    apply (pos_is_pos).
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity.  
    rewrite Hn.
    rewrite mult_1_r.
    reflexivity.
    rewrite Hb; trivial.
    rewrite dec_quotients.
    rewrite (mult_comm a _).
    rewrite (mult_comm b _).
    rewrite <- (semiring_distr Q).
    rewrite <- E3.
    rewrite mult_assoc.
    rewrite (mult_comm _ x).
    rewrite <- mult_assoc.
    assert (H1 : (Qmult (pos N) (pos N))
                / (Qmult (pos N) (pos N)) = 1).
    transitivity (1/1).
    apply equal_dec_quotients.
    apply not_le_ne.
    intros HF.
    apply le_iff_not_lt_flip in HF. 
    assert (Hp : 0 < Qmult (pos N) (pos N)).
    apply pos_mult_compat; apply pos_is_pos.
    case (HF Hp).
    generalize rational_1_neq_0.
    apply apartness.apart_ne.
    rewrite mult_comm; reflexivity.
    rewrite dec_recip_1.
    rewrite mult_1_r; reflexivity. 
    rewrite H1.
    rewrite mult_1_r.
    reflexivity.
    apply lt_ne_flip.
    apply pos_is_pos.
    apply lt_ne_flip.
    apply pos_is_pos.
  - apply imply_le.
    intros Hx.
    unfold pred_multQ.
    apply pred_plus_pr.
    apply pred_plus_pr in Hx.
    revert Hx; apply (Trunc_ind _); 
    intros (a,(b,(E1,(E2,E3)))).
    apply tr.
    exists (Qmult (pos N) a), (Qmult (pos N) b).
    repeat split.
    unfold pred_multQ in E1.
    trivial.
    unfold pred_multQ in E2.
    trivial.
    rewrite E3.
    rewrite (semiring_distr Q).
    reflexivity. 
+ apply sum_n_moy_prob.
+ unfold mon_opens. 
  intros f g Hfg.
  intros q Hq. 
  unfold random_aux in *; simpl in *.
  unfold pred_multQ in *.
  revert Hq. 
  apply RC_mon with Qle.
  intros x y; apply (antisymmetry Qle). 
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply sum_n_moy_aux_mon.
  trivial.
Defined.   

Lemma random_cont N : forall F : IncreasingSequence (mf nat), 
                   random N (lub F) <=
                     RllubPos (fun n => random N (F n)).
Proof.
intros F q Hq.
simpl in Hq; unfold pred_multQ in Hq.
apply top_le_enumerable_sup.
assert (H : (sum_n_moy_aux N
           (λ x, RllubPos (λ n, F n x))) = 
             RllubPos (fun n => sum_n_moy_aux N 
           (λ x, F n x))).
apply (antisymmetry Rllepos).
+ clear Hq.
  induction N; 
  intros v Hv.
  apply top_le_enumerable_sup.
  unfold semi_decide, toRlseq.
  - simpl in Hv.
    apply tr.
    exists 0.
    simpl; trivial.
  - simpl in Hv.
    unfold semi_decide, toRlseq in *.
    unfold SDseq_Rlow, semi_decide_exists, 
     semi_decide in *.
    apply pred_plus_pr in Hv.
    revert Hv; apply (Trunc_ind _).
    intros (e1,(e2,(E1,(E2,E3)))).
    apply top_le_enumerable_sup in E1.
    apply IHN in E2.
    apply top_le_enumerable_sup in E2.
    unfold semi_decide, toRlseq in E2.
    apply top_le_enumerable_sup.
    unfold semi_decide, toRlseq.
    revert E1; apply (Trunc_ind _); 
    intros (k1,E1).
    revert E2; apply (Trunc_ind _); 
    intros (k2,E2).
    apply tr.
    simpl.  
    destruct (decide (k1 < k2)).
    exists k2.
    apply pred_plus_pr.
    apply tr; exists e1, e2.
    repeat split; trivial.
    revert E1; apply RC_mon with Qle.
    intros x y; apply (antisymmetry Qle). 
    intros x y; apply orders.le_or_lt.
    reflexivity.
    assert (H : F k1 <= F k2).
    apply seq_increasing_le.
    apply lt_le; trivial.
    apply H.
    exists k1.
    apply pred_plus_pr.
    apply tr; exists e1, e2.
    repeat split; trivial.
    revert E2; apply RC_mon with Qle.
    intros x y; apply (antisymmetry Qle). 
    intros x y; apply orders.le_or_lt.
    reflexivity.
    apply sum_n_moy_aux_mon.
    assert (H : F k2 <= F k1).
    apply seq_increasing_le.
    apply not_lt_le_flip in n; trivial.
    apply H.
+ clear Hq.
  induction N; 
  intros v Hv.
  apply top_le_enumerable_sup in Hv.
  unfold semi_decide, toRlseq in *.
  - simpl. 
    revert Hv; apply (Trunc_ind _).
    intros (n,Hn).
    simpl in Hn; trivial.
  - simpl.
    unfold semi_decide, toRlseq in *.
    unfold SDseq_Rlow, semi_decide_exists, 
     semi_decide in *.
    apply pred_plus_pr.
    apply top_le_enumerable_sup in Hv.
    unfold semi_decide, toRlseq in Hv.
    revert Hv; apply (Trunc_ind _).
    intros (e,E). simpl in E.
    apply pred_plus_pr in E.
    revert E; apply (Trunc_ind _); 
    intros (e1,(e2,(E1,(E2,E3)))).
    apply tr.
    exists e1, e2.
    repeat split. 
    apply top_le_enumerable_sup.
    apply tr; exists e; trivial.
    revert E2; apply RC_mon with Qle.
    intros x y; apply (antisymmetry Qle). 
    intros x y; apply orders.le_or_lt.
    reflexivity.
    apply sum_n_moy_aux_mon.
    intros x.
    apply (RllubPos_lub (fun n => F n x) e).
    trivial.
+ rewrite H in Hq.
  apply top_le_enumerable_sup in Hq.
  unfold semi_decide, toRlseq in Hq.
  unfold semi_decide, toRlseq.
  simpl; unfold pred_multQ; simpl.
  trivial.
Qed.

     
(** ** Fixpoints *)
Section Fixpoints. 

Context {P : Type} {lP : Le P}
        {wCP : cpo P}.

Context {A : hSet}.

Fixpoint iter (f : P -> P) n : P := match n with 
                       | O => cpobot 
                       | S m => f (iter f m) end.

Definition fixp f : P := lub (iter f).
(*
Lemma fixp_le f : fixp <= (f fixp).
unfold fixp.
apply Ole_trans with (lub (fmon_comp f iter)); auto.
Save.
Hint Resolve fixp_le.

Lemma fixp_eq : fixp == f fixp.
apply Ole_antisym; auto.
unfold fixp.
apply Ole_trans with (1:= fcont iter).
rewrite (lub_lift_left iter (S O)); auto.
Save.

Lemma fixp_inv : forall g, f g <= g -> fixp <= g.
unfold fixp; intros.
apply lub_le.
induction n; intros; auto.
simpl; apply Ole_trans with (f g); auto.
Save.*)

End Fixpoints.

Global Instance Le_fun_IntPos {A B:hSet} : Le (A -> IntPos B).
Proof.
intros f g.
refine (forall x u, (f x) u <= (g x) u).
Defined.

Lemma fun_IntPos_eq0 {A B:hSet}: forall (f g : A -> IntPos B), 
                       f = g <-> forall x, f x = g x.
Proof.
intros f g.  
split.
intros H.
rewrite H; trivial.
intros Hx.
apply path_forall; trivial. 
Qed.

Global Instance le_Intpos {A:hSet} : Le (IntPos A) := 
             fun I J => forall f, I f <= J f.

Definition IntPos_cpobot  {A:hSet} : IntPos A.
Proof.
exists (fun f => RlP_0).
+ hnf; reflexivity.
+ intros J K.
  transitivity (RlP_plus RlP_0 RlP_0).
  rewrite RlPPlus_left_id.
  reflexivity.
  reflexivity.  
+ hnf.
  intros q Hq; unfold semi_decide in *. 
  simpl in *; unfold semi_decide in *.
  destruct (decide (q < 0)).
  destruct (decide (q < 1)).
  trivial.
  assert (Hnn : q < 1).
  transitivity Qzero.
  trivial.
  apply lt_0_1.
  case (n Hnn).
  destruct (decide (q < 1)).
  apply top_greatest.
  trivial.
+ intros a b C.
  reflexivity. 
Defined.

Definition IntPos_cpolub  {A:hSet} : (nat -> IntPos A) 
                                      -> IntPos A.
Proof.
intros F.
exists (fun f => RllubPos (fun n => F n f)).
+ hnf. 
  apply (antisymmetry Rllepos).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    rewrite I_def.
    intros H; trivial.
  - transitivity ((F 0) (fzero A)).
    rewrite I_def; simpl.
    reflexivity.
    apply (RllubPos_lub 
       (fun n => (F n) (fzero A)) 0).
+ intros f g.
  apply (antisymmetry Rllepos).
  admit. admit.
+ hnf.
  intros q Hq.
  apply top_le_enumerable_sup in Hq.
  revert Hq; simpl; apply (Trunc_ind _).
  intros (n,Hn); unfold semi_decide, toRlseq in *.
  assert (Hk : val RlP_1 q).
  revert Hn; apply RC_mon with Qle.
  intros x y; apply (antisymmetry Qle).
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_prob.
  simpl in Hk; trivial.
+ intros f g Hfg.
  apply Rllub_mon.
  intros n; unfold toRlseq.
  apply I_mon; trivial.      
Admitted. 

Global Instance Cpo_IntPos {A:hSet} : cpo (IntPos A).
Proof.
exists IntPos_cpobot IntPos_cpolub.
+ intros f n.
  admit.
+ admit.
+ intros x; simpl.
  unfold IntPos_cpobot.
  intros z; simpl.
  intros q Hq.
  simpl in Hq; unfold semi_decide in Hq.
  destruct (decide (q < 0)).
  apply rlpos; trivial.
  apply not_bot in Hq; case Hq.   
Admitted. 
  
Global Instance Cpo_fun_IntPos {A B:hSet} : cpo (A -> IntPos B).
Proof.
exists (fun x:A => cpobot)
       (fun f:(nat -> (A -> IntPos B)) => 
       (fun x:A => lub (fun n => f n x))).
+ intros f n.
  intros x u.
  generalize (@le_lub (IntPos B) le_Intpos Cpo_IntPos
             (fun n => f n x)).
  intros XG; apply XG.
+ intros f n.
  intros Hx x u.
  generalize (@lub_le (IntPos B) le_Intpos Cpo_IntPos
             (fun n => f n x)).
  intros XG; apply XG.
  intros m.
  specialize (Hx m x).
  trivial.
+ intros X.
  intros f u.
  assert (Hu : cpobot <= X f).
  apply cpobot_bot.
  apply Hu.
Defined.

Definition Mfix {A B:hSet} (F: (A -> IntPos B) -> A -> IntPos B) 
                 : A -> IntPos B := fixp F.

Definition Fiter  : (nat -> IntPos nat) -> (nat -> IntPos nat)
    := (fun f x => Mif flip (f (S x)) (unit nat x)).

Definition iterflip : nat -> IntPos nat := Mfix Fiter.