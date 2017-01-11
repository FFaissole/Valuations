Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               hit.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals D_op OpenFun. 

Set Implicit Arguments. 

Section Sum_p_r.
(** *   *)
Variable (A : hSet). 

Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n). 

(** sum_prod_sub: sum before rationalization*) 
Fixpoint sum_prod_sub (p : nat) (f : mf A) (m :Val A) 
         {struct p} : RlowPos := match p with
           | 0 => (mu _ m) (D_op 0 f)
           | S p => (sum_prod_sub p f m) + 
              ((mu _ m) (D_op (qn (S p)) f))
     end.                         

(** sum_p_r: sum after rationalization*) 
Definition sum_p_r (N : nat) (f :  mf A) (m : Val A) := match N with
           | 0 => (mu _ m) (D_op 0 f)
           | S p => Rlow_mult_q (1/(qnp (S N))) (sum_prod_sub (S N) f m) end.

(** Properties of sum_p_r *)
Lemma sum_p_r_prod : forall q S mm, 0 < q -> 
    Rlow_mult_q (1 / (qnp q)) (sum_prod_sub q S mm) =
    Rlow_mult_q 1 (sum_prod_sub 1 S mm).
Proof.
intros n f mm.
induction n.
+ intros H1.
  assert (Hr : O <= O).
  reflexivity.
  apply orders.le_not_lt_flip in Hr.
  case (Hr H1).
+ intros Hs0; clear Hs0.
  apply (antisymmetry le).
  - intros q Hq.
    unfold Rlow_mult_q in *;
    unfold pred_multQ in *. 
    simpl.
    simpl in Hq.
    simpl in IHn.
    unfold pred_multQ in *. 
    simpl in IHn.
(* cumbersome *)
Admitted.


Lemma sum_prod_sub_mon_f : forall n f g mm, f <= g -> 
      sum_prod_sub n f mm <= sum_prod_sub n g mm.
Proof.
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+ simpl.
  transitivity (sum_prod_sub n f mm
                + mu _ mm (D_op (qn (S n)) g)).
  apply Rllepos_plus_le_preserving.
  apply mu_mon.
  apply D_op_mon_f; trivial.  
  unfold plus.
  rewrite RlPPlus_comm.
  rewrite (RlPPlus_comm (sum_prod_sub n g mm) _).
  apply Rllepos_plus_le_preserving.
  trivial.
Qed.

Lemma sum_p_r_mon_f : forall n f g mm, f <= g -> 
      sum_p_r n f mm <= sum_p_r n g mm.
Proof.
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+ simpl.
Admitted. 
  
Lemma Rlow_mult_q_mon_f : forall q n f g mm, f <= g -> 
    Rlow_mult_q q (sum_prod_sub n f mm) <=
    Rlow_mult_q q (sum_prod_sub n g mm).
Proof.
intros q n f g mm Hfg s Hs.
unfold Rlow_mult_q in *.  
simpl in *. unfold pred_multQ in *.
apply RC_mon with Qle (rl (sum_prod_sub n f mm))
                      (pos q * s).
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply sum_prod_sub_mon_f; trivial.
trivial.
Qed.

Lemma toRlseq_antimon' : forall n Mu f,
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) (S n))
    <=
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) n).
Proof.
intros n Mu U.  
unfold toRlseq.
intros q Hq.
induction n.
+ unfold sum_p_r in *.
  unfold Rlow_mult_q in Hq.
  unfold pred_multQ in Hq.
  simpl in Hq. 
  apply pred_plus_pr in Hq.
  revert Hq; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  apply pred_plus_pr in E1.
  revert E1; apply (Trunc_ind _).
  intros (r1,(r2,(E11,(E12,E13)))).
  assert (Hpos : forall q : Q+, pos (1 / q) = pos q).
  admit.  

  rewrite Hpos in E3.
  simpl in E3.
  rewrite E13 in E3.
  assert (H2 : 2*q = r1 + r2 + s).
  apply E3.
  clear E3.
  assert (H4 : q = (r1 + r2 + s) / 2).
  admit.

  rewrite H4.
  apply RC_le with Qle r1.
  intros x y; apply (antisymmetry le).
  intros x y; apply orders.le_or_lt.
  trivial.
  admit.

+ simpl.
  unfold pred_multQ.
  assert (Hpos : forall q : Q+, pos (1 / q) = pos q).
  admit.  

  rewrite Hpos.
  simpl.
  simpl in Hq.
  unfold pred_multQ in Hq.
  rewrite Hpos in Hq; simpl in Hq.
  apply pred_plus_pr in Hq.
  revert Hq; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  apply pred_plus_pr in E1.
  revert E1; apply (Trunc_ind _).
  intros (r1,(r2,(E11,(E12,E13)))).

  
  admit.
Admitted.

Lemma sum_p_r_add : forall n f g mm, 
    sum_p_r n f mm + sum_p_r n g mm =
    sum_p_r n (fun x => f x + g x) mm. 
Proof.
intros n f g mm.
induction n.  
+ simpl.
  apply (antisymmetry le).
  - intros q Hq.
    unfold D_op in *.
    simpl in *.
    apply pred_plus_pr in Hq.
    revert Hq; apply (Trunc_ind _).
    intros (r,(s,(E1,(E2,E3)))).

    admit. (* add mu*)

    
  - intros q Hq.
    apply pred_plus_pr.
    apply tr.
    
    admit.   (* add mu*)
    
+ apply (antisymmetry le).
  intros q Hq.

  admit.
  transitivity (sum_p_r  n f mm + sum_p_r n g mm).
  rewrite IHn.
  apply toRlseq_antimon'.
    
  admit. 
Admitted.


(* OK *)
Lemma toRlseq_antimon : forall n n' Mu f, n <= n' -> 
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) n')
    <=
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) n).
Proof.
intros n n' Mu f Hnn'.
assert (X : exists P : nat, n' = P + S n).
admit.

destruct X as (p,Hp).
induction n'.
+ assert (Hn0 : n = 0).
  apply peano_naturals.minus_ge in Hnn'.
  unfold CutMinus in Hnn'.
  assert (Hnn'' : peano_naturals.nat_cut_minus n 0 = 0).
  apply Hnn'.
  admit.

  rewrite Hn0.
  intros q; trivial.
+ rewrite Hp.
  induction p.
  assert (Ho : O + S n = S n). admit.

  rewrite Ho.
  apply toRlseq_antimon'.
  admit.

Admitted.

Lemma sum_p_r_mon_f2 : forall n f g mm, f <= g -> 
      sum_p_r n f mm <= sum_p_r n g mm.
Proof. 
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+admit. 
Admitted.


End Sum_p_r. 
