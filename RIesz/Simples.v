
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

(** * Variant of the definition of simple functions. 
We define measures of simples "functions" as sum of the
measures of the D_op corresponding to a subdivision of
size n. When n is near infinity, the measure of the
simple function approachs the integral of the function  *)

Section Simples. 
Context {A : hSet}. 

Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n). 

(** sum_prod_sub: sum before rationalization*) 
Fixpoint sum_prod_sub (p : nat) (f : mf A) (m :D A) 
         {struct p} : RlowPos := match p with
           | 0 => (mu _ m) (D_op 0 f)
           | S p => (sum_prod_sub p f m) + 
              ((mu _ m) (D_op (qn (S p)) f))
     end.                         

(** sum_p_r: sum after rationalization*) 
Definition sum_p_r (N : nat) (f :  mf A) (m : D A) := match N with
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

(** Definition of the integral from measures and 
subdivisions as classically in measure theory *)
Definition I_mu (mm : D A) : IntPos A.
Proof.
exists (fun f => RllubPos (fun n => (sum_p_r n f mm))); red. 
+ assert (HO : forall n, sum_p_r n (fzero A) mm = RlP_0).
  * induction 0; unfold sum_p_r.
    - simpl; unfold qn, pos_of_nat; simpl.
      unfold fzero.
      assert (HO : (D_op 0 (λ _ : A, RlP_0)) = OS_empty).
      unfold D_op.
      simpl. unfold semi_decide.
      destruct (decide (0 < 0)).
      assert (Hrfl : Qzero <= Qzero).
      reflexivity.
      apply orders.le_not_lt_flip in Hrfl.
      case (Hrfl l).
      reflexivity.
      rewrite HO.
      rewrite mu_empty_op.
      reflexivity.
    - unfold sum_p_r in *.
      rewrite sum_p_r_prod.
      unfold sum_prod_sub.
      unfold D_op.
      simpl. unfold semi_decide.
      destruct (decide (0 < 0)).
      apply orders.lt_not_le_flip in l. 
      assert (Hu : Qzero <= Qzero).
      reflexivity. 
      case (l Hu).
      destruct (decide (qn 1 < 0)).
      unfold qn in l.
      assert (Hl : 0 <= pos (pos_of_nat 1)).
      apply orders.lt_le.
      apply (pos_of_nat 1).
      apply orders.lt_not_le_flip in l. 
      case (l Hl).      
      rewrite mu_empty_op. unfold plus.
      rewrite RlPPlus_left_id.
      apply Rlow_mult_q_RlP_0.
      apply peano_naturals.S_gt_0.
  * apply (antisymmetry le).
    apply RllubPos_le. 
    intros n. 
    rewrite (HO n). 
    unfold Rlle, RCLe_l; auto.  
    specialize (HO 0). 
    transitivity (sum_p_r 0 (fzero A) mm).
    rewrite HO; reflexivity. 
    generalize (RllubPos_lub (λ n : nat, sum_p_r n (fzero A) mm)). 
    intros Hrl. 
    specialize (Hrl 0). 
    trivial.  
+ intros f g.
  apply (antisymmetry le).
  - intros z Hq1.
    unfold fplus in Hq1.
    assert (Hrll : (λ n : nat,
           sum_p_r n (λ x : A, RlP_plus (f x) (g x)) mm)
                  =
                 λ n : nat, sum_p_r n (λ x : A, f x) mm +
                            sum_p_r n (λ x : A, g x) mm ).
    apply path_forall. intros n.
    symmetry. apply sum_p_r_add.
    --  rewrite Hrll in Hq1.
        assert (Hlub : RllubPos (λ n : nat,
                             sum_p_r n (fplus f g) mm)
                  =
                  RllubPos (λ n : nat, sum_p_r n f mm) +
                  RllubPos (λ n : nat, sum_p_r n g mm)).
    apply (antisymmetry le). 
    --- apply Rllub_le. 
        intros n. 
        unfold toRlseq. 
        assert (H1 : Rlle ((λ n : nat, sum_p_r n
              (λ x : A, RlP_plus (f x) (g x)) mm) n)
                          ((fun n => sum_p_r n f mm + sum_p_r n g         mm) n)).
        rewrite sum_p_r_add.        
        intros q Hq; trivial.           
        simpl in H1. 
        assert (H2 : Rlle (RlPlus (sum_p_r n f mm) (sum_p_r n g mm))
          (RllubPos (λ n0 : nat, sum_p_r n0 f mm) +
           RllubPos (λ n0 : nat, sum_p_r n0 g mm))).
        assert (Hle1 : Rlle (RlPlus
                        (RllubPos (λ n0 : nat, sum_p_r n0 f mm))
                        (sum_p_r n g mm))
                     (RllubPos (λ n0 : nat, sum_p_r n0 f mm) +
              RllubPos (λ n0 : nat, sum_p_r n0 g mm))).
        apply RlPlus_le_preserving.
        apply (Rllub_lub (λ n0 : nat, sum_p_r n0 g mm) n).
        assert (Hle2 : Rlle (RlPlus (sum_p_r n f mm)
                                    (sum_p_r n g mm))
                            ((RlPlus (RllubPos (λ n0 : nat,
                                  sum_p_r n0 f mm))
                                 (sum_p_r n g mm)))).
        rewrite RlPlus_comm.
        rewrite (RlPlus_comm _ (sum_p_r n g mm)).
        apply RlPlus_le_preserving.
        apply (Rllub_lub (λ n0 : nat, sum_p_r n0 f mm) n).
        intros q Hq.
        specialize (Hle1 q).
        specialize (Hle2 q).
        apply Hle1, Hle2.
        trivial.
        unfold Rlle, RCLe_l in *. 
        intros q Hq. 
        apply H2. 
        apply H1; trivial.
    --- intros s Hs.  
        apply (RllubPos_le
              (λ n : nat, sum_p_r n (fplus f g) mm)).
        intros n. 
        apply (RllubPos_lub (λ n0 : nat, sum_p_r n0
                                                 (fplus f g) mm) n).
        rewrite Hrll; simpl; unfold toRlseq; clear Hq1.
        assert (Hpl :  elt Q Qlt
         (rl (RlP_plus (RllubPos (λ n : nat, sum_p_r n f mm))
                       (RllubPos (λ n : nat, sum_p_r n g mm)))) s).
        apply Hs; clear Hs; rewrite Hrll. 
        rewrite RlP_plus_RlPlus in Hpl.
        unfold semi_decide.
        unfold SDseq_Rlow.
        unfold semi_decide_exists.         
        unfold semi_decide.
        apply pred_plus_pr in Hpl.
        revert Hpl; apply (Trunc_ind _).         
        intros (r,(x,(Hrs1,(Hrs2,Hrs3)))).
        unfold RllubPos in Hrs1.
        simpl in Hrs1.
        unfold RllubPos in Hrs2.
        simpl in Hrs2.
        unfold semi_decide, SDseq_Rlow, semi_decide_exists,
               semi_decide in *.
        unfold toRlseq in Hrs1, Hrs2.
        apply top_le_enumerable_sup'.
        apply top_le_enumerable_sup' in Hrs1.
        apply top_le_enumerable_sup' in Hrs2.
        revert Hrs1; apply (Trunc_ind _).
        intros (s1,Hrs1).
        revert Hrs2; apply (Trunc_ind _).
        intros (s2,Hrs2).
        destruct (peano_naturals.nat_le_dec s1 s2).
        * apply tr. exists s1.            
          apply pred_plus_pr.
          apply tr.
          exists r, x.
          repeat split; trivial.
          generalize (toRlseq_antimon).
          intros HM.
          specialize (HM s1 s2 mm g).          
          apply HM; trivial.          
        * apply tr. exists s2.
          apply pred_plus_pr.
          apply tr.
          exists r, x.
          repeat split; trivial.
          generalize (toRlseq_antimon).
          intros HM.
          specialize (HM s2 s1 mm f).
          apply HM.
          apply peano_naturals.nat_not_lt_le.
          intro F.
          apply n.
          apply orders.lt_le; trivial.
          trivial.
     --- rewrite <- Hlub.
         unfold fplus. simpl.
         rewrite Hrll.
         trivial.
- intros q Hq.
  simpl in *.
  unfold toRlseq in *; simpl in *.
  assert (Hlub : RllubPos (λ n : nat, sum_p_r n (fplus f g) mm)
                  =
                  RllubPos (λ n : nat, sum_p_r n f mm) +
                  RllubPos (λ n : nat, sum_p_r n g mm)).
  apply pred_plus_pr in Hq.
  apply (antisymmetry Rllepos).
  unfold Rllepos; simpl.
  unfold toRlseq. 
  intros c Hc.
  revert Hq; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  unfold Rllub in Hc.
  simpl in Hc.
  unfold semi_decide, SDseq_Rlow, semi_decide_exists,
         semi_decide in E1, E2, Hc.
  apply top_le_enumerable_sup' in Hc.
  apply top_le_enumerable_sup' in E1.
  apply top_le_enumerable_sup' in E2.
  revert Hc; apply (Trunc_ind _).
  intros (nc,Hc).
  rewrite <- sum_p_r_add in Hc.
  apply pred_plus_pr in Hc.
  revert E1; apply (Trunc_ind _).
  intros (n1,E1).
  revert E2; apply (Trunc_ind _).
  intros (n2,E2).
  apply pred_plus_pr.
  revert Hc; apply (Trunc_ind _).
  intros (r',(s',(HC1,(HC2,HC3)))).
  apply tr.
  exists r', s'.
  repeat split; trivial.
  apply Rllub_lub with nc; trivial.
  apply Rllub_lub with nc; trivial.
  unfold Rllepos; simpl.
  unfold toRlseq. 
  intros c Hc.
  apply pred_plus_pr in Hc.
  revert Hc; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  apply top_le_enumerable_sup' in E1.
  apply top_le_enumerable_sup' in E2.
  apply top_le_enumerable_sup'.
  revert E1; apply (Trunc_ind _).
  intros (n1,E1).
  revert E2; apply (Trunc_ind _).
  intros (n2,E2).
  apply tr.
  unfold semi_decide, SDseq_Rlow, semi_decide_exists,
  semi_decide in *.
  assert (Hn : forall n : nat, sum_p_r n (fplus f g) mm =
          sum_p_r n f mm + sum_p_r n g mm).
  intros m.
  rewrite sum_p_r_add; reflexivity.
  destruct (peano_naturals.nat_le_dec n1 n2).
  * exists n1.            
    rewrite (Hn n1).
    apply pred_plus_pr.
    apply tr.
    exists r, s.
    repeat split; trivial.
    generalize (toRlseq_antimon).
    intros HM.
    specialize (HM n1 n2 mm g).          
    apply HM; trivial.          
  * exists n2. rewrite (Hn n2).
    apply pred_plus_pr.
    apply tr.
    exists r, s.
    repeat split; trivial.
    generalize (toRlseq_antimon).
    intros HM.
    specialize (HM n2 n1 mm f).
    apply HM.
    apply peano_naturals.nat_not_lt_le.
    intro F. apply n.
    apply orders.lt_le; trivial. trivial.
  * unfold semi_decide, SDseq_Rlow, semi_decide_exists,
    semi_decide in *.
    apply pred_plus_pr in Hq.
    revert Hq; apply (Trunc_ind _).
    intros (r,(s,Hq)).
    apply top_le_enumerable_sup'.
    destruct Hq as (E1,(E2,E3)).
    apply top_le_enumerable_sup' in E1.
    apply top_le_enumerable_sup' in E2.
    revert E1; apply (Trunc_ind _).
    intros (n1,E1).
    revert E2; apply (Trunc_ind _).
    intros (n2,E2).
    apply tr.
    destruct (peano_naturals.nat_le_dec n1 n2).
    ** exists n1.
       assert (Hn : forall n : nat, sum_p_r n (fplus f g) mm =
          sum_p_r n f mm + sum_p_r n g mm).
       intros m.
       rewrite sum_p_r_add; reflexivity.
       rewrite (Hn n1).
       generalize (toRlseq_antimon).
       intros HM.
       specialize (HM n1 n2 mm g).
       apply pred_plus_pr.
       apply tr.
       exists r,s.
       repeat split;trivial.
       apply HM; trivial.          
    ** exists n2.
       assert (Hn : forall n : nat, sum_p_r n (fplus f g) mm =
          sum_p_r n f mm + sum_p_r n g mm).
       intros m.
       rewrite sum_p_r_add; reflexivity.
       rewrite (Hn n2).
       apply pred_plus_pr.
       apply tr.
       exists r, s.
       repeat split; trivial.
       generalize (toRlseq_antimon).
       intros HM.
       specialize (HM n2 n1 mm f).
       apply HM.
       apply peano_naturals.nat_not_lt_le.
       intro F. apply n.
       apply orders.lt_le; trivial. trivial.
  + apply Rllub_le. 
  intros n. 
  induction n.
  - assert (Hone : D_op 0 (fone A) = Ω).
    unfold D_op; simpl.   
    apply path_forall. 
    intros z. unfold semi_decide. 
    destruct (decide (0 < 1)). 
    unfold OS_full; reflexivity.  
    assert (H01 : Qzero < Qone).
    apply semirings.lt_0_1. 
    case (n H01). unfold sum_p_r. 
    rewrite Hone.
    apply mu_prob.
  - generalize toRlseq_antimon'.
    intro HG.
    specialize (HG n mm).
    unfold toRlseq in *. 
    specialize (HG (fone A)).
    unfold le in HG. 
    unfold Rlle, RCLe_l in *. 
    intros q Hq. 
    apply IHn. 
    apply HG.
    trivial. 
+ intros f g Hfg. 
  apply Rllub_mon. 
  intros n. 
  unfold toRlseq.
  induction n. 
  * unfold sum_p_r; simpl.
    apply mu_mon.
    apply D_op_mon_f; trivial.  
  * unfold sum_p_r.
    apply Rlow_mult_q_mon_f; trivial.
+ intros f. apply (antisymmetry le). 
  apply Rllub_mon; intros n. 
  unfold toRlseq.
  intros v Hv. 
  apply Rllub_lub with n.
  unfold toRlseq; trivial.
  intros v Hv.
  assert (Hi : RllubPos (λ _ : nat,
          RllubPos (λ n0 : nat, sum_p_r n0 (λ x : A, f x) mm)) =
           RllubPos (λ n0 : nat, sum_p_r n0 (λ x : A, f x) mm)).
  apply (antisymmetry le). 
  apply Rllub_le. 
  intros m. unfold toRlseq. 
  unfold Rlle, RCLe_l; auto. 
  apply Rllub_le.  
  intros m. unfold toRlseq.
  assert (H1: (λ _ : nat,
                 RllubPos (λ n0 : nat, sum_p_r n0
                  (λ x : A, f x) mm)) 0 <=
           (RllubPos
       (λ _ : nat,
        RllubPos (λ n0 : nat, sum_p_r n0 (λ x : A, f x) mm)))
      ).
  apply (Rllub_lub (λ _ : nat,
                 RllubPos (λ n0 : nat, sum_p_r n0
                  (λ x : A, f x) mm)) 0).  
  assert (H3 : (λ _ : nat, sum_p_r m (λ x : A, f x) mm) 0 <=
   (λ _ : nat,
        RllubPos (λ n0 : nat, sum_p_r n0 (λ x : A, f x) mm)) 0).
  apply (Rllub_lub (λ n0 : nat, sum_p_r n0 (λ x : A, f x) mm) m).
  intros q. unfold Rlle in H1.
  unfold Rlle in H3.
  intros HX.
  apply H1, H3; trivial.
  rewrite Hi in Hv. 
  trivial.
Qed.


End Simples. 
