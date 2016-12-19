
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

Section Simples. 
Context {A : hSet}. 

Definition qn (n : nat) := pos (pos_of_nat n). 

Fixpoint sum_prod_sub (p : nat) (f : mf A) (m :D A) 
         {struct p} : RlowPos := match p with
           | 0 => RlP_0
           | S p => (sum_prod_sub p f m) + 
              ((mu _ m) (D_op (qn (S p)) f))
     end.                         

Definition sum_p_r (N : nat) (f :  mf A) (m : D A) :=
                Rlow_mult_q (1/(qn N)) (sum_prod_sub N f m). 

Lemma sum_p_r_prod : forall q S mm,
    Rlow_mult_q (1 / (qn q)) (sum_prod_sub q S mm) =
    Rlow_mult_q 1 (sum_prod_sub 1 S mm).
Proof.
intros q S mm.
Admitted.

Lemma Rlow_mult_q_mon_f : forall q n f g mm, f <= g -> 
    Rlow_mult_q q (sum_prod_sub n f mm) <=
    Rlow_mult_q q (sum_prod_sub n g mm).
Proof.
intros q n f g mm Hfg s.
Admitted.


Definition I_mu (mm : D A) : IntPos A.
Proof.
exists (fun f => RllubPos (fun n => (sum_p_r n f mm))); red. 
+ assert (HO : forall n, sum_p_r n (fzero A) mm = RlP_0).
  * induction 0; unfold sum_p_r.
    - simpl; unfold qn, pos_of_nat; simpl.
      rewrite Rlow_mult_q_RlP_0.     
      reflexivity.
    - simpl. unfold sum_p_r in IHn.
      unfold D_op. 
      unfold fzero; simpl.
      unfold semi_decide. 
      destruct (decide (qn (S n) < 0)). 
      unfold qn in l.
      destruct (pos_of_nat (S n)).
      simpl in l.
      generalize (pseudo_order_antisym Qzero pos).
      intros F.
      assert (False).
      apply F.
      split; trivial.
      case H.
      rewrite mu_empty_op. 
      unfold plus. 
      rewrite RlPPlus_comm, RlPPlus_left_id.
      admit. (* faisable mais long et chiant *)                   
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
  apply RllubPos_le.
  intros n. unfold Rlle, RCLe_l.
  intros q Hq1. apply pred_plus_pr.
  apply tr.
  unfold fplus in Hq1.
  unfold sum_p_r in *.
  unfold sum_prod_sub in *.
  admit.
  
  intros n.
  admit.
  (* moins trivial *)
     
+ apply Rllub_le. 
  intros n. 
  unfold sum_p_r. 
  unfold toRlseq.
  rewrite sum_p_r_prod. 
  simpl.
  assert (Hl : (RlP_0 + mu _ mm (D_op (qn 1) (fone A))) =
               RlP_plus RlP_0 (mu _ mm (D_op (qn 1) (fone A)))).
  reflexivity. rewrite Hl. clear Hl.
  rewrite RlPPlus_left_id.
  unfold D_op; simpl.  
  unfold semi_decide.
  destruct (decide (qn 1 < 1)).
  assert (1 <= qn 1).
  reflexivity.
  apply orders.lt_not_le_flip in l.
  case (l X).
  rewrite mu_empty_op.
  rewrite Rlow_mult_q_RlP_0.
  simpl. exact Rlle_O_I. 
+ intros f g Hfg. 
  apply Rllub_mon. 
  intros n. 
  unfold toRlseq.
  induction n. 
  * unfold sum_p_r; simpl. 
    unfold Rlle, RCLe_l; auto.  
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
Admitted.


End Simples. 
