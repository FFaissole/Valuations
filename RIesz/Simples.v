Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Spaces".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Theories".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Orders".


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

Definition I_mu (mm : D A) : IntPos A.
Proof.
exists (fun f => RllubPos (fun n => (sum_p_r n f mm))); red. 
+ assert (HO : forall n, sum_p_r n (fzero A) mm = RlP_0).
  * induction 0; unfold sum_p_r.
    - simpl; unfold qn, pos_of_nat; simpl. 
      assert (H11: 1/1 = 1). admit.

      rewrite H11.
      rewrite Rlow_mult_q1.
      reflexivity. 
    - simpl. unfold sum_p_r in IHn.
      unfold D_op. 
      unfold fzero; simpl.
      unfold semi_decide. 
      destruct (decide (qn (S n) < 0)). 
      unfold qn in l.       
      unfold pos in l. 
      simpl in l. 
      admit. (* ok *)

      rewrite mu_empty_op. 
      (*rewrite Rlow_mult_q_RlP_0.*)
      unfold plus. 
      rewrite RlPPlus_comm, RlPPlus_left_id.
      admit. (* it's ok *)
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
  admit.
  
  intros n.   
  unfold sum_p_r, sum_prod_sub.    
  admit.    
+ apply Rllub_le. 
  intros n. 
  unfold sum_p_r. 
  unfold toRlseq. 
  admit. (* ok*)
+ intros f g Hfg. 
  apply Rllub_mon. 
  intros n. 
  unfold toRlseq.
  induction n. 
  * unfold sum_p_r; simpl. 
    unfold Rlle, RCLe_l; auto.  
  * unfold sum_p_r.
    admit. 
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
  admit. (* ok *)

  rewrite Hi in Hv. 
  trivial.  
Admitted.

Lemma I_mu_simpl (mm : D A) : I (I_mu mm) = (fun f =>
           RllubPos (fun n => (sum_p_r n f mm))).
Admitted.

End Simples. 