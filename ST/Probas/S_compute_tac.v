
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
               HIT.quotient Spaces.Nat.

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1.
              
Set Implicit Arguments.
Close Scope nat. 

Lemma inc_seq_dec_r_prop (m : nat) A {La : Le A}
           (f : IncreasingSequence A) : (forall p, 
             (fun n => f (n + m)%nat) p 
          <= (fun n => f (n + m)%nat) (S p)).
Proof.
intros p; apply f.
Qed.

Definition inc_seq_dec_r (m : nat) A {La : Le A} 
            {Pa : PartialOrder La}
           (f : IncreasingSequence A) : IncreasingSequence A := 
      Build_IncreasingSequence (fun n => f (n + m)%nat) 
                (inc_seq_dec_r_prop m f).

Lemma sup_dec_r (m : nat) : forall f, 
        sup Unit f = sup Unit (inc_seq_dec_r m f).
Proof.
intros f.
apply (antisymmetry SierLe).
+ apply imply_le.
  intros Hs.
  apply top_le_sup in Hs; 
  apply top_le_sup.
  revert Hs; apply (Trunc_ind _); 
  intros (n,Hn).
  apply tr.
  exists n; simpl.
  revert Hn; 
  apply SierLe_imply.
  apply seq_increasing_le.
  induction m.
  - rewrite <- nat_plus_n_O; 
    reflexivity.
  - transitivity (n + m)%nat; 
    trivial.
    rewrite <- nat_plus_n_Sm.
    apply le_S; reflexivity.
+ apply imply_le.
  intros Hs.
  apply top_le_sup in Hs; 
  apply top_le_sup.
  revert Hs; apply (Trunc_ind _); 
  intros (n,Hn).
  apply tr.
  exists (n + m)%nat; 
  simpl in *; trivial. 
Qed.
            
Ltac S_compute n := match goal with 
          | [H : _ |- IsTop SierTop] => apply top_greatest
          | [H :_ |- IsTop (sup Unit _)] => match n with 
              | _ => (tryif (apply top_le_sup; 
                     apply tr; exists n; assumption) 
                     then idtac else 
                     (timeout 4 (rewrite (sup_dec_r n)); 
                     S_compute n))
              end
end.
