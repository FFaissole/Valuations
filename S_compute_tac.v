
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.premetric
               HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient Spaces.Nat.

Require Import HoTTClasses.sierpinsky partiality dedekind.

Require Export Rlow Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Flip Random.


              
Set Implicit Arguments.
Close Scope nat. 

(** A little tactic to compute with partial values *)


Lemma inc_seq_dec_r_prop (m : nat) A {La : Le A}
           (f : IncreasingSequence A) : forall p, 
               La ((fun n => f (n + m)%nat) p)
                  ((fun n => f (n + m)%nat) (S p)).
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


Ltac S_compute_aux n := tryif (assumption || apply top_greatest) then 
                     idtac else (
                     apply top_le_sup; 
                     apply tr; exists n; simpl; 
                     assumption || apply top_greatest). 

Ltac S_compute n := 
         tryif (S_compute_aux n) then 
               idtac else (rewrite (sup_dec_r n); S_compute n).
  

Definition switch : OS bool -> OS bool.
Proof.
intros U [].
refine (U false).
refine (U true).
Defined.

Definition Utrue : OS bool := fun x:bool => match x with 
        | true => SierTop
        | false => SierBot
end.

Definition seq_sier : OS nat := 
   fun x:nat => match x with 
        | O => SierBot 
        | S O => SierBot 
        | S (S O) => SierBot 
        | S (S (S O))  => SierBot 
        | S (S (S (S O))) => SierBot 
        | S (S (S (S (S O)))) => SierBot 
        | S (S (S (S (S (S O))))) => SierBot 
        | S (S (S (S (S (S (S O)))))) => SierBot 
        | S (S (S (S (S (S (S (S O))))))) => SierBot 
        | _ => SierTop
end.


Definition seq_sier_mon : IncreasingSequence Sier.
Proof.
exists seq_sier.
intros n.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; reflexivity.
induction n.
simpl; apply top_greatest.
simpl; reflexivity. 
Defined.


Lemma switch_compute : forall U : OS bool, 
         IsTop (switch (Utrue) false). 
Proof.
intros x; simpl.
S_compute O. 
Qed. 

Lemma seq_compute : IsTop (sup Unit (seq_sier_mon)).
Proof. 
S_compute (S O).
Qed. 

Definition open_b (b: bool) : OS bool := fun x => match b with 
      | true => match x with 
             | true => SierTop 
             | false => SierBot
        end
      | false => match x with 
             | true => SierBot
             | false => SierTop
        end 
end.


                  
                                



