Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

Require Import Qaxioms LowerR Distr Dedekind_pos.

Set Implicit Arguments.  

Definition Phao (f : Sier -> Sier) := forall (u : Sier), 
    (f u) <-> join (meet (f SierTop) u) (f SierBot).

Definition Dominance : forall (s : Sier) (p : Type), Sier.  
Proof.
intros s p.   
revert s; apply (partial_rec Unit _ le).   
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
+ intros _; exact SierTop. 
+ exact bottom. 
+ intros f Hf. 
  apply sup.
  exists f. exact Hf. 
+ reflexivity.
+ apply bot_least.   
+ intros ss pp xx IH;apply (sup_le_l _ _ _ IH). 
+ intros ss pp xx IH; apply sup_le_r. apply IH.  
Defined. 

Definition IncreasingSeq_f (f : Sier -> Sier)
                  (H : forall x y, x <= y -> f x <= f y)
                  (u : IncreasingSequence Sier) : IncreasingSequence Sier.
Proof.
exists (fun n => f (u n)). 
intros n. 
apply H; apply u. 
Defined.

Lemma IncreasingSeq_f_simpl : forall (f : Sier -> Sier) 
    (H : forall x y, x <= y -> f x <= f y), forall n u, IncreasingSeq_f f H u n = f (u n).
Proof. 
intros f H n u. 
unfold IncreasingSeq_f. 
reflexivity. 
Qed.

Definition scott_mon_sier (f : Sier -> Sier) (H : forall x y, x <= y-> f x <= f y) :=
  forall (u : IncreasingSequence Sier),
    f (sup Unit u) = (sup Unit ((IncreasingSeq_f f H u))).

Lemma Phao_mon : forall (f : Sier -> Sier) (Hm : forall x y, x <= y -> f x <= f y),
          (scott_mon_sier f Hm)  -> Phao f.  
Proof.
intros f Hf Hm. 
unfold Phao.   
intros u.
split; intros H.
revert H.
revert u. 
apply (partial_ind0 _ (fun s  =>  _ -> _)).
+ intros [] Hx.
  pose (HfO := Hf). 
  specialize (HfO SierBot SierTop). 
  assert (Hf' : SierBot <= SierTop). 
  apply top_greatest. specialize (HfO Hf'). clear Hf'. 
  assert (Hf2 : f SierBot <= eta Unit tt).   
  apply top_greatest. 
  assert (Hff : f SierBot <= (f SierTop ⊓ eta Unit tt)). 
  apply imply_le.
  intros Hu. 
  apply top_le_meet.
  split. 
  - trivial.  
  - apply SierLe_imply in Hf2; trivial.
  - apply top_le_join. apply tr.
    left.     
    apply top_le_meet. 
    split; try trivial. 
    apply top_greatest. 
+ intros Hx. 
  apply top_le_join.
  apply tr. right.         
  trivial.     
+ intros g H0 H1. 
  unfold scott_mon_sier in Hm. 
  specialize (Hm g).
  rewrite Hm in H1. 
  apply top_le_join. apply tr.     
  left.
  apply top_le_meet.
  split. 
  admit. 
  admit. 
Admitted.

Record No := mkNo{
                 u :> nat -> bool;
                 Hno : forall n, u n = false -> u (n+1) = false             
            }.

Definition infNo : No. 
Proof.
exists (fun n => true). auto.    
Defined. 

Definition WSO := forall (O : No -> Sier), O (infNo)
    -> exists un : No, (O un) /\ (exists p, (un p) = false).  

Fixpoint nth (n:nat) (l:list bool) {struct l} : option bool :=
    match n, l with
      | O, cons x l' => Some x
      | O, other => None
      | S m, nil => None 
      | S m, cons x t => nth m t
    end.

Definition bars_aux (l : list bool) (a : nat -> option bool)
                   := exists (n:nat), a n = nth n l. 

Inductive bars (a : (nat -> option bool)) : (list (list bool)) -> Type :=
      | bars_empty : bars a nil
      | bars_head : forall c, bars_aux c a -> bars a (cons c nil)
      | bars_tail : forall c l, bars a l -> bars a (cons c l).

Definition subovert (a : nat -> option bool) l (x : bars a l) : Type. 
induction x. 
+ refine True.
Admitted. 





