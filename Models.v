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

(*
Lemma dominance_correct : forall (p : Type) (s : Sier),
          (IsTop s -> p) -> IsTop (Dominance s p) <-> (IsTop s /\ p). 
Admitted. *)

Lemma Phao_mon : forall (f : Sier -> Sier), (forall x y, x <= y -> f x <= f y)
                                           -> Phao f.  
Proof.
intros f Hf. 
unfold Phao.   
intros u.
split; intros H.
revert H.
revert u. 
apply (partial_ind0 _ (fun s  =>  _ -> _)).
+ intros [] Hx. 
  specialize (Hf SierBot SierTop). 
  assert (Hf' : SierBot <= SierTop). 
  apply top_greatest. specialize (Hf Hf'). clear Hf'. 
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

Inductive bars (a : (nat -> option bool)) : (list (list bool)) -> Prop :=
      | bars_empty : bars a nil
      | bars_head : forall c, bars_aux c a -> bars a (cons c nil)
      | bars_tail : forall c l, bars a l -> bars a (cons c l). 




