(*** Some definitions for models, axioms, further work ***)

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

(* Phoa's principle *)
Definition Phoa (f : Sier -> Sier) := forall (u : Sier), 
    (f u) <-> join (meet (f SierTop) u) (f SierBot).

(* Proof of the dominance *)
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


(* to move ==> some continuity auxiliar definitions *)
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
     (sup Unit ((IncreasingSeq_f f H u))) = f (sup Unit u).


(* Definition of N with point at infinity*)
Record No := mkNo{
                 u :> nat -> bool;
                 Hno : forall n, u n = false -> u (n+1) = false    
            }.

(* infinity *)
Definition infNo : No. 
exists (fun n => true); auto.    
Defined. 

(* WSO principle *)
Definition WSO := forall (O : No -> Sier), O (infNo)
    -> exists un : No, (O un) /\ (exists p, (un p) = false).  


(* a beginning of definitions to state the Fan's principle, 
but I'm not entirely satisfied *)
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
