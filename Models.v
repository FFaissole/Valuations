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

Require Import LowerR Distr Dedekind_pos.

Set Implicit Arguments.  

Definition Phao (f : Sier -> Sier) := forall (u : Sier), 
    (f u) <-> join (meet (f SierTop) u) (f SierBot).

Definition Dominance := forall (s : Sier) (p : Type),
           (IsTop s -> p) -> (exists v, IsTop v = (IsTop s) /\ p). 

Lemma Dom : Dominance. 
Proof.
intros s p H.
generalize (partial_rec Unit Sier SierLe).
Admitted.

Definition Scott_cont (A B : Type) : (A -> B) -> Type.
Admitted.

Lemma Phao_scott : forall (f : Sier -> Sier), Scott_cont f -> Phao f.  
Proof. 
Admitted. 

(* dominance : how to express it ? *)

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

Search list. 

Fixpoint nth (n:nat) (l:list bool) {struct l} : option bool :=
    match n, l with
      | O, cons x l' => Some x
      | O, other => None
      | S m, nil => None 
      | S m, cons x t => nth m t
    end.

Definition bars_aux (l : list bool) (a : nat -> option bool) (n : nat) :=
                a n = nth n l. 

(*
Inductive bars (a : (nat -> option bool)) : (list (list bool)) -> Prop :=
          | bars_empty : bars a nil
          | bars_coll : forall c l, exists n:nat, (bars_aux c a n)
          | bars_coll2 : forall c l, bars a l end. 
          
Definition Fan := forall (u : nat -> bool), 
)*)
