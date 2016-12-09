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

Section monotonic_def. 

Context {A : hSet}.
Context {LA : Le A}.
Context {B : hSet}.
Context {LB : Le B}.


Definition monotonic  {OA : PartialOrder LA}
                     {OB : PartialOrder LB}
                     (f : A -> B) := forall x y, x <= y -> f x <= f y.

Hint Unfold monotonic.

Record fmono {OA : PartialOrder  LA}
             {OB : PartialOrder  LB} : Type :=
              mk_fmono{ fmonot :> A -> B;
                        fmonotonic: monotonic fmonot}.
Hint Resolve fmonotonic.

Definition fmon {OA : PartialOrder LA}
                {OB : PartialOrder LB} : Le fmono.
refine (fun f g:fmono => BuildhProp (forall x, fmonot f x <= fmonot g x)).
Defined.

Definition fmonP {OA : PartialOrder LA}
                 {OB : PartialOrder LB} : PartialOrder fmon. 
Proof.
split. 
+ admit. 
+ intros x y. 
  apply _. 
+ split. 
  - intros f x. red; unfold fmon. 
    destruct OB. apply po_preorder.
  - intros f g h Hfg Hgh x. red; unfold fmon. 
    destruct OB. destruct po_preorder.
    apply (PreOrder_Transitive (f x) (h x)). 
    transitivity (g x).
    apply (Hfg x). apply (Hgh x). 
    reflexivity. 
+ hnf; intros f g Hf Hg. destruct f as (f,Hff).
  destruct g as (g,Hgg). apply hprop_allpath. 
  admit. 
Admitted.

End monotonic_def. 

(* No use for the moment 
Section seq_lift. 

Definition seq_lift_right {O} (f:nat -> O) n : nat -> O := fun k => f (k+n)%nat.

Definition mon_seq_lift_right : forall n (A :hSet) (LA : Le A)
                       (OA:PartialOrder LA) (f:nat -> A) {m:monotonic f},
                        monotonic (seq_lift_right f n).
Proof. 
intros n A LA OA f Hf x y Hxy. 
unfold monotonic in *; simpl in *. 
unfold seq_lift_right. 
apply Hf. induction n.
+ transitivity (Peano.plus x 0). reflexivity.
  transitivity (Peano.plus y 0).
  repeat rewrite <- Peano.plus_n_O; trivial.  
  reflexivity. 
+ admit.
Admitted. 

Infix "-m>" := fmono (at level 30, right associativity). 

End seq_lift.  *)
                                                        
Class cpo C LC {ordA : PartialOrder LC} := {
     cpobot : C; 
     lub : forall (f : nat -> C), C; 
     le_lub : forall (f : nat -> C) n, f n <= lub f; 
     lub_le : forall (f : nat -> C) x, (forall n, f n <= x)
                                             -> lub f <= x  
}.   

Lemma lub_le_compat : forall `{c : cpo C} (f g : nat -> C),
                      (forall x, f x <= g x) -> lub f <= lub g. 
Proof.                              
intros C Cle oC cC f g Hfg.
apply lub_le. 
intros n.
transitivity (g n).
apply Hfg. 
apply le_lub. 
Qed. 

Definition lub_fun {B} `{c : cpo A} (h : nat -> (B -> A)) : B -> A
                       := fun x => lub (fun n => (h n x)). 

Global Instance fle {A} {LeA : Le A} {ordA : PartialOrder LeA} `{c : cpo B}
  : Le (A -> B).
Proof. 
intros f g. 
refine (forall x, f x <= g x).
Defined.
  (*
Lemma lub_lift_right : forall A (LA : Le A) (OA : PartialOrder LA)
                              (CA:cpo _ LA) (f:nat -> A) n, monotonic f -> 
                             (@lub A LA OA CA) f = (@lub A LA OA CA) (seq_lift_right f n).
Proof. 
intros A LA OA CA U n Hf.   
unfold seq_lift_right.
destruct CA; unfold lub.
apply (antisymmetry le). 
apply lub_le0. 
intros m. 
transitivity (U (m + n)). 
apply Hf. 
induction n.
transitivity (Peano.plus m 0).
rewrite <- Peano.plus_n_O. 
reflexivity.
reflexivity. Search Peano.plus.
transitivity (Peano.plus m (S n)).
rewrite <- Peano.plus_n_Sm. 
transitivity (m + n).
transitivity (Peano.plus m n). 
auto. reflexivity.
transitivity (Peano.plus m n). 
reflexivity.
apply Peano.le_S. 
reflexivity. 
reflexivity. 
Admitted.

Hint Resolve lub_lift_right.*)



Context `{Univalence} `{Funext}.  

Class continuity `{c1 : cpo A1} `{c2 : cpo A2} (f : A1 -> A2) :=
  cont : forall (h : nat -> A1), f (lub h) <= lub (fun n => (f (h n))). 
(*
Instance lub_continuous `{c1:cpo D1} `{c2:cpo D2} `{Lef :Le (D1 -> D2)}
     (Of : PartialOrder Lef) (Cpf : cpo (D1 -> D2) Lef)
     (f:nat -> (D1 -> D2)) {cf:forall n, continuity (f n)} : continuity (lub f).
Proof. 
unfold continuity in *. 
intros h.
destruct Cpf. 
simpl. destruct c1, c2. 
simpl in *.
Admitted. *)

Record fcont `{c1:cpo D1} `{c2:cpo D2}: Type
     := mk_fc {fcontm :> D1 -> D2; fcontinuous : continuity fcontm}.

Hint Resolve @fcontinuous.