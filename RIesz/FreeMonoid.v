
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

(** * Free modular monoid on the open subsets of a set **)

(** - Free monoid on (OS A): 
           all the finite sets of elements of OS A, modulo commutativity
           :: is the monoidal operator
    - Free modular monoid on (OS A): 
           free monoid such that forall U, V in OS A, 
           U::V::l <-> meet U V::join U V::l *)

Section Bags_equiv.
  
  
(** Coquand-Spitters, Vickers build the set of simple functions to define the integral from a measure; they both use the Tarski's free monoid quotiented by a modularity law. 
Here we provide the construction of the free monoid using bag equivalence (see Danielson : http://www.cse.chalmers.se/~nad/publications/danielsson-bag-equivalence.pdf)
*)

(** Free modular monoid on a type T*)
Variable T : Type.
Context {T_isset : IsHSet T}.

(** equivalence relation for commutativity*)
Fixpoint Any (l : list T) (P : T -> Type) : Type := match l with
              | nil => False
              | cons x q => (P x) \/ (Any q P)
         end.                         

Definition EqT := fun (a b: T) => a = b.
Definition App (l: list T) (s : T) := (Any l (EqT s)).

Definition eq_bag := fun l1 l2 => forall r,
                      merely ((App l1 r) <~> (App l2 r)). 

 
Definition free_mon : Type := @quotient _ eq_bag _. 

(** T should be a lattice *)
Context {Tjoin : Join T}.
Context {Tmeet : Meet T}.
Context {Tlatt : Lattice T}.

(** equivalence relation for modularity*)
Fixpoint Any2 (l : list T) (P : T -> T -> Type) : Type := match l with
              | nil => False
              | cons x nil => False
              | cons x (cons y q) => (P x y) \/ (Any2 q P)
         end.    

Definition EqT2 := fun (a b c d : T) => a = c /\ b = d.

Definition App2 (l : list T) (s t : T) := (Any2 l (EqT2 s t)).

Definition eq_mod := fun l1 l2 => forall r s,
          merely (App2 l1 r s <~>
                  App2 l2 (Tmeet r s) (Tjoin r s)).

Definition eq_free_mod := fun l1 l2 => eq_bag l1 l2 /\ eq_mod l1 l2. 

(** Free modular monoid using HoTT quotient *)
Definition modular_mon : Type := @quotient _ eq_free_mod _.  

End Bags_equiv. 



