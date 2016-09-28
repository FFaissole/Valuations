(** A categorical a la Kleisli's definition of monad **)

Require Export Overture.
Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Require Import HoTT.Categories.
Require Import HoTT.HSet.
Require Import HoTT.Categories.SetCategory.
Require Import HoTT.Types.Bool.
Require Import Category.Core Category.Strict.
Require Import HoTT.Basics.Trunc HProp HSet Types.Universe UnivalenceImpliesFunext TruncType.

Record Monad (C : PreCategory) :=  {
                     T :> object C -> object C ;
                     eta : forall A : object C, morphism C A (T A) ;
                     star : forall (A B : object C)
                       (f : (morphism C A (T B))), (morphism C (T A) (T B)) ;  
                     rule1 : forall A : object C,
                        star A A (eta A) = identity (T A); 
                     rule2 : forall (A B : object C) (f : morphism C A (T B)),
                         compose (star A B f) (eta A) = f;
                     rule3 : forall (A B D : object C) (f : morphism C A (T B))
                          (g : morphism C B (T D)),
                         compose (star B D g) (star A B f)
                         = star A D (compose (star B D g) f)}.
