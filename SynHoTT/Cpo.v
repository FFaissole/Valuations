
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               partiality
               sierpinsky
               dedekind. 

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 

(** * Definition of wCpo on A:hSet *)


Section Mono.

Context {A : hSet}.
Context {LA : Le A}.
Context {B : hSet}.
Context {LB : Le B}.

Definition monotonic  {OA : PartialOrder LA}
                     {OB : PartialOrder LB}
                     (f : A -> B) := forall (x y:A), 
                                 LA x y -> LB (f x) (f y).


Record fmono {OA : PartialOrder  LA}
             {OB : PartialOrder  LB} : Type :=
              mk_fmono{ fmonot :> A -> B;
                        fmonotonic: monotonic fmonot}.

Definition fmon {OA : PartialOrder LA}
                {OB : PartialOrder LB} : Le fmono.
Proof.
refine (fun f g:fmono => BuildhProp (forall x, LB (fmonot f x) (fmonot g x))).
Defined.

End Mono.

Section Cpo.

Context {A : hSet}.
Context {LA : Le A}.
Context {B : hSet}.
Context {LB : Le B}.
                                   
Class cpo C {LC : Le C} := mkcpo{
     cpobot : C;
     lub : forall (f : IncreasingSequence C), C; 
     le_lub : forall (f : IncreasingSequence C) n, 
                                      LC (f n) (lub f); 
     lub_le : forall (f : IncreasingSequence C) x, 
               (forall n, LC (f n) x) -> LC (lub f) x ;
     cpobot_bot : forall x, LC cpobot x    
}.

End Cpo.
   
