
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind. 

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
                     (f : A -> B) := forall x y, x <= y -> f x <= f y.


Record fmono {OA : PartialOrder  LA}
             {OB : PartialOrder  LB} : Type :=
              mk_fmono{ fmonot :> A -> B;
                        fmonotonic: monotonic fmonot}.

Definition fmon {OA : PartialOrder LA}
                {OB : PartialOrder LB} : Le fmono.
Proof.
refine (fun f g:fmono => BuildhProp (forall x, fmonot f x <= fmonot g x)).
Defined.

End Mono.

Section Cpo.

Context {A : hSet}.
Context {LA : Le A}.
Context {B : hSet}.
Context {LB : Le B}.
                                   
Class cpo C {ordA : Le C} := mkcpo{
     cpobot : C;
     lub : forall (f : IncreasingSequence C), C; 
     le_lub : forall (f : IncreasingSequence C) n, 
                                      f n <= lub f; 
     lub_le : forall (f : IncreasingSequence C) x, 
               (forall n, f n <= x) -> lub f <= x ;
     cpobot_bot : forall x, cpobot <= x    
}.

End Cpo.
   
