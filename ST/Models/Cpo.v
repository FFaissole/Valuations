
Add Rec LoadPath "~/Documents/HoTTClasses/".
Add Rec LoadPath "~/Documents/CoqPL/".

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties. 


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
                                   
Class cpo C LC {ordA : PartialOrder LC} := {
     cpobot : C; 
     lub : forall (f : nat -> C), C; 
     le_lub : forall (f : nat -> C) n, f n <= lub f; 
     lub_le : forall (f : nat -> C) x, (forall n, f n <= x)
                                             -> lub f <= x  
}.   
