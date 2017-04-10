
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.interfaces.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric
               HoTTClasses.theory.rings
               HoTTClasses.orders.semirings
               HoTTClasses.orders.rings
               HoTTClasses.theory.dec_fields.

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export Cpo.

Section wCpo_compl.

Context {P : Type} {lP : Le P} {PP : PartialOrder lP}
        {wCP : cpo P lP}.

Context {A : hSet}.

Definition completion_map (f : A -> P) : partial A -> P.
Proof.
apply (partial_rec A _ le).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
+ intros x. exact (f x). 
+ exact cpobot. 
+ intros ff Hn.
  generalize (Build_IncreasingSequence ff Hn).
  intros w.
  refine (lub w). 
+ reflexivity.
+ intros x.
  apply cpobot_bot. 
+ intros s Hp x Hi n.
  simpl in Hi.
  transitivity (lub s).
  apply le_lub.
  trivial. 
+ intros s Hi x Hn.
  simpl; apply lub_le; trivial. 
Defined.

End wCpo_compl.