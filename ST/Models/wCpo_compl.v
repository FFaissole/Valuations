

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

(** * Partial type as free wCpo *)

Require Export Cpo.

Section wCpo_compl.

Context {P : Type} {lP : Le P} {PP : PartialOrder lP}
        {wCP : cpo P}.

Context {A : hSet}.

(** free wCpo completion *)
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
  transitivity 
    (lub (Build_IncreasingSequence s Hp)).
  transitivity 
    ((Build_IncreasingSequence s Hp) n); 
  try reflexivity.
  apply le_lub.
  trivial. 
+ intros s Hi x Hn.
  simpl; apply lub_le; trivial. 
Defined.

(** factorization lemma *)
Lemma factorization_compl : forall f a, f a = (completion_map f) (eta A a).
Proof.
intros f a.
unfold completion_map; simpl.
reflexivity. 
Qed.

(** unique map Partial A -> Partial Unit *) 

Definition Punique : partial A -> Sier.
Proof.
apply (partial_rec A _ le).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
+ intros _. exact SierTop. 
+ exact SierBot. 
+ intros f Hn.
  generalize (Build_IncreasingSequence f Hn).
  intros ff.
  refine (sup Unit ff). 
+ reflexivity.
+ intros x.
  apply imply_le; intros b.
  apply not_bot in b.
  case b. 
+ intros s Hp x Hi n.
  simpl in Hi.
  transitivity (sup Unit (Build_IncreasingSequence s Hp)).
  apply imply_le; intros H.
  apply top_le_sup.
  apply tr; exists n.
  apply H. trivial.
+ intros s Hi x Hn.
  simpl; apply imply_le.
  intros H.
  apply top_le_sup in H.
  revert H.
  apply (Trunc_ind _); intros (m,Hm).
  revert Hm; apply SierLe_imply.
  apply Hn. 
Defined.

End wCpo_compl.