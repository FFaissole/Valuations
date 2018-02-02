

Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.interfaces.rationals
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.premetric
               HoTT.Classes.theory.rings
               HoTT.Classes.orders.semirings
               HoTT.Classes.orders.rings
               HoTT.Classes.theory.dec_fields.

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient HIT.unique_choice.

Require Import HoTTClasses.sierpinsky partiality dedekind.

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
simple refine (Build_Recursors
    _ _ _ _ _ _ _ _ _ _ _ _);simpl.
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
Lemma factorization_compl : forall f a, 
       f a = (completion_map f) (eta A a).
Proof.
intros f a.
unfold completion_map; simpl.
reflexivity. 
Qed.


(** unique map Partial A -> Partial Unit *) 

Definition umap : A -> Unit := fun x => tt.

Definition extend : partial A -> Sier := partial_map umap.

Lemma equiv_istop_umap : forall y, IsTop (extend y) -> 
                       hexists (fun w => eta A w = y).
Proof.
apply (partial_ind0 _ (fun a => _ -> _)).
+ intros s Hs.
  apply tr; exists s.
  reflexivity.
+ intros Hk.
  apply not_bot in Hk.
  case Hk.
+ intros f Hf Hn.
  assert (Hnn : hexists (fun n => extend (f n))).
  apply top_le_sup in Hn.
  trivial.
  revert Hnn; apply (Trunc_ind _); 
  intros (m,Hm).
  apply Hf in Hm.
  revert Hm; apply (Trunc_ind _).
  intros (w,Hw).
  apply tr.
  exists w.
  symmetry.
  apply eta_is_greatest.
  apply _.
  rewrite Hw.
  apply sup_is_ub.
Qed.

Definition val (y : partial A) : IsTop (extend y) -> A.
Proof.
intros H.
unfold extend in H.
generalize (equiv_istop_umap y H).
intros Hg.
unfold extend in H.
assert (exists w:A, eta A w = y).
generalize (unique_choice (fun n:Unit => 
     (fun w:A => eta A w = y))).
intros HH. 
unfold hexists.
assert (H1 :(Unit -> forall y0 : A, IsHProp (eta A y0 = y))).
intros X z.
apply _.
assert (H2 : (Unit -> hunique (fun w : A => eta A w = y))).
intros z.
split.
apply Hg.
unfold atmost1P.
intros a b Ha Hb.
rewrite <- Hb in Ha.
apply eta_le_eta.
apply _.
rewrite Ha; reflexivity.
specialize (HH H1 H2).
destruct HH as (f,Hff).
exists (f tt).
apply Hff.
destruct X as (w,HX).
refine w.
Defined.
 
Definition map_lift : partial A -> {s : Sier | merely (IsTop s ->  A)}.
Proof.  
intros y.
exists (extend y).
apply tr.
refine (val y).
Defined.

End wCpo_compl.