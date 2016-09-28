(** Proof of the Riesz's representation theorem **)

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.interfaces.rationals
               HoTTClasses.theory.rationals
               HoTTClasses.theory.rings
               HoTTClasses.orders.rings
               HoTTClasses.interfaces.integers
               HoTTClasses.interfaces.naturals
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.natpair_integers
               HoTTClasses.theory.rings
               HoTTClasses.theory.integers
               HoTTClasses.theory.dec_fields
               HoTTClasses.orders.dec_fields
               HoTTClasses.theory.lattices
               HoTTClasses.orders.lattices
               HoTTClasses.theory.additional_operations
               HoTTClasses.theory.premetric
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky.
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient Types.Forall
               Types.Paths.
               
Local Open Scope path_scope. 

Require Export Qaxioms Duilq Distr2 IntPos2.

Set Implicit Arguments. 

Context {A : hSet}.
Context {Hf : Funext} {Hu : Univalence}.

(* Map from Sier to RlowPos *)
Definition OpenFun_aux : forall s : Sier, RlowPos.
Proof.
apply (partial_rec Unit _ le).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
+ intros _. exact RlP_1. 
+ exact RlP_0. 
+ intros f Hn. 
  exact (RllubPos f).
+ reflexivity.
+ intros x.
  apply RlowPos_pos. 
+ intros s Hp x Hi n.
  transitivity ((λ (f0 : nat → RlowPos)
       (_ : ∀ n : nat, f0 n ≤ f0 (S n)), 
       RllubPos f0) s Hp).
  simpl.
  apply RllubPos_lub. 
  trivial.
+ intros s Hi x Hn q Hh.
  assert (Hx : (val (rl (RllubPos s)) q)).
  trivial.
  assert (H2 : RllubPos s <= x).
  apply RllubPos_le. trivial.
  apply gen_mon with Qle (Rllub s) q. 
  red; auto with qarith. apply le_or_lt.
  reflexivity. trivial. trivial.
Defined.

(* Monotonicity of the map from Sier to RlowPos *)
Lemma OpenFun_aux_mon : forall s1 s2, s1 <= s2
                        -> OpenFun_aux s1 <= OpenFun_aux s2.
Proof.
apply (partialLe_ind0 _ _).
+ reflexivity.
+ assert (X : OpenFun_aux (bot Unit) = RlP_0).
  auto. rewrite X.
  intros. apply RlowPos_pos.
+ intros f x H1 H2 n.
  transitivity (OpenFun_aux (sup Unit f)).
  assert (Hr : OpenFun_aux (sup Unit f) = RllubPos (fun n => OpenFun_aux (f n))).
  auto. rewrite Hr.
  apply (Rllub_lub (fun n => OpenFun_aux (f n))); trivial.
  trivial.
+ intros f x H1 H2.
  assert (Hr : OpenFun_aux (sup Unit f) = RllubPos (fun n => OpenFun_aux (f n))).
  auto. rewrite Hr.
  apply Rllub_le.
  intros n.
  apply H2.
Qed.

(* Map from Opens to characteristic function *)
Definition OpenFun : forall (U : A -> Sier), (A -> RlowPos). 
Proof. 
intros s z. 
specialize (s z).
exact (OpenFun_aux s).
Defined.

(* Monotonicity *)
Lemma OpenFun_mon : forall U V, U <= V -> OpenFun U <= OpenFun V.
Proof.
intros U V H1 s.
unfold OpenFun.
apply OpenFun_aux_mon; trivial.
apply (H1 s).
Qed.

(* new definitions, new proof, to fix soon *)
Lemma OpenFun_mod : forall U V, fplus (OpenFun U) (OpenFun V) =
                                fplus (OpenFun (OS_meet U V))
                                      (OpenFun (OS_join U V)).
Proof. 
Admitted.

(* First part of theorem : mu(I) *)
Definition mu_radon : IntPos A  -> D A. 
Proof. 
intros J. 
exists (fun U => I J (OpenFun U)). 
+ red. intros U V. 
  transitivity (I J (OpenFun U) + I J (OpenFun V)).
  reflexivity.
  rewrite <- (I_add J (OpenFun U) (OpenFun V)).
  transitivity
     ((I J( OpenFun (OS_join U V)))+
      (I J (OpenFun (OS_meet U V)))); 
  try reflexivity.
  rewrite <- (I_add J (OpenFun (OS_join U V))
                    (OpenFun (OS_meet U V))).
  rewrite OpenFun_mod, fplus_comm. reflexivity.  
+ red. destruct J. 
  assert (HO : OpenFun OS_empty = fzero).
  auto. rewrite HO. 
  apply I_def. 
+ red.   
  intros U V H. 
  apply I_mon. 
  apply OpenFun_mon; trivial.
+ apply I_prob.
Qed.

(** second part of the theorem : need simple functions**)

Definition I_mu : D A -> IntPos A. 
Proof. 
intros M.
Admitted.

(* homeomorphism *)
Theorem Riesz : forall J mu, (I_mu (mu_radon J) = J)
                          /\ (mu_radon (I_mu mu) = mu).
Proof.
Admitted. 


