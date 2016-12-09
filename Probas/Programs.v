
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient Spaces.Int. 

Require Export RoundedClosed Opens Functions 
        Valuations LowerIntegrals D_op OpenFun
        Riesz Giry.

Set Implicit Arguments.

(** Conditional *)

Variable Bool : hSet. 

(** Image distributions : Rml 3 *) 

Definition im_distr {A B : hSet} (f : A -> B) (m : D A) : D B :=
       bind A B m (fun a => unit B (f a)). 

Lemma im_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C) (m : D A) : 
         im_distr g (im_distr f m) = im_distr (fun a => g (f a)) m.
Proof.   
unfold im_distr; simpl.   
Admitted. 

Lemma im_distr_id {A : hSet}: forall (f : A -> A) (m : D A),
          (forall x, f x = x) -> im_distr f m = m. 
Proof. 
intros f m Hx. 
unfold im_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu. destruct m.   
Admitted. 

(** *  Conditional distribution : Rml 4 *)

Definition Mif {A} (b : D Bool) (m1 m2 : D A)
           := bind Bool A b (fun x: Bool => m1). 
(* to change... of course *)

Lemma Mif_le_compat {A} : forall (b1 b2 : D Bool) (m1 m2 n1 n2 : D A)
                                 (B: OS Bool) (U : OS A),
       vD b1 B <= vD b2 B -> vD m1 U <= vD m2 U -> vD n1 U <= vD n2 U
        -> vD (Mif b1 m1 n1) U <= vD (Mif b2 m2 n2) U. 
Proof. Admitted. 

(** Correctness judgement *) 

Definition ok {A} (p : RlowPos) (nu : D A) (F : OS A) :=
                         p <= mu _ nu F. 

Definition ok_fun {A B} (f : OS A) (E : A -> D B) (F : A -> OS B) :=
                     forall x:A, ok ((OpenFun _ f) x) (E x) (F x). 

Definition ok_up {A} (p : RlowPos) (nu : D A) (F : OS A) :=
                        mu _ nu F <= p. 

Definition up_fun {A B} (f : OS A) (E : A -> D B) (F : A -> OS B) :=
                     forall x:A, ok_up ((OpenFun _ f) x) (E x) (F x). 

(** Rules for applications *)

Lemma apply_rule {A B} : forall (mu : D A) (f : A -> D B) (r : RlowPos)
                                (F : OS A) (G : OS B),
         ok r mu F -> ok_fun F f (fun x => G) -> ok r (bind A B mu f) G. 
Proof. Admitted. 

Lemma apply_rule_up {A B} : forall (mu : D A) (f : A -> D B) (r : RlowPos)
                                (F : OS A) (G : OS B),
         ok_up r mu F -> up_fun F f (fun x => G) -> ok_up r (bind A B mu f) G. 
Proof. Admitted. 

(** Rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> D B) (F : OS A) (G : A -> OS B),
       (forall x:A, ok (OpenFun _ F x) (f x) (G x)) -> ok_fun F f G. 
Proof. Admitted.

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> D B) (F : OS A) (G : A -> OS B),
       (forall x:A, ok_up (OpenFun _ F x) (f x) (G x)) -> up_fun F f G. 
Proof. Admitted.

(** Rules for conditional *) 

(* TODO *) 

(** Fixpoints *)

(* TODO *)

Definition bset : hSet.
Proof. exists Bool; apply hset_bool. Qed.


  
Section Random.

Definition Nset : IsHSet nat. apply _. Qed. 
Definition nset : hSet.
Proof. exists nat; apply Nset. Qed.

Fixpoint sigma (N : nat) (f : nat -> RlowPos) :=
   match N with
    | O => f O
    | S n => sigma n f end. 

Definition random (N : Int) : Mes hset_int. 

Definition random (N : nset) : Mes nset.
Proof.
intros U. 
refine (sigma ( N) ((OpenFun _ U) N)).
Defined.  
