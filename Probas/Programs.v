
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


(** Image distributions : Rml 3 *) 

Definition im_distr {A B : hSet} (f : A -> B) (m : D A) : D B :=
       bind A B m (fun a => unit B (f a)). 

Lemma im_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C) (m : D A) : 
         im_distr g (im_distr f m) = im_distr (fun a => g (f a)) m.
Proof.   
unfold im_distr; simpl.
rewrite monad3.
assert (Hu : (λ x : A, bind B C (unit B (f x))
                            (λ a : B, unit C (g a))) =
             (λ a : A, unit C (g (f a)))). 
apply path_forall. 
intros x. assert (Hmu : mu _ (bind B C (unit B (f x))
                     (λ a : B, unit C (g a))) =
                  mu _ (unit C (g (f x)))).
unfold unit, bind. simpl. apply path_forall.
intros z.
unfold unit_aux.
simpl.

Admitted. 

Lemma im_distr_id {A : hSet}: forall (f : A -> A) (m : D A),
          (forall x, f x = x) -> im_distr f m = m. 
Proof. 
intros f m Hx. 
unfold im_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu, monad2; reflexivity. 
Qed.  

(** *  Conditional distribution : Rml 4 *)

(* TODO *)

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

Lemma apply_rule {A B} : forall (nu : D A) (f : A -> D B)
                                (r : RlowPos)
                                (F : OS A) (G : OS B),
          ok r nu F -> ok_fun F f (fun x => G) ->
          ok r (bind A B nu f) G. 
Proof.
intros nu f r F G H1 H2.
unfold ok_fun, ok in *.
unfold bind.
simpl. transitivity (mu _ nu F); trivial.
transitivity (I (Riesz2 nu) (OpenFun A (D_op 0
                     (λ x : A, OpenFun A F x)))).
unfold Riesz2.
rewrite I_mu_simpl.
transitivity (sum_p_r 1 (OpenFun A (D_op 0
                     (λ x : A, OpenFun A F x))) nu).
unfold sum_p_r; simpl.
assert (Hqq : (1 / qn 1) = 1).
admit.

rewrite Hqq.
transitivity (Rlow_mult_q 1
      (RlP_plus RlP_0
       (mu _ nu
         (D_op (qn 1)
               (OpenFun A (D_op 0 (λ x : A, OpenFun A F x))))))).
rewrite RlPPlus_left_id.
rewrite Rlow_mult_q1.
apply mu_mon.
intros s; apply imply_le.
intros Hss.
apply D_op_correct.
unfold D_op.
unfold OpenFun, OpenFun_aux; simpl.
admit.

reflexivity. Check RllubPos_lub.
apply (RllubPos_lub ((λ n : nat,
       sum_p_r n (OpenFun A (D_op 0 (λ x : A, OpenFun A F x)))
         nu)) 1).
apply I_mon.
apply OpenFun_mon.
apply D_op_mon_f.
intros z; trivial.
Admitted.


Lemma apply_rule_up {A B} : forall (mu : D A) (f : A -> D B)
                                   (r : RlowPos)
                                (F : OS A) (G : OS B),
    ok_up r mu F -> up_fun F f (fun x => G) ->
    ok_up r (bind A B mu f) G. 
Proof.
intros mu f r F G H1 H2. 
unfold up_fun, ok_up in *. 
unfold bind.
Admitted. 

(** Rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> D B) (F : OS A)
                                      (G : A -> OS B),
    (forall x:A, ok (OpenFun _ F x) (f x) (G x)) -> ok_fun F f G. 
Proof.
intros f F G HO. 
unfold ok_fun, ok in *; trivial. 
Qed. 

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> D B) (F : OS A) (G : A -> OS B),
       (forall x:A, ok_up (OpenFun _ F x) (f x) (G x)) -> up_fun F f G. 
Proof.
intros f F G HO. 
unfold up_fun, ok_up in *; trivial. 
Qed. 

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
