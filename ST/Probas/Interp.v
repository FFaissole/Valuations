

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

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1 Giry Cpo.
              
Set Implicit Arguments.


Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n).
Coercion qn : nat >-> Q.
Coercion qnp : nat >-> Qpos.

(** * Interpretation of probabilistic programs *)
(**
      .  --> [.] ;

      v  --> unit v ;

 let x=a in b --> bind  [a] (fun x => [b]) ;

     f a  -->  bind  [a] (fun x => [f] x) ;

    if b then a1 else a2 --> bind  [b] (fun x:bool => 
    if b then [a1] else [a2]).
**)


(** * Interpretation of programs *)

(** Image distributions by a function f :  *) 

Definition Iim_distr {A B : hSet} (f : A -> B) (J : IntPos A) : IntPos B
                                      := bind J (fun a => unit B (f a)).

Lemma Iim_distr_id {A : hSet}: forall (f : A -> A) (J : IntPos A),
          (forall x, f x = x) -> Iim_distr f J = J. 
Proof. 
intros f m Hx. 
unfold Iim_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu. simpl; rewrite monad2; reflexivity. 
Qed.  

Lemma Iim_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C) (m : IntPos A) : 
   Iim_distr g (Iim_distr f m) = Iim_distr (fun a => g (f a)) m.
Proof.
apply IntPos_eq0; apply path_forall.
intros h; unfold Iim_distr; simpl; 
reflexivity. 
Qed.

(**  
Conditional distribution *) 
Definition bool : hSet := default_TruncType 0 bool hset_bool. 


Definition Iif (A:hSet) (b: IntPos bool) (m1 m2:IntPos A) : IntPos A. 
Proof.                         
exists (fun X => (bind b (fun x:bool => if x then m1 else m2)) X).
+ hnf; unfold bind; simpl. 
  assert (Hb : (λ y : bool, (if y then m1 else m2) (fzero A)) = 
               λ y : bool, RlP_0).
  apply path_forall; intros y.
  destruct y; rewrite I_def; reflexivity.
  rewrite Hb, I_def; reflexivity.
+ intros f g; unfold bind; simpl.
  rewrite <- I_add.
  assert (H : (λ x : bool, (if x then m1 else m2) (fplus f g)) = 
             (fplus (λ x : bool, (if x then m1 else m2) f)
                    (λ x : bool, (if x then m1 else m2) g))).
  apply path_forall; intros y. unfold fplus. 
  simpl; destruct y;
  apply I_add.
  rewrite H; reflexivity.  
+ intros q Hq.
  unfold bind in Hq.
  simpl in Hq.
  assert (H : val (b (fone bool)) q).
  revert Hq; apply RC_mon with Qle.
  intros x y; apply (antisymmetry le).
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_mon.
  intros y; destruct y;
  apply I_prob.
  revert H; apply RC_mon with Qle.
  intros x y; apply (antisymmetry le).
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_prob.     
+ intros f g Hfg.
  apply I_mon; trivial. 
+ intros F; unfold bind.
  simpl. 
  pose (g := (λ n : nat, 
        (λ x:bool, (if x then m1 else m2) 
           (λ x0 : A, (F n x0))))).
  assert (Hg : forall n, g n <= g (S n)).
  intros n x; unfold g.
  destruct x.
  apply m1; intros x;
  apply F.
  apply m2; intros x; 
  apply F.
  pose (G := Build_IncreasingSequence g Hg).
  transitivity (b (Cpo.lub G)).
  apply I_mon.
  intros x.
  destruct x.
  apply m1.
  apply m2.
  pose (ff := (λ (n : nat), 
   (fun x : bool =>  (if x then m1 else m2) 
                     (λ x0 : A, F n x0)))).
  assert (Hff : forall n, ff n <= ff (S n)).
  intros n; unfold ff; intros x.
  destruct x.
  apply m1; intros y; apply F.
  apply m2; intros y; apply F.
  pose (H := Build_IncreasingSequence ff Hff).
  assert (Hf : b (Cpo.lub H) 
      <= RllubPos (fun n => b (H n))).
  apply b.
  trivial. 
Defined. 

(** Fixpoints *)

Section Fixpoints. 

Context {P : Type} {lP : Le P}
        {wCP : cpo P}.

Context {A : hSet}.

Fixpoint iter (f : P -> P) 
              (H : forall a b, a <= b -> f a <= f b)
              n : P := match n with 
                       | O => cpobot 
                       | S m => f (iter f H m) end.

Lemma iter_mon f H : forall n, (iter f H) n <= (iter f H) (S n).
Proof.
intros n.
induction n.
apply cpobot_bot.
simpl in *.
apply H; trivial.
Qed.

Definition fixp f H : P := 
          lub (Build_IncreasingSequence (iter f H) 
                                        (iter_mon f H)).


End Fixpoints.

Definition Ifix {A B:hSet} (F: (A -> IntPos B) -> A -> IntPos B) Monf
                 : A -> IntPos B := fixp F Monf.


(** * Correctness judgements *)

(** ok: the measure of F by the program associated 
        to nu is at least p, here p plays the role of 
        the probability.

    ok_up: the measure of F by the program associated 
           to nu is at most p. *)

Definition ok {A} (p : RlowPos) (nu : IntPos A) (F : mf A) :=
                         p <= nu F. 

Definition ok_fun {A B} (f : mf A) (E : A -> IntPos B) (F : A -> mf B) :=
                     forall x:A, ok (f x) (E x) (F x). 

Definition ok_up {A} (p : RlowPos) (nu : IntPos A) (F : mf A) := nu F <= p. 

Definition up_fun {A B} (f : mf A) (E : A -> IntPos B) (F : A -> mf B) :=
                     forall x:A, ok_up (f x) (E x) (F x). 

(** Correctness rules for applications *)

Lemma apply_rule {A B} : forall (J : IntPos A) (f : A -> IntPos B)
                                (r : RlowPos)
                                (F : mf A) (G : OS B),
          ok r J F -> ok_fun F f (fun x => G) ->
          ok r (bind J f) G. 
Proof.
intros nu f r F G H1 H2.
unfold ok_fun, ok in *.
unfold bind.
simpl. transitivity (nu F); trivial.
apply I_mon; trivial.
Qed. 

Lemma apply_rule_up {A B} : forall (J : IntPos A) (f : A -> IntPos B)
                      (r : RlowPos) (F : mf A) (G : mf B),
    ok_up r J F -> up_fun F f (fun x => G) ->
    ok_up r (bind J f) G. 
Proof.
intros nu f r U V H1 H2. 
unfold up_fun, ok_up in *. 
unfold bind; simpl.
transitivity (nu U); trivial.
apply I_mon; trivial.
Qed.


(** Correctness rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> IntPos B) (F : mf A)
                                      (G : A -> mf B),
    (forall x:A, ok (F x) (f x) (G x)) -> ok_fun F f G. 
Proof.
intros f F G HO. 
unfold ok_fun, ok in *; trivial. 
Qed. 

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> IntPos B) (F : mf A) (G : A -> mf B),
       (forall x:A, ok_up (F x) (f x) (G x)) -> up_fun F f G. 
Proof.
intros f F G HO. 
unfold up_fun, ok_up in *; trivial. 
Qed. 
