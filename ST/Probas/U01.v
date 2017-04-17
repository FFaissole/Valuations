

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.theory.rationals
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.dedekind
               HoTTClasses.orders.orders. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod.

Require Export RoundedClosed Opens Valuations LowerIntegrals
               Compactness.


Section Unit_int.

Definition btw01 (c : Cut)  := 
              merely (CutZero <= c /\ c <= CutOne).

Definition unit_interval := {c : Cut | btw01 c : hProp}.

Lemma btw01_eq0 : forall a b : unit_interval, 
            proj1_sig a = proj1_sig b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 

Instance unit_interval_isset@{} : IsHSet (unit_interval).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => proj1_sig a = proj1_sig b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply btw01_eq0;apply E.
Qed.

Definition U01 : hSet.
Proof.
exists unit_interval;
apply unit_interval_isset.
Defined.

End Unit_int.

Notation "[ 0 ; 1 ]" := U01.

Definition open_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p < x /\ x < QCut q.

Definition closed_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p <= x /\ x <= QCut q.

Definition os_open_int (p q : Q) : OS [ 0 ; 1 ] := 
              fun x => (semi_decide 
                        ((open_interval p q) (proj1_sig x))).

Notation "] p ; q [" := (os_open_int p q) (at level 50).
Notation "[ p ; q ]" := (closed_interval p q) (at level 50).

Definition WSO := forall (U : OS U01) x, U x -> 
                             exists p q, ] p ; q [ x /\ ( ] p ; q [ <= U ).

Definition WSO_strong := forall (U : OS U01), exists (W : nat -> Q*Q), forall x, 
                  (U x -> exists n, (] fst (W n) ; snd (W n) [ x)) /\
                               (forall k, ] fst (W k) ; snd (W k) [ ⊆ U).


Definition covers_open_int := forall U: OS (U01), exists W : nat -> Q*Q, 
                             (forall n, snd (W n) <= snd (W (S n))) /\
                             (forall x, U x -> exists n, 
                                            ] fst (W n) ; snd (W n) [ x). 

Definition fc_open_int (U: OS (U01)) := 
                      exists (W : nat -> Q*Q) (N : nat), 
                             (forall n, snd (W n) <= snd (W (S n))) /\
                             (forall x, U x -> exists n, n<=N /\ 
                                             ] fst (W n) ; snd (W n) [ x). 

Fixpoint sum_lengths (W : nat -> Q*Q) (N : nat) := match N with 
    | O => snd (W O) - fst (W O)
    | S n => sum_lengths W n + snd (W N) - fst (W N)
end.


Definition fc_sum_length (U : OS [ 0 ; 1 ]) : fc_open_int U -> Q.
Proof.
intros (W,(N,(H1,H2))).
refine (sum_lengths W N).
Defined. 

Definition is_closed_rat (U : OS [ 0 ; 1 ]) p q := 
                              forall z, U z <-> [ p ; q ] z.1.  


Fixpoint sum_mu  (W : nat -> OS U01) (N : nat) (m : Val U01) 
    := match N with 
      | O => m (W 0)
      | S n => m (W N) + sum_mu W n m
end.

(** Spec of valuation on [0,1] *)
Record U01_val := mkom{ 
        mu01 : Val U01;
        mu_rat : forall p q, 
            rl (mu01 (] p ; q [)) = QRlow (q - p);
        mu_sup : forall (U : OS U01) f, cover U f -> 
            (forall n m, ((f n) ⋂ (f m)) = ∅) ->
             mu01 U = RllubPos (fun n => sum_mu f n mu01);
        mu_U01 : mu01 (fun x => SierTop) = RlP_1
}.

(** * Compactness and local compactness in synthetic topology *)

Definition cover {A : hSet} (U : OS A) (f : nat -> OS A) := 
                    forall x, U x -> exists n, (f n) x. 

Definition finite_cover {A : hSet} (U : OS A) (f : nat -> OS A) := 
                    exists N, forall x, U x -> exists n, n <= N /\ (f n) x.

Definition compactness {A : hSet} (U : OS A) := 
                        hexists (fun f => cover U f) -> 
                        hexists (fun g => finite_cover U g).

Definition below {A : hSet} (U V : OS A) := forall f, cover V f -> 
                exists g, (forall i, exists j:nat, g i = f i) 
                           /\ (finite_cover U g).

Notation "U << V" := (below U V) (at level 50).

Definition local_compactness_weak {A : hSet} (V : OS A) := 
               (forall U, U << V -> (U ⊆ V)) /\ 
               (exists U, U << V /\ U = V).

Section local_compactness_seq.

Context {A : hSet}.

Hypothesis seq_below : forall V : OS A, exists f : nat -> OS A, 
                 forall U, U << V -> exists i, (f i) << V.

Definition sup_below (V : OS A) : OS A.
Proof.
destruct (seq_below V) as (f,Hf).
refine (fun x => CountableSup (fun n => f n x)).
Defined. 

Definition local_compactness := forall V:OS A, V = sup_below V. 

End local_compactness_seq.


 


