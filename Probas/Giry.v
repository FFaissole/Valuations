
Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Spaces".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Theories".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Orders".
Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Riesz".


Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient. 

Require Export RoundedClosed Opens Functions 
        Valuations LowerIntegrals D_op OpenFun
        Riesz.

(*Set Implicit Arguments.*)

Definition unit_aux (A : hSet) (x : A) : Mes A. 
Proof.
refine (fun U : OS A => (OpenFun _ U) x). 
Defined. 

Definition unit (A : hSet) (x:A) : D A.
Proof.
exists (unit_aux _ x).    
+ unfold modular. intros U V.
  generalize (OpenFun_mod U V).
  intros Hmod; unfold fplus in Hmod.
  transitivity ((λ x : A, RlP_plus (OpenFun A U x)
                                   (OpenFun A V x)) x). 
  reflexivity. rewrite Hmod. 
  transitivity ((λ x : A, RlP_plus (OpenFun A (U ⋂ V) x)
                                   (OpenFun A (U ∪ V) x)) x).
  reflexivity. 
  rewrite RlPPlus_comm.
  reflexivity. 
+ unfold empty_op, unit_aux.
  rewrite OpenFun_def. 
  reflexivity. 
  reflexivity. 
+ unfold mon_opens. 
  intros U V HUV. 
  apply OpenFun_mon; trivial. 
+ unfold unit_aux. 
  apply OpenFun_prob; reflexivity. 
Defined. 

Lemma unit_aux_unit (A : hSet) (x:A) : mu _ (unit _ x) = unit_aux _ x. 
Proof. 
simpl; reflexivity. 
Qed. 
  
Definition bind (A B : hSet) : D A -> (A -> D B) -> D B.
Proof.
intros Nu F.
split with (fun U:OS B => I (Riesz2 Nu)
           (OpenFun _ (D_op 0 (fun x:A => (mu _ (F x)) U)))). 
+ intros U V. admit. 
+ unfold empty_op; simpl.
  assert (Hk : (fun x : A => mu _ (F x) ∅) = fun x:A => RlP_0).
  apply path_forall; intros x.  
  rewrite (mu_empty_op _ (F x)); reflexivity.
  rewrite Hk. unfold D_op. simpl. 
  unfold semi_decide. 
  destruct (decide (0 < 0)).   
  admit. (* ok pas de soucis *)

  rewrite OpenFun_def. 
  rewrite I_def; reflexivity.   
  reflexivity. 
+ intros U V HUV. 
  apply I_mon. 
  apply OpenFun_mon. 
  apply D_op_mon_f. 
  intros s; apply mu_mon; trivial.  
+ assert (Hk : (fun x : A => mu _ (F x)  Ω) <= fun x:A => RlP_1).
  intros x.  
  apply (mu_prob  _ (F x)); reflexivity.
  transitivity (I (Riesz2 Nu )(fun x =>  RlP_1)).
  apply I_mon.
  unfold D_op. 
  admit.
Admitted. 

Lemma monad1 {A B : hSet} : forall (x : A) (F : A -> D B) (f: OS B),
               mu _ (bind A B (unit A  x) F) f = mu _ (F x) f. 
Proof. 
intros x F f.
Admitted.

Lemma monad2 {A : hSet} : forall (nu : D A) (U : OS A),
    mu _ (bind A A nu (fun x:A => unit A x)) U = mu _ nu (fun x => U x).
Proof.
intros nu U.
Admitted.
(*
Lemma monad3 {A B C: hSet} : forall (nu : D A) (F : A -> D B) (G : B -> D C) (f : OS C),
     mu _ (bind B C (bind A B nu F) G) f = bind A B (fun x:A => bind A B (F x) G) f.  
Proof.*)

Definition vD {A :hSet} (nu : D A) (U : OS A) := mu _ nu U.

Lemma unit_aux_mon {A :hSet} : forall (x:A) (U V : OS A),
    U <= V -> (unit_aux A x) U <= (unit_aux A x) V.
Proof. 
intros x U V HUV.
apply OpenFun_mon; trivial.  
Qed. 

Lemma unit_mon {A :hSet} : forall (x:A) (U V : OS A),
    U <= V -> vD (unit A x) U <= vD (unit A x) V.
Proof. 
intros x U V HUV; unfold vD. 
rewrite unit_aux_unit. 
apply unit_aux_mon; trivial.
Qed. 

Lemma bind_mon {A B :hSet} : forall (x:A) (nu: D A) (F : A -> D B) (f g : OS B), 
       f <= g -> vD (bind A B nu F) f <= vD (bind A B nu F) g. 
Admitted.
(*
Lemma bind_le_comp {A B :hSet} : forall (nu1 nu2 : D A) (F1 F2 : A -> D B),
         nu1 <= nu2 -> F1 <= F2 -> star  *)
