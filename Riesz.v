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
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.field_of_fractions. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient Types.Forall
               Types.Paths.
               
Local Open Scope path_scope. 
Require Export RoundedClosed Valuations LowerIntpos.

Set Implicit Arguments. 

Section Riesz1. 

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
  apply RC_mon with Qle (Rllub s) q. 
  intros ss sh; apply (antisymmetry le). apply le_or_lt.
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
intros U V.   
apply path_forall; intros z. 
unfold fplus.
apply (antisymmetry le).
Admitted. 

Definition IntP := @IntPos A _ _. 
Definition VP := @Val A _ _.

(* First part of theorem : mu(I) *)
Definition Riesz1 : IntP  -> VP. 
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

End Riesz1. 

Section Bags_equiv.
  
Context {Hf : Funext} {Hu : Univalence}.
(** Coquand-Spitters, Vickers build the set of simple functions to define the integral from a measure; they both use the Tarski's free monoid quotiented by a modularity law. 

Here we provide the construction of the free monoid using bag equivalence (see Danielson : http://www.cse.chalmers.se/~nad/publications/danielsson-bag-equivalence.pdf)
*)

Variable T : Type.
Context {T_isset : IsHSet T}.

Fixpoint Any (l : list T) (P : T -> Type) : Type := match l with
              | nil => False
              | cons x q => (P x) \/ (Any q P)
         end.                         

Definition EqT := fun (a b: T) => a = b. 

Definition App (l: list T) (s : T) := (Any l (EqT s)).

Definition eq_bag := fun l1 l2 => forall r,
                      merely ((App l1 r) <~> (App l2 r)). 

 
Definition free_mon : Type := @quotient _ eq_bag _. 

Context {Tjoin : Join T}.
Context {Tmeet : Meet T}.
Context {Tlatt : Lattice T}.

Fixpoint Any2 (l : list T) (P : T -> T -> Type) : Type := match l with
              | nil => False
              | cons x nil => False
              | cons x (cons y q) => (P x y) \/ (Any2 q P)
         end.    

Definition EqT2 := fun (a b c d : T) => a = c /\ b = d. 

Definition App2 (l : list T) (s t : T) := (Any2 l (EqT2 s t)). 

Definition eq_mod := fun l1 l2 => forall r s,
                merely (App2 l1 r s <~> App2 l2 (Tmeet r s) (Tjoin r s)).

Definition eq_free_mod := fun l1 l2 => eq_bag l1 l2 /\ eq_mod l1 l2. 

Definition modular_mon : Type := @quotient _ eq_free_mod _.  

End Bags_equiv. 

Section Rationalization. 

Context {Hf : Funext} {Hu : Univalence}.
Context {T : Type}.
Context {T_isset : IsHSet T}.
Context {Tjoin : Join T}.
Context {Tmeet : Meet T}.
Context {Tlatt : Lattice T}.

Open Scope type_scope.
Definition rat_mod_mon_aux := Q+ * (list T).

Definition frac_quot : rat_mod_mon_aux -> rat_mod_mon_aux -> hProp.
Proof.   
intros r s. 
unfold rat_mod_mon_aux in r, s.
Admitted. 

Definition eq_rmm := fun (M N : rat_mod_mon_aux) =>
           eq_bag (snd M) (snd N) /\ eq_mod (snd M) (snd N) /\ frac_quot M N.

Definition rat_modular_mon :=  @quotient _ eq_rmm _.  

End Rationalization.   

Section SimpleFunctions. 

Context {Hf : Funext} {Hu : Univalence}.
Context {A : hSet}.  

Global Instance OS_isset : IsHSet (@OS A). 
apply _. 
Qed.

Definition simples := (@rat_modular_mon _ _ (@OS A)). 

End SimpleFunctions. 

Section Subdivisions. 

Context {T : hSet}.

Variable p : nat. 
Hypothesis Hp : 0 < p. 

Check / pos_of_nat p. 

Definition h : Q+ := / pos_of_nat p.  

(* TODO : faire les quotients, avec rec rect etc *)

Definition sv_monoid : nat -> (@simples _ _ T _
                                OS_join OS_meet os_lattice). 
Proof. 
intros n. 
unfold rat_modular_mon.   
Admitted. 

(* TODO : faire 1ere ineq. "mu" s <= I f etc *)

End Subdivisions.   


Section List_OS_aux. 

Context {A : hSet}.
  
Fixpoint isin (T : Type) (l : list T) (t : T) := match l with  
              | nil => False
              | cons x q => (x = t) \/ (isin q t) end. 

Fixpoint is_subl (l : list (@OS A)) (ll : list (@OS A)) := match ll with
              | nil => True
              | cons x q => (isin l x) /\ (is_subl l q) end. 

Record set_index (l : list (@OS A)) := {
              subl :> list (@OS A);
              is_sub : forall x, isin l x -> isin subl x                                  
}. 

Record set_index_length (l : list (@OS A)) (n : nat) := {
              subl_n :> set_index l;
              is_length_n : list.length subl_n = n 
}. 

Fixpoint meet_list_os (l : list (@OS A)) := match l with
              | nil => OS_empty
              | cons x q => OS_meet x (meet_list_os q) end.

Fixpoint join_list_os (l : list (@OS A)) := match l with
              | nil => OS_empty
              | cons x q => OS_join x (meet_list_os q) end.

Definition is_le_simples (l m : list (@OS A)) := forall (n : nat)
                         (Ln : set_index_length l n),
                         exists (Mn : set_index_length m n),
                    meet_list_os (subl (subl_n Ln)) <= meet_list_os Mn. 

(*Close Scope nat_scope. *)

Definition is_btw (a b c : Q) := (a <= c) /\ (c <= b). 

Inductive sv (a b : Q) :=        
  | sub0 : sv a b
  | subn : forall q : Q, is_btw a b q -> sv a b -> sv a b. 

Inductive lsubdiv (a b : Q) (δ : nat) : sv a b -> Type :=
    | lsubdiv0 :  (@lsubdiv a b) δ (sub0 a b)
    | lsubdiv1 q Hq :
             (@lsubdiv a b) δ ((@subn a b) q Hq (sub0 a b))
    | lsubdivn p q l Hp Hq :
        (@lsubdiv a b) δ ((@subn a b) q Hq l) -> p < q
             -> ((p - q) <= pos (pos_of_nat δ))
             -> (@lsubdiv a b) δ ((@subn a b) p Hp ((@subn a b) q Hq (sub0 a b))).

Inductive Hdrel a b p (δ : nat): sv a b -> Type :=
    | Hdrel0 : (@Hdrel a b) p δ (sub0 a b)
    | Hdreln q Hq l : p < q -> ((p - q) <= pos (pos_of_nat δ)) -> (@Hdrel a b) p δ
                                                         ((@subn a b) q Hq l).

Inductive is_subdiv a b (δ : nat) : sv a b -> Type :=
    | subv0 : (@is_subdiv a b) δ (sub0 a b)
    | subvn q Hq l : (@is_subdiv a b) δ l -> (@Hdrel a b) q δ l
                    -> (@is_subdiv a b) δ ((@subn a b) q Hq l).

Record subdivision a b (δ : nat) := mkSub {
         suv :> sv a b ;     
         Hsv : (@is_subdiv a b) δ suv 
}.

Definition MF := (@mf A).

Definition sv_subdiv a b (δ : nat) (l : sv a b) :
                 (@is_subdiv a b) δ l -> subdivision a b δ. 
Proof. 
intros Hl. 
exists l; trivial.  
Defined.

End List_OS_aux. 
