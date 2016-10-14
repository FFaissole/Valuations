(** A very preliminary development for the free monoid of a lattice 
    
         ------ WIP ------
          
*)

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
               HoTTClasses.implementations.list. 

Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient Types.Forall
               Types.Paths.
Local Open Scope path_scope. 

Require Export Qaxioms Duilq Distr IntPos.

Section Bags_equiv.

Variable T : Type.
                                                          
Definition equiv_rel (A B : Type) :=
  exists (to : A -> B) (from : B -> A),
    (forall x, from (to x) = x) /\ (forall y, to (from y) = y). 


Fixpoint Any (l : list T) (P : T -> Type) : Type := match l with
              | nil => False
              | cons x q => (P x) \/ (Any q P)
         end.

Variable EqT : T -> T -> Type. 

Definition App (l: list T) (s : T) := (Any l (EqT s)).

Definition eq_bag := fun l1 l2 => forall r:T, equiv_rel (App l1 r) (App l2 r).

Global Instance eq_bag_ishProp : ∀ x y : list T, IsHProp (eq_bag x y).
Proof.
intros x y.
apply hprop_allpath.
intros s s'.
apply path_forall. 
intros z.
destruct (s z) as (H,H0). 
unfold App in *. 
destruct H0 as (L,H0). 
destruct H0 as (H1,H2). 
destruct (s' z) as (J,J0). 
unfold App in *. 
destruct J0 as (M,J0). 
destruct J0 as (J1,J2). 
unfold eq_bag in *.   
assert (Hrr : forall r, IsHProp (equiv_rel (App x r) (App y r))).
admit. 
Admitted.

Variable A : hSet. 
Context {Tjoin : Join A}.
Context {Tmeet : Meet A}.
Context {Tlatt : Lattice A}. 

Definition equiv_mod : forall (x y:A) l, cons x (cons y l)
                    = cons (Tmeet x y) (cons (Tjoin x y) l).

Definition free_mon : Type := @quotient _ eq_bag _.

Variable A : hSet.  

Fixpoint isin (T : Type) (l : list T) (t : T) := match l with  
              | nil => False
              | cons x q => (x = t) \/ (isin _ q t) end. 

Fixpoint is_subl (l : list (@OS A)) (ll : list (@OS A)) := match ll with
              | nil => True
              | cons x q => (isin _ l x) /\ (is_subl l q) end. 

Record set_index (l : list (@OS A)) := {
              subl :> list (@OS A);
              is_sub : forall x, isin _ l x -> isin _ subl x                                  
}. 

Record set_index_length (l : list (@OS A)) (n : nat) := {
              subl_n :> set_index l;
              is_length_n : length subl_n = n 
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
                    meet_list_os (subl _ (subl_n _ _ Ln)) <= meet_list_os Mn. 

Definition is_eq_simples l m := is_le_simples l m /

Definition free_mon_os := free_mon (list (@OS A)) is_le_simples. 

Close Scope nat_scope. 

Definition is_btw (a b c : Q) := (a <= c) /\ (c <= b). 

Inductive sv (a b : Q) :=        
| sub0 : sv a b
| subn : forall q : Q, is_btw a b q -> sv a b -> sv a b. 

Inductive lsubdiv (a b : Q) (δ : nat) : sv a b -> Type :=
    | lsubdiv0 :  lsubdiv a b δ (sub0 a b)
    | lsubdiv1 q Hq :
             lsubdiv a b δ (subn a b q Hq (sub0 a b))
    | lsubdivn p q l Hp Hq :
        lsubdiv a b δ (subn a b q Hq l) -> p < q
             -> ((p - q) <= pos (pos_of_nat δ))
             -> lsubdiv a b δ (subn a b p Hp (subn a b q Hq (sub0 a b))).

Inductive Hdrel a b p (δ : nat): sv a b -> Type :=
    | Hdrel0 : Hdrel a b p δ (sub0 a b)
    | Hdreln q Hq l : p < q -> ((p - q) <= pos (pos_of_nat δ)) -> Hdrel a b p δ (subn a b q Hq l).

Inductive is_subdiv a b (δ : nat) : sv a b -> Type :=
    | subv0 : is_subdiv a b δ (sub0 a b)
    | subvn q Hq l : is_subdiv a b δ l -> Hdrel a b q δ l
                    -> is_subdiv a b δ (subn a b q Hq l).

Record subdivision a b (δ : nat) := mkSub {
         suv :> sv a b ;     
         Hsv : is_subdiv a b δ suv 
}.

Definition rat_f (A : hSet) (q : Q) : MF A. 
Proof. 
intros x.
refine (QCut q).
Defined.

Lemma rat_f_simpl (A : hSet) (q : Q) : forall x:A, rat_f A q x = QCut q. 
Proof. 
auto. 
Qed.

Lemma rat_f_def (A : hSet) (q : Q) : rat_f A q = fun x => QCut q. 
Proof.
auto.
Qed.

Definition sv_subdiv a b (δ : nat) (l : sv a b) :
                 is_subdiv a b δ l -> subdivision a b δ. 
Proof. 
intros Hl. 
exists l; trivial.  
Defined. 

Fixpoint sum_sv (A : hSet) (a b : Q) (δ : nat) (f : MF A) (m : D A)
                    (s : sv a b) : Rlow := match s with 
       | sub0 => Q_inject a
       | subn q Hq sub0 => Rl_Q_Mult q (mu m (MF_Open (fminus f (rat_f _ q))))
       | subn q Hq (subn p Hp l) => Rl_Plus
                           (Rl_Q_Mult q (mu m (MeetOpen (MF_Open (fminus f (rat_f _ q)))
                                                        (MF_Open (fminus (rat_f _ p) f)))))
(sum_sv A a b δ f m l) end. 

End BagsEquiv.

