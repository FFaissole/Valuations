Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Spaces".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Theories".

Add Rec LoadPath "/Users/faissole/Desktop/HoTT/Measures/CoqPL/Orders".


Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               hit.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals D_op OpenFun. 

Set Implicit Arguments. 







Section Bags_equiv.
  

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
          merely (App2 l1 r s <~>
                  App2 l2 (Tmeet r s) (Tjoin r s)).

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
Context {Hf : Funext} {Hu : Univalence}.



Variable p : nat. 
Hypothesis Hp : 0 < p. 

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