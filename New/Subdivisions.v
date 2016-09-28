(** Some definitions of subdivisions for integration 
TODO : see if it is needed or not **)

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties Spaces.Nat. 

Require Import Qaxioms LowerR Dedekind_pos Distr Integral Riesz2.

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

