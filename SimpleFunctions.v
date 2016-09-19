Add Rec LoadPath "/Users/faissole/Desktop/HoTT/HoTTClasses/theories".

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

Fixpoint sum_subdiv (A : hSet) (a b : Q) (δ : nat) (f : MF A) (m : D A)
                    (s : sv a b) : Rlow := match s with 
       | sub0 => [a]
       | subn q Hq sub0 => Rl_Q_Mult q (mu m (MF_Open (fminus f (rat_f _ q))))
       | subn q Hq (subn p Hp l)  => Rl_Plus
                           (Rl_Q_Mult q (mu m (MeetOpen (MF_Open (fminus f (rat_f _ q)))
                                                        (MF_Open (fminus (rat_f _ p) f)))))
                          (sum_subdiv A a b δ f m l) end. 
(*
Section Deltas. 

Variable A : hSet.
Variable a b : Q.
Variable p : nat. 
Hypothesis Hab : Qlt a b.
Hypothesis Hpp : 0 < p. 

Definition delta_f (r s f : MF A) : OpenSub A :=   
  MeetOpen (MF_Open (fun x => CutPlus (f x) (CutNeg (r x))))
           (MF_Open (fun x => CutPlus (s x) (CutNeg (f x)))). 

Definition sub_rat_opens (n : nat) (Hn : n <= p) (f : MF A) (m : Mes A) :=
  RlP_Q_Mult (Qplus a (n_Q_m n (on (Qplus b (-a)) p)))
             (m (delta_f
                    (fun x => QCut (Qplus a (n_Q_m n (on (Qplus b (-a)) p))))
                    (fun x => QCut (Qplus a (n_Q_m (n+1) (on (Qplus b (-a)) p)))) f)). 

End Deltas. 

*)
     