
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               HoTT.Classes.theory.rationals
               HoTT.Classes.orders.orders
               HoTT.Classes.implementations.assume_rationals
               HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom HIT.quotient
               Basics.FunextVarieties FunextAxiom
               Types.Prod.

Require Import HoTTClasses.sierpinsky partiality dedekind.

Require Export Rlow Opens Valuations LowerIntegrals Riesz1.

Section Unit_int.

Definition btw01 (c : Cut)  := 
              merely (CutLe CutZero c /\ CutLe c CutOne).

Record unit_interval := mkU01 {
    c :> Cut ;  
    is_btw01 : btw01 c 
}.

Lemma btw01_eq0 : forall a b : unit_interval, 
            c a = c b -> a = b. 
Proof.  
intros (a,Ha) (b,Hb); simpl; 
intros E. destruct E. apply ap.
apply path_ishprop. 
Qed. 

Instance unit_interval_isset : IsHSet (unit_interval).
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => c a = c b)).
- intros a;split;
  reflexivity.
- apply _.
- intros a b E;
  apply btw01_eq0;apply E.
Qed.

Definition U01 : hSet.
Proof.
exists unit_interval;
apply unit_interval_isset.
Defined.

Definition U01_le : Le U01 := 
          fun x y => CutLe (c x) (c y).

Notation "[ 0 ; 1 ]" := U01.

Definition open_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p < x < QCut q.

Definition os_open_int (p q : Q) : OS U01 := 
              fun x => (semi_decide ((open_interval p q) x)).

Notation "] p ; q [" := (os_open_int p q).

Notation "f | U" := (OpenFun_meet_fun U f) (at level 50).

Hypothesis RiemInt : IntPos U01.

Notation "∫_( a ; b ) f" := (RiemInt (OpenFun_meet_fun (os_open_int a b) f)) 
                                       (at level 80).

Hypothesis RiemInt_add : forall (a b c : Q) {H : (a <= b /\ b <= c)%mc} f,  
      ( ∫_( a ; b ) f ) ++ ( ∫_( b ; c ) f )  = ∫_( a ; c ) f.

Hypothesis RiemInt_bounded_prim : 
         forall (a b mid :Q) (r : Q+) (f : mf U01) {H : (0 <= b - a)%mc}, 
              (forall x, ('a <= c x)%mc /\ (c x <= 'b)%mc -> 
                    ((f x) -- 'r <= 'mid /\ 'mid <= (f x) ++ ''r))%mc
         ->  ((∫_( a ; b ) f) -- ((b - a) * 'r) <=  '((b - a)*mid))%mc
         /\ ('((b - a)*mid) <=  (∫_( a ; b ) f) ++ '((b - a) * 'r))%mc.

Definition Unif := Riesz1 U01 RiemInt.

End Unit_int.

 


