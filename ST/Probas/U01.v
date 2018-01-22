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
               Compactness Riesz1.

Section U01_mes.

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

Definition U01_le : Le U01 := 
          fun x y => proj1_sig x <= proj1_sig y.

Definition U01_is_Q : U01 -> Type :=
         fun x => exists q:Q, QCut q = proj1_sig x.

Notation "[ 0 ; 1 ]" := U01.

Definition open_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p < x < QCut q.

Definition closed_interval (p q : Q) : Cut -> Type := 
                               fun x => QCut p <= x /\ x <= QCut q.

Definition os_open_int (p q : Q) : OS [ 0 ; 1 ] := 
              fun x => (semi_decide 
                        ((open_interval p q) (proj1_sig x))).

End Unit_int.

Section Uniform.

Definition OpenFun_meet_fun (U : OS U01) (f : mf U01) := 
             fun x => RlPMeet (f x) (OpenFun _ U x).

Notation "] p ; q [" := (os_open_int p q).

Notation "f | U" := (OpenFun_meet_fun U f) (at level 50).


Hypothesis RiemInt : IntPos U01.

Hypothesis RiemInt_add : forall (a b c : Q) {H : a <= b /\ b <= c} f,  
          RiemInt (f | ] a ; b [) + RiemInt (f | ] b ; c [) 
        = RiemInt (f | ] a ; c [).

Hypothesis RiemInt_bounded_prim : forall (a b :Q) mid (r : Q) {H : 0 <= r} (f : mf U01), 
              (forall x, QCut a <= proj1_sig x /\ proj1_sig x <= QCut b -> 
                       Rl_minus_q2 (f x) r <= QRlow mid 
                    /\  QRlow mid <= RlPlus (f x) (QRlow r))
         ->  Rl_minus_q2 (RiemInt (f | ] a ; b [)) ((b - a) * r) 
            <= QRlow ((b - a)*mid) 
         /\ 
             QRlow ((b - a)*mid) 
            <= RlPlus (RiemInt (f | ] a ; b [)) (QRlow ((b - a) * r)). 


Definition Uniform_distr := Riesz1 RiemInt.

Lemma uniform_open_interval_inf : forall p q, 
               rl (Uniform_distr (os_open_int p q)) <= QRlow (q - p).
Proof.
intros p q; unfold Uniform_distr.
simpl.
assert (ho : Qzero <= Qzero).
reflexivity.
assert (H1 : (∀ x : ∃ c : Cut, btw01 c : hProp,
                        QCut p ≤ x.1 ≤ QCut q
                        → Rl_minus_q2 ((λ _ : U01, RlP_1) x) 0 ≤ QRlow 1
                          ≤ RlPlus ((λ _ : U01, RlP_1) x) (QRlow 0))).
admit.

specialize (RiemInt_bounded_prim p q 1 0 ho (fun x => RlP_1) H1).
clear ho.

assert (H2 : (q - p)*0 = 0).
admit.

rewrite H2 in RiemInt_bounded_prim.
rewrite (RlPlus_comm _ (QRlow 0)) in RiemInt_bounded_prim.
assert (H3 : QRlow 0 = Rl0).
reflexivity.
rewrite H3 in RiemInt_bounded_prim.
rewrite RlPlus_left_id in RiemInt_bounded_prim.
assert (H4 : forall r, Rl_minus_q2 r 0 = r).
intros r.
admit.

rewrite H4 in RiemInt_bounded_prim.
assert (H5 : (q - p) *1 = q-p).
admit.

rewrite H5 in RiemInt_bounded_prim.
assert (H6 : (λ _ : U01, RlP_1) | ] p; q [ = 
             OpenFun _ (os_open_int p q)).
unfold OpenFun_meet_fun.
admit.

rewrite <- H6.
apply RiemInt_bounded_prim.
Admitted. 

Lemma uniform_open_interval : forall p q, 
               rl (Uniform_distr (os_open_int p q)) = QRlow (q - p).
Admitted.


Lemma uniform_U01 : Uniform_distr (fun x => SierTop) = RlP_1.
Proof.
apply (antisymmetry le).
+ apply RiemInt.
+ assert (H1 : rl (Uniform_distr (os_open_int 0 1)) = Rl1).
  rewrite uniform_open_interval.
  rewrite rings.negate_0, rings.plus_0_r.
  reflexivity.
  assert (H2 : Rlle (RiemInt (OpenFun U01 (os_open_int 0 1))) 
                    ((RiemInt (OpenFun U01 (λ _ : unit_interval, SierTop))))).
  apply RiemInt.
  apply OpenFun_mon.
  intros s; apply top_greatest.
  rewrite H1 in H2.
  trivial.
Qed.

End Uniform.

