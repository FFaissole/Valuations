
Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               partiality
               sierpinsky
               dedekind
               HoTT.Classes.theory.rationals
               HoTT.Classes.orders.orders
               HoTT.Classes.theory.premetric
               HoTT.Classes.implementations.assume_rationals. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export Rlow Opens Functions.
              
Set Implicit Arguments.

(** * D_op: operator which takes a function and a rational 
and gives the open in which the function is bigger than the 
rational *)

(** see a similart construction with Dedekind cuts in 
Coquand-Spitters 09, Integrals and valuations *)

Section Dop.

Context `{Funext} `{Univalence}.

Definition D_op {A :hSet} (q : Q) : mf A -> OS A :=
   fun f z => let (rl,_) := (f z) in (elt rl q).

(** Correctness of the definition *)
Lemma D_op_correct {A:hSet}: forall f q (x:A),
    (D_op q f) x <->  QRlow q < (f x).
Proof. 
intros f q x; split; intro HH. 
+ unfold D_op in HH.
  destruct (f x); simpl.
  red; unfold Rllt. 
  apply tr.   
  exists q. 
  split; trivial.
  unfold QRlow. 
  simpl; intros Hn. 
  unfold semi_decide, Rllt_semi_dec, 
         decidable_semi_decide in Hn. 
  destruct (dec (q < q)).
  generalize (@eq_not_lt Q). 
  intros SS; specialize (SS _ _ q q). 
  apply SS. 
  reflexivity. 
  apply l.   
  case (not_bot Hn). 
+ unfold D_op.
  red in HH. 
  destruct (f x). 
  simpl in H.
  unfold QRlow in H. 
  unfold Rllt in H. 
  revert HH; apply (Trunc_ind _); 
  intros (s,(E1,E2)). 
  simpl in E2. 
  unfold semi_decide, Rllt_semi_dec, 
         decidable_semi_decide in E2. 
  destruct (dec (s < q)) in E2.
  case E2; apply top_greatest.  
  assert (Hsq : Qle q s). 
  apply Fpo_Qle_Qlt; trivial.  
  apply Rlow_mon with rl s.
  trivial.
  unfold Rlle; trivial.
  trivial. 
Qed.

(** Monotonicity of the operator on the functional arg*)
Lemma D_op_mon_f {A:hSet}: forall q (f:mf A) g,
    fle f g -> D_op q f ⊆  D_op q g. 
Proof. 
intros q f g Hfg z; unfold D_op.
assert (Hle : Rlle (f z) (g z)).   
apply Hfg. 
destruct (f z). 
destruct (g z).
apply imply_le.
exact (Hle q). 
Qed. 

(** Monotonicity of the operator on the rational arg*)
Lemma D_op_mon_q {A:hSet} : forall p q (f : mf A),
    Qle p q -> D_op q f ⊆  D_op p f. 
Proof. 
intros p q f Hpq.
assert (Haux : forall z, D_op q f z -> D_op p f z).   
intros z. 
intros Hq. 
apply D_op_correct. 
apply D_op_correct in Hq. 
red; red in Hq. 
unfold Rllt in *.  
revert Hq; apply (Trunc_ind _). 
intros Hq; apply tr. 
destruct Hq as (s,(Hq1,Hq2)). 
exists s; split. 
+ trivial. 
+ intros Ho. apply Hq2. 
  apply Rlow_mon with (QRlow p) s. 
  reflexivity. 
  intros v Hv. 
  unfold QRlow. 
  simpl in *. 
  unfold semi_decide, Rllt_semi_dec, 
         decidable_semi_decide in *. 
  destruct (dec (v < q)). 
  apply top_greatest. 
  destruct (dec (v < p)). 
  assert (Hr : v < q). 
  apply orders.lt_le_trans with p; try trivial. 
  case (n Hr). 
  trivial. trivial.
+ intros z; apply imply_le; exact (Haux z). 
Qed.

Hint Resolve D_op_mon_f D_op_mon_q.

End Dop. 