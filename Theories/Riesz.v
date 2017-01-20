
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

Require Export Spaces.RoundedClosed
               Spaces.Opens Spaces.Functions 
               Theories.Valuations
               Theories.LowerIntegrals.
              

Set Implicit Arguments.



(** * D_op: operator which takes a function and a rational 
and gives the open in which the function is bigger than the 
rational *)

(** see a similart construction with Dedekind cuts in 
Coquand-Spitters 09, Integrals and valuations *)

Section Dop.

Context `{Funext} `{Univalence}.

Definition D_op {A :hSet} (q : Q) : mf A -> OS A.
Proof. 
intros f z.
destruct (f z). 
refine (val rl q). 
Defined. 

(** Correctness of the definition *)
Lemma D_op_correct {A:hSet}: forall f q (x:A),
    (D_op q f) x <-> QRlow q < (f x).
Proof. 
intros f q x; split; intro HH. 
+ unfold D_op in HH.
  simpl in HH. 
  destruct (f x); simpl.
  red; unfold Rllt, RCLt_l. 
  apply tr.   
  exists q. 
  split; trivial.
  unfold QRlow. 
  simpl; intros Hn. 
  unfold semi_decide in Hn. 
  destruct (decide (q < q)).
  generalize (@orders.eq_not_lt Q). 
  intros SS; specialize (SS _ _ q q). 
  apply SS. reflexivity. apply l.   
  case (not_bot Hn). 
+ unfold D_op.
  red in HH. 
  destruct (f x). 
  simpl in H.
  unfold QRlow in H. 
  unfold Rllt, RCLt_l in H. 
  revert HH; apply (Trunc_ind _); intros HH. 
  destruct HH as (s,(E1,E2)). 
  simpl in E2. 
  unfold semi_decide in E2. 
  destruct (decide (s < q)) in E2.
  case E2; apply top_greatest.  
  assert (Hsq : q <= s). 
  apply Fpo_Qle_Qlt; trivial.  
  apply RC_mon with Qle rl s.   
  intros s1 s2; apply (antisymmetry le).
  apply orders.le_or_lt. 
  apply Fpo_Qle_Qlt. 
  intros F. case (n F). 
  unfold RCLe_l; auto. 
  trivial. 
Qed.

(** Monotonicity of the operator on the functional arg*)
Lemma D_op_mon_f {A:hSet}: forall q f g,
    f <= g -> D_op q f <= @D_op A q g. 
Proof. 
intros q f g Hfg z; unfold D_op.
assert (Hle : f z <= g z).   
apply Hfg. destruct (f z). 
destruct (g z).
red in Hle.
unfold Rl_pos_Le, Rlle, RCLe_l in Hle.
apply imply_le.
exact (Hle q). 
Qed. 

(** Monotonicity of the operator on the rational arg*)
Lemma D_op_mon_q {A:hSet} : forall p q f,
    p <= q -> @D_op A q f <= @D_op A p f. 
Proof. 
intros p q f Hpq.
assert (Haux : forall z, D_op q f z -> D_op p f z).   
intros z. intros Hq. 
apply D_op_correct. 
apply D_op_correct in Hq. 
red; red in Hq. 
unfold Rllt, RCLt_l in *.  
revert Hq; apply (Trunc_ind _). 
intros Hq; apply tr. 
destruct Hq as (s,(Hq1,Hq2)). 
exists s; split. 
+ trivial. 
+ intros Ho. apply Hq2. 
  apply RC_mon with Qle (QRlow p) s. 
  intros x y; apply (antisymmetry le). 
  apply orders.le_or_lt. 
  reflexivity. unfold RCLe_l. 
  intros v Hv. 
  unfold QRlow. simpl in *. 
  unfold semi_decide in *. 
  destruct (decide (v < q)). 
  apply top_greatest. 
  destruct (decide (v < p)). 
  assert (Hr : v < q). 
  apply orders.lt_le_trans with p; try trivial. 
  case (n Hr). 
  trivial. trivial.
+ intros z; apply imply_le; exact (Haux z). 
Qed.

Hint Resolve D_op_mon_f D_op_mon_q.

End Dop. 

(** * OpenFun : operator which take an open and return 
the characteristic function of this open *)

(** such a construction is possible because of the way 
we have defined the lower reals as maps from Q to Sier. 
We define the OpenFun by induction on the Sierpinski sets
*)

Section OpenFun. 
Context `{Funext} `{Univalence}. 

(** Map from Sier to RlowPos *)
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
  intros ss sh; apply (antisymmetry le). apply orders.le_or_lt.
  reflexivity. trivial. trivial.
Defined.

(** Monotonicity of the map from Sier to RlowPos *)
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
  assert (Hr : OpenFun_aux (sup Unit f) = RllubPos
                        (fun n => OpenFun_aux (f n))).
  auto. rewrite Hr.
  apply (Rllub_lub (fun n => OpenFun_aux (f n))); trivial.
  trivial.
+ intros f x H1 H2.
  assert (Hr : OpenFun_aux (sup Unit f) = RllubPos
                        (fun n => OpenFun_aux (f n))).
  auto. rewrite Hr.
  apply Rllub_le.
  intros n.
  apply H2.
Qed.
      
(** Map from Opens to characteristic function *)
Definition OpenFun (A : hSet) : forall (U : A -> Sier),
                                       (A -> RlowPos). 
Proof. 
intros s z. 
specialize (s z).
exact (OpenFun_aux s).
Defined.

(** OpenFun is definite *)
Lemma OpenFun_def {A} : forall U:OS A, U = OS_empty
                               -> OpenFun _ U = fun x => RlP_0. 
Proof.
intros U HU.   
apply path_forall. 
intros x. 
rewrite HU. 
auto. 
Qed. 

(** OpenFun is sub-probabilistic*)
Lemma OpenFun_prob {A} : forall U:OS A, U = OS_full
                               -> OpenFun _ U <= fun x => RlP_1. 
Proof.
intros U HU x. 
rewrite HU. 
auto. 
Qed. 

(** OpenFun is monotonic *)
Lemma OpenFun_mon {A} : forall U V:OS A, U <= V -> OpenFun _ U <= OpenFun _ V.
Proof.
intros U V H1 s.
unfold OpenFun.
apply OpenFun_aux_mon; trivial.
apply (H1 s).
Qed.

(** OpenFun on the Meet *)
Definition OpenFun_meet {A} (U V : OS A) := OpenFun _ (OS_meet U V).

Lemma OpenFun_meet_is_meet {A}: forall (U V : OS A) s r,
      (val (rl ((OpenFun _ U) s)) r
    /\ val (rl ((OpenFun _ V) s)) r) <->
       val (rl ((OpenFun_meet U V) s)) r. 
Proof.
intros U V r s.  
split.
+ intros (H1,H2).
  unfold OpenFun_meet.
  unfold OS_meet.  
   
  unfold val.  admit.
  
+ intros HH. 
  split.
  - apply RC_mon with Qle (rl (OpenFun_aux ((OS_meet U V) r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierMeet_is_meet.
    apply HH. 
  - apply RC_mon with Qle (rl (OpenFun_aux ((OS_meet U V) r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierMeet_is_meet.
    apply HH. 
Admitted.

(** OpenFun on the Join *)
Definition OpenFun_join {A} (U V : OS A) := OpenFun _ (OS_join U V). 

Lemma OpenFun_join_is_join {A}: forall (U V : OS A) s r,
      (val (rl ((OpenFun _ U) s)) r
    \/ val (rl ((OpenFun _ V) s)) r) <->
       val (rl ((OpenFun_join U V) s)) r. 
Proof.
intros U V r s.  
split.
+ intros HD. case HD; intros HDO. 
  - unfold OpenFun_meet.
    apply RC_mon with Qle (rl (OpenFun_aux (U r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierJoin_is_join.
    apply HDO.
  - unfold OpenFun_meet.
    apply RC_mon with Qle (rl (OpenFun_aux (V r))) s.
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    apply OpenFun_aux_mon. 
    apply SierJoin_is_join.
    apply HDO.  
+ intros HH.
  unfold OpenFun_join in HH.
  unfold OS_join in HH.
  admit. 
Admitted. 

(** OpenFun is modular : more tricky... *)
Lemma OpenFun_mod {A}: forall (U V : OS A), fplus (OpenFun _ U) (OpenFun _ V) =
                                fplus (OpenFun _ (OS_meet U V))
                                      (OpenFun _ (OS_join U V)).
Proof.
intros U V.
apply path_forall; intros z. 
apply (antisymmetry le). 
+ intros q Hs. simpl in *. 
  apply Rlplus_eq_pr in Hs.
  assert (Ho : merely
         (∃ r' s' : Q,
          val (rl (OpenFun _ (OS_meet U V) z)) r'
          ∧ val (rl (OpenFun _ (OS_join U V) z)) s'
          ∧ q = r' + s')).
  revert Hs. apply (Trunc_ind _). 
  intros Hs; apply tr. 
  destruct Hs as (r,(s,(Hr,(Hs,Hq)))). 
  destruct (Qle_total r s).
  - exists r, s. 
    repeat split; try trivial.
    * unfold OS_meet.
      assert (HrV : val (rl (OpenFun A V z)) r). 
      apply RC_le with Qle s. 
      intros ss ss'; apply (antisymmetry le). 
      apply orders.le_or_lt. apply Hs. apply l. 
      apply OpenFun_meet_is_meet.            
       split; trivial.
    * apply RC_mon with Qle (rl (OpenFun_aux (V z))) s. 
      intros ss ss'; apply (antisymmetry le). 
      apply orders.le_or_lt. reflexivity. 
      apply OpenFun_aux_mon. 
      apply SierJoin_is_join.
      apply Hs.  
  - exists s, r. 
    repeat split; try trivial.
    * unfold OS_meet. 
      assert (HrV : val (rl (OpenFun_aux (U z))) s). 
      apply RC_le with Qle r. 
      intros ss ss'; apply (antisymmetry le). 
      apply orders.le_or_lt. apply Hr. apply l.  
      apply OpenFun_meet_is_meet. 
      split; trivial.   
    * apply RC_mon with Qle (rl (OpenFun_aux (U z))) r. 
      intros ss ss'; apply (antisymmetry le). 
      apply orders.le_or_lt. reflexivity. 
      apply OpenFun_aux_mon. 
      apply SierJoin_is_join.
      apply Hr.  
    * rewrite Hq. 
      rewrite rings.plus_comm.  
      reflexivity. 
  - apply pred_plus_pr; trivial.  
+ intros q Hs. simpl in *.
  apply rlow_pred_plus_pr in Hs.
  assert (Ho : merely
         (∃ r' s' : Q,
          val (rl (OpenFun _ U z)) r'
          ∧ val (rl (OpenFun _ V z)) s'
          ∧ q < r' + s')).
  revert Hs. apply (Trunc_ind _). 
  intros Hs; apply tr. 
  destruct Hs as (r,(s,(Hr,(Hs,Hq)))).
  destruct (Qle_total r s).
   - apply OpenFun_join_is_join in Hs.
     destruct Hs. 
     -- exists s, r.               
        repeat split; try trivial. 
        * apply OpenFun_meet_is_meet in Hr. 
          destruct Hr as (Hr1,Hr2). 
          trivial.  
        * rewrite (rings.plus_comm). 
          trivial.
     -- exists r, s. 
        repeat split; try trivial. 
        apply OpenFun_meet_is_meet in Hr. 
        destruct Hr as (Hr1,Hr2). 
        trivial.  
   - exists r, r. 
     repeat split; try trivial.
     * apply RC_mon with Qle (rl (OpenFun _ (OS_meet U V) z)) r. 
       intros ss ss'; apply (antisymmetry le). 
       apply orders.le_or_lt. reflexivity.
       apply OpenFun_aux_mon. 
       apply SierMeet_is_meet.
       apply Hr.  
     * apply RC_mon with Qle (rl (OpenFun _ (OS_meet U V) z)) r. 
       intros ss ss'; apply (antisymmetry le). 
       apply orders.le_or_lt. reflexivity.
       apply OpenFun_aux_mon. 
       apply SierMeet_is_meet.
       apply Hr.
     * apply orders.lt_le_trans with (r + s); trivial.  
       apply semirings.plus_le_compat; try reflexivity; trivial. 
   - apply pred_plus_pr.      
     revert Ho; apply (Trunc_ind _). 
     intros (r,(s,(Ho1,Ho2))); apply tr. 
     exists r.
     exists (q - r). 
     split; try trivial.      
     split. 
     * apply RC_le with Qle s. 
      -- intros x y; apply (antisymmetry le). 
      -- intros x y; apply orders.le_or_lt.       
      -- apply (fst Ho2). 
      -- apply rings.flip_le_minus_l.
         rewrite rings.plus_comm.
         apply orders.lt_le. 
         apply (snd Ho2). 
     * apply rings.plus_conjugate_alt.
Qed.


Lemma D_op_OpenFun {A  : hSet}: forall (U : OS A),
           (D_op 0 (OpenFun A U)) = U. 
Proof. Admitted. 


End OpenFun. 



Section Sum_p_r.
(** *   *)
Variable (A : hSet). 

Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n). 

(** sum_prod_sub: sum before rationalization*) 
Fixpoint sum_prod_sub (p : nat) (f : mf A) (m :Val A) 
         {struct p} : RlowPos := match p with
           | 0 => (mu _ m) (D_op 0 f)
           | S p => (sum_prod_sub p f m) + 
              ((mu _ m) (D_op (qn (S p)) f))
     end.                         

(** sum_p_r: sum after rationalization*) 
Definition sum_p_r (N : nat) (f :  mf A) (m : Val A) := match N with
           | 0 => (mu _ m) (D_op 0 f)
           | S p => Rlow_mult_q (1/(qnp (S N))) (sum_prod_sub (S N) f m) end.

(** Properties of sum_p_r *)
Lemma sum_p_r_prod : forall q S mm, 0 < q -> 
    Rlow_mult_q (1 / (qnp q)) (sum_prod_sub q S mm) =
    Rlow_mult_q 1 (sum_prod_sub 1 S mm).
Proof.
intros n f mm.
induction n.
+ intros H1.
  assert (Hr : O <= O).
  reflexivity.
  apply orders.le_not_lt_flip in Hr.
  case (Hr H1).
+ intros Hs0; clear Hs0.
  apply (antisymmetry le).
  - intros q Hq.
    unfold Rlow_mult_q in *;
    unfold pred_multQ in *. 
    simpl.
    simpl in Hq.
    simpl in IHn.
    unfold pred_multQ in *. 
    simpl in IHn.
(* cumbersome *)
Admitted.


Lemma sum_prod_sub_mon_f : forall n f g mm, f <= g -> 
      sum_prod_sub n f mm <= sum_prod_sub n g mm.
Proof.
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+ simpl.
  transitivity (sum_prod_sub n f mm
                + mu _ mm (D_op (qn (S n)) g)).
  apply Rllepos_plus_le_preserving.
  apply mu_mon.
  apply D_op_mon_f; trivial.  
  unfold plus.
  rewrite RlPPlus_comm.
  rewrite (RlPPlus_comm (sum_prod_sub n g mm) _).
  apply Rllepos_plus_le_preserving.
  trivial.
Qed.

Lemma sum_p_r_mon_f : forall n f g mm, f <= g -> 
      sum_p_r n f mm <= sum_p_r n g mm.
Proof.
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+ simpl.
Admitted. 
  
Lemma Rlow_mult_q_mon_f : forall q n f g mm, f <= g -> 
    Rlow_mult_q q (sum_prod_sub n f mm) <=
    Rlow_mult_q q (sum_prod_sub n g mm).
Proof.
intros q n f g mm Hfg s Hs.
unfold Rlow_mult_q in *.  
simpl in *. unfold pred_multQ in *.
apply RC_mon with Qle (rl (sum_prod_sub n f mm))
                      (pos q * s).
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply sum_prod_sub_mon_f; trivial.
trivial.
Qed.

Lemma toRlseq_antimon' : forall n Mu f,
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) (S n))
    <=
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) n).
Proof.
intros n Mu U.  
unfold toRlseq.
intros q Hq.
induction n.
+ unfold sum_p_r in *.
  unfold Rlow_mult_q in Hq.
  unfold pred_multQ in Hq.
  simpl in Hq. 
  apply pred_plus_pr in Hq.
  revert Hq; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  apply pred_plus_pr in E1.
  revert E1; apply (Trunc_ind _).
  intros (r1,(r2,(E11,(E12,E13)))).
  assert (Hpos : forall q : Q+, pos (1 / q) = pos q).
  admit.  

  rewrite Hpos in E3.
  simpl in E3.
  rewrite E13 in E3.
  assert (H2 : 2*q = r1 + r2 + s).
  apply E3.
  clear E3.
  assert (H4 : q = (r1 + r2 + s) / 2).
  admit.

  rewrite H4.
  apply RC_le with Qle r1.
  intros x y; apply (antisymmetry le).
  intros x y; apply orders.le_or_lt.
  trivial.
  admit.

+ simpl.
  unfold pred_multQ.
  assert (Hpos : forall q : Q+, pos (1 / q) = pos q).
  admit.  

  rewrite Hpos.
  simpl.
  simpl in Hq.
  unfold pred_multQ in Hq.
  rewrite Hpos in Hq; simpl in Hq.
  apply pred_plus_pr in Hq.
  revert Hq; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  apply pred_plus_pr in E1.
  revert E1; apply (Trunc_ind _).
  intros (r1,(r2,(E11,(E12,E13)))).

  
  admit.
Admitted.

Lemma sum_p_r_add : forall n f g mm, 
    sum_p_r n f mm + sum_p_r n g mm =
    sum_p_r n (fun x => f x + g x) mm. 
Proof.
intros n f g mm.
induction n.  
+ simpl.
  apply (antisymmetry le).
  - intros q Hq.
    unfold D_op in *.
    simpl in *.
    apply pred_plus_pr in Hq.
    revert Hq; apply (Trunc_ind _).
    intros (r,(s,(E1,(E2,E3)))).

    admit. (* add mu*)

    
  - intros q Hq.
    apply pred_plus_pr.
    apply tr.
    
    admit.   (* add mu*)
    
+ apply (antisymmetry le).
  intros q Hq.

  admit.
  transitivity (sum_p_r  n f mm + sum_p_r n g mm).
  rewrite IHn.
  apply toRlseq_antimon'.
    
  admit. 
Admitted.


Lemma sum_p_r_Sn : forall n Mu f,
    sum_p_r (S n) f Mu =  Rlow_mult_q (qnp (S n) / qnp n)
                                     (sum_p_r n f Mu)
                          +  Rlow_mult_q (1 / qnp (S n))
                        ((mu _ Mu) (D_op (qn (S n)) f)).
Proof. 

Admitted. 

  
(* OK *)
Lemma toRlseq_antimon : forall n n' Mu f, n <= n' -> 
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) n')
    <=
    (toRlseq (λ n0 : nat, sum_p_r n0 f Mu) n).
Proof.
intros n n' Mu f Hnn'.
assert (X : exists P : nat, n' = P + S n).
admit.

destruct X as (p,Hp).
induction n'.
+ assert (Hn0 : n = 0).
  apply peano_naturals.minus_ge in Hnn'.
  unfold CutMinus in Hnn'.
  assert (Hnn'' : peano_naturals.nat_cut_minus n 0 = 0).
  apply Hnn'.
  admit.

  rewrite Hn0.
  intros q; trivial.
+ rewrite Hp.
Admitted.

Lemma sum_p_r_mon_f2 : forall n f g mm, f <= g -> 
      sum_p_r n f mm <= sum_p_r n g mm.
Proof. 
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+admit. 
Admitted.


End Sum_p_r. 


(** * Free modular monoid on the open subsets of a set **)

(** - Free monoid on (OS A): 
           all the finite sets of elements of OS A, modulo commutativity
           :: is the monoidal operator
    - Free modular monoid on (OS A): 
           free monoid such that forall U, V in OS A, 
           U::V::l <-> meet U V::join U V::l *)

Section Bags_equiv.
  
  
(** Coquand-Spitters, Vickers build the set of simple functions to define the 
integral from a measure; they both use the Tarski's free monoid quotiented by a modularity law. 
Here we provide the construction of the free monoid using bag equivalence (see Danielson : 
http://www.cse.chalmers.se/~nad/publications/danielsson-bag-equivalence.pdf)
*)

(** Free modular monoid on a type T*)
Variable T : Type.
Context {T_isset : IsHSet T}.

(** equivalence relation for commutativity*)
Fixpoint Any (l : list T) (P : T -> Type) : Type := match l with
              | nil => False
              | cons x q => (P x) \/ (Any q P)
         end.                         

Definition EqT := fun (a b: T) => a = b.
Definition App (l: list T) (s : T) := (Any l (EqT s)).

Definition eq_bag := fun l1 l2 => forall r,
                      merely ((App l1 r) <~> (App l2 r)). 

 
Definition free_mon : Type := @quotient _ eq_bag _. 

(** T should be a lattice *)
Context {Tjoin : Join T}.
Context {Tmeet : Meet T}.
Context {Tlatt : Lattice T}.

(** equivalence relation for modularity*)
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

(** Free modular monoid using HoTT quotient *)
Definition modular_mon : Type := @quotient _ eq_free_mod _.  

End Bags_equiv.


(** * Variant of the definition of simple functions. 
We define measures of simples "functions" as sum of the
measures of the D_op corresponding to a subdivision of
size n. When n is near infinity, the measure of the
simple function approachs the integral of the function  *)

Section Simples. 
Context {A : hSet}. 

(** Definition of the integral from measures and 
subdivisions as classically in measure theory *)
Definition I_mu (mm : Val A) : IntPos A.
Proof.
exists (fun f => RllubPos (fun n => (sum_p_r n f mm))); red. 
+ assert (HO : forall n, sum_p_r n (fzero A) mm = RlP_0).
  * induction 0; unfold sum_p_r.
    - simpl; unfold qn, pos_of_nat; simpl.
      unfold fzero.
      assert (HO : (D_op 0 (λ _ : A, RlP_0)) = OS_empty).
      unfold D_op.
      simpl. unfold semi_decide.
      destruct (decide (0 < 0)).
      assert (Hrfl : Qzero <= Qzero).
      reflexivity.
      apply orders.le_not_lt_flip in Hrfl.
      case (Hrfl l).
      reflexivity.
      rewrite HO.
      rewrite mu_empty_op.
      reflexivity.
    - unfold sum_p_r in *.
      rewrite sum_p_r_prod.
      unfold sum_prod_sub.
      unfold D_op.
      simpl. unfold semi_decide.
      destruct (decide (0 < 0)).
      apply orders.lt_not_le_flip in l. 
      assert (Hu : Qzero <= Qzero).
      reflexivity. 
      case (l Hu).
      destruct (decide (qn 1 < 0)).
      unfold qn in l.
      assert (Hl : 0 <= pos (pos_of_nat 1)).
      apply orders.lt_le.
      apply (pos_of_nat 1).
      apply orders.lt_not_le_flip in l. 
      case (l Hl).      
      rewrite mu_empty_op. unfold plus.
      rewrite RlPPlus_left_id.
      apply Rlow_mult_q_RlP_0.
      apply peano_naturals.S_gt_0.
  * apply (antisymmetry le).
    apply RllubPos_le. 
    intros n. 
    rewrite (HO n). 
    unfold Rlle, RCLe_l; auto.  
    specialize (HO 0). 
    transitivity (sum_p_r 0 (fzero A) mm).
    rewrite HO; reflexivity. 
    generalize (RllubPos_lub (λ n : nat, sum_p_r n (fzero A) mm)). 
    intros Hrl. 
    specialize (Hrl 0). 
    trivial.  
+ intros f g.
  apply (antisymmetry le).
  - intros z Hq1.
    unfold fplus in Hq1.
    assert (Hrll : (λ n : nat,
           sum_p_r n (λ x : A, RlP_plus (f x) (g x)) mm)
                  =
                 λ n : nat, sum_p_r n (λ x : A, f x) mm +
                            sum_p_r n (λ x : A, g x) mm ).
    apply path_forall. intros n.
    symmetry. apply sum_p_r_add.
    --  rewrite Hrll in Hq1.
        assert (Hlub : RllubPos (λ n : nat,
                             sum_p_r n (fplus f g) mm)
                  =
                  RllubPos (λ n : nat, sum_p_r n f mm) +
                  RllubPos (λ n : nat, sum_p_r n g mm)).
    apply (antisymmetry le). 
    --- apply Rllub_le. 
        intros n. 
        unfold toRlseq. 
        assert (H1 : Rlle ((λ n : nat, sum_p_r n
              (λ x : A, RlP_plus (f x) (g x)) mm) n)
                          ((fun n => sum_p_r n f mm + sum_p_r n g         mm) n)).
        rewrite sum_p_r_add.        
        intros q Hq; trivial.           
        simpl in H1. 
        assert (H2 : Rlle (RlPlus (sum_p_r n f mm) (sum_p_r n g mm))
          (RllubPos (λ n0 : nat, sum_p_r n0 f mm) +
           RllubPos (λ n0 : nat, sum_p_r n0 g mm))).
        assert (Hle1 : Rlle (RlPlus
                        (RllubPos (λ n0 : nat, sum_p_r n0 f mm))
                        (sum_p_r n g mm))
                     (RllubPos (λ n0 : nat, sum_p_r n0 f mm) +
              RllubPos (λ n0 : nat, sum_p_r n0 g mm))).
        apply RlPlus_le_preserving.
        apply (Rllub_lub (λ n0 : nat, sum_p_r n0 g mm) n).
        assert (Hle2 : Rlle (RlPlus (sum_p_r n f mm)
                                    (sum_p_r n g mm))
                            ((RlPlus (RllubPos (λ n0 : nat,
                                  sum_p_r n0 f mm))
                                 (sum_p_r n g mm)))).
        rewrite RlPlus_comm.
        rewrite (RlPlus_comm _ (sum_p_r n g mm)).
        apply RlPlus_le_preserving.
        apply (Rllub_lub (λ n0 : nat, sum_p_r n0 f mm) n).
        intros q Hq.
        specialize (Hle1 q).
        specialize (Hle2 q).
        apply Hle1, Hle2.
        trivial.
        unfold Rlle, RCLe_l in *. 
        intros q Hq. 
        apply H2. 
        apply H1; trivial.
    --- intros s Hs.  
        apply (RllubPos_le
              (λ n : nat, sum_p_r n (fplus f g) mm)).
        intros n. 
        apply (RllubPos_lub (λ n0 : nat, sum_p_r n0
                                                 (fplus f g) mm) n).
        rewrite Hrll; simpl; unfold toRlseq; clear Hq1.
        assert (Hpl :  elt Q Qlt
         (rl (RlP_plus (RllubPos (λ n : nat, sum_p_r n f mm))
                       (RllubPos (λ n : nat, sum_p_r n g mm)))) s).
        apply Hs; clear Hs; rewrite Hrll. 
        rewrite RlP_plus_RlPlus in Hpl.
        unfold semi_decide.
        unfold SDseq_Rlow.
        unfold semi_decide_exists.         
        unfold semi_decide.
        apply pred_plus_pr in Hpl.
        revert Hpl; apply (Trunc_ind _).         
        intros (r,(x,(Hrs1,(Hrs2,Hrs3)))).
        unfold RllubPos in Hrs1.
        simpl in Hrs1.
        unfold RllubPos in Hrs2.
        simpl in Hrs2.
        unfold semi_decide, SDseq_Rlow, semi_decide_exists,
               semi_decide in *.
        unfold toRlseq in Hrs1, Hrs2.
        apply top_le_enumerable_sup'.
        apply top_le_enumerable_sup' in Hrs1.
        apply top_le_enumerable_sup' in Hrs2.
        revert Hrs1; apply (Trunc_ind _).
        intros (s1,Hrs1).
        revert Hrs2; apply (Trunc_ind _).
        intros (s2,Hrs2).
        destruct (peano_naturals.nat_le_dec s1 s2).
        * apply tr. exists s1.            
          apply pred_plus_pr.
          apply tr.
          exists r, x.
          repeat split; trivial.
          generalize (toRlseq_antimon).
          intros HM.
          specialize (HM A s1 s2 mm g).          
          apply HM; trivial.          
        * apply tr. exists s2.
          apply pred_plus_pr.
          apply tr.
          exists r, x.
          repeat split; trivial.
          generalize (toRlseq_antimon).
          intros HM.
          specialize (HM A s2 s1 mm f).
          apply HM.
          apply peano_naturals.nat_not_lt_le.
          intro F.
          apply n.
          apply orders.lt_le; trivial.
          trivial.
     --- rewrite <- Hlub.
         unfold fplus. simpl.
         rewrite Hrll.
         trivial.
- intros q Hq.
  simpl in *.
  unfold toRlseq in *; simpl in *.
  assert (Hlub : RllubPos (λ n : nat, sum_p_r n (fplus f g) mm)
                  =
                  RllubPos (λ n : nat, sum_p_r n f mm) +
                  RllubPos (λ n : nat, sum_p_r n g mm)).
  apply pred_plus_pr in Hq.
  apply (antisymmetry Rllepos).
  unfold Rllepos; simpl.
  unfold toRlseq. 
  intros c Hc.
  revert Hq; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  unfold Rllub in Hc.
  simpl in Hc.
  unfold semi_decide, SDseq_Rlow, semi_decide_exists,
         semi_decide in E1, E2, Hc.
  apply top_le_enumerable_sup' in Hc.
  apply top_le_enumerable_sup' in E1.
  apply top_le_enumerable_sup' in E2.
  revert Hc; apply (Trunc_ind _).
  intros (nc,Hc).
  rewrite <- sum_p_r_add in Hc.
  apply pred_plus_pr in Hc.
  revert E1; apply (Trunc_ind _).
  intros (n1,E1).
  revert E2; apply (Trunc_ind _).
  intros (n2,E2).
  apply pred_plus_pr.
  revert Hc; apply (Trunc_ind _).
  intros (r',(s',(HC1,(HC2,HC3)))).
  apply tr.
  exists r', s'.
  repeat split; trivial.
  apply Rllub_lub with nc; trivial.
  apply Rllub_lub with nc; trivial.
  unfold Rllepos; simpl.
  unfold toRlseq. 
  intros c Hc. 
  assert (E : merely (exists r s,
              val (Rllub (λ n : nat, sum_p_r n f mm)) r  ∧
              val (Rllub (λ n : nat, sum_p_r n g mm)) s  ∧
              c = r + s)).  
  apply pred_plus_pr. apply Hc. 
  revert E; apply (Trunc_ind _).
  intros (r,(s,(E1,(E2,E3)))).
  apply top_le_enumerable_sup' in E1.
  apply top_le_enumerable_sup' in E2.
  apply top_le_enumerable_sup'.
  revert E1; apply (Trunc_ind _).
  intros (n1,E1).
  revert E2; apply (Trunc_ind _).
  intros (n2,E2).
  apply tr.
  unfold semi_decide, SDseq_Rlow, semi_decide_exists,
  semi_decide in *.
  assert (Hn : forall n : nat, sum_p_r n (fplus f g) mm =
          sum_p_r n f mm + sum_p_r n g mm).
  intros m.
  rewrite sum_p_r_add; reflexivity.
  destruct (peano_naturals.nat_le_dec n1 n2).
  * exists n1.            
    rewrite (Hn n1).
    apply pred_plus_pr.
    apply tr.
    exists r, s.
    repeat split; trivial.
    generalize (toRlseq_antimon).
    intros HM.
    specialize (HM A n1 n2 mm g).          
    apply HM; trivial.          
  * exists n2. rewrite (Hn n2).
    apply pred_plus_pr.
    apply tr.
    exists r, s.
    repeat split; trivial.
    generalize (toRlseq_antimon).
    intros HM.
    specialize (HM A n2 n1 mm f).
    apply HM.
    apply peano_naturals.nat_not_lt_le.
    intro F. apply n.
    apply orders.lt_le; trivial. trivial.
  * unfold semi_decide, SDseq_Rlow, semi_decide_exists,
    semi_decide in *.
    apply pred_plus_pr in Hq.
    revert Hq; apply (Trunc_ind _).
    intros (r,(s,Hq)).
    apply top_le_enumerable_sup'.
    destruct Hq as (E1,(E2,E3)).
    apply top_le_enumerable_sup' in E1.
    apply top_le_enumerable_sup' in E2.
    revert E1; apply (Trunc_ind _).
    intros (n1,E1).
    revert E2; apply (Trunc_ind _).
    intros (n2,E2).
    apply tr.
    destruct (peano_naturals.nat_le_dec n1 n2).
    ** exists n1.
       assert (Hn : forall n : nat, sum_p_r n (fplus f g) mm =
          sum_p_r n f mm + sum_p_r n g mm).
       intros m.
       rewrite sum_p_r_add; reflexivity.
       rewrite (Hn n1).
       generalize (toRlseq_antimon).
       intros HM.
       specialize (HM A n1 n2 mm g).
       apply pred_plus_pr.
       apply tr.
       exists r,s.
       repeat split;trivial.
       apply HM; trivial.          
    ** exists n2.
       assert (Hn : forall n : nat, sum_p_r n (fplus f g) mm =
          sum_p_r n f mm + sum_p_r n g mm).
       intros m.
       rewrite sum_p_r_add; reflexivity.
       rewrite (Hn n2).
       apply pred_plus_pr.
       apply tr.
       exists r, s.
       repeat split; trivial.
       generalize (toRlseq_antimon).
       intros HM.
       specialize (HM A n2 n1 mm f).
       apply HM.
       apply peano_naturals.nat_not_lt_le.
       intro F. apply n.
       apply orders.lt_le; trivial. trivial.
  + apply Rllub_le. 
  intros n. 
  induction n.
  - assert (Hone : D_op 0 (fone A) = Ω).
    unfold D_op; simpl.   
    apply path_forall. 
    intros z. unfold semi_decide. 
    destruct (decide (0 < 1)). 
    unfold OS_full; reflexivity.  
    assert (H01 : Qzero < Qone).
    apply semirings.lt_0_1. 
    case (n H01). unfold sum_p_r. 
    rewrite Hone.
    apply mu_prob.
  - unfold toRlseq in *. 
    simpl. generalize toRlseq_antimon'.
    intro HG.
    specialize (HG A n mm).
    unfold toRlseq in *. 
    specialize (HG (fone A)).
    unfold le in HG. 
    unfold Rlle, RCLe_l in *. 
    intros q Hq. 
    apply IHn. 
    apply HG.
    trivial. 
+ intros f g Hfg. 
  apply Rllub_mon. 
  intros n. 
  unfold toRlseq.
  induction n. 
  * unfold sum_p_r; simpl.
    apply mu_mon.
    apply D_op_mon_f; trivial.  
  * unfold sum_p_r.
    apply Rlow_mult_q_mon_f; trivial.
+ intros f. apply (antisymmetry le). 
  - intros q Hq.
    
  
    admit. 
  - intros q.
    apply RllubPos_le; intros N.  
    apply Rllub_mon. 
    intros n p; unfold toRlseq. 
    apply sum_p_r_mon_f. 
    intros x r Hr. 
    unfold RlP_minus_q2 in Hr.   
    simpl in Hr. 
    unfold pred_minusQ_l2 in Hr;
    unfold semi_decide in Hr. 
    apply top_le_join in Hr.
    unfold hor in Hr;
    revert Hr; apply (Trunc_ind _). 
    intros Hr; destruct Hr.
    -- revert i.
       apply RC_mon with Qle.
       intros x' y'; apply (antisymmetry le).  
       intros x' y'; apply orders.le_or_lt. 
       transitivity (r + 0).
       rewrite rings.plus_0_r. 
       reflexivity. 
       apply semirings.plus_le_compat.  
       reflexivity.
       apply orders.lt_le. 
       apply (pos_of_nat N). 
       intros v; trivial. 
    -- destruct (decide (r < 0)).      
       apply (f x); trivial.  
       apply not_bot in i; case i. 
Admitted.

(* to disappear *)
Lemma I_mu_simpl (mm : Val A) : I (I_mu mm) = (fun f =>
               RllubPos (fun n => (sum_p_r n f mm))).
Proof.  
Admitted.

End Simples. 


(** * Formal proof of a constructive Riesz Theorem: for 
the detailed pen-and-paper proof, see Coquand-Spitters09, 
Integrals and valuations, or Vickers08, Monad of valuation 
locales *)

(** From Integrals to Valuations: 
  mu_I (U)  = I (1_U) *)
Definition Riesz1 (A : hSet) : IntPos A -> Val A. 
Proof. 
intros J. 
exists (fun U:OS A => (I J (OpenFun A U))). 
+ red. intros U V.  
  transitivity (I J (OpenFun _ U) + I J (OpenFun _ V)).
  unfold plus; reflexivity. 
  rewrite <- (I_add J (OpenFun _ U) (OpenFun _ V)). 
  transitivity
     ((I J( OpenFun _ (OS_join U V)))+
      (I J (OpenFun _ (OS_meet U V)))); 
  try reflexivity.
  rewrite <- (I_add J (OpenFun _ (OS_join U V))
                    (OpenFun _ (OS_meet U V))).
  rewrite OpenFun_mod, fplus_comm. reflexivity.  
+ red. destruct J. 
  assert (HO : OpenFun A OS_empty = fun x => RlP_0).
  apply path_forall; intros z.
  rewrite OpenFun_def; reflexivity.  
  rewrite HO. simpl. unfold Mdef in I_def. apply I_def. 
+ red. intros U V H. 
  apply I_mon. 
  apply OpenFun_mon; trivial.
+ unfold OS_full; apply I_prob. 
Defined.

(** From Integrals to Valuations : 
I_mu (f) = sup (fun n => sum(i)_0^n (mu (D_op i))
 *)

Definition Riesz2 (A : hSet) : Val A -> IntPos A.
Proof.
intros Nu. 
refine (I_mu Nu). 
Defined. 

(** Homeorphism between integrals and Valuations: 
    - hom1: mu_(I_nu) (U) = nu(U)
    - hom2: I_(mu_J) (f) = J(f) 
 *) 
Lemma Riesz_hom1 (A : hSet) : forall (Mu :Val A) U,
    mu _ (Riesz1 (Riesz2 Mu)) U = mu _ Mu U.
Proof.
intros Mu U.  
simpl. 
rewrite I_mu_simpl.
apply (antisymmetry le).
+ apply Rllub_le; intros n.
  induction n.
  - unfold toRlseq, sum_p_r, sum_prod_sub.
    assert (D_op 0 (OpenFun A U) =  U).  
    generalize (@D_op_correct _ _ A (OpenFun A U) 0).
    intros HGF.
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (U z).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros x. unfold semi_decide.
       destruct (decide (0 < 1)).
       * destruct x; reflexivity.
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * reflexivity.       
    -- intros h HU. 
       admit. 
       
     
    -- rewrite X; unfold Rlle, RCLe_l; auto.    
  - simpl in *. 
    assert (H22 : Rlle ((toRlseq (λ n : nat, sum_p_r n
                 (OpenFun A U) Mu) (S n)))
                       ((toRlseq (λ n0 : nat, sum_p_r n0
                 (OpenFun A U) Mu) n))). 
    apply toRlseq_antimon.
    apply Peano.le_S.
    reflexivity.
    intros s Hs.
    apply IHn.
    apply H22; trivial.
+ unfold sum_p_r.
  transitivity (sum_p_r 0 (OpenFun A U) Mu).
  unfold sum_p_r.  
  unfold sum_prod_sub.
  simpl.
  assert (D_op 0 (OpenFun A U) = U).
  generalize (@D_op_correct _ _ A (OpenFun A U) 0).
  intros HGF.
  unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (U z).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros x. unfold semi_decide.
       destruct (decide (0 < 1)).
       * destruct x; reflexivity.
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * reflexivity.       
    -- simpl. admit.
    -- rewrite X; unfold Rlle, RCLe_l; auto.
    -- simpl. assert (Hu : D_op 0 (OpenFun A U) = U).
       generalize (@D_op_correct _ _ A (OpenFun A U) 0).
       intros HGF.
       unfold D_op, OpenFun, OpenFun_aux.
       apply path_forall; intros z.
       generalize (U z).
       apply (partial_ind0 _ (fun a => _)).
       --- simpl; intros x. unfold semi_decide.
           destruct (decide (0 < 1)).
           * destruct x; reflexivity.
           * assert (Hos : Qzero < Qone).
             apply semirings.lt_0_1.
             case (n Hos).
       --- simpl; unfold semi_decide.
           destruct (decide (0 < 0)).
           * assert (Hj : Qzero <= Qzero). reflexivity.
             generalize (orders.le_not_lt_flip 0 0 Hj).
             intros Hj'; case (Hj' l).          
           * reflexivity.       
       --- simpl. admit.
       --- rewrite Hu. 
       apply (RllubPos_lub (λ n : nat,
       match n with
       | 0 => mu _ Mu U
       | S _ =>
           Rlow_mult_q (1 / qnp (S n))
             (sum_prod_sub n (OpenFun A U) Mu +
              mu _ Mu (D_op (qn (S n)) (OpenFun A U)))
       end) 0).
Admitted.  

Definition Riesz_hom2 (A : hSet) : forall (It : IntPos A) f,
    I (Riesz2 (Riesz1 It)) f = I It f.
Proof.
intros It.
unfold Riesz2.  
rewrite I_mu_simpl.
intros f.
apply (antisymmetry le).
+ unfold sum_p_r. simpl. generalize (I_cont It).
  intros HcI.
  unfold Mcont in *.
  rewrite HcI.
  apply Rllub_le.
  intros n. 
  unfold toRlseq.
   admit.
  
+ rewrite I_cont.
  apply RllubPos_mon.
  intros n. admit. (* ok revoir cont *) 
Admitted.



Lemma Hx1 (A B : hSet) : forall U V (F : A -> Val B), ((λ z : A, val (let (rl, _) :=
                                    mu B (F z) U in rl) 0)
                   ⋂ (λ z : A, val (let (rl, _) :=
                                    mu _ (F z) V in rl) 0))  =
                (λ z : A, val (let (rl, _) :=
                                   mu _ (F z) (U ⋂ V) in rl) 0).
Proof.
simpl.
intros U V F.
apply path_forall.
intros z.
unfold OS_meet.
destruct (F z).
simpl.
apply (antisymmetry le). 
+ apply imply_le. intros H1.
  apply top_le_meet in H1.
  destruct H1 as (H1,H2).  
  assert (H3 : val ((RlMeet (mu U) (mu V))) 0). admit.

  revert H3. 
  apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt. 
  reflexivity.
  assert (H4 : forall X Y, RlMeet (mu X) (mu Y)
              <= mu (X ⊓ Y)). 
  intros X Y q Hq.
  unfold RlMeet in Hq. 
  simpl in Hq; unfold semi_decide in Hq. 
  apply top_le_meet in Hq. 
  destruct Hq as (Hq1,Hq2).
  
 
        
 
  admit.   

   
 
  unfold SierMeet. 
  generalize (val (rl (mu (λ x : B, U x))) 0). 
  generalize (val (rl (mu  (λ x : B, V x))) 0).
  apply (partiality.partial_ind0 _
                   (fun a => forall b, _)).
  simpl.   
    
  generalize (val (let (rl, _) := mu U in rl) 0).
  generalize (val (let (rl, _) := mu V in rl) 0).

  
  assert (rl (mu (λ x : B, SierMeet (U x) (V x))) =
          RlJoin (rl (mu U)) (rl (mu V))).
  
Admitted. 
  


Lemma Hx2 (A B : hSet) : forall U V F, ((λ z : A, val (let (rl, _) :=
                                        mu B (F z) U in rl) 0)
                  ∪ (λ z : A, val (let (rl, _) := mu _ (F z) V in rl) 0))  =
                 (λ z : A, val (let (rl, _) := mu _ (F z) (U ∪ V) in rl) 0).
Proof.
simpl.
intros U V F.
apply path_forall.
intros z.
unfold OS_join.
destruct (F z).
simpl.
apply (antisymmetry le). 
+ apply imply_le. intros H1.
  apply top_le_join in H1.
  unfold hor in H1.
  revert H1; apply (Trunc_ind _).
  intros HH. destruct HH. 
  - apply RC_mon with Qle (let (rl, _) := mu U in rl) 0.
    intros x y; apply (antisymmetry le).
    intros x y; apply orders.le_or_lt.
    reflexivity. simpl.
    apply mu_mon.
    intros s.
    apply SierJoin_is_join.
    simpl; trivial.
  - apply RC_mon with Qle (let (rl, _) := mu V in rl) 0.
    intros x y; apply (antisymmetry le).
    intros x y; apply orders.le_or_lt.
    reflexivity. simpl.
    apply mu_mon.
    intros s.
    apply SierJoin_is_join.
    simpl; trivial.
+ apply imply_le. intros H1.
  apply top_le_join.
  unfold hor. 
  apply tr. 
  unfold SierJoin in H1.
  simpl in H1.   
  assert (Hj2 : val
         (let (rl, _) := RlPJoin (mu U) (mu V) in
          rl) 0).
Admitted.


Lemma OpenFun_D_op {A B : hSet} :
  forall (Mu_X:A -> Val B) U z, 
    OpenFun A (D_op 0 (λ x : A, mu _ (Mu_X x) U)) z
    = mu _ (Mu_X z) U. 
Admitted. 