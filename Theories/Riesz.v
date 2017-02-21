
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

Lemma Meet_pres_openfun {A:hSet}: forall z s,
          MeetPreserving (fun (U: OS A) => val (rl (OpenFun A U z)) s). 
Proof.
intros z s x y.
apply (antisymmetry le).
+ apply meet_glb;
  apply imply_le;
  apply OpenFun_mon;
  intros k; apply SierMeet_is_meet.
+ Admitted. 

Lemma Join_pres_openfun {A:hSet}: forall z s,
          JoinPreserving (fun (U: OS A) => val (rl (OpenFun A U z)) s). 
Proof.
intros z s x y.
apply (antisymmetry le).
+ admit. 
+ apply join_lub;
  apply imply_le;
  apply OpenFun_mon;
  intros k; apply SierJoin_is_join.
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
  apply Rlplus_eq_pr.
  revert Hs; apply (Trunc_ind _).
  intros Hs; apply tr.
  destruct Hs as (r,(r',(Hr,(Hr',Hq1)))).
  destruct (Qle_total r r') as [E|E].
  - generalize (SierMeet_is_meet). 
    intros Hsm; destruct Hsm.    
    exists r, r'.
    repeat split; try trivial.  
    -- red.
       rewrite Meet_pres_openfun.
       apply meet_glb. 
       * trivial.
       * revert Hr'.
         apply RC_mon with Qle; trivial.
         intros x y; apply (antisymmetry le).
         intros x y; apply orders.le_or_lt.
         intros s Hs; trivial.
    -- apply RC_mon with Qle (rl (OpenFun A V z)) r'; trivial.
       intros x y; apply (antisymmetry Qle).
       intros x y; apply orders.le_or_lt.
       reflexivity.
       apply OpenFun_mon. 
       intros s; apply SierJoin_is_join; apply Hr'.       
  - exists r', r.
    repeat split; try trivial.   
    -- red.
       rewrite Meet_pres_openfun.  
       apply meet_glb. 
       * revert Hr.
         apply RC_mon with Qle; trivial.
         intros x y; apply (antisymmetry le).
         intros x y; apply orders.le_or_lt.
         intros s Hs;trivial.
       * trivial. 
    -- apply RC_mon with Qle (rl (OpenFun A U z)) r; trivial.
       intros x y; apply (antisymmetry Qle).
       intros x y; apply orders.le_or_lt.
       reflexivity.
       apply OpenFun_mon. 
       intros s; apply SierJoin_is_join; apply Hr.
    -- rewrite rings.plus_comm; trivial.
+ intros q Hs. simpl in *. 
  apply Rlplus_eq_pr in Hs.
  apply Rlplus_eq_pr.
  revert Hs; apply (Trunc_ind _).
  intros Hs.
  destruct Hs as (r,(r',(Hr,(Hr',Hq1)))).
  destruct (Qle_total r r') as [E|E].
  - rewrite Join_pres_openfun in Hr'.
    apply top_le_join in Hr'.
    unfold hor in Hr'.
    revert Hr'; apply (Trunc_ind _); intros Hr'.
    apply tr.
    destruct Hr'.
    -- exists r', r.       
       repeat split; try trivial.
       * rewrite Meet_pres_openfun in Hr.
         revert Hr.
         apply SierLe_imply.
         apply SierMeet_is_meet.
       * rewrite rings.plus_comm; trivial.
    -- exists r, r'.       
       repeat split; try trivial.
       * rewrite Meet_pres_openfun in Hr.
         revert Hr.
         apply SierLe_imply.
         apply SierMeet_is_meet.
  - apply tr. exists r', r. 
    repeat split; try trivial.  
    -- rewrite Meet_pres_openfun in Hr.
       assert (Hr1 : val (rl (OpenFun A U z)) r).
       revert Hr.
       apply SierLe_imply.
       apply SierMeet_is_meet.
       revert Hr1.
       apply RC_mon with Qle; try trivial.
       intros x y; apply (antisymmetry Qle).
       intros x y; apply orders.le_or_lt.
       intros s Hs; trivial.
    -- revert Hr; apply OpenFun_mon.
       intros s; apply SierMeet_is_meet.
    -- rewrite rings.plus_comm; trivial.
Qed.

Lemma D_op_OpenFun {A  : hSet}: forall (U : OS A),
           (D_op 0 (OpenFun A U)) = U. 
Proof.
intros U.
pose (Hdp := D_op_correct (OpenFun A U) 0).
apply path_forall.
intros z.
apply (antisymmetry le).
apply imply_le.
intros Hz.
apply Hdp in Hz.
Admitted. 


End OpenFun. 



Section Approx.

Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n).

Definition qP (n : nat) := ((qnp n) * (1 / qnp (S n))).
Definition qbp (n : nat) (b : Q+) := b * (1 / qnp n). 
Definition qb (n : nat) (b : Q+) := pos (qbp n b). 


Fixpoint appr_aux {A : hSet} (f : mf A) (N : nat) (b : Q+)
         (m : Val A):= match N with
             |O => RlP_0
             |S P => mu _ m (D_op (qb N b) f) + appr_aux f P b m
end.       

Definition appr {A : hSet} (f : mf A) (N : nat)
                           (b : Q+) (m : Val A):=
          Rlow_mult_q (1 / qnp N) (appr_aux f N b m).

Lemma appr_aux_0 {A : hSet} : forall N b m, appr_aux (fzero A) N b m = RlP_0. 
Proof.
intros N b m. 
induction N. 
+ simpl; reflexivity.
+ simpl.
  rewrite IHN.
  unfold plus; rewrite RlPPlus_comm.
  rewrite RlPPlus_left_id.
  unfold D_op; simpl.
  unfold semi_decide. 
  destruct (decide
              (qb (S N) b < 0)).
  - assert (H1 : 0 < qb (S N) b).
    unfold qb, qbp.   
    apply is_pos.
    apply orders.lt_flip in H1. 
    case (H1 l). 
  - rewrite mu_empty_op. 
    reflexivity.
Qed.
  
Lemma appr_0 {A : hSet} : forall N b m, appr (fzero A) N b m = RlP_0. 
Proof.
intros N b m. 
unfold appr.
rewrite appr_aux_0.
rewrite Rlow_mult_q_RlP_0.
reflexivity.
Qed.

Lemma appr_aux_add {A : hSet} : forall (f g : mf A) N b m,
         appr_aux (fplus f g) N b m = appr_aux f N b m + appr_aux g N b m. 
Proof. 
intros f g N b m. 
induction N. 
+ simpl; unfold plus;
  rewrite RlPPlus_left_id; reflexivity.
+ simpl; rewrite IHN. 
  assert (H1 : mu _ m (D_op (qb (S N) b) (fplus f g)) =
               mu _ m (D_op (qb (S N) b) f) +
               mu _ m (D_op (qb (S N) b) g)).
  admit.

  rewrite H1.
  unfold plus.
  rewrite <- RlPPlus_assoc.
  rewrite <- RlPPlus_assoc.
  assert (H2 : (RlP_plus
           (mu _ m (D_op (qb (S N) b) g))
           (RlP_plus (appr_aux f N b m)
                     (appr_aux g N b m))) =
               (RlP_plus (appr_aux f N b m)
          (RlP_plus
          (mu _ m (D_op (qb (S N) b) g))
          (appr_aux g N b m)))).
  rewrite RlPPlus_assoc.
  rewrite RlPPlus_assoc.
  rewrite (RlPPlus_comm _ (appr_aux f N b m)).
  reflexivity.
  rewrite H2.
  reflexivity.
Admitted.

Lemma appr_add {A : hSet} : forall (f g : mf A) N b m,
         appr (fplus f g) N b m = appr f N b m + appr g N b m. 
Proof. 
intros f g N b m.
unfold appr.
rewrite appr_aux_add.
apply (antisymmetry le).
+ intros s.
  unfold Rlow_mult_q; simpl; unfold pred_multQ.
  intros hs.
  apply pred_plus_pr in hs.
  apply pred_plus_pr.
  revert hs; apply (Trunc_ind _);
  intros hs; apply tr.
  destruct hs as (r,(t,(hr,(ht,H1)))).
  exists ((qn N)*r), ((qn N)*t).
  repeat split.
  admit. admit.
  admit. (* field for the 3 *)
+ intros s.
  unfold Rlow_mult_q; simpl; unfold pred_multQ.
  intros hs.
  apply pred_plus_pr in hs.
  apply pred_plus_pr.
  revert hs; apply (Trunc_ind _);
  intros hs; apply tr.
  destruct hs as (r,(t,(hr,(ht,H1)))).
  exists ((1 / qn N)*r), ((1 / qn N)*t).
  repeat split.
  admit. admit.
  admit. (* field for the 3 *)
Admitted.
  
Lemma appr_aux_prob {A : hSet} : forall N b m,
         appr_aux (fun x:A => RlP_1) N b m <= Rlow_mult_q (qnp N) RlP_1. 
Proof. 
intros N b m. 
induction N. 
+ simpl. admit. 
+ simpl.
Admitted.

Lemma appr_prob {A : hSet} : forall N b m,
         appr (fun x:A => RlP_1) N b m <= RlP_1. 
Proof.
intros N b m; unfold appr.
transitivity ((Rlow_mult_q (1 / qnp N))
                 (Rlow_mult_q (qnp N) RlP_1)).
intros s.
unfold Rlow_mult_q; simpl; unfold pred_multQ.
intros hs.
unfold semi_decide.
Admitted.

Lemma appr_aux_mon_f {A : hSet} : forall n (f g: mf A) mm b,
    f <= g -> appr_aux f n b mm <= appr_aux g n b mm.
Proof.
intros n f g m b Hfg.
induction n.  
simpl.
intros s hs; trivial.
simpl.
transitivity (mu _ m (D_op (qb (S n) b) f) +
              appr_aux g n b m).
unfold plus.
apply Rllepos_plus_le_preserving; trivial.
unfold plus; rewrite RlPPlus_comm;
rewrite (RlPPlus_comm (mu _ m (D_op (qb (S n) b) g))).
apply Rllepos_plus_le_preserving; trivial.
apply mu_mon.
apply D_op_mon_f; trivial.
Qed.

Lemma appr_mon_f {A : hSet} : forall n (f g: mf A) mm b,
    f <= g -> appr f n b mm <= appr g n b mm.
Proof.
intros n f g m b Hfg.
unfold appr.
intros s; unfold Rlow_mult_q;
simpl; unfold pred_multQ.
apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply appr_aux_mon_f; trivial.
Qed.

Lemma appr_mon_n {A : hSet} : forall n m (f: mf A) mm b,
    n <= m -> appr f n b mm <= appr f m b mm.
Proof.
Admitted.

End Approx. 



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



Definition Riesz2 (A : hSet) (b:Q+) : Val A -> IntPos A. 
Proof.
intros mm. 
exists (fun f => RllubPos (fun n => appr f n b mm)); red.
+ apply (antisymmetry le).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    rewrite appr_0; intros s Hs; trivial.
  - transitivity (appr (fzero A) 0 b mm). 
    rewrite appr_0; intros s Hs; trivial.
    generalize (RllubPos_lub (λ n : nat, appr
                    (fzero A) n b mm) 0); trivial.
+ intros f g.  
  apply (antisymmetry le).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    intros s hs.
    assert (H1 : elt Q Qlt (rl ((appr f n b mm) +
                                (appr g n b mm))) s).
    rewrite appr_add in hs; trivial.
    apply pred_plus_pr.
    assert (H2 : merely
            (∃ r s0 : Q,
             val (rl (appr f n b mm)) r
           ∧ val (rl (appr g n b mm)) s0
           ∧ s = r + s0)).    
    apply pred_plus_pr; trivial.
    revert H2.
    apply (Trunc_ind _); intros (r,(t,(Hr,(Ht,Hrt)))); apply tr.
    exists r, t.        
    repeat split; try trivial.
    revert Hr.   
    apply RC_mon with Qle.
    intros x y; apply (antisymmetry le).
    intros x y; apply orders.le_or_lt.
    reflexivity.
    apply (RllubPos_lub (λ n0 : nat, appr f n0 b mm) n); trivial.
    apply (RllubPos_lub (λ n0 : nat, appr g n0 b mm) n); trivial.
  - intros s hs.
    apply pred_plus_pr in hs.
    revert hs; apply (Trunc_ind _);
    intros (r,(t,(Hr,(Ht,Hrt)))).
    assert (val
         (rl (RllubPos
            (λ n : nat,
                   appr f n b mm + appr g n b mm))) s).
    apply top_le_enumerable_sup in Hr.
    apply top_le_enumerable_sup in Ht.
    apply top_le_enumerable_sup.
    revert Hr; apply (Trunc_ind _).
    intros (n,Hr).
    revert Ht; apply (Trunc_ind _).
    intros (m,Ht).
    unfold semi_decide in *.
    apply tr.    
    exists (n+m).
    apply pred_plus_pr.
    apply tr.
    unfold toRlseq in *.
    exists r, t.
    assert (H1 : forall n m : nat, n <= n + m).
    -- intros p k.
       induction k.
       * unfold plus, peano_naturals.nat_plus.
         rewrite <- Peano.plus_n_O.
         reflexivity.    
       * transitivity (p + k); trivial.
         apply semirings.plus_le_compat.
         reflexivity. 
         rewrite peano_naturals.S_nat_plus_1.
         transitivity (k + 0).
         rewrite rings.plus_0_r; reflexivity.
         apply semirings.plus_le_compat.
         reflexivity.
         apply semirings.le_0_1.
    -- repeat split; trivial.
       * revert Hr.
         apply RC_mon with Qle.
         intros x y; apply (antisymmetry le).
         intros x y; apply orders.le_or_lt.
         reflexivity.
         apply appr_mon_n.
         apply H1.
       * revert Ht.
         apply RC_mon with Qle.
         intros x y; apply (antisymmetry le).
         intros x y; apply orders.le_or_lt.
         reflexivity.
         apply appr_mon_n.
         rewrite rings.plus_comm.
         apply H1.  
    -- revert H.
       apply Rllub_mon.
       intros n; unfold toRlseq.
       rewrite appr_add.
       intros z; trivial.
+ apply Rllub_le.
  intros n; unfold toRlseq.      
  apply appr_prob.
+ intros f g Hfg. 
  apply Rllub_mon. 
  intros n. 
  unfold toRlseq.
  apply appr_mon_f; trivial.
+ admit. 
Admitted. 
 
(* will become useless as soon as Riesz2 is defined *)
Lemma Riesz2_simpl (A : hSet) (b:Q+) : forall Nu,
    I (Riesz2 b Nu) = fun f:mf A =>
                        RllubPos (fun n => appr f n b Nu). 
Admitted.



Lemma Riesz_hom1 (A : hSet) : forall (Mu :Val A) U,
    mu _ (Riesz1 (Riesz2 1 Mu)) U = mu _ Mu U.
Proof.
intros Mu U.  
simpl. 
rewrite Riesz2_simpl. 
apply (antisymmetry le). 
+ apply Rllub_le; intros n.
  unfold toRlseq.
  apply appr_corr_inf.
+ admit. 
Admitted. 

Definition Riesz_hom2 (A : hSet) : forall (It : IntPos A) f,
    I (Riesz2 1 (Riesz1 It)) f = I It f.
Proof.
intros It.
rewrite Riesz2_simpl.
intros f.
apply (antisymmetry le).
+ apply Rllub_le; intros n. 
  unfold toRlseq.
  induction n. 
  - simpl.
    destruct (I It f).
    intros s hs; simpl; apply rlpos.
    simpl in hs; unfold semi_decide in hs.
    destruct (decide (s < 0)); trivial.
    apply not_bot in hs; case hs. 
  - simpl. 
    unfold qP.
Admitted.
 


