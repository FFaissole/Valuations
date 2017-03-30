

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
               HIT.quotient. 

Require Export RoundedClosed Opens Functions 
               Valuations LowerIntegrals
               D_op OpenFun Riesz1.
              
Set Implicit Arguments.


Section Approx.

Definition qnp (n : nat) := pos_of_nat n.
Definition qn (n : nat) := pos (pos_of_nat n).

Definition qP (n : nat) := ((qnp n) * (1 / qnp (S n))).
Definition qbp (n : nat) (b : Q+) := b * (1 / qnp n). 
Definition qb (n : nat) (b : Q) := (qn n) * b. 

Coercion qn : nat >-> Q.
Coercion qnp : nat >-> Qpos.

Fixpoint appr_aux {A : hSet} (f : mf A) (N : nat)
         (m : Val A):= match N with
             |O => RlP_0
             |S P => m (D_op N f) + appr_aux f P m
end.       

Fixpoint appr_os_aux {A : hSet} (f : mf A) (N : nat)
          := match N with
             |O => (fun x:A => RlP_0)
             |S P => fun x:A => (OpenFun A (D_op N f) x +
                                 (appr_os_aux f P x))
end. 
                                            
Definition appr {A : hSet} (f : mf A) (N : nat) (m : Val A):=
  Rlow_mult_q (1 / qnp N) (appr_aux f N m).

Definition appr_os {A : hSet} (f : mf A) (N : nat) : mf A :=
           fun x:A => Rlow_mult_q (1 / qnp N) (appr_os_aux f N x).

Lemma appr_aux_0 {A : hSet} : forall N m, 
                    appr_aux (fzero A) N m = RlP_0. 
Proof.
intros N m. 
induction N. 
+ simpl; reflexivity.
+ simpl.
  rewrite IHN.
  unfold plus; rewrite RlPPlus_comm.
  rewrite RlPPlus_left_id.
  unfold D_op; simpl.
  unfold semi_decide. 
  destruct (decide
              (qn (S N) < 0)).
  - unfold qb in l.
    apply orders.lt_flip in l.
    assert (l2 : 0 < qn (S N)).
    apply pos_of_nat.
    case (l l2).
  - rewrite mu_empty_op. 
    reflexivity.
Qed.
  
Lemma appr_0 {A : hSet} : forall N m, 
                  appr (fzero A) N m = RlP_0. 
Proof.
intros N m. 
unfold appr.
rewrite appr_aux_0.
rewrite Rlow_mult_q_RlP_0.
reflexivity.
Qed.

Lemma appr_add {A : hSet} : forall (f g : mf A) N  m,
         appr (fplus f g) N m = appr f N m + appr g N m. 
Proof. 
intros f g N m.
unfold appr.
apply (antisymmetry le).
+ intros s.
  unfold Rlow_mult_q; simpl; unfold pred_multQ.
  intros hs.
  apply pred_plus_pr.
  apply tr.
Admitted.
  
Lemma appr_aux_prob {A : hSet} : forall N m,
         appr_aux (fone A) N m <= Rlow_mult_q N RlP_1. 
Proof. 
intros N m. 
induction N. 
+ simpl; intros q Hq;
  simpl in Hq; unfold semi_decide in *;
  destruct (decide (q < 0)).
  - apply rlpos. admit. (* ok *)
  - apply not_bot in Hq; case Hq.
+ simpl.
Admitted.
Axiom T1 : forall  a b :Q, a < b -> 0 < b - a. 
Axiom T2 : forall  a b :Q, a + (b - a) = b.


Axiom T3 : forall A (q:Q+) (f:mf A) (J : IntPos A), 
       RlP_minus_q2 (J f) q <= 
       J (fun x => RlP_minus_q2 (f x) q). 
Axiom Rlow_mult_q_distr : forall q r,
    Rlow_mult_q (1 / q) (Rlow_mult_q q r) = r. 

Axiom Rlow_mult_q'_RlP_0 : forall q,
    Rlow_mult_q' q RlP_0 = RlP_0.

Axiom appr_aux_simpl : forall A Mu U n,
           n <> O -> 
           appr_aux (OpenFun A U) n Mu = Rlow_mult_q (qnp n) (Mu U).

Lemma appr_prob {A : hSet} : forall N m,
         appr (fone A) N m <= RlP_1. 
Proof.
intros N m; unfold appr.
transitivity ((Rlow_mult_q (1 / qnp N))
                 (Rlow_mult_q (qnp N) RlP_1)).
intros s.
unfold Rlow_mult_q; simpl; unfold pred_multQ.
intros hs.
unfold semi_decide.
destruct (decide (pos (qnp N) * 
                 (pos (1 / qnp N) * s) < 1)).
apply top_greatest.
case n.
assert (val (rl (Rlow_mult_q (qnp N) RlP_1))
       ((pos (1 / qnp N) * s))).
revert hs; apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply appr_aux_prob.
simpl in H;
unfold pred_multQ in H;
unfold semi_decide in H; 
destruct (decide (pos (qnp N) * 
                 (' 1 * ' (/ qnp N) * s) < 1)).
trivial.
apply not_bot in H; case H.
rewrite Rlow_mult_q_distr.
reflexivity.
Qed.

Lemma appr_aux_mon_f {A : hSet} : forall n (f g: mf A) mm,
    f <= g -> appr_aux f n mm <= appr_aux g n mm.
Proof.
intros n f g m Hfg.
induction n.  
+ simpl; intros s hs; trivial.
+ simpl; transitivity (m (D_op (S n) f) +
                               appr_aux g n m).
  unfold plus; apply Rllepos_plus_le_preserving; trivial.
  unfold plus; rewrite RlPPlus_comm;
  rewrite (RlPPlus_comm (m (D_op (S n) g))).
  apply Rllepos_plus_le_preserving; trivial.
  apply mu_mon.
  apply D_op_mon_f; trivial.
Qed.

Lemma appr_mon_f {A : hSet} : forall n (f g: mf A) mm,
    f <= g -> appr f n mm <= appr g n mm.
Proof.
intros n f g m Hfg.
unfold appr.
intros s; unfold Rlow_mult_q;
simpl; unfold pred_multQ.
apply RC_mon with Qle.
intros x y; apply (antisymmetry le).
intros x y; apply orders.le_or_lt.
reflexivity.
apply appr_aux_mon_f; trivial.
Qed.

Axiom appr_mon_n : forall (A : hSet) n m (f: mf A) mm,
    n <= m -> appr f n mm <= appr f m mm.

Axiom appr_os_inf :forall (A : hSet) n (f: mf A),
                   appr_os f n <= f. 


Axiom appr_os_It_inf : forall (A : hSet) n (f: mf A) J,
       appr f n (Riesz1 J) = J (appr_os f n). 

Axiom appr_corr_inf : forall (A : hSet) (nu:Val A) U n,
                  appr (OpenFun A U) n nu <= nu U.


Axiom Ax3 : forall (A:hSet) (f:mf A) mm, Rllepos
   (RllubPos (λ n : nat, appr f n mm))
   (RllubPosQP
      (λ q : Q+,
       RllubPos
         (λ n : nat,
          appr (fun x => RlP_minus_q2 (f x) q) n mm))). 


Axiom Q_distr_inv : forall n s a,   1 / n * s = a ->
                                    s = n * a.

Axiom I_cont_nat : forall A (It : IntPos A) f s, 
    (exists q:Q+, elt Q Qlt (rl (I It (λ x : A,
                    RlP_minus_q2 (f x) q))) s) ->
  exists n:nat, elt Q Qlt (rl (I It (λ x : A,
                RlP_minus_q2 (f x) (1 / qnp n)))) s.

Axiom Ax2 : forall A h m f, (RlP_minus_q2 (f h) (1 / qnp m)) <= 
            (@appr_os A f m h). 

End Approx. 



Definition Riesz2 (A : hSet): Val A -> IntPos A. 
Proof.
intros mm.
exists (fun f => RllubPos (fun n => 
         appr f n mm)); red.
+ apply (antisymmetry le).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    rewrite appr_0; intros s Hs; trivial.
  - transitivity (appr (fzero A) 0 mm). 
    rewrite appr_0; intros s Hs; trivial.
    generalize (RllubPos_lub (λ n : nat, appr
                    (fzero A) n mm) 0); trivial.
+ intros f g.
  apply (antisymmetry le).
  - apply Rllub_le.
    intros n; unfold toRlseq.
    intros s hs.
    assert (H1 : elt Q Qlt (appr f n mm +
                            appr g n mm) s).
    rewrite appr_add in hs; trivial.
    apply pred_plus_pr.
    assert (H2 : merely
            (∃ r s0 : Q,
             val (appr f n mm) r
           ∧ val (appr g n mm) s0
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
    apply (RllubPos_lub (λ n0 : nat, appr f n0 mm) n); trivial.
    apply (RllubPos_lub (λ n0 : nat, appr g n0 mm) n); trivial.
  - intros s hs.
    apply pred_plus_pr in hs.
    revert hs; apply (Trunc_ind _);
    intros (r,(t,(Hr,(Ht,Hrt)))).
    assert (H' : val (Rllub (λ n : nat,
                 appr f n mm + appr g n mm)) s).
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
    -- revert H'.
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
+ intros f.
  apply Ax3. 
Defined. 

