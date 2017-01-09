
Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.partiality
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient Spaces.Int. 

Require Export RoundedClosed Opens Functions 
        Valuations LowerIntegrals D_op OpenFun
        Riesz Giry.

Set Implicit Arguments.

(** Conditional *)

(** Image distributions : Rml 3 *) 

Definition im_distr {A B : hSet} (f : A -> B) (m : Val A) : Val B :=
       bind A B m (fun a => unit B (f a)). 

Lemma im_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C) (m : Val A) : 
         im_distr g (im_distr f m) = im_distr (fun a => g (f a)) m.
Proof.   
unfold im_distr; simpl.
rewrite monad3.
assert (Hu : (λ x : A, bind B C (unit B (f x))
                            (λ a : B, unit C (g a))) =
             (λ a : A, unit C (g (f a)))). 
apply path_forall. 
intros x. assert (Hmu : mu _ (bind B C (unit B (f x))
                     (λ a : B, unit C (g a))) =
                        mu _ (unit C (g (f x)))).
rewrite unit_aux_unit; unfold unit_aux.
apply path_forall; intros U. 
simpl in *. 
unfold Riesz2.
rewrite I_mu_simpl.
apply (antisymmetry le). 
+ apply Rllub_le. intros n.
  unfold toRlseq. 
  induction n. 
  - simpl.
    assert (Ho1 : D_op 0 (OpenFun B (D_op 0 (λ x0 : B,
                          OpenFun C U (g x0)))) =
                 (D_op 0 (λ x0 : B, OpenFun C U (g x0)))).
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (U (g z)).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros s. unfold semi_decide.
       destruct (decide (0 < 1)).
       * transitivity (val (rl RlP_1) 0).
         reflexivity. 
         unfold RlP_1. 
         simpl. unfold semi_decide.
         destruct (decide (0 < 1)). 
         reflexivity. 
         case (n l). 
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * transitivity (elt Q Qlt (rl RlP_0) 0).
         reflexivity.  
         unfold RlP_0. simpl. 
         unfold semi_decide. 
         destruct (decide (0 < 0)). 
         case (n l). 
         reflexivity.       
    -- simpl. admit.
    -- rewrite Ho1. 
       assert (Ho2 : (D_op 0 (λ x0 : B, OpenFun C U (g x0))) =
                (λ x0 : B, U (g x0))).    
       unfold D_op; simpl. 
       apply path_forall. 
       intros z.     
       unfold OpenFun, OpenFun_aux. generalize (U (g z)). 
       apply (partial_ind0 _ (fun a => _)).
       --- simpl; intros s. unfold semi_decide.
           transitivity (elt Q Qlt (rl RlP_1) 0). 
           reflexivity. simpl. unfold semi_decide. 
           destruct (decide (0 < 1)).
           * destruct s. reflexivity.
           * assert (Hos : Qzero < Qone).
             apply semirings.lt_0_1.
             case (n Hos).
       --- simpl; unfold semi_decide.
           destruct (decide (0 < 0)).
           * assert (Hj : Qzero <= Qzero). reflexivity.
             generalize (orders.le_not_lt_flip 0 0 Hj).
             intros Hj'; case (Hj' l).          
           * transitivity (elt Q Qlt (rl RlP_0) 0). simpl.
             unfold semi_decide. 
             destruct (decide (0 < 0)). 
             case (n l). reflexivity. 
             simpl. unfold semi_decide. 
             destruct (decide (0 < 0)). 
             case (n l). 
             reflexivity. 
        --- admit. 
        --- rewrite Ho2.
            unfold OpenFun.
            unfold Rlle, RCLe_l; auto. 
  -  unfold unit, unit_aux; simpl.
    simpl. admit.
+ assert (Hv : (λ n : nat,
       sum_p_r n
         (OpenFun B (D_op 0 (λ x0 : B, unit_aux C (g x0) U)))
         (unit B (f x))) =
               (λ n : nat,
       sum_p_r n
         ((λ x0 : B, unit_aux C (g x0) U))
         (unit B (f x)))). 
  admit. 

  rewrite Hv. 
  unfold unit, unit_aux.
  admit. 
Admitted. 

Lemma im_distr_id {A : hSet}: forall (f : A -> A) (m : Val A),
          (forall x, f x = x) -> im_distr f m = m. 
Proof. 
intros f m Hx. 
unfold im_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu, monad2; reflexivity. 
Qed.  


(** Correctness judgement *) 

Definition ok {A} (p : RlowPos) (nu : Val A) (F : OS A) :=
                         p <= mu _ nu F. 

Definition ok_fun {A B} (f : OS A) (E : A -> Val B) (F : A -> OS B) :=
                     forall x:A, ok ((OpenFun _ f) x) (E x) (F x). 

Definition ok_up {A} (p : RlowPos) (nu : Val A) (F : OS A) :=
                        mu _ nu F <= p. 

Definition up_fun {A B} (f : OS A) (E : A -> Val B) (F : A -> OS B) :=
                     forall x:A, ok_up ((OpenFun _ f) x) (E x) (F x). 

(** Rules for applications *)

Lemma apply_rule {A B} : forall (nu : Val A) (f : A -> Val B)
                                (r : RlowPos)
                                (F : OS A) (G : OS B),
          ok r nu F -> ok_fun F f (fun x => G) ->
          ok r (bind A B nu f) G. 
Proof.
intros nu f r F G H1 H2.
unfold ok_fun, ok in *.
unfold bind.
simpl. transitivity (mu _ nu F); trivial.
transitivity (I (Riesz2 nu) (OpenFun A (D_op 0
               (λ x : A, OpenFun A F x)))).
+ clear H1 H2. 
  unfold Riesz2. 
  rewrite I_mu_simpl.
  transitivity (sum_p_r 0 (OpenFun A (D_op 0 (λ x : A,
            OpenFun A F x  ))) nu).
  - simpl.   
    assert (H1 : D_op 0 (OpenFun A (D_op 0
                 (λ x : A, OpenFun A F x))) =
            (D_op 0 (λ x : A, OpenFun A F x))). 
    generalize (@D_op_correct _ _ A (fun x => OpenFun A F x) 0).
    intros HGF.
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (F z).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros x. unfold semi_decide.
       destruct (decide (0 < 1)).
       * transitivity (val (rl RlP_1) 0).
         reflexivity. 
         unfold RlP_1. 
         simpl. unfold semi_decide.
         destruct (decide (0 < 1)). 
         reflexivity. 
         case (n l). 
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * transitivity (elt Q Qlt (rl RlP_0) 0).
         reflexivity.  
         unfold RlP_0. simpl. 
         unfold semi_decide. 
         destruct (decide (0 < 0)). 
         case (n l). 
         reflexivity.       
    -- simpl. admit.
    -- rewrite H1. 
       assert (H2 : (D_op 0 (λ x : A, OpenFun A F x)) =
                  fun x =>  F x). 
       unfold D_op; simpl. 
       apply path_forall. 
       intros z.     
       unfold OpenFun, OpenFun_aux. generalize (F z). 
       apply (partial_ind0 _ (fun a => _)).
       --- simpl; intros x. unfold semi_decide.
           transitivity (elt Q Qlt (rl RlP_1) 0). 
           reflexivity. simpl. unfold semi_decide. 
           destruct (decide (0 < 1)).
           * destruct x. reflexivity.
           * assert (Hos : Qzero < Qone).
             apply semirings.lt_0_1.
             case (n Hos).
       --- simpl; unfold semi_decide.
           destruct (decide (0 < 0)).
           * assert (Hj : Qzero <= Qzero). reflexivity.
             generalize (orders.le_not_lt_flip 0 0 Hj).
             intros Hj'; case (Hj' l).          
           * transitivity (elt Q Qlt (rl RlP_0) 0). simpl.
             unfold semi_decide. 
             destruct (decide (0 < 0)). 
             case (n l). generalize (F z). intros; auto.
             simpl. unfold semi_decide. 
             destruct (decide (0 < 0)). 
             case (n l). 
             reflexivity. 
        --- admit. 
        --- rewrite H2.
            reflexivity. 
   - apply (Rllub_lub (λ n : nat,
                          sum_p_r n (OpenFun A (D_op 0
                      (λ x : A, OpenFun A F x))) nu) 0). 
+ apply I_mon, OpenFun_mon, D_op_mon_f.        
  intros x; trivial. 
Admitted. 

Lemma apply_rule_up {A B} : forall (mu : Val A) (f : A -> Val B)
                                   (r : RlowPos)
                                (F : OS A) (G : OS B),
    ok_up r mu F -> up_fun F f (fun x => G) ->
    ok_up r (bind A B mu f) G. 
Proof.
intros nu f r F G H1 H2. 
unfold up_fun, ok_up in *. 
unfold bind.
simpl. unfold Riesz2. rewrite I_mu_simpl. 
transitivity (mu _ nu F); trivial.
transitivity (I (Riesz2 nu) (OpenFun A (D_op 0
               (λ x : A, OpenFun A F x)))).
+ unfold Riesz2. 
  rewrite I_mu_simpl. apply Rllub_mon. 
  intros n. 
  unfold toRlseq. 
  apply sum_p_r_mon_f2. 
  apply OpenFun_mon. 
  apply D_op_mon_f. 
  intros s. 
  apply H2.  
+ clear H1 H2. 
  unfold Riesz2. 
  rewrite I_mu_simpl.
  transitivity (sum_p_r 0 (OpenFun A (D_op 0 (λ x : A,
            OpenFun A F x  ))) nu).
  - simpl.   
    assert (H1 : D_op 0 (OpenFun A (D_op 0
                 (λ x : A, OpenFun A F x))) =
            (D_op 0 (λ x : A, OpenFun A F x))). 
    generalize (@D_op_correct _ _ A (fun x => OpenFun A F x) 0).
    intros HGF.
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (F z).
    apply (partial_ind0 _ (fun a => _)).
    -- simpl; intros x. unfold semi_decide.
       destruct (decide (0 < 1)).
       * transitivity (val (rl RlP_1) 0).
         reflexivity. 
         unfold RlP_1. 
         simpl. unfold semi_decide.
         destruct (decide (0 < 1)). 
         reflexivity. 
         case (n l). 
       * assert (Hos : Qzero < Qone).
         apply semirings.lt_0_1.
         case (n Hos).
    -- simpl; unfold semi_decide.
       destruct (decide (0 < 0)).
       * assert (Hj : Qzero <= Qzero). reflexivity.
         generalize (orders.le_not_lt_flip 0 0 Hj).
         intros Hj'; case (Hj' l).          
       * transitivity (elt Q Qlt (rl RlP_0) 0).
         reflexivity.  
         unfold RlP_0. simpl. 
         unfold semi_decide. 
         destruct (decide (0 < 0)). 
         case (n l). 
         reflexivity.       
    -- simpl. admit.
    -- rewrite H1. 
       assert (H2 : (D_op 0 (λ x : A, OpenFun A F x)) =
                  fun x =>  F x). 
       unfold D_op; simpl. 
       apply path_forall. 
       intros z.     
       unfold OpenFun, OpenFun_aux. generalize (F z). 
       apply (partial_ind0 _ (fun a => _)).
       --- simpl; intros x. unfold semi_decide.
           transitivity (elt Q Qlt (rl RlP_1) 0). 
           reflexivity. simpl. unfold semi_decide. 
           destruct (decide (0 < 1)).
           * destruct x. reflexivity.
           * assert (Hos : Qzero < Qone).
             apply semirings.lt_0_1.
             case (n Hos).
       --- simpl; unfold semi_decide.
           destruct (decide (0 < 0)).
           * assert (Hj : Qzero <= Qzero). reflexivity.
             generalize (orders.le_not_lt_flip 0 0 Hj).
             intros Hj'; case (Hj' l).          
           * transitivity (elt Q Qlt (rl RlP_0) 0). simpl.
             unfold semi_decide. 
             destruct (decide (0 < 0)). 
             case (n l). generalize (F z). intros; auto.
             simpl. unfold semi_decide. 
             destruct (decide (0 < 0)). 
             case (n l). 
             reflexivity. 
        --- admit. 
        --- rewrite H2.
            apply Rllub_le.
            intros n. unfold toRlseq. 
            unfold sum_p_r. 
            induction n. 
            * simpl. rewrite H2. 
              intros q; trivial. 
            * rewrite sum_p_r_prod. 
              rewrite Rlow_mult_q1. 
              rewrite sum_p_r_prod in IHn. 
              rewrite Rlow_mult_q1 in IHn.
              simpl. 
              rewrite H2.
              rewrite H2 in IHn. 
              induction n. 
              admit. 
              apply IHn0. 
              induction n. 
              intros q; trivial. 
              simpl. 
              rewrite H2. 
              assert (H3 : mu _ nu (D_op (qn 1)
                     (OpenFun A (λ x : A, F x))) = RlP_0).
              generalize (@D_op_correct _ _ A
                                 (OpenFun A (λ x : A, F x)) 1). 
              intros HG. 
              assert (HL : forall x : A,
               D_op 1 (OpenFun A (λ x0 : A, F x0)) x <->
               False).          
              split. 
              intros HL'.
              apply HG in HL'. 
              assert (HL2 : OpenFun A (λ x : A, F x) x <= RlP_1). 
              admit. admit. admit.

              admit. admit. admit. admit. 
  - simpl. admit. 
Admitted. 


(** Rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> Val B) (F : OS A)
                                      (G : A -> OS B),
    (forall x:A, ok (OpenFun _ F x) (f x) (G x)) -> ok_fun F f G. 
Proof.
intros f F G HO. 
unfold ok_fun, ok in *; trivial. 
Qed. 

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> Val B) (F : OS A) (G : A -> OS B),
       (forall x:A, ok_up (OpenFun _ F x) (f x) (G x)) -> up_fun F f G. 
Proof.
intros f F G HO. 
unfold up_fun, ok_up in *; trivial. 
Qed. 

(** Distribution on the hSet version of Bool *)

Definition hS_of_hset (A : Type) (hset_A : IsHSet A) : hSet.
Proof. 
exists A; trivial. 
Defined.

Definition hS_of_t (A : Type) (hset_A : IsHSet A)
           (x : hS_of_hset hset_A) : A. 
Proof. 
refine x. 
Qed. 

Definition DH (A : Type) (hset_A : IsHSet A) := 
                             Val (hS_of_hset hset_A).

Definition valb (b : hS_of_hset hset_bool) : bool.
Proof. 
destruct (hS_of_t hset_bool b). 
+ refine true. 
+ refine false. 
Defined.

Definition OSb (B : OS (hS_of_hset hset_bool)) : bool -> RlowPos. 
Proof. 
intros b. 
assert (b' : hS_of_hset hset_bool). 
refine b.
refine ((OpenFun (hS_of_hset hset_bool) B) b'). 
Defined.


(** Rules for conditional *)

Definition Mif (A:hSet) (b: Val (hS_of_hset hset_bool)) (m1 m2:Val A) : Mes A. 
Proof.                          
intros X.
exists (rl (mu _ (bind (hS_of_hset hset_bool) A b
        (fun x:Bool => if x then m1 else m2)) X)).
intros p Hp. 
apply (mu _ (bind (hS_of_hset hset_bool) A b
        (λ x : Bool, if x then m1 else m2)) X); trivial. 
Defined. 

(** Boundedness of OSb *)
 
Lemma OSb_prob : forall B x, OSb B x <= RlP_1. 
Proof. 
intros B x. 
unfold OSb.
transitivity (OpenFun (hS_of_hset hset_bool) Ω x).
apply OpenFun_mon.
unfold OS_full.
simpl. 
intros s. 
apply top_greatest. 
apply OpenFun_prob. 
reflexivity. 
Qed. 

(** Distribution on the hSet version of nat *)

Lemma hset_nat : IsHSet nat. 
Proof. 
apply _. 
Qed. 

Definition valn (n : hS_of_hset hset_nat) : nat.
Proof. 
destruct (hS_of_t hset_nat n). 
+ refine O. 
+ refine (S n0). 
Defined.

Definition OSn (N : OS (hS_of_hset hset_nat)) : nat -> RlowPos. 
Proof. 
intros n. 
assert (n' : hS_of_hset hset_nat). 
refine n.
refine ((OpenFun (hS_of_hset hset_nat) N) n'). 
Defined.

(** Flip program *)

Definition flip_aux : Mes (hS_of_hset hset_bool). 
Proof.
intros B.
pose (B' := OSb B).
exists (rl ((Rlow_mult_q (1 / 2) (B' true))
       + 
       (Rlow_mult_q (1 / 2) (B' false)))).
intros p Hp. 
apply ((Rlow_mult_q (1 / 2) (B' true))
       + 
       (Rlow_mult_q (1 / 2) (B' false))); trivial.  
Defined. 

Definition flip : Val (hS_of_hset hset_bool). 
Proof. 
exists flip_aux.  
+ unfold modular. intros U V.
  apply (antisymmetry le). 
  intros p Hp. 
  simpl in *. 
  unfold OSb. 
  admit. 
  admit. 
+ unfold empty_op.
  apply (antisymmetry le). 
  - intros p Hp.
    simpl in Hp.
    unfold pred_multQ, semi_decide in Hp.
    simpl in Hp.
    apply pred_plus_pr in Hp. 
    revert Hp; apply (Trunc_ind _). 
    intros (r,(s,(H1,(H2,H3)))).
    destruct (decide (' 1 * ' (/ 2) * r < 0)).
    destruct (decide (' 1 * ' (/ 2) * s < 0)).
    -- apply RlP_0. 
       admit. (* ok j'y crois *)
    -- apply not_bot in H2; case H2. 
    -- apply not_bot in H1; case H1. 
  - intros p Hp. 
    unfold flip_aux; simpl.  
    unfold pred_multQ, semi_decide.
    simpl.
    apply pred_plus_pr. 
    apply tr.
    exists (p/2), (p/2). 
    destruct (decide (' 1 * ' (/ 2) * (p/2) < 0)).

    repeat split; try (apply top_greatest). 
    admit. (* ok *)
    admit. (* ok *)
+ unfold mon_opens. 
  intros U V HUV.
  intros q Hq. 
  unfold flip_aux in *; simpl in *. 
  unfold pred_multQ in *.   
  apply pred_plus_pr.
  apply pred_plus_pr in Hq. 
  revert Hq; apply (Trunc_ind _). 
  intros (r,(s,(H1,(H2,H3)))). 
  apply tr. 
  exists r, s. 
  repeat split; try trivial.
  - revert H1. 
    apply RC_mon with Qle. 
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    unfold OSb. 
    apply OpenFun_mon; trivial.
  - revert H2. 
    apply RC_mon with Qle. 
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    unfold OSb. 
    apply OpenFun_mon; trivial.
+ intros p Hp.
  apply RC_mon with Qle (rl (flip_aux Ω)) p. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt.   
  reflexivity. 
  assert (HPP : Rlow_mult_q (1 / 2) (OSb Ω true) +
               Rlow_mult_q (1 / 2) (OSb Ω false) <= RlP_1). 
  admit. 

  unfold flip_aux. 
  simpl. 
  apply HPP.
  trivial.
Admitted.

SearchAbout RlowPos. 

Definition QRlow_qpos (q : Q+)  : RlowPos. 
Proof.
assert (HP : Rlle ('0) (QRlow (rationals.pos q))).
intros p Hp.   
simpl in *. 
unfold semi_decide in *. 
destruct (decide (p < 0)). 
destruct (decide (p < rationals.pos q)). 
trivial. 
assert (p < rationals.pos q). 
apply orders.lt_le_trans with 0; trivial.
destruct q as (q,Hq).
simpl. apply orders.lt_le.
trivial. 
case (n X). 
destruct (decide (p < rationals.pos q)).
apply top_greatest. 
trivial. 
refine (Rlow_RlowPos (QRlow (rationals.pos q)) HP). 
Defined. 

Fixpoint sum_n_moy_aux (p : nat) (f : nat -> RlowPos) : RlowPos := match p with
          |O => RlP_0
          |S p0 => RlP_plus (f (S p0)) (sum_n_moy_aux p0 f)
end.


Definition O_Sp (p : nat) : Q+. 
Proof. 
refine (1 / qnp (S p)). 
Defined. 

Fixpoint sum_n_moy (p : nat) f : RlowPos := Rlow_mult_q (O_Sp p)
                                                  (sum_n_moy_aux p f). 

(** Random program *)

Definition random_aux (M : nat) : Mes (hS_of_hset hset_nat). 
Proof.
intros N.
pose (N' := OSn N).
exists (rl (sum_n_moy M N')).
apply (sum_n_moy M). 
Defined. 

Definition random (M : nat) :  Val (hS_of_hset hset_nat). 
Proof. 
exists (random_aux M).  
+ unfold modular. intros U V.
  admit.    
+ unfold empty_op. 
  apply (antisymmetry le). 
  - intros p Hp.
    simpl in Hp.
    induction M. 
    -- simpl in Hp.
       unfold semi_decide in Hp.
       unfold pred_multQ in Hp.
       destruct (decide (rationals.pos (O_Sp 0) * p < 0)).
       simpl. unfold semi_decide.
       destruct (decide (p < 0)). 
       apply top_greatest. 
       admit. (* ok *)
       apply not_bot in Hp. 
       case Hp. 
    -- assert (Hnn : elt Q Qlt (rl (sum_n_moy M (OSn ∅))) p).
       revert Hp. 
       apply RC_mon with Qle.   
       intros x y; apply (antisymmetry le). 
       intros x y; apply orders.le_or_lt. 
       reflexivity. 
       intros q Hq. 
       unfold sum_n_moy in *. 
       simpl in Hq.        
       unfold pred_multQ in Hq. 
       apply pred_plus_pr in Hq.
       revert Hq; apply (Trunc_ind _).
       intros (r,(s,(H1,(H2,H3)))).
       admit. (* ok but cumbersome *)

       apply IHM; trivial.
  - admit. 
+ unfold mon_opens. 
  intros U V HUV.
  intros q Hq. 
  unfold random_aux in *; simpl in *.
  induction M.
  - simpl in *. 
    trivial.
  - unfold sum_n_moy. 
    unfold sum_n_moy_aux.
    unfold sum_n_moy in Hq. 
    unfold sum_n_moy_aux in Hq.
    simpl.    
    simpl in Hq.     
    admit. 
+ admit. 
Admitted. 
 
