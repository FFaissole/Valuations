
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

Definition im_distr {A B : hSet} (f : A -> B) (m : D A) : D B :=
       bind A B m (fun a => unit B (f a)). 

    
Lemma im_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C)
      (m : D A) : 
   im_distr g (im_distr f m) = im_distr (fun a => g (f a)) m.
Proof.    
unfold im_distr; simpl.
generalize (@monad3 A).   
intros HGm. 
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
    rewrite D_op_OpenFun. 
    reflexivity.
    rewrite Ho1.
    rewrite D_op_OpenFun. unfold unit, unit_aux; simpl.  
    intros q Hq. 
    unfold OpenFun, OpenFun_aux in *; simpl in *. 
    trivial.        
  - repeat rewrite D_op_OpenFun. 
    intros q Hq.
    apply IHn.     
    revert Hq. 
    apply RC_mon with Qle. 
    intros x' y'; apply (antisymmetry le). 
    intros x' y'; apply orders.le_or_lt. 
    reflexivity.
    unfold unit_aux. 
    rewrite OpenFun_D_op.
    unfold OpenFun. 
    apply toRlseq_antimon'.  
+ assert (Hv : (λ n : nat,
       sum_p_r n
         (OpenFun B (D_op 0 (λ x0 : B, unit_aux C (g x0) U)))
         (unit B (f x))) =
               (λ n : nat,
       sum_p_r n
         ((λ x0 : B, unit_aux C (g x0) U))
         (unit B (f x)))).
  rewrite OpenFun_D_op. 
  reflexivity.
  rewrite Hv.
  unfold unit_aux; simpl. 
  intros q Hq. 
  assert (Ho : elt Q Qlt (rl (sum_p_r 0 (λ x0 : B, OpenFun C U (g x0))
                                      (unit B (f x)))) q). 
  simpl. unfold unit_aux; simpl.     
  rewrite OpenFun_D_op; trivial. 
  apply Rllub_lub with 0.
  trivial.
+ admit. (* pb of universes *)
+ rewrite <- Hu. 
  reflexivity. 
Admitted. 

Lemma im_distr_id {A : hSet}: forall (f : A -> A) (m : D A),
          (forall x, f x = x) -> im_distr f m = m. 
Proof. 
intros f m Hx. 
unfold im_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu, monad2; reflexivity. 
Qed.  

(** *  Conditional distribution : Rml 4 *)

(* TODO *)

(** Correctness judgement *) 

Definition ok {A} (p : RlowPos) (nu : D A) (F : OS A) :=
                         p <= mu _ nu F. 

Definition ok_fun {A B} (f : OS A) (E : A -> D B) (F : A -> OS B) :=
                     forall x:A, ok ((OpenFun _ f) x) (E x) (F x). 

Definition ok_up {A} (p : RlowPos) (nu : D A) (F : OS A) :=
                        mu _ nu F <= p. 

Definition up_fun {A B} (f : OS A) (E : A -> D B) (F : A -> OS B) :=
                     forall x:A, ok_up ((OpenFun _ f) x) (E x) (F x). 

(** Rules for applications *)

Lemma apply_rule {A B} : forall (nu : D A) (f : A -> D B)
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
    rewrite D_op_OpenFun. 
    reflexivity. 
    rewrite H1. 
    assert (H2 : (D_op 0 (λ x : A, OpenFun A F x)) =
                  fun x =>  F x). 
    rewrite D_op_OpenFun.
    reflexivity. 
    rewrite H2.
    reflexivity. 
   - apply (Rllub_lub (λ n : nat,
                          sum_p_r n (OpenFun A (D_op 0
                      (λ x : A, OpenFun A F x))) nu) 0). 
+ apply I_mon, OpenFun_mon, D_op_mon_f.        
  intros x; trivial.
Qed. 

Lemma apply_rule_up {A B} : forall (mu : D A) (f : A -> D B)
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
    rewrite OpenFun_D_op. 
    reflexivity.
    rewrite H1. 
    rewrite OpenFun_D_op. 
    apply Rllub_le.
    intros n. unfold toRlseq.
    induction n. 
    * simpl.
      intros q; trivial. 
    * intros q Hq. 
      assert (Ho :  elt Q Qlt (rl (sum_p_r 0
                    (λ x : A, OpenFun A F x) nu)) q).
      revert Hq.       
      apply RC_mon with Qle. 
      intros x y; apply (antisymmetry le). 
      intros x y; apply orders.le_or_lt. 
      reflexivity.
      generalize (@toRlseq_antimon A 0 (S n) nu
                 (fun z : A => OpenFun A F z)). 
      intros HRL. unfold toRlseq in HRL. 
      apply HRL.
      apply orders.lt_le.
      apply peano_naturals.S_gt_0. 
      trivial. 
   - simpl.        
     repeat rewrite D_op_OpenFun. 
     reflexivity. 
Qed. 


(** Rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> D B) (F : OS A)
                                      (G : A -> OS B),
    (forall x:A, ok (OpenFun _ F x) (f x) (G x)) -> ok_fun F f G. 
Proof.
intros f F G HO. 
unfold ok_fun, ok in *; trivial. 
Qed. 

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> D B) (F : OS A) (G : A -> OS B),
       (forall x:A, ok_up (OpenFun _ F x) (f x) (G x)) -> up_fun F f G. 
Proof.
intros f F G HO. 
unfold up_fun, ok_up in *; trivial. 
Qed. 

(** Distribution on the hSet version of Bool *)

Definition DH (A : Type) (hset_A : IsHSet A) := 
                             D (default_TruncType 0 A hset_A).

Definition Bool_s : hSet := default_TruncType 0 bool hset_bool. 

Definition valb (b : Bool_s) : bool := b.

Definition OSb (B : OS (Bool_s)) : bool -> RlowPos :=
        fun b => (OpenFun Bool_s B) b. 

(** Rules for conditional *)

Definition Mif (A:hSet) (b: DH hset_bool) (m1 m2:D A) : Mes A. 
Proof.                          
intros X.
exists (rl (mu _ (bind Bool_s A b
        (fun x:Bool => if x then m1 else m2)) X)).
intros p Hp. 
apply (mu _ (bind Bool_s A b
        (λ x : Bool, if x then m1 else m2)) X); trivial. 
Defined. 

(** Boundedness of OSb *)
 
Lemma OSb_prob : forall B x, OSb B x <= RlP_1. 
Proof. 
intros B x. 
unfold OSb.
transitivity (OpenFun Bool_s Ω x).
apply OpenFun_mon.
unfold OS_full.
simpl. 
intros s. 
apply top_greatest. 
apply OpenFun_prob. 
reflexivity. 
Qed. 

(** Distribution on the hSet version of nat *)

Require Export Spaces.Nat.  
Close Scope nat. 
Definition Nat_s : hSet := default_TruncType 0 nat hset_nat. 

Definition valn (n : Nat_s) : nat := n.

Definition OSn (N : OS (Nat_s)) : nat -> RlowPos :=
        fun n => (OpenFun Nat_s N) n. 

(** Flip program *)

Definition flip_aux : Mes Bool_s. 
Proof.
intros B.
pose (B' := OSb B).
exists (rl (RlP_plus (Rlow_mult_q (1 / 2) (B' true))
       (Rlow_mult_q (1 / 2) (B' false)))).
intros p Hp. 
apply (RlP_plus (Rlow_mult_q (1 / 2) (B' true))
       (Rlow_mult_q (1 / 2) (B' false))); trivial.  
Defined. 

Definition flip : D Bool_s. 
Proof. 
exists flip_aux.  
+ unfold modular. intros U V.
  apply (antisymmetry Rllepos). 
  - intros p Hp. 
    simpl in *. 
    unfold OSb in *.
    unfold pred_multQ in *.
    simpl in *. 
    apply pred_plus_pr. 
    apply pred_plus_pr in Hp. 
    revert Hp; apply (Trunc_ind _).
    intros (t,(f,(Ht,(Hf,Hs)))).
    apply pred_plus_pr in Hf. 
    apply pred_plus_pr in Ht. 
    revert Ht; apply (Trunc_ind _). 
    intros (t1,(f1,(Ht1,(Hf1,Hs1)))).
    revert Hf; apply (Trunc_ind _). 
    intros (t2,(f2,(Ht2,(Hf2,Hs2)))).
    apply tr. 
    exists t, f. 
    split. 
    -- apply pred_plus_pr. apply tr. 
       exists t1,f1. 
       repeat split; admit.     
    -- repeat split; admit.
  - intros p Hp. 
    simpl in *.    
    unfold OSb in *.
    unfold pred_multQ in *.
    simpl in *. 
    apply pred_plus_pr. 
    apply pred_plus_pr in Hp. 
    revert Hp; apply (Trunc_ind _).
    intros (t,(f,(Ht,(Hf,Hs)))).
    apply pred_plus_pr in Hf. 
    apply pred_plus_pr in Ht. 
    revert Ht; apply (Trunc_ind _). 
    intros (t1,(f1,(Ht1,(Hf1,Hs1)))).
    revert Hf; apply (Trunc_ind _). 
    intros (t2,(f2,(Ht2,(Hf2,Hs2)))).
    apply tr. 
    exists t, f. 
    split. 
    -- apply pred_plus_pr. apply tr. 
       exists t1,f1. 
       repeat split; admit.     
    -- repeat split; admit.
+ unfold empty_op.
  apply (antisymmetry Rllepos). 
  - intros p Hp.
    simpl in Hp.
    unfold pred_multQ, semi_decide in Hp.
    simpl in Hp.
    apply pred_plus_pr in Hp. 
    revert Hp; apply (Trunc_ind _). 
    intros (r,(s,(H1,(H2,H3)))).
    destruct (decide ((' 1 * ' (/ 2) * r)%mc < 0)).
    destruct (decide ((' 1 * ' (/ 2) * s)%mc < 0)).
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
    destruct (decide ((' 1 * ' (/ 2) * (p/2))%mc < 0)%mc).
    repeat split; try (apply top_greatest).
    admit. (* field ? *)
    
    repeat split; admit.
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
    intros x y; apply (antisymmetry Qle). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    unfold OSb. 
    apply OpenFun_mon; trivial.
  - revert H2. 
    apply RC_mon with Qle. 
    intros x y; apply (antisymmetry Qle). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    unfold OSb. 
    apply OpenFun_mon; trivial.
+ intros p Hp.
  apply RC_mon with Qle (rl (flip_aux Ω)) p. 
  intros x y; apply (antisymmetry Qle). 
  intros x y; apply orders.le_or_lt.   
  reflexivity. 
  assert (HPP : RlP_plus (Rlow_mult_q (1 / 2) (OSb Ω true))
               (Rlow_mult_q (1 / 2) (OSb Ω false)) <= RlP_1). 
  pose (Htrue := OSb_prob Ω true). 
  pose (Hfalse := OSb_prob Ω false). 
  assert (H1 : forall b, (Rlow_mult_q (1 / 2) (OSb Ω b))
                         <= Rlow_mult_q (1/2) RlP_1). 
  intros b; case b;
  intros q Hq; 
  unfold Rlow_mult_q in *; simpl in *;
  unfold pred_multQ in *; simpl in *;
  trivial.     
  intros q Hq.

  Check pred_plus_pr. 
  assert (HC : merely (exists t f : Q,
             val (rl ((Rlow_mult_q (1 / 2) (OSb Ω true)))) t  ∧
             val (rl ((Rlow_mult_q (1 / 2) (OSb Ω false)))) f  ∧
             q = (t + f)%mc)). 
  apply pred_plus_pr; apply Hq.  
  revert HC; apply (Trunc_ind _); intros (t,(f,(Hct,(Hcf,HQ)))).  
  simpl. rewrite HQ. 
  unfold Rlow_mult_q in Hct, Hcf; 
  simpl in *; unfold pred_multQ in Hct, Hcf; simpl in *. 
  unfold semi_decide in *. 
  destruct (decide ((t + f)%mc < 1));
  destruct (decide ((' 1 * ' (/ 2) * t)%mc < 1)); 
  destruct (decide ((' 1 * ' (/ 2) * f)%mc < 1)); try trivial. 
  apply top_greatest. 
  case n. 
  assert (Hsum : ((' 1 * ' (/ 2) * t) +
                 (' 1 * ' (/ 2) * f))%mc = (t + f)%mc). 
  admit. admit. (* field *) 

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

Definition random (M : nat) :  D (hS_of_hset hset_nat). 
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
