

Require Import HoTTClasses.interfaces.abstract_algebra
               HoTTClasses.interfaces.orders
               HoTTClasses.implementations.sierpinsky
               HoTTClasses.implementations.dedekind
               HoTTClasses.theory.rationals
               HoTTClasses.theory.premetric. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe UnivalenceImpliesFunext
               TruncType UnivalenceAxiom Types.Sigma
               FunextVarieties hit.quotient. 

Require Export RoundedClosed Opens Functions 
        Valuations LowerIntegrals D_op OpenFun
        Riesz.

(*Set Implicit Arguments.*)

Definition unit_aux (A : hSet) (x : A) : Mes A. 
Proof.
refine (fun U : OS A => (OpenFun _ U) x). 
Defined. 

Definition unit (A : hSet) (x:A) : D A.
Proof.
exists (unit_aux _ x).    
+ unfold modular. intros U V.
  generalize (OpenFun_mod U V).
  intros Hmod; unfold fplus in Hmod.
  transitivity ((λ x : A, RlP_plus (OpenFun A U x)
                                   (OpenFun A V x)) x). 
  reflexivity. rewrite Hmod. 
  transitivity ((λ x : A, RlP_plus (OpenFun A (U ⋂ V) x)
                                   (OpenFun A (U ∪ V) x)) x).
  reflexivity. 
  rewrite RlPPlus_comm.
  reflexivity. 
+ unfold empty_op, unit_aux.
  rewrite OpenFun_def. 
  reflexivity. 
  reflexivity. 
+ unfold mon_opens. 
  intros U V HUV. 
  apply OpenFun_mon; trivial. 
+ unfold unit_aux. 
  apply OpenFun_prob; reflexivity. 
Defined. 

Lemma unit_aux_unit (A : hSet) (x:A) : mu _ (unit _ x) = unit_aux _ x. 
Proof. 
simpl; reflexivity. 
Qed. 

Lemma Hx1 (A B : hSet) : forall U V (F : A -> D B), ((λ z : A, val (let (rl, _) :=
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
  assert (rl (mu (λ x : B, SierMeet (U x) (V x))) =
          RlJoin (rl (mu U)) (rl (mu V))).
 
  admit. 

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
  assert (Hj : mu
                 (λ x : B, SierJoin (U x) (V x)) =
               RlPJoin (mu U) (mu V)).
  apply (antisymmetry Rllepos).
  unfold Rllepos.
  intros q Hq.
  unfold RlPJoin.
  simpl.
  unfold semi_decide.
  
  unfold SierJoin in Hq.
  
  simpl.
  simpl.
  admit.

  assert (Hj2 : val
         (let (rl, _) := RlPJoin (mu U) (mu V) in
          rl) 0).
  admit.
 
  simpl in Hj2.
  unfold semi_decide in Hj2.
  apply top_le_join in Hj2.
  unfold hor in Hj2; trivial.
  unfold Rllepos.
  intros q Hq.
  unfold RlPJoin in Hq.  

Admitted.
  
  
Definition bind (A B : hSet) : D A -> (A -> D B) -> D B.
Proof.
intros Nu F.
split with (fun U:OS B => I (Riesz2 Nu)
           (OpenFun _ (D_op 0 (fun x:A => (mu _ (F x)) U)))). 
+ intros U V.
  transitivity ((I (Riesz2 Nu) (OpenFun A (D_op 0 (λ x : A,
        mu _ (F x) (U ∪ V))))) + (I (Riesz2 Nu)
       (OpenFun A (D_op 0 (λ x : A, mu _ (F x) (U ⋂ V)))))).
  rewrite <- I_add.
  unfold D_op.
  transitivity (
    (I (Riesz2 Nu)
       (OpenFun A (λ z : A, val (let (rl, _)
                          := mu _ (F z) U in rl) 0)))
    + (I (Riesz2 Nu)
         (OpenFun A (λ z : A, val (let (rl, _)
                          := mu _ (F z) V in rl) 0)))).
  reflexivity. 
  simpl.
  rewrite <- I_add. 
  rewrite OpenFun_mod.
  rewrite Hx1, Hx2. simpl.
  assert (Ha : (λ x : A,
     RlP_plus
       (OpenFun A
          (λ z : A,
           val (let (rl, _) := mu _ (F z) (U ∪ V) in rl) 0)
          x)
       (OpenFun A
          (λ z : A,
           val (let (rl, _) := mu _ (F z) (U ⋂ V) in rl) 0)
          x))=
        (λ x : A,RlP_plus
       (OpenFun A
          (λ z : A,
           val (let (rl, _) := mu _ (F z) (U ⋂ V) in rl) 0)
          x)
       (OpenFun A
          (λ z : A,
           val (let (rl, _) := mu _ (F z) (U ∪ V) in rl) 0)
          x))).
  apply path_forall; intros x.
  rewrite RlPPlus_comm.
  reflexivity. unfold fplus. rewrite Ha.
  reflexivity. reflexivity.
+ unfold empty_op; simpl.
  assert (Hk : (fun x : A => mu _ (F x) ∅) = fun x:A => RlP_0).
  apply path_forall; intros x.  
  rewrite (mu_empty_op _ (F x)); reflexivity.
  rewrite Hk. unfold D_op. simpl. 
  unfold semi_decide. 
  destruct (decide (0 < 0)). 
  apply orders.eq_not_lt in l.
  case l. reflexivity. 
  rewrite OpenFun_def. rewrite I_def.
  reflexivity. reflexivity.  
+ intros U V HUV. 
  apply I_mon. 
  apply OpenFun_mon. 
  apply D_op_mon_f. 
  intros s; apply mu_mon; trivial.  
+ assert (Hk : (fun x : A => mu _ (F x)  Ω) <= fun x:A => RlP_1).
  intros x.  
  apply (mu_prob  _ (F x)); reflexivity.
  transitivity (I (Riesz2 Nu )(fun x =>  RlP_1)).
  apply I_mon.
  unfold D_op.
  simpl. transitivity (OpenFun A Ω).
  apply OpenFun_mon.
  unfold OS_full; intros s.  
  apply top_greatest. 
  apply OpenFun_prob; reflexivity. 
  apply I_prob. 
Defined.

Lemma monad1_aux {A B : hSet} : forall (x : A) (F : A -> D B),
               mu _ (bind A B (unit A  x) F) = mu _ (F x). 
Proof.
intros x F.
unfold bind; simpl.
apply path_forall.
intros U.
unfold Riesz2.
rewrite I_mu_simpl.
apply (antisymmetry le).
+ apply Rllub_le; intros n.
  unfold toRlseq, sum_p_r.
  induction n. 
  - unfold unit. unfold unit_aux. simpl.
    assert (HV : forall V, D_op 0 (OpenFun A V) =  V).
    intros V. 
    generalize (@D_op_correct _ _ A (OpenFun A V) 0).
    intros HGF.
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (V z).
    admit.

    rewrite HV.
    admit. 
  - admit. 
+ intros q Hq. apply (Rllub_lub  (λ n : nat,
        sum_p_r n (OpenFun A (D_op 0 (λ x0 : A, mu _ (F x0) U)))
          (unit A x)) 0). 
  simpl.
  unfold unit_aux; simpl.
  admit.   
Admitted.

Lemma monad1 {A B : hSet} : forall (x : A) (F : A -> D B),
               bind A B (unit A  x) F = F x.
Proof. 
intros x F. destruct (F x).
destruct (bind A B (unit A x) F). 
Admitted. 

Lemma monad2_aux {A : hSet} : forall (nu : D A),
    mu _ (bind A A nu (unit A)) = mu _ nu.
Proof.
intros nu; simpl.
unfold Riesz2.
rewrite I_mu_simpl.
apply path_forall; intros U.
apply (antisymmetry le).
+ apply Rllub_le.
  unfold toRlseq; intros n. 
  induction n. 
  - simpl. unfold unit_aux. 
    assert (HV : forall V, D_op 0 (OpenFun A V) =  V).
    intros V. 
    generalize (@D_op_correct _ _ A (OpenFun A V) 0).
    intros HGF.
    unfold D_op, OpenFun, OpenFun_aux.
    apply path_forall; intros z.
    generalize (V z).
    admit.

    repeat rewrite HV. 
    intros q; trivial.
  - simpl. admit.
+ unfold unit_aux; simpl.
  intros q Hq.       
  apply (Rllub_lub  (λ n : nat,
                           sum_p_r n (OpenFun A (D_op 0
                         (λ x : A, OpenFun A U x))) nu) 0).
  simpl. 
  assert (HV : forall V, D_op 0 (OpenFun A V) =  V).
  intros V. 
  generalize (@D_op_correct _ _ A (OpenFun A V) 0).
  intros HGF.
  unfold D_op, OpenFun, OpenFun_aux.
  apply path_forall; intros z.
  generalize (V z).
  admit. 

  repeat rewrite HV; trivial. 
Admitted.


Lemma monad2 {A : hSet} : forall (nu : D A),
    bind A A nu (unit A) = nu.
Proof.
intros nu; simpl.
unfold Riesz2.
Admitted.


Lemma monad3_aux {A B C: hSet} : forall (nu : D A) (F : A -> D B) (G : B -> D C),
     mu _ (bind B C (bind A B nu F) G) = mu _ (bind A C nu (fun x:A => bind B C (F x) G)).  
Proof.
intros nu F G. simpl.
unfold Riesz2.
rewrite I_mu_simpl.
apply path_forall; intros U.
apply (antisymmetry le).
+ apply Rllub_le. 
  unfold toRlseq. 
  induction 0. 
  simpl. unfold Riesz2. 
  intros q Hq. simpl.
  unfold D_op in *; simpl in *. 
  admit. admit. 
+ intros q Hq.
  apply (Rllub_lub (λ n : nat,
       sum_p_r n
         (OpenFun B
            (D_op 0 (λ x : B, mu _ (G x) U)))
         (bind A B nu F)) 0). 
  simpl. unfold Riesz2. 
  admit. 
Admitted. 


Lemma monad3 {A B C: hSet} : forall (nu : D A) (F : A -> D B) (G : B -> D C),
     (bind B C (bind A B nu F) G) = (bind A C nu (fun x:A => bind B C (F x) G)).  
Proof.
  Admitted. 

Definition vD {A :hSet} (nu : D A) (U : OS A) := mu _ nu U.

Lemma unit_aux_mon {A :hSet} : forall (x:A) (U V : OS A),
    U <= V -> (unit_aux A x) U <= (unit_aux A x) V.
Proof. 
intros x U V HUV.
apply OpenFun_mon; trivial.  
Qed. 

Lemma unit_mon {A :hSet} : forall (x:A) (U V : OS A),
    U <= V -> vD (unit A x) U <= vD (unit A x) V.
Proof. 
intros x U V HUV; unfold vD. 
rewrite unit_aux_unit. 
apply unit_aux_mon; trivial.
Qed. 

Lemma sum_p_r_mon_f2 {A :hSet} : forall n f g mm, f <= g -> 
      sum_p_r n f mm <= @sum_p_r A n g mm.
Proof.
intros n f g mm Hfg.
induction n.  
+ simpl.
  apply mu_mon.
  apply D_op_mon_f; trivial.
+admit. 
Admitted. 

Lemma bind_mon {A B :hSet} : forall (x:A) (nu: D A) (F : A -> D B) (f g : OS B), 
       f <= g -> vD (bind A B nu F) f <= vD (bind A B nu F) g. 
Proof.
intros x nu F f g Hfg q Hq. 
unfold bind.
simpl in *. 
unfold Riesz2 in *; rewrite I_mu_simpl. 
rewrite I_mu_simpl in Hq.
revert Hq. apply Rllub_mon. 
intros n.
unfold toRlseq.
apply sum_p_r_mon_f2.
apply OpenFun_mon. 
apply D_op_mon_f.
intros s. 
apply mu_mon; trivial. 
Qed. 
