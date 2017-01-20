
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

Require Export Spaces.RoundedClosed
               Spaces.Opens
               Spaces.Functions 
               Theories.Valuations
               Theories.LowerIntegrals
               Theories.Riesz.

Definition unit_aux (A : hSet) (x : A) : Mes A. 
Proof.
refine (fun U : OS A => (OpenFun _ U) x). 
Defined. 

Definition unit (A : hSet) (x:A) : Val A.
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

  
Definition bind (A B : hSet) : Val A -> (A -> Val B) -> Val B.
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


  
Lemma monad1_aux {A B : hSet} : forall (x : A) (F : A -> Val B),
               mu _ (bind A B (unit A x) F) = mu _ (F x). 
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
    apply D_op_OpenFun. 
    rewrite HV.
    rewrite OpenFun_D_op. 
    intros q; trivial. 
  - intros q Hq.
    apply IHn. 
    revert Hq.
    apply RC_mon with Qle. 
    intros x' y'; apply (antisymmetry le). 
    intros x' y'; apply orders.le_or_lt.
    reflexivity.     
    apply toRlseq_antimon'. 
+ intros q Hq. apply (Rllub_lub  (λ n : nat,
        sum_p_r n (OpenFun A (D_op 0 (λ x0 : A, mu _ (F x0) U)))
          (unit A x)) 0). 
  simpl.
  unfold unit_aux; simpl.
  simpl. 
  rewrite <- (OpenFun_D_op F U x) in Hq. 
  rewrite D_op_OpenFun. 
  trivial.
Qed.

Global Instance LeVal  {A : hSet} : Le (Val A). 
Proof.
intros a b.
refine (forall u:OS A, (mu _ a) u <= (mu _ b) u).
Defined.

Lemma Val_eq {A : hSet} : forall a b :Val A, (forall U,
                       (mu _ a) U = (mu _ b) U)
                                    -> a = b.
Proof.
intros a b E; auto.
destruct a; destruct b; simpl; auto.
simpl.
Admitted.
 
Global Instance Val_isset {A : hSet} :  IsHSet (Val A). 
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => a <= b /\ b <= a)).
- intros s. split; intros x; reflexivity.
- apply _.
- intros x y Hxy.
  destruct Hxy. 
  apply Val_eq.
  intros U; apply (antisymmetry le).
  apply fst. apply snd.
Defined.

Lemma monad1 {A B : hSet} : forall (x : A) (F : A -> Val B),
               bind A B (unit A  x) F = F x.
Proof. 
intros x F.
apply Val_eq.
intros U.
rewrite monad1_aux.
reflexivity.
Defined.

Lemma monad2_aux {A : hSet} : forall (nu : Val A),
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
    intros V; rewrite D_op_OpenFun. 
    reflexivity. 
    repeat rewrite HV. 
    intros q; trivial.
  - intros q Hq.
    apply IHn.
    revert Hq.
    apply RC_mon with Qle. 
    intros x' y'; apply (antisymmetry le). 
    intros x' y'; apply orders.le_or_lt.
    reflexivity.     
    apply toRlseq_antimon'. 
+ unfold unit_aux; simpl.
  intros q Hq.       
  apply (Rllub_lub  (λ n : nat,
                           sum_p_r n (OpenFun A (D_op 0
                         (λ x : A, OpenFun A U x))) nu) 0).
  simpl.
  repeat rewrite OpenFun_D_op. 
  repeat rewrite D_op_OpenFun; trivial. 
Qed.


Lemma monad2 {A : hSet} : forall (nu : Val A),
    bind A A nu (unit A) = nu.
Proof.
intros nu.
apply Val_eq.
intros U.
rewrite monad2_aux.
reflexivity.
Defined.

Lemma monad3_aux {A B C: hSet} : forall (nu : Val A)
                   (F : A -> Val B) (G : B -> Val C),
    mu _ (bind B C (bind A B nu F) G) =
    mu _ (bind A C nu (fun x:A => bind B C (F x) G)).  
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
  repeat rewrite OpenFun_D_op. 
  repeat rewrite OpenFun_D_op in Hq.
  revert Hq. 
  apply RC_mon with Qle. 
  intros x' y'; apply (antisymmetry le). 
  intros x' y'; apply orders.le_or_lt.
  reflexivity. 
  apply I_mon. 
  intros x. simpl. 
  repeat rewrite OpenFun_D_op.
  repeat rewrite D_op_OpenFun.
  intros p Hp. 
  assert (Ho : elt Q Qlt (rl (sum_p_r 0 (λ x0 : B,
                (mu _ (G x0)) U) (F x))) p).
  simpl; trivial.
  admit. 
(*  rewrite OpenFun_D_op. 
  apply (Rllub_lub _ 0). 
  trivial.
  rewrite I_mu_simpl. 
  intros p Hp. 
  assert (Ho : elt Q Qlt (rl (sum_p_r 0 (λ x0 : B,
                (mu _ (G x0)) U) (F x))) p).
  simpl; trivial.
  apply (Rllub_lub _ 0). 
  trivial.*)
  intros q Hq. 
  apply IHn. 
  revert Hq. 
  apply RC_mon with Qle. 
  intros x' y'; apply (antisymmetry le). 
  intros x' y'; apply orders.le_or_lt.
  reflexivity. 
  apply toRlseq_antimon'. 
+ intros q Hq.
  apply (Rllub_lub (λ n : nat,
       sum_p_r n
         (OpenFun B
            (D_op 0 (λ x : B, mu _ (G x) U)))
         (bind A B nu F)) 0). 
  simpl. unfold Riesz2. 
  repeat rewrite OpenFun_D_op. 
  repeat rewrite OpenFun_D_op in Hq.
  repeat rewrite D_op_OpenFun. 
  repeat rewrite OpenFun_D_op in Hq. 
  rewrite I_mu_simpl in Hq. 
  rewrite I_mu_simpl. 
  revert Hq. 
  apply RC_mon with Qle. 
  intros x' y'; apply (antisymmetry le). 
  intros x' y'; apply orders.le_or_lt.
  reflexivity.
  apply Rllub_mon. 
  intros n r Hle. 
  unfold toRlseq in *.
  revert Hle. 
  apply sum_p_r_mon_f.
  intros z.
  transitivity ((λ x : A,
                       I (I_mu (F x))
              (OpenFun B (D_op 0 (λ x0 : B, mu _ (G x0) U)))) z).
  admit. 

  simpl. 
  rewrite I_mu_simpl.   
  simpl. apply Rllub_le.
  intros m; unfold toRlseq.
  intros v Hv. 
  assert (H' : elt Q Qlt (rl (sum_p_r 0
                           (λ x : B, mu _ (G x) U) (F z))) v).   
  revert Hv; apply RC_mon with Qle.
  intros x' y'; apply (antisymmetry le). 
  intros x' y'; apply orders.le_or_lt.
  reflexivity. simpl. 
  induction m. 
  - simpl. intros a Ha.
    rewrite D_op_OpenFun in Ha.
    trivial. 
Admitted. 
    

Lemma monad3 {A B C: hSet} : forall (nu : Val A) (F : A -> Val B) (G : B -> Val C),
     (bind B C (bind A B nu F) G) = (bind A C nu (fun x:A => bind B C (F x) G)).  
Proof.
intros nu F G.
apply Val_eq.
intros U.
rewrite monad3_aux.
reflexivity.
Defined.


Definition vD {A :hSet} (nu : Val A) (U : OS A) := mu _ nu U.

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

Lemma bind_mon {A B :hSet} : forall (x:A) (nu: Val A) (F : A -> Val B) (f g : OS B), 
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

