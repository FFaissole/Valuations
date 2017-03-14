
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
               Valuations LowerIntegrals.
              
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
    (D_op q f) x <->  QRlow q < (f x).
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


Section S_to_RlP. 

(** Map from Sier to RlowPos *)
Definition S_to_RlP : forall s : Sier, RlowPos.
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
  assert (Hx : (val (Rllub s) q)).
  trivial.
  assert (H2 : RllubPos s <= x).
  apply RllubPos_le. trivial.
  apply RC_mon with Qle (Rllub s) q. 
  intros ss sh; apply (antisymmetry le). apply orders.le_or_lt.
  reflexivity. trivial. trivial.
Defined.

(** Monotonicity of the map from Sier to RlowPos *)
Lemma S_to_RlP_mon : forall s1 s2, s1 <= s2
                        -> S_to_RlP s1 <= S_to_RlP s2.
Proof.
apply (partialLe_ind0 _ _).
+ reflexivity.
+ assert (X : S_to_RlP (bot Unit) = RlP_0).
  auto; rewrite X.
  intros. apply RlowPos_pos.
+ intros f x H1 H2 n.
  transitivity (S_to_RlP (sup Unit f)).
  assert (Hr : S_to_RlP (sup Unit f) = RllubPos
                        (fun n => S_to_RlP (f n))).
  auto. rewrite Hr.
  apply (Rllub_lub (fun n => S_to_RlP (f n))); trivial.
  trivial.
+ intros f x H1 H2.
  assert (Hr : S_to_RlP (sup Unit f) = RllubPos
                        (fun n => S_to_RlP (f n))).
  auto. rewrite Hr.
  apply Rllub_le.
  intros n;
  apply H2.
Qed.
  

Lemma meet_pres_S_to_RlP : 
          MeetPreserving (fun (s: Sier) => S_to_RlP s). 
Proof. 
intros x y;
unfold sg_op, meet_is_sg_op, S_to_RlP. 
revert x.
apply (partial_ind0 _ (fun a => _)).
+ intros x.
  assert (H1 : SierMeet (eta Unit x) y = y).
  generalize (SierMeet_top y).
  intros Hst;
  destruct x;
  fold SierTop;
  unfold meet in Hst; trivial. 
  rewrite H1. 
  assert (H2 : forall x, x <= RlP_1 -> 
                    RlPMeet RlP_1 x = x). 
  intros rr Hrr.
  apply (antisymmetry le). 
  - intros s Hs. 
    simpl in Hs. 
    unfold semi_decide in Hs. 
    destruct (decide (s < 1)).
    unfold meet in Hs. 
    apply top_le_meet in Hs. 
    apply (snd Hs). 
    apply top_le_meet in Hs. 
    apply (snd Hs). 
  - intros s Hs.
    simpl; unfold semi_decide.
    apply top_le_meet. 
    split. 
    destruct (decide (s < 1)). 
    apply top_greatest. 
    case n. 
    red in Hrr;
    unfold Rl_pos_Le, Rlle, RCLe_l in Hrr. 
    specialize (Hrr s Hs). 
    simpl in Hrr; unfold semi_decide in Hrr. 
    destruct (decide (s < 1)).     
    case (n l). 
    apply not_bot in Hrr; case Hrr. 
    trivial.
  - rewrite H2.
    reflexivity.
    transitivity (S_to_RlP SierTop).
    apply S_to_RlP_mon. 
    apply top_greatest.
    reflexivity. 
+ assert (HsB : SierMeet (bot Unit) y  = bot Unit).
  apply (antisymmetry le). 
  - apply imply_le.
    intros Hz; apply top_le_meet in Hz. 
    apply (fst Hz). 
  - apply imply_le. 
    intros Hz;
    apply not_bot in Hz; 
    case Hz. 
  - assert (HrB : forall r, RlPMeet RlP_0 r = RlP_0).
    intros r. 
    apply (antisymmetry le). 
    -- intros s Hs. 
       unfold RlPMeet in Hs; simpl in Hs; 
       unfold semi_decide in Hs. 
       apply top_le_meet in Hs. 
       destruct (decide (s < 0)). 
       destruct Hs as (_,Hs). 
       simpl; unfold semi_decide. 
       destruct (decide (s < 0)). 
       apply top_greatest. 
       case (n l).
       destruct Hs as (Hs,_). 
       apply not_bot in Hs; case Hs.
    -- intros s Hs; simpl in Hs. 
       destruct (RlPMeet RlP_0 r) as (rr,Hprr); simpl. 
       unfold semi_decide in *; destruct (decide (s < 0)).            
       apply Hprr; trivial.        
       apply not_bot in Hs; case Hs.
    -- rewrite HsB.
       transitivity RlP_0.   
       reflexivity. 
       rewrite HrB.
       reflexivity. 
+ intros f Hn.
  apply (antisymmetry le).   
  - intros q Hn'.
    assert (H2 : SierMeet (sup Unit f) y =
                 sup _ (SierMeet_seq_l f y)). 
    apply SierMeet_sup.     
    rewrite H2 in Hn'.
    assert (Hn'2 : elt Q Qlt (Rllub
                  (fun n => S_to_RlP ((SierMeet_seq_l f y) n))) q). 
    trivial.
    clear Hn'.
    apply top_le_enumerable_sup in Hn'2.   
    unfold semi_decide, toRlseq in Hn'2.           
    revert Hn'2; apply (Trunc_ind _). 
    intros (n,Hn'2). 
    specialize (Hn n).
    simpl in Hn'2. 
    unfold meet in Hn'2.
    assert (H3 : val (rl (S_to_RlP y)) q).
    revert Hn'2. 
    apply RC_mon with Qle. 
    intros ss sh; apply (antisymmetry le).
    apply orders.le_or_lt.
    reflexivity. 
    apply S_to_RlP_mon. 
    apply SierMeet_is_meet.
    trivial.
    assert (Ho : elt Q Qlt 
                     (RlMeet (RllubPos (fun n => S_to_RlP (f n)))
                              (S_to_RlP y)) q). 
    unfold RlPMeet. 
    simpl; unfold semi_decide, SDseq_Rlow, toRlseq,
           semi_decide_exists.
    apply top_le_meet. 
    split. 
    -- apply top_le_enumerable_sup. 
       apply tr. unfold semi_decide.
       exists n.
       revert Hn'2.
       apply RC_mon with Qle. 
       intros ss sh; apply (antisymmetry le).
       apply orders.le_or_lt.
       reflexivity. 
       apply S_to_RlP_mon.
       apply SierMeet_is_meet. 
    -- apply H3.
    -- trivial. 
  - intros q Hn'.
    unfold RlPMeet in Hn'.
    apply top_le_meet in Hn'.
    destruct Hn' as (Hna,Hnb). 
    assert (Hna2 : elt Q Qlt (Rllub
                                    (fun n => S_to_RlP (f n))) q).
    trivial. clear Hna.
    apply top_le_enumerable_sup in Hna2.
    revert Hna2; apply (Trunc_ind _). 
    intros (m,Hm).
    unfold semi_decide, toRlseq in Hm. 
    assert (H2 : SierMeet (sup Unit f) y =
                 sup _ (SierMeet_seq_l f y)). 
    apply SierMeet_sup.   
    rewrite H2.
    assert (H3 : elt Q Qlt (Rllub
                 (fun n => S_to_RlP ((SierMeet_seq_l f y) n))) q).
    apply top_le_enumerable_sup.
    unfold semi_decide, toRlseq.
    apply tr. 
    exists m. 
    simpl; specialize (Hn m).
    unfold S_to_RlP.
    rewrite Hn.
    unfold RlPMeet. 
    simpl; unfold semi_decide.
    apply top_le_meet.
    split; trivial.
    trivial. 
Qed. 

Lemma join_pres_S_to_RlP : 
          JoinPreserving (fun (s: Sier) => S_to_RlP s). 
Proof. 
intros x y;
unfold sg_op, join_is_sg_op, S_to_RlP. 
revert x.
apply (partial_ind0 _ (fun a => _)).
+ intros x.
  assert (H1 : SierJoin (eta Unit x) y = eta Unit x).
  generalize (SierJoin_top y).
  intros Hst;
  destruct x;
  fold SierTop;
  unfold join in Hst; trivial. 
  rewrite H1. 
  assert (H2 : forall x, x <= RlP_1 -> 
                    RlPJoin RlP_1 x = RlP_1). 
  intros rr Hrr.
  apply (antisymmetry le). 
  - intros s Hs. 
    simpl in Hs. 
    unfold semi_decide in Hs. 
    destruct (decide (s < 1)).
    unfold join in Hs. 
    apply top_le_join in Hs.
    unfold hor in Hs.
    revert Hs; (apply (Trunc_ind _)).
    intros Hs. 
    destruct Hs;
    simpl; unfold semi_decide;
    destruct (decide (s < 1)); try trivial.   
    case (n l).
    apply top_greatest.
    case (n l).
    apply top_le_join in Hs.
    unfold hor in Hs.
    revert Hs; (apply (Trunc_ind _)).
    intros Hs. 
    destruct Hs. 
    -- apply not_bot in i; case i. 
    -- simpl; unfold semi_decide;
       destruct (decide (s < 1)); try trivial. 
       apply top_greatest.
       red in Hrr; unfold Rl_pos_Le, Rlle, RCLe_l in Hrr. 
       apply Hrr in i. 
       simpl in i; unfold semi_decide in i;
       destruct (decide (s < 1)); try trivial. 
       case (n0 l).                                       
  - intros s Hs.
    apply top_le_join; unfold hor. 
    apply tr.
    simpl in Hs; simpl; unfold semi_decide in *. 
    destruct (decide (s < 1)). 
    left; trivial. 
    left; trivial.
  - simpl.
    rewrite H2.
    reflexivity.
    clear H1. 
    revert y.
    assert (H3 : forall y, S_to_RlP y <= S_to_RlP (eta Unit tt)).
    intros y; apply S_to_RlP_mon. 
    apply top_greatest. 
    trivial.  
+ assert (HsB : SierJoin (bot Unit) y  = y).
  reflexivity. 
  assert (HrB : forall r, RlPJoin RlP_0 r = r).
  intros r. 
  apply (antisymmetry le).
  -- intros s Hs. 
     unfold RlPJoin in Hs; simpl in Hs; 
     unfold semi_decide in Hs. 
     apply top_le_join in Hs. 
     destruct (decide (s < 0)).
     * apply rlpos; trivial.  
     * unfold hor in Hs. 
       revert Hs; apply (Trunc_ind _). 
       intros Hs.
       case Hs; intros Ho. 
       ** apply not_bot in Ho; case Ho.
       ** trivial.
  -- intros s Hs; simpl in Hs.
     simpl; unfold semi_decide.             
     destruct (decide (s < 0)). 
     apply top_le_join. 
     unfold hor; apply tr. 
     left; apply top_greatest. 
     apply top_le_join. 
     unfold hor; apply tr. 
     right; trivial.
  -- rewrite HrB, HsB. 
     reflexivity. 
+ intros f Hn.
  apply (antisymmetry le).   
  - intros q Hn'.
    assert (H2 : SierJoin (sup Unit f) y =
                 sup _ (SierJoin_seq_l f y)).
    rewrite <- SierJoin_sup.
    reflexivity. 
    rewrite H2 in Hn'.
    assert (Hn'2 : elt Q Qlt (Rllub
                  (fun n => S_to_RlP ((SierJoin_seq_l f y) n))) q). 
    trivial.
    clear Hn'.
    apply top_le_enumerable_sup in Hn'2.   
    unfold semi_decide, toRlseq in Hn'2.           
    revert Hn'2; apply (Trunc_ind _). 
    intros (n,Hn'2). 
    specialize (Hn n).
    simpl in Hn'2. 
    unfold join in Hn'2.
    apply top_le_join.
    unfold hor.
    assert (Hn'3 : val (rl (RlPJoin
                           (S_to_RlP (f n)) (S_to_RlP y))) q). 
    rewrite <- Hn; trivial.
    simpl in Hn'3. 
    unfold semi_decide in Hn'3.
    apply top_le_join in Hn'3. 
    unfold hor in Hn'3. 
    revert Hn'3; apply (Trunc_ind _).
    intros Hn'3. 
    apply tr. 
    case Hn'3; intros Hh. 
    -- left; unfold semi_decide, semi_decide_sier.
       assert (H1 : elt Q Qlt (Rllub
                               (fun n => S_to_RlP (f n))) q).
       apply top_le_enumerable_sup. 
       apply tr; exists n. 
       unfold semi_decide, toRlseq; trivial.
       trivial. 
    -- right; unfold semi_decide, semi_decide_sier. 
       trivial.
  - intros q Hn'.
    unfold RlPJoin in Hn'.
    apply top_le_join in Hn'.
    unfold hor in Hn'. 
    revert Hn'; apply (Trunc_ind _). 
    intros Hn'.
    assert (H2 : SierJoin (sup Unit f) y =
                     sup _ (SierJoin_seq_l f y)).
    rewrite <- SierJoin_sup.
    reflexivity.
    rewrite H2.
    assert (H3 : elt Q Qlt (Rllub
                                  (fun n => S_to_RlP
                                   ((SierJoin_seq_l f y) n))) q).
    apply top_le_enumerable_sup.     
    case Hn'; intros H;
    unfold semi_decide, semi_decide_sier in H. 
    -- assert (H' : elt Q Qlt (Rllub (fun n => S_to_RlP
                                   (f n))) q).
       trivial. clear H. 
       apply top_le_enumerable_sup in H'. 
       revert H'; apply (Trunc_ind _). 
       intros (n,H'). 
       apply tr. 
       exists n; unfold semi_decide, toRlseq. 
       simpl; unfold semi_decide, toRlseq in H'.
       revert H'.         
       apply RC_mon with Qle. 
       intros ss sh; apply (antisymmetry le).
       apply orders.le_or_lt.
       reflexivity.
       apply S_to_RlP_mon, SierJoin_is_join. 
    -- apply tr.     
       exists 0. 
       unfold semi_decide, toRlseq. 
       simpl.   
       revert H. 
       apply RC_mon with Qle. 
       intros ss sh; apply (antisymmetry le).
       apply orders.le_or_lt.
       reflexivity.
       apply S_to_RlP_mon, SierJoin_is_join. 
    -- trivial. 
Qed. 

Coercion S_to_RlP : Sier >-> RlowPos. 

End S_to_RlP.   


Section OpenFun. 

(** Map from Opens to characteristic function *)
Definition OpenFun (A : hSet) : forall (U : A -> Sier),
                                       (A -> RlowPos). 
Proof. 
intros s z. 
specialize (s z).
exact (S_to_RlP s).
Defined.

(** OpenFun is definite *)
Lemma OpenFun_def {A} : forall U:OS A, U = OS_empty
                               -> OpenFun _ U = fun x => RlP_0. 
Proof.
intros U HU; 
apply path_forall; 
intros x; rewrite HU; auto. 
Qed. 

(** OpenFun is sub-probabilistic*)
Lemma OpenFun_prob {A} : forall U:OS A, U = OS_full
                               -> OpenFun _ U <= fun x => RlP_1. 
Proof.
intros U HU x;
rewrite HU; auto.
Qed. 

(** OpenFun is monotonic *)
Lemma OpenFun_mon {A} : forall U V:OS A, U <= V -> OpenFun _ U <= OpenFun _ V.
Proof.
intros U V H1 s;
unfold OpenFun;
apply S_to_RlP_mon; trivial.
apply (H1 s).
Qed.


Lemma OpenFun_0_1 {A  : hSet}: forall (U : OS A) z,
    OpenFun A U z = RlP_1 <-> RlP_0 < OpenFun A U z.
Proof. 
intros U z.
split; intros H1.    
+ rewrite H1.
  red; unfold Rlltpos, Rllt, RCLt_l. 
  apply tr. 
  exists 0. 
  split. 
  - simpl; unfold semi_decide; destruct (decide (0 < 1)).  
    apply top_greatest.
    case n.
    apply semirings.lt_0_1. 
  - intros HF. 
    simpl in HF;
    unfold semi_decide in HF; destruct (decide (0 < 0)).  
    apply orders.lt_ne in l. 
    case l; reflexivity. 
    apply not_bot in HF; case HF. 
+ revert H1.
  unfold OpenFun, S_to_RlP. 
  generalize (U z).
  apply (partial_ind0 _ (fun a => _ -> _)). 
  - intros t H.
    assert (H1 : RlP_0 < RlP_1) by trivial. 
    trivial.
  - intros H.
    assert (H1 : RlP_0 < RlP_0). 
    trivial.
    apply Rllt_strict_order in H1.
    case H1.     
  - intros f Hn Hsup. 
    assert (Hs : RlP_0 < (RllubPos (fun n =>
                           (S_to_RlP (f n)))));  
    trivial; clear Hsup.
    red in Hs.     
    unfold Rlltpos, Rllt, RCLt_l in Hs. 
    revert Hs; apply (Trunc_ind _). 
    intros (q,(Hq,H0q)).
    apply top_le_enumerable_sup in Hq. 
    revert Hq; apply (Trunc_ind _). 
    intros (m,Hm).
    unfold semi_decide, toRlseq in Hm.
    assert (H2 : RlP_0 < S_to_RlP (seq f m)).
    apply tr. 
    exists q.
    split; trivial.
    assert (H3 : RllubPos (fun n => S_to_RlP (f n)) = RlP_1).
    apply (antisymmetry le). 
    -- assert (Hn2 := Hn).  
       specialize (Hn m H2). 
       assert (H4 : val (rl RlP_1) q).
       rewrite <- Hn. 
       trivial.
       apply RllubPos_le. 
       intros p.
       destruct (peano_naturals.le_lt_dec p m).
       * assert (Hfc : f p <= f m).      
         destruct f as (f,Hff).
         simpl. admit. 
         
   
         intros s Hs.
         assert (Hfm : elt Q Qlt (rl (S_to_RlP (f m))) s). 
         revert Hs; apply RC_mon with Qle. 
         intros x y; apply (antisymmetry le). 
         intros x y; apply orders.le_or_lt. 
         reflexivity.
         assert (Hfc' : S_to_RlP (f p) <= S_to_RlP (f m)). 
         apply S_to_RlP_mon; trivial. 
         apply Hfc'.
         rewrite <- Hn.
         trivial.
       * assert (Hfc : S_to_RlP (f m) <= S_to_RlP (f p)). 
         admit. 

         assert (H00 : RlP_0 < S_to_RlP (f p)).
         red; unfold Rlltpos, Rllt, RCLt_l. 
         red in H2; unfold Rlltpos, Rllt, RCLt_l in H2. 
         revert H2; apply (Trunc_ind _);
         intros (q2,(H21,H22)); apply tr.          
         exists q2. 
         split; try trivial. 
         apply Hfc; trivial.  
         specialize (Hn2 p H00).
         rewrite <- Hn2.
         intros s Hs; trivial.     
    -- intros s Hs. 
       apply top_le_enumerable_sup. 
       apply tr; unfold semi_decide, toRlseq.
       specialize (Hn m H2).
       exists m.
       revert Hs. 
       apply RC_mon with Qle.
       intros x y; apply (antisymmetry le). 
       intros x y; apply orders.le_or_lt. 
       reflexivity. 
       unfold RCLe_l. 
       intros v Hv. 
       rewrite <- Hn in Hv. 
       trivial.         
Admitted. 

Lemma OpenFun_correct {A : hSet} : forall (x:A) U,
               OpenFun A U x = RlP_1 <-> (U x) = SierTop.
Proof. 
intros x U. 
split; intros Hu.
apply OpenFun_0_1 in Hu. 
+ unfold OpenFun, S_to_RlP in *.
  revert Hu. generalize (U x).
  apply (partial_ind0 _ (fun a => _->_)). 
  - simpl; intros v Hv.
    unfold SierTop.
    destruct v. 
    reflexivity. 
  - simpl; intros Hv.
    assert (Hf : RlP_0 < RlP_0); trivial.
    red in Hf; 
    unfold Rllt, RCLt_l in Hf.
    revert Hf; apply (Trunc_ind _).       
    intros (q,(E1,E2)).
    case (E2 E1). 
  - intros f Hn Hn'.
    assert (Hn'2 : RlP_0 < RllubPos (fun n => S_to_RlP (f n))).
    trivial.    
    clear Hn'.
    assert (Ha: merely (exists n : nat, RlP_0 < S_to_RlP (f n))). 
    red in Hn'2; 
    unfold Rlltpos, Rllt, RCLt_l in Hn'2. 
    revert Hn'2; apply (Trunc_ind _).              
    intros (p,(Hp1,Hp2)). 
    apply top_le_enumerable_sup in Hp1.
    revert Hp1; apply (Trunc_ind _).  
    unfold semi_decide, toRlseq.
    intros (m,Hm).
    apply tr. 
    exists m.
    red;unfold Rlltpos, Rllt, RCLt_l. 
    apply tr. 
    exists p. 
    split; trivial.
    revert Ha; apply (Trunc_ind _). 
    intros (w,Hw).    
    specialize (Hn w Hw). 
    apply top_le_eq.
    apply top_le_sup. 
    apply tr; exists w; rewrite Hn; apply top_greatest. 
+ unfold OpenFun, S_to_RlP; rewrite Hu; simpl. 
  reflexivity. 
Qed.
    
Lemma OpenFun_D_op {A B : hSet} : 
        forall (nu:A -> Val B) (U:OS B) z,
        OpenFun A (D_op 0 (λ x : A, (nu x) U)) z
    = (nu z) U.                              
Proof.
intros nu U z.
apply (antisymmetry le).
+ intros q Hq.
  revert Hq; unfold OpenFun, S_to_RlP.
  generalize (D_op 0 (λ x : A, (nu x) U) z). 
  admit.

+ intros q Hq.
  assert (H : D_op 0 (λ x : A, (nu x) U) z <->
              RlP_0 < (nu z) U).
  apply D_op_correct.
  destruct H as (H',H).
  revert H Hq.
  unfold OpenFun, S_to_RlP.
  generalize (D_op 0 (λ x : A, (nu x) U) z). 
  apply (partial_ind0 _ (fun a => _ -> _ -> _)).
  - simpl.
    intros t He H; unfold semi_decide.    
    destruct (decide (q < 1)).
    apply top_greatest.
    assert (H2 : elt Q Qlt (rl RlP_1) q).
    revert H.
    apply RC_mon with Qle.
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    assert (H : Rlle ((nu z) U)
                     ((nu z) OS_full)).
    apply mu_mon.
    intros s; apply top_greatest.
    red; red in H.
    intros p Hp.  
    specialize (H p Hp).
    revert H.
    apply RC_mon with Qle.
    intros x y; apply (antisymmetry le). 
    intros x y; apply orders.le_or_lt. 
    reflexivity. 
    apply mu_prob.
    simpl in H2; unfold semi_decide in H2.
    destruct (decide (q < 1)).
    case (n l).
    trivial.    
  - intros He H; simpl.
    unfold semi_decide.
    destruct (decide (q < 0)).
    apply top_greatest.
    apply He.
    red; unfold Rlltpos, Rllt, RCLt_l.
    apply tr.
    exists q.
    split; try trivial.
    intros HO; simpl in HO.
    unfold semi_decide in HO.
    destruct (decide (q < 0)).
    case (n l).
    apply not_bot in HO; case HO.
  - intros f Hn H2 Hn'.
    assert (H1 : elt Q Qlt (Rllub
               (fun n => (S_to_RlP (f n)))) q).
    apply top_le_enumerable_sup.    
    unfold semi_decide, toRlseq.
    assert (Hen : merely (exists n:nat, RlP_0 < (nu z) U
                                -> IsTop (f n))).
    assert (Hen' : RlP_0 < (nu z) U ->
                  merely (exists n:nat,  IsTop (f n))).
    intros Hr0.
    apply top_le_sup.
    apply H2; trivial.
    destruct (Qle_total 0 q).
    -- assert (H3 : RlP_0 < (nu z) U).
       admit.
  
       apply Hen' in H3.
       revert H3; apply (Trunc_ind _).
       intros (m,Hm).
       apply tr.
       exists m.       
       intros _; trivial.
    -- destruct (Qdec q 0).
       * rewrite p in Hn'. 
         assert (H3 : RlP_0 < (nu z) U).
         admit.
  
         apply Hen' in H3.
         revert H3; apply (Trunc_ind _).
         intros (m,Hm).
         apply tr.
         exists m.       
         intros _; trivial.
       * apply tr.
         exists O.
         intros Hf.
         admit.
         --
       admit.
--admit. 
Admitted.

Lemma Meet_pres_openfun {A:hSet}: forall z s,
          MeetPreserving (fun (U: OS A) => val (OpenFun A U z) s). 
Proof.
intros z s x y;
unfold OpenFun, sg_op, meet_is_sg_op.
assert (H1 : (x ⋂ y) z = meet (x z) (y z)).
unfold OS_meet, meet.
apply (antisymmetry le);
apply imply_le; intros Hs;
apply top_le_meet in Hs; 
apply top_le_meet; trivial. 
rewrite H1. 
rewrite meet_pres_S_to_RlP. 
reflexivity. 
Qed. 

Lemma Join_pres_openfun {A:hSet}: forall z s,
          JoinPreserving (fun (U: OS A) => val (OpenFun A U z) s). 
Proof.
intros z s x y;
unfold OpenFun, sg_op, join_is_sg_op.
assert (H1 : (x ∪ y) z = join (x z) (y z)).
unfold OS_join, join.
apply (antisymmetry le);
apply imply_le; intros Hs;
apply top_le_join in Hs; 
apply top_le_join; trivial. 
rewrite H1. 
rewrite join_pres_S_to_RlP.
reflexivity. 
Qed. 

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
       apply SierMeet_is_meet.  
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
+ apply imply_le.
  intros Hz.
  apply Hdp in Hz. 
  apply OpenFun_0_1 in Hz. 
  apply OpenFun_correct in Hz. 
  rewrite Hz; apply top_greatest. 
+ apply imply_le.
  intros Hz.
  apply Hdp.
  apply OpenFun_0_1. 
  apply OpenFun_correct.
  apply top_le_eq; trivial. 
Qed.


End OpenFun.

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


Lemma Riesz_hom1 (A : hSet) : forall (Mu :Val A) U,
    Riesz1 (Riesz2 Mu) U = Mu U.
Proof.
intros Mu U.  
simpl; unfold Riesz2.
apply (antisymmetry le). 
+ apply Rllub_le. 
  intros n; unfold toRlseq.
  induction n. 
  - simpl.
    rewrite Rlow_mult_q'_RlP_0.
    simpl; intros s Hs. 
    simpl in Hs; unfold semi_decide in Hs. 
    destruct (decide (s < 0)).
    apply rlpos; trivial.
    apply not_bot in Hs; case Hs. 
  - unfold appr; rewrite appr_aux_simpl.
    rewrite Rlow_mult_q_distr.
    intros s; trivial.
    apply peano_naturals.S_neq_0. 
+ intros s Hs. 
  apply Rllub_lub with 1. 
  unfold toRlseq.
  unfold appr; rewrite appr_aux_simpl. 
  rewrite Rlow_mult_q_distr; trivial.
  apply peano_naturals.S_neq_0. 
Qed. 


Definition Riesz_hom2 (A : hSet) : forall (It : IntPos A) f,
    Riesz2 (Riesz1 It) f = It f.
Proof.
intros It.
unfold Riesz2; simpl; intros f.
apply (antisymmetry le).
+ apply Rllub_le; intros n. 
  unfold toRlseq.
  assert (H: Rlle (It (appr_os f n)) (It f)).
  apply I_mon.
  apply appr_os_inf.
  assert (H2 : Rlle (appr f n (Riesz1 It))
                    (I It (appr_os f n))).  
  rewrite appr_os_It_inf.
  intros s; trivial. 
  intros s Hs. 
  apply H, H2; trivial. 
+ generalize (I_cont It f). 
  intros Hc.  
  assert (H2 : RllubPosQP
                 (λ q : Q+, I It
                 (λ x : A, RlP_minus_q2 (f x) q)) <=
               RllubPos (λ n : nat,
                               appr f n (Riesz1 It))).
  apply RllubPosQP_le.
  intros q. 
  intros s Hs. 
  apply top_le_enumerable_sup. 
  unfold semi_decide, toRlseq. 
  apply tr.
  assert (H' : ∃ x : nat,
             val (rl (I It (appr_os f x))) s).
  assert (Hs' : exists n:nat, elt Q Qlt (It (λ x : A,
               RlP_minus_q2 (f x) (1 / qnp n))) s).
  apply I_cont_nat.
  exists q; trivial.
  destruct Hs' as (m,Hs').
  exists m. 
  revert Hs'. 
  apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt.
  reflexivity.
  apply I_mon. 
  intros h z. 
  apply Ax2.  
  destruct H' as (n,H').
  exists n.
  revert H'. 
  apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt.
  reflexivity. 
  rewrite appr_os_It_inf. 
  intros k; trivial.    
  intros s Hs. 
  apply H2, Hc; trivial.  
Qed.
