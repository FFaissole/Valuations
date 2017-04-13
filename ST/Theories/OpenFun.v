


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

Require Export RoundedClosed Opens Functions D_op.
              
Set Implicit Arguments.
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
  intros ss sh; 
  apply (antisymmetry le). 
  apply orders.le_or_lt.
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
  

(** S_to_RlP preserves meets *)
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
    destruct (decide (s < 1)).
    unfold meet in Hs. 
    apply top_le_meet in Hs. 
    apply (snd Hs). 
    apply top_le_meet in Hs. 
    apply (snd Hs). 
  - intros s Hs.
    simpl.
    apply top_le_meet. 
    split. 
    destruct (decide (s < 1)). 
    apply top_greatest. 
    case n. 
    red in Hrr;
    unfold Rl_pos_Le, Rlle, RCLe_l in Hrr. 
    specialize (Hrr s Hs). 
    simpl in Hrr. 
    destruct (decide (s < 1)).     
    case (n l). 
    apply not_bot in Hrr; 
    case Hrr. 
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
       simpl in Hs. 
       apply top_le_meet in Hs. 
       destruct (decide (s < 0)). 
       destruct Hs as (_,Hs). 
       simpl. 
       destruct (decide (s < 0)). 
       apply top_greatest. 
       case (n l).
       destruct Hs as (Hs,_). 
       apply not_bot in Hs; case Hs.
    -- intros s Hs; simpl in Hs. 
       destruct (RlPMeet RlP_0 r) as (rr,Hprr); simpl. 
       destruct (decide (s < 0)).            
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
    revert Hn'2; apply (Trunc_ind _). 
    intros (n,Hn'2). 
    specialize (Hn n).
    simpl in Hn'2. 
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
    simpl.
    apply top_le_meet. 
    split. 
    -- apply top_le_enumerable_sup. 
       apply tr. unfold semi_decide.
       exists n.
       revert Hn'2.
       apply RC_mon with Qle. 
       intros ss sh; 
       apply (antisymmetry le).
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
    assert (H2 : SierMeet (sup Unit f) y =
                 sup _ (SierMeet_seq_l f y)). 
    apply SierMeet_sup.   
    rewrite H2.
    assert (H3 : elt Q Qlt (Rllub
                 (fun n => S_to_RlP ((SierMeet_seq_l f y) n))) q).
    apply top_le_enumerable_sup.
    apply tr. 
    exists m. 
    simpl; specialize (Hn m).
    unfold S_to_RlP.
    rewrite Hn.
    unfold RlPMeet. 
    simpl.
    apply top_le_meet.
    split; trivial.
    trivial. 
Qed. 

(** S_to_RlP preserves joins *)
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
  trivial. 
  rewrite H1. 
  assert (H2 : forall x, x <= RlP_1 -> 
                    RlPJoin RlP_1 x = RlP_1). 
  intros rr Hrr.
  apply (antisymmetry le). 
  - intros s Hs. 
    simpl in Hs. 
    destruct (decide (s < 1)).
    apply top_le_join in Hs.
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
    intros []. 
    -- apply not_bot in i; case i. 
    -- simpl;
       destruct (decide (s < 1)); try trivial. 
       apply top_greatest.
       red in Hrr. 
       apply Hrr in i. 
       simpl in i;
       destruct (decide (s < 1)); try trivial. 
       case (n0 l).                                       
  - intros s Hs.
    apply top_le_join. 
    apply tr.
    simpl in Hs; simpl. 
    destruct (decide (s < 1)). 
    left; trivial. 
    left; trivial.
  - simpl.
    rewrite H2.
    reflexivity.
    clear H1. 
    revert y.
    assert (H3 : forall y, S_to_RlP y
                        <= S_to_RlP (eta Unit tt)).
    intros y; apply S_to_RlP_mon. 
    apply top_greatest. 
    trivial.  
+ assert (HsB : SierJoin (bot Unit) y  = y).
  reflexivity. 
  assert (HrB : forall r, RlPJoin RlP_0 r = r).
  intros r. 
  apply (antisymmetry le).
  -- intros s Hs. 
     unfold RlPJoin in Hs; simpl in Hs. 
     apply top_le_join in Hs. 
     destruct (decide (s < 0)).
     * apply rlpos; trivial.  
     * revert Hs; apply (Trunc_ind _). 
       intros Hs.
       case Hs; intros Ho. 
       ** apply not_bot in Ho; case Ho.
       ** trivial.
  -- intros s Hs; 
     simpl in Hs.
     simpl.             
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
    revert Hn'2; apply (Trunc_ind _). 
    intros (n,Hn'2). 
    specialize (Hn n).
    simpl in Hn'2. 
    unfold join in Hn'2.
    apply top_le_join.
    assert (Hn'3 : val (rl (RlPJoin
                 (S_to_RlP (f n)) (S_to_RlP y))) q). 
    rewrite <- Hn; 
    trivial.
    simpl in Hn'3. 
    apply top_le_join in Hn'3. 
    revert Hn'3; 
    apply (Trunc_ind _);
    intros Hn'3. 
    apply tr. 
    case Hn'3; intros Hh. 
    -- left.
       assert (H1 : elt Q Qlt (Rllub
                               (fun n => S_to_RlP (f n))) q).
       apply top_le_enumerable_sup. 
       apply tr; exists n; trivial.
       trivial. 
    -- right;
       trivial.
  - intros q Hn'.
    unfold RlPJoin in Hn'.
    apply top_le_join in Hn'.
    revert Hn'; 
    apply (Trunc_ind _); 
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
       exists n. 
       simpl.
       revert H'.         
       apply RC_mon with Qle. 
       intros ss sh; apply (antisymmetry le).
       apply orders.le_or_lt.
       reflexivity.
       apply S_to_RlP_mon, 
             SierJoin_is_join. 
    -- apply tr.     
       exists 0. 
       simpl.   
       revert H. 
       apply RC_mon with Qle. 
       intros ss sh; apply (antisymmetry le).
       apply orders.le_or_lt.
       reflexivity.
       apply S_to_RlP_mon,
             SierJoin_is_join. 
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

(** 1_U (x) = 1 iff 1_U (x) > 0 *) 
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
  - simpl; destruct (decide (0 < 1)).  
    apply top_greatest.
    case n.
    apply semirings.lt_0_1. 
  - intros HF. 
    simpl in HF;
    destruct (decide (0 < 0)).  
    apply orders.lt_ne in l. 
    case l; reflexivity. 
    apply not_bot in HF; 
    case HF. 
+ revert H1; unfold OpenFun, S_to_RlP.
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
  - intros f Hn' Hsup'.
    assert (Hn : forall n, RlP_0 < S_to_RlP (f n) -> 
            S_to_RlP (f n) = RlP_1).
    trivial.
    clear Hn'. 
    assert (Hsup : RlP_0 < (RllubPos (fun n =>
                           (S_to_RlP (f n)))));  
    trivial; clear Hsup'.
    assert (H : (RllubPos (fun n => (S_to_RlP (f n)))) 
               = RlP_1).
    apply (antisymmetry le).
    * intros q Hql. 
      apply top_le_enumerable_sup in Hql.
      unfold semi_decide, toRlseq in Hql.
      revert Hql; apply (Trunc_ind _).
      intros (x,Hx).
      destruct (Qle_total 0 q). 
      ** assert (H1 : S_to_RlP (f x) = RlP_1). 
         apply Hn.
         red; unfold Rlltpos, Rllt, RCLt_l; 
         apply tr; exists q.
         split; trivial.
         intros Hf; simpl in Hf; 
         unfold semi_decide in *; 
         destruct (decide (q < 0)).
         apply orders.lt_not_le_flip in l0.
         case (l0 l). 
         apply not_bot in Hf; case Hf.
         rewrite H1 in Hx; trivial.
      ** simpl; unfold semi_decide; 
         destruct (decide (q < 1)).
         apply top_greatest.
         assert (n' : q < 1).
         apply orders.le_lt_trans with 0; trivial.
         apply semirings.lt_0_1.
         case (n n').   
    * intros q Hq1. 
      apply top_le_enumerable_sup.
      unfold semi_decide, toRlseq.
      assert (Hm : hexists 
               (fun m => RlP_0 < S_to_RlP (f m))).
      red in Hsup; unfold Rlltpos, 
                   Rllt, RCLt_l in Hsup.
      revert Hsup; apply (Trunc_ind _); 
      intros (r,(Hr1,Hr2)).
      apply top_le_enumerable_sup in Hr1.
      revert Hr1; apply (Trunc_ind _); 
      intros (m,Hm); 
      unfold semi_decide, toRlseq in *.
      apply tr; exists m.
      red; unfold Rlltpos, Rllt, RCLt_l.
      apply tr.
      exists r; split;  trivial.
      revert Hm; apply (Trunc_ind _); 
      intros (m,Hm).
      apply Hn in Hm.
      apply tr; exists m.
      rewrite Hm; trivial.   
    * trivial.
Qed.   

(** 1_U (x) = 1 iff x ∈ U *) 
Lemma OpenFun_correct {A : hSet} : forall (x:A) U,
               OpenFun A U x = RlP_1 <-> (U x) = SierTop.
Proof. 
intros x U. 
split; intros Hu.
apply OpenFun_0_1 in Hu. 
+ unfold OpenFun, S_to_RlP in *.
  revert Hu.
  generalize (U x).
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
    assert (Hn'2 : RlP_0 < RllubPos 
           (fun n => S_to_RlP (f n))).
    trivial.    
    clear Hn'.
    assert (Ha: merely (exists n : nat, 
              RlP_0 < S_to_RlP (f n))). 
    red in Hn'2; 
    unfold Rlltpos, Rllt, RCLt_l in Hn'2. 
    revert Hn'2; apply (Trunc_ind _).              
    intros (p,(Hp1,Hp2)). 
    apply top_le_enumerable_sup in Hp1.
    revert Hp1; apply (Trunc_ind _).  
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
    apply tr; exists w; 
    rewrite Hn; 
    apply top_greatest. 
+ unfold OpenFun, S_to_RlP; 
  rewrite Hu; simpl. 
  reflexivity. 
Qed.

(** 1_(U /\ V) = (1_U) /\ (1_V) *)
Lemma Meet_pres_openfun {A:hSet}: forall z s,
          MeetPreserving (fun (U: OS A) => val (OpenFun A U z) s). 
Proof.
intros z s x y;
unfold OpenFun, sg_op, meet_is_sg_op.
assert (H1 : (x ⋂ y) z = meet (x z) (y z)).
unfold OS_meet, meet.
apply (antisymmetry le);
apply imply_le; 
intros Hs;
apply top_le_meet in Hs; 
apply top_le_meet; trivial. 
rewrite H1. 
rewrite meet_pres_S_to_RlP. 
reflexivity. 
Qed. 

(** 1_(U \/ V) = (1_U) \/ (1_V) *)
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

(** 1_U + 1_V = 1_(U \/ V) + 1_(U /\ V)*)
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

(* D_op 0 1_U = U *)
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
