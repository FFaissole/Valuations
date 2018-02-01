

Require Import HoTT.Classes.interfaces.abstract_algebra
               HoTT.Classes.interfaces.orders
               partiality
               sierpinsky
               dedekind
               HoTT.Classes.theory.rationals
               HoTT.Classes.theory.premetric
               HoTT.Classes.orders.orders
               HoTT.Classes.orders.semirings
               HoTT.Classes.implementations.assume_rationals. 
Require Import HoTT.HSet HoTT.Basics.Trunc HProp HSet
               Types.Universe
               TruncType Types.Sigma
               HIT.quotient. 

Require Export Rlow Opens Functions D_op.
              

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
  assert (Rlle (s n) ((fun (f0 : nat -> RlowPos)
       (_ : forall n : nat, Rlle (f0 n) (f0 (S n))) => 
       RllubPos f0) s Hp)).
  simpl.
  apply RllubPos_lub.
  unfold Rlle in *; red in Hi; auto.
  red; unfold Rllepos, Rlle in *.
  auto.
+ intros s Hi x Hn q Hh.
  assert (Hx : (elt (Rllub s) q)).
  trivial.
  assert (H2 : Rlle (RllubPos s) x).
  apply RllubPos_le. trivial.
  apply Rlow_mon with (Rllub s) q. 
  reflexivity. 
  trivial. 
  trivial.
Defined.

(** Monotonicity of the map from Sier to RlowPos *)
Lemma S_to_RlP_mon : forall s1 s2, SierLe s1 s2
                        -> Rlle (S_to_RlP s1) (S_to_RlP s2).
Proof.
apply (partialLe_ind0 _ _).
+ unfold Rlle; auto.
+ assert (X : S_to_RlP (bot Unit) = RlP_0).
  auto; rewrite X.
  intros. apply RlowPos_pos.
+ intros f x H1 H2 n.
  assert (H : Rlle (S_to_RlP (f n)) (S_to_RlP (sup Unit f))).
  assert (Hr : S_to_RlP (sup Unit f) = RllubPos
                        (fun n => S_to_RlP (f n))).
  auto. rewrite Hr.
  apply (Rllub_lub (fun n => S_to_RlP (f n))); trivial.
  unfold Rlle in *; auto.
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
  assert (H2 : forall x:RlowPos, Rlle x RlP_1 -> 
                    RlPMeet RlP_1 x = x). 
  intros rr Hrr.
  apply (antisymmetry le). 
  - intros s Hs. 
    simpl in Hs. 
    destruct (dec (s < 1)%mc).
    unfold meet in Hs. 
    apply top_le_meet in Hs. 
    apply (snd Hs). 
    apply top_le_meet in Hs. 
    apply (snd Hs). 
  - intros s Hs.
    simpl.
    apply top_le_meet. 
    split.
    unfold semi_decide, Rllt_semi_dec, decidable_semi_decide. 
    destruct (dec (s < Qone)%mc). 
    apply top_greatest. 
    case n. 
    red in Hrr;
    unfold Rlle in Hrr. 
    specialize (Hrr s Hs). 
    simpl in Hrr. 
    unfold semi_decide, Rllt_semi_dec, decidable_semi_decide in *.
    destruct (dec (s < Qone)).     
    case (n l). 
    apply not_bot in Hrr; 
    case Hrr. 
    trivial.
  - rewrite H2.
    reflexivity.
    assert (H : Rlle (S_to_RlP SierTop) RlP_1).
    unfold Rlle; auto.
    unfold Rlle in *; intros q Hq.
    apply H. 
    revert Hq.
    apply S_to_RlP_mon. 
    apply top_greatest.
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
       unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
       destruct (dec (s < Qzero)). 
       destruct Hs as (_,Hs). 
       simpl. 
       unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
       destruct (dec (s < Qzero)). 
       apply top_greatest. 
       case (n l).
       destruct Hs as (Hs,_). 
       apply not_bot in Hs; case Hs.
    -- intros s Hs; simpl in Hs. 
       destruct (RlPMeet RlP_0 r) as (rr,Hprr); simpl. 
       unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
       destruct (dec (s < Qzero)).            
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
    assert (Hn'2 : elt (Rllub
                  (fun n => S_to_RlP ((SierMeet_seq_l f y) n))) q). 
    trivial.
    clear Hn'.
    apply top_le_enumerable_sup in Hn'2.             
    revert Hn'2; apply (Trunc_ind _). 
    intros (n,Hn'2). 
    specialize (Hn n).
    simpl in Hn'2. 
    assert (H3 : elt (rl (S_to_RlP y)) q).
    revert Hn'2. 
    apply Rlow_mon. 
    reflexivity. 
    apply S_to_RlP_mon. 
    apply SierMeet_is_meet.
    trivial.
    assert (Ho : elt 
                     (RlMeet (RllubPos (fun n => S_to_RlP (f n)))
                              (S_to_RlP y)) q). 
    unfold RlPMeet. 
    simpl.
    apply top_le_meet. 
    split. 
    -- apply top_le_enumerable_sup. 
       apply tr. 
       unfold semi_decide.
       exists n.
       revert Hn'2.
       apply Rlow_mon. 
       reflexivity. 
       apply S_to_RlP_mon.
       apply SierMeet_is_meet. 
    -- apply H3.
    -- trivial. 
  - intros q Hn'.
    unfold RlPMeet in Hn'.
    apply top_le_meet in Hn'.
    destruct Hn' as (Hna,Hnb). 
    assert (Hna2 : elt (Rllub
                   (fun n => S_to_RlP (f n))) q).
    trivial. clear Hna.
    apply top_le_enumerable_sup in Hna2.
    revert Hna2; apply (Trunc_ind _). 
    intros (m,Hm).
    assert (H2 : SierMeet (sup Unit f) y =
                 sup _ (SierMeet_seq_l f y)). 
    apply SierMeet_sup.   
    rewrite H2.
    assert (H3 : elt (Rllub
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
  assert (H2 : forall x:RlowPos, Rlle x RlP_1 -> 
                    RlPJoin RlP_1 x = RlP_1). 
  intros rr Hrr.
  apply (antisymmetry le). 
  - intros s Hs. 
    simpl in Hs. 
    unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
    destruct (dec (s < Qone)).
    apply top_le_join in Hs.
    revert Hs; (apply (Trunc_ind _)).
    intros Hs. 
    destruct Hs;
    simpl; unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
    destruct (dec (s < Qone)); try trivial.   
    case (n l).
    destruct (dec (s < Qone)); try trivial.   
    apply top_greatest.
    case (n l).
    apply top_le_join in Hs.
    unfold hor in Hs.
    revert Hs; (apply (Trunc_ind _)).
    intros []. intros i. 
    -- apply not_bot in i; case i. 
    -- simpl; intros i.
       unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
       destruct (dec (s < Qone)); try trivial. 
       apply top_greatest.
       red in Hrr. 
       apply Hrr in i. 
       simpl in i; unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
       destruct (dec (s < Qone)); try trivial. 
       case (n0 l).
                                        
  - intros s Hs.
    apply top_le_join. 
    apply tr.
    simpl in Hs; simpl. 
    unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
    destruct (dec (s < Qone)). 
    left; trivial. 
    left; trivial.
  - simpl.
    rewrite H2.
    reflexivity.
    clear H1. 
    revert y.
    assert (H3 : forall y, Rlle (S_to_RlP y)
                        (S_to_RlP (eta Unit tt))).
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
     unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *. 
     destruct (dec (s < Qzero)).
     * apply rlpos; trivial.  
     * revert Hs; apply (Trunc_ind _). 
       intros Hs.
       case Hs; intros Ho. 
       ** apply not_bot in Ho; case Ho.
       ** trivial.
  -- intros s Hs; 
     simpl in Hs.
     simpl.             
     unfold semi_decide, Rllt_semi_dec, 
              decidable_semi_decide in *.
     destruct (dec (s < Qzero)). 
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
    assert (Hn'2 : elt (Rllub
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
    assert (Hn'3 : elt (rl (RlPJoin
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
       assert (H1 : elt (Rllub
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
    assert (H3 : elt (Rllub
                     (fun n => S_to_RlP
                     ((SierJoin_seq_l f y) n))) q).
    apply top_le_enumerable_sup.     
    case Hn'; intros H;
    unfold semi_decide, semi_decide_sier in H. 
    -- assert (H' : elt (Rllub (fun n => S_to_RlP
                                   (f n))) q).
       trivial. clear H. 
       apply top_le_enumerable_sup in H'. 
       revert H'; apply (Trunc_ind _). 
       intros (n,H'). 
       apply tr. 
       exists n. 
       simpl.
       revert H'.         
       apply Rlow_mon.
       reflexivity.
       apply S_to_RlP_mon, 
             SierJoin_is_join. 
    -- apply tr.     
       exists O. 
       simpl.   
       revert H. 
       apply Rlow_mon.
       reflexivity.
       apply S_to_RlP_mon,
             SierJoin_is_join. 
    -- trivial. 
Qed. 

Coercion S_to_RlP : Sier >-> RlowPos. 

End S_to_RlP.   


Section OpenFun. 

(** Map from Opens to characteristic function *)
Definition OpenFun {A : hSet} : forall (U : A -> Sier),
                                       (A -> RlowPos). 
Proof. 
intros s z. 
exact (let sz := s z in (S_to_RlP sz)).
Defined.

(** OpenFun is definite *)
Lemma OpenFun_def {A} : forall U:OS A, U = OS_empty
                               -> OpenFun U = fun x => RlP_0. 
Proof.
intros U HU; 
apply path_forall; 
intros x; rewrite HU; auto. 
Qed. 

(** OpenFun is sub-probabilistic*)
Lemma OpenFun_prob {A} : forall U:OS A, U = OS_full
                               -> ffle (OpenFun U) (fun x => RlP_1). 
Proof.
intros U HU x;
rewrite HU; unfold Rlle; auto.
Qed. 

(** OpenFun is monotonic *)
Lemma OpenFun_mon {A} : forall U V:OS A, Osle U V -> fle (OpenFun U) (OpenFun V).
Proof.
intros U V H1 s;
unfold OpenFun;
apply S_to_RlP_mon; trivial.
Qed.

Lemma Toto : forall p, p = 0%mc -> elt RlP_1 p.
Proof.
intros p Hp.
unfold RlP_1.
simpl.
unfold semi_decide, Rllt_semi_dec, 
       decidable_semi_decide in *.
destruct (dec (p < Qone)).
apply top_greatest.
rewrite Hp in n.
assert (X : 0%mc < Qone).
apply lt_0_1.
case (n X).
Qed.

(** 1_U (x) = 1 iff 1_U (x) > 0 *) 
Lemma OpenFun_0_1 {A  : hSet}: forall (U : OS A) z,
    OpenFun U z = RlP_1 <-> RlP_0 < OpenFun U z.
Proof. 
intros U z.
split; intros H1.  
+ rewrite H1.
  red; unfold Rlltpos, Rllt. 
  apply tr. 
  exists Qzero. 
  split. 
  - assert (Hh : forall p, p = 0%mc -> elt RlP_1 p).
    intros p Hp; unfold RlP_1.
    simpl.
    unfold semi_decide, Rllt_semi_dec, 
       decidable_semi_decide in *.
    destruct (dec (p < Qone)).
    apply top_greatest.
    rewrite Hp in n.
    assert (X : 0%mc < Qone).
    apply lt_0_1.
    case (n X).
    apply Hh. 
    reflexivity. 
  - intros HF.
    assert (Hh : forall p, p = 0%mc -> ~ elt RlP_0 p). 
    intros p Hp H.
    simpl in H.
    unfold semi_decide, Rllt_semi_dec, 
       decidable_semi_decide in *.
    destruct (dec (p < Qzero)).
    rewrite Hp in l.
    assert (Hl : ~ 0%mc < Qzero).
    apply le_not_lt_flip.
    reflexivity.
    case (Hl l).
    apply not_bot in H; case H.
    specialize (Hh Qzero). 
    assert (Hj : Qzero = 0%mc). 
    reflexivity. 
    apply Hh in Hj. 
    case (Hj HF).
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
      destruct (Qle_total Qzero q). 
      ** assert (H1 : S_to_RlP (f x) = RlP_1). 
         apply Hn.
         red; unfold Rlltpos, Rllt; 
         apply tr; exists q.
         split; trivial.
         intros Hf; simpl in Hf; 
         unfold semi_decide, Rllt_semi_dec, 
            decidable_semi_decide in *; 
         destruct (dec (q < Qzero)).
         apply orders.lt_not_le_flip in l0.
         case (l0 l). 
         apply not_bot in Hf; case Hf.
         rewrite H1 in Hx; trivial.
      ** simpl; unfold semi_decide, Rllt_semi_dec, 
                decidable_semi_decide; 
         destruct (dec (q < Qone)).
         apply top_greatest.
         assert (n' : q < Qone).
         apply orders.le_lt_trans with Qzero; trivial.
         apply semirings.lt_0_1.
         case (n n').   
    * intros q Hq1. 
      apply top_le_enumerable_sup.
      unfold semi_decide, toRlseq.
      assert (Hm : hexists 
               (fun m => RlP_0 < S_to_RlP (f m))).
      red in Hsup; unfold Rlltpos, 
                   Rllt in Hsup.
      revert Hsup; apply (Trunc_ind _); 
      intros (r,(Hr1,Hr2)).
      apply top_le_enumerable_sup in Hr1.
      revert Hr1; apply (Trunc_ind _); 
      intros (m,Hm); 
      unfold semi_decide, toRlseq in *.
      apply tr; exists m.
      red; unfold Rlltpos, Rllt.
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
               OpenFun U x = RlP_1 <-> (U x) = SierTop.
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
    unfold Rllt in Hf.
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
    unfold Rlltpos, Rllt in Hn'2. 
    revert Hn'2; apply (Trunc_ind _).              
    intros (p,(Hp1,Hp2)). 
    apply top_le_enumerable_sup in Hp1.
    revert Hp1; apply (Trunc_ind _).  
    intros (m,Hm).
    apply tr. 
    exists m.
    red;unfold Rlltpos, Rllt. 
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
          MeetPreserving (fun (U: OS A) => elt (OpenFun U z) s). 
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
          JoinPreserving (fun (U: OS A) => elt (OpenFun U z) s). 
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
Lemma OpenFun_mod {A}: forall (U V : OS A), fplus (OpenFun U) (OpenFun V) =
                                fplus (OpenFun (OS_meet U V))
                                      (OpenFun (OS_join U V)).
Proof.
intros U V.
apply path_forall; intros z. 
apply (antisymmetry le). 
+ intros q Hs. 
  simpl in *. 
  apply RlPlus_eq_pr in Hs.
  apply RlPlus_eq_pr.
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
         apply Rlow_mon; trivial.
         intros s Hs; trivial.
    -- apply Rlow_mon with (rl (OpenFun V z)) r'; trivial.
       reflexivity.
       apply OpenFun_mon. 
       intros s; apply SierJoin_is_join; apply Hr'.       
  - exists r', r.
    repeat split; try trivial.   
    -- red.
       rewrite Meet_pres_openfun.
       apply SierMeet_is_meet.  
       * revert Hr.
         apply Rlow_mon; trivial.
         intros s Hs;trivial.
       * trivial. 
    -- apply Rlow_mon with (rl (OpenFun U z)) r; trivial.
       reflexivity.
       apply OpenFun_mon. 
       intros s; apply SierJoin_is_join; apply Hr.
    -- rewrite rings.plus_comm; trivial.
+ intros q Hs. simpl in *. 
  apply RlPlus_eq_pr in Hs.
  apply RlPlus_eq_pr.
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
       assert (Hr1 : elt (rl (OpenFun U z)) r).
       revert Hr.
       apply SierLe_imply.
       apply SierMeet_is_meet.
       revert Hr1.
       apply Rlow_mon; try trivial.
       intros s Hs; trivial.
    -- revert Hr; apply OpenFun_mon.
       intros s; apply SierMeet_is_meet.
    -- rewrite rings.plus_comm; trivial.
Qed.

(* D_op 0 1_U = U *)
Lemma D_op_OpenFun {A  : hSet}: forall (U : OS A),
           (D_op Qzero (OpenFun U)) = U. 
Proof.
intros U.
pose (Hdp := D_op_correct (OpenFun U) Qzero).
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

(** 1_U preserves lub *)
Lemma OpenFun_lub {A : hSet} : 
    forall (U : IncreasingSequence (OS A)) x, 
         OpenFun (Cpo.lub U) x = 
                RllubPos (fun n => (OpenFun (U n)) x).
Proof. 
intros U x.
unfold OpenFun; simpl.
apply (antisymmetry le).
+ intros s Hs. 
  apply top_le_enumerable_sup in Hs. 
  unfold semi_decide, toRlseq in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (m,Hm).
  apply top_le_enumerable_sup.
  apply tr; exists m.  
  revert Hm; apply S_to_RlP_mon.
  apply imply_le.
  intros Hv. 
  apply top_le_joined_seq_n' in Hv.
  revert Hv; apply (Trunc_ind _).
  intros (p,Hp).
  destruct Hp as (Hpm,HUp).
  revert HUp.
  apply SierLe_imply.
  assert (H' : Osle (U p) (U m)).
  apply seq_increasing_le; trivial.
  apply H'.  
+ intros s Hs.
  apply top_le_enumerable_sup in Hs.
  unfold semi_decide, toRlseq in Hs.
  revert Hs; apply (Trunc_ind _).
  intros (m,Hm).
  revert Hm; apply S_to_RlP_mon.
  apply imply_le. 
  intros H. 
  apply top_le_countable_sup.
  apply tr; exists m; trivial.
Qed. 

(** fun n => U n ---> fun n => 1_(U n) *)
Definition OpenFun_increasing_sequence {A : hSet} : 
   IncreasingSequence (OS A) -> IncreasingSequence (mf A).
Proof.
intros U.
exists (fun n => OpenFun (U n)).  
intros n x.
apply OpenFun_mon.
apply U.
Defined. 

Definition OpenFun_meet_fun {A : hSet} (U : OS A) (f : mf A) := 
             fun x => RlPMeet (f x) (OpenFun U x).


End OpenFun.
