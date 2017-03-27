
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

Require Export Spaces.RoundedClosed
               Spaces.Opens Spaces.Functions 
               Theories.Valuations
               Theories.LowerIntegrals
               Theories.Riesz Probas.Giry.


(** * Interpretation of probabilistic programs *)
(**
      .  --> [.] ;

      v  --> unit v ;

 let x=a in b --> bind  [a] (fun x => [b]) ;

     f a  -->  bind  [a] (fun x => [f] x) ;

    if b then a1 else a2 --> bind  [b] (fun x:bool => 
    if b then [a1] else [a2]).
**)



(** Image distributions by a function f :  *) 

Definition im_distr {A B : hSet} (f : A -> B) (J : IntPos A) : IntPos B
                                      := bind J (fun a => unit B (f a)).

Lemma im_distr_id {A : hSet}: forall (f : A -> A) (J : IntPos A),
          (forall x, f x = x) -> im_distr f J = J. 
Proof. 
intros f m Hx. 
unfold im_distr.
assert (Hu : (λ a : A, unit A (f a)) = unit A). 
apply path_forall; intros a.  
rewrite (Hx a); reflexivity. 
rewrite Hu. simpl; rewrite monad2; reflexivity. 
Qed.  

Lemma im_distr_comp {A B C: hSet} (f : A -> B) (g : B -> C) (m : IntPos A) : 
   im_distr g (im_distr f m) = im_distr (fun a => g (f a)) m.
Proof.
apply IntPos_eq0; apply path_forall.
intros h; unfold im_distr; simpl; 
reflexivity. 
Qed.












(**  Conditional distribution *)

Definition DH (A : Type) (hset_A : IsHSet A) := 
                             Val (default_TruncType 0 A hset_A).

Definition Bool_s : hSet := default_TruncType 0 bool hset_bool. 

Definition valb (b : Bool_s) : bool := b.

Definition OSb (B : OS (Bool_s)) : bool -> RlowPos :=
        fun b => (OpenFun Bool_s B) b. 


(** Boundedness of OSb *)
 
Lemma OSb_prob : forall B x, OSb B x <= RlP_1. 
Proof. 
intros B x. 
unfold OSb.
transitivity (OpenFun Bool_s Ω x).
apply OpenFun_mon.
unfold OS_full.
simpl; intros s. 
apply top_greatest. 
apply OpenFun_prob. 
reflexivity. 
Qed. 


Definition Mif (A:hSet) (b: IntPos Bool_s) (m1 m2:IntPos A) : Mes A. 
Proof.                          
intros X.
exists ((bind b (fun x:Bool => if x then m1 else m2)) X).
intros p Hp. 
apply ((bind b (λ x : Bool, if x then m1 else m2)) X); 
trivial. 
Defined. 

(** * Correctness judgements *)

(** ok: the measure of F by the program associated 
        to nu is at least p, here p plays the role of 
        the probability.

    ok_up: the measure of F by the program associated 
           to nu is at most p. *)

Definition ok {A} (p : RlowPos) (nu : IntPos A) (F : mf A) :=
                         p <= nu F. 

Definition ok_fun {A B} (f : mf A) (E : A -> IntPos B) (F : A -> mf B) :=
                     forall x:A, ok (f x) (E x) (F x). 

Definition ok_up {A} (p : RlowPos) (nu : IntPos A) (F : mf A) := nu F <= p. 

Definition up_fun {A B} (f : mf A) (E : A -> IntPos B) (F : A -> mf B) :=
                     forall x:A, ok_up (f x) (E x) (F x). 

(** Correctness rules for applications *)

Lemma apply_rule {A B} : forall (J : IntPos A) (f : A -> IntPos B)
                                (r : RlowPos)
                                (F : mf A) (G : OS B),
          ok r J F -> ok_fun F f (fun x => G) ->
          ok r (bind J f) G. 
Proof.
intros nu f r F G H1 H2.
unfold ok_fun, ok in *.
unfold bind.
simpl. transitivity (nu F); trivial.
apply I_mon; trivial.
Qed. 

Lemma apply_rule_up {A B} : forall (J : IntPos A) (f : A -> IntPos B)
                      (r : RlowPos) (F : mf A) (G : mf B),
    ok_up r J F -> up_fun F f (fun x => G) ->
    ok_up r (bind J f) G. 
Proof.
intros nu f r U V H1 H2. 
unfold up_fun, ok_up in *. 
unfold bind; simpl.
transitivity (nu U); trivial.
apply I_mon; trivial.
Qed.


(** Correctness rules for abstraction *)

Lemma lambda_rule {A B:hSet} : forall (f : A -> IntPos B) (F : mf A)
                                      (G : A -> mf B),
    (forall x:A, ok (F x) (f x) (G x)) -> ok_fun F f G. 
Proof.
intros f F G HO. 
unfold ok_fun, ok in *; trivial. 
Qed. 

Lemma lambda_rule_up {A B:hSet} : forall (f : A -> IntPos B) (F : mf A) (G : A -> mf B),
       (forall x:A, ok_up (F x) (f x) (G x)) -> up_fun F f G. 
Proof.
intros f F G HO. 
unfold up_fun, ok_up in *; trivial. 
Qed. 

(** * Little examples of probabilistic programs *)

(** Flip program : Val bool
 
   fun f: bool -> Sier  => (1/2) (f true) + 
                           (1/2) (f false)
*)

Definition flip : IntPos Bool_s. 
Proof.
exists (fun f => (RlP_plus (Rlow_mult_q (1 / 2) (f true))
       (Rlow_mult_q (1 / 2) (f false)))).
+ unfold Mdef.
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
       admit. (* ok *)
    -- apply not_bot in H2; case H2. 
    -- apply not_bot in H1; case H1. 
  - intros p Hp; simpl;   
    unfold pred_multQ, semi_decide; simpl.
    apply pred_plus_pr. 
    apply tr.
    exists (p/2), (p/2).
    destruct (decide ((' 1 * ' (/ 2) * (p/2))%mc < 0)%mc);
    admit. 
(*field *)
+ intros f g.
  apply (antisymmetry le).
  - intros q Hq.
    apply pred_plus_pr in Hq; 
    apply pred_plus_pr.
    revert Hq; apply (Trunc_ind _); 
    intros (r,(s,(Hrs1,(Hrs2,Hrs3)))). 
    assert (Hrs1' : val (RlP_plus 
                         (Rlow_mult_q (1 / 2) (f true))  
                         (Rlow_mult_q (1 / 2) (g true))) r).
    admit.
 
    assert (Hrs2' : val (RlP_plus 
                         (Rlow_mult_q (1 / 2) (f false))  
                         (Rlow_mult_q (1 / 2) (g false))) s).
    admit.

    apply pred_plus_pr in Hrs1'.
    apply pred_plus_pr in Hrs2'.
    revert Hrs1'; apply (Trunc_ind _); 
    intros (r1,(s1,(H11,(H12,H13)))).
    revert Hrs2'; apply (Trunc_ind _); 
    intros (r2,(s2,(H21,(H22,H23)))).
    apply tr.
    exists (r1 + r2).
    exists (s1 + s2).
    repeat split.
    -- apply pred_plus_pr.
       apply tr.
       exists r1, r2.
       repeat split; trivial.
    -- apply pred_plus_pr.
       apply tr.
       exists s1, s2.
       repeat split; trivial.
    -- rewrite H13, H23 in Hrs3;
       rewrite <- rings.plus_assoc;
       rewrite (rings.plus_comm r2 (s1 + s2));
       rewrite <- rings.plus_assoc;
       rewrite (rings.plus_comm s2 r2);
       rewrite rings.plus_assoc;
       rewrite rings.plus_assoc;
       rewrite rings.plus_assoc in Hrs3;
       trivial.
  - intros q Hq.
    apply pred_plus_pr in Hq; 
    apply pred_plus_pr.
    revert Hq; apply (Trunc_ind _); 
    intros (r,(s,(Hrs1,(Hrs2,Hrs3)))).
    apply pred_plus_pr in Hrs1.
    apply pred_plus_pr in Hrs2.
    revert Hrs1; apply (Trunc_ind _); 
    intros (r1,(s1,(H11,(H12,H13)))).
    revert Hrs2; apply (Trunc_ind _); 
    intros (r2,(s2,(H21,(H22,H23)))).
    apply tr.
    exists (r1 + r2).
    exists (s1 + s2).
    repeat split.
    -- assert (H1' : val (RlP_plus (Rlow_mult_q (1 / 2) (f true)) 
                                   (Rlow_mult_q (1 / 2) (g true)))
                       (r1 + r2)).
       apply pred_plus_pr.
       apply tr.
       exists r1, r2.
       repeat split; trivial.   
       admit.
    -- assert (H2' : val (RlP_plus (Rlow_mult_q (1 / 2) (f false)) 
                                   (Rlow_mult_q (1 / 2) (g false)))
                       (s1 + s2)).
       apply pred_plus_pr.
       apply tr.
       exists s1, s2.
       repeat split; trivial.   
       admit.
    -- 
    assert (Hrs1' : val (RlP_plus  *)
                         (Rlow_mult_q (1 / 2) (f true))  
                         (Rlow_mult_q (1 / 2) (g true))) r).
    admit.
 
    assert (Hrs2' : val (RlP_plus 
                         (Rlow_mult_q (1 / 2) (f false))  
                         (Rlow_mult_q (1 / 2) (g false))) s).
    admit.

    apply pred_plus_pr in Hrs1'.
    apply pred_plus_pr in Hrs2'.
    revert Hrs1'; apply (Trunc_ind _); 
    intros (r1,(s1,(H11,(H12,H13)))).
    revert Hrs2'; apply (Trunc_ind _); 
    intros (r2,(s2,(H21,(H22,H23)))).
    apply tr.
    exists (r1 + r2).
    exists (s1 + s2).
    repeat split.
    -- apply pred_plus_pr.
       apply tr.
       exists r1, r2.
       repeat split; trivial.
    -- apply pred_plus_pr.
       apply tr.
       exists s1, s2.
       repeat split; trivial.
    -- rewrite H13, H23 in Hrs3;
       rewrite <- rings.plus_assoc;
       rewrite (rings.plus_comm r2 (s1 + s2));
       rewrite <- rings.plus_assoc;
       rewrite (rings.plus_comm s2 r2);
       rewrite rings.plus_assoc;
       rewrite rings.plus_assoc;
       rewrite rings.plus_assoc in Hrs3;
       trivial.    

    
    exists r, s.
    repeat split. 
    -- unfold fplus in Hrs1.
       assert (Hrs1' : val (RlP_plus 
                             (Rlow_mult_q (1 / 2) (f true))  
                             (Rlow_mult_q (1 / 2) (g true))) r).
       admit.
+ admit. 
+ intros f g Hfg.
  transitivity (RlP_plus (Rlow_mult_q (1 / 2) 
      (f true)) (Rlow_mult_q (1 / 2) (g false))). 
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt. 
  reflexivity.
  apply Hfg.
  rewrite RlPPlus_comm.
  rewrite (RlPPlus_comm 
       (Rlow_mult_q (1 / 2) (g true))).    
  apply RlPlus_le_preserving.
  intros s Hs.
  unfold Rlow_mult_q in *.
  simpl in *; unfold pred_multQ in *.
  revert Hs; apply RC_mon with Qle. 
  intros x y; apply (antisymmetry le). 
  intros x y; apply orders.le_or_lt. 
  reflexivity.
  apply Hfg.
+ admit. 
Admitted. 

Definition Nat_s : hSet := default_TruncType 0 nat hset_nat. 

Definition valn (n : Nat_s) : nat := n.

Definition OSn (N : OS (Nat_s)) : nat -> RlowPos :=
        fun n => (OpenFun Nat_s N) n. 


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

Definition random_aux (M : nat) : Mes Nat_s. 
Proof.
intros N.
pose (N' := OSn N).
exists (rl (sum_n_moy M N')).
apply (sum_n_moy M). 
Defined. 

Definition random (M : nat) :  Val Nat_s.  
Proof. 
exists (random_aux M).  
+ unfold modular. intros U V.
  apply (antisymmetry Rllepos).   
  unfold Rllepos; simpl. 
  intros q Hq. 
  - unfold OSn in *. 
    apply pred_plus_pr. 
    apply pred_plus_pr in Hq. 
    revert Hq; apply (Trunc_ind _). 
    intros (r,(s,(E1,(E2,E3)))).
    apply tr. 
    exists r, s. 
    admit. 
  - admit. 
+ unfold empty_op. 
  apply (antisymmetry Rllepos). 
  - intros p Hp.
    simpl in Hp.
    induction M. 
    -- simpl in Hp.
       unfold semi_decide in Hp.
       unfold pred_multQ in Hp.
       destruct (decide ((rationals.pos (O_Sp 0) * p)%mc < 0)).
       simpl. unfold semi_decide.
       destruct (decide (p < 0)). 
       apply top_greatest. 
       unfold O_Sp in l. 
       simpl in l. 
       admit. (* ok *)
       apply not_bot in Hp. 
       case Hp. 
    -- assert (Hnn : elt Q Qlt (rl (sum_n_moy M (OSn ∅))) p).
       revert Hp. 
       apply RC_mon with Qle.   
       intros x y; apply (antisymmetry Qle). 
       intros x y; apply orders.le_or_lt. 
       reflexivity. 
       intros q Hq. 
       unfold sum_n_moy in *. 
       simpl in Hq.        
       unfold pred_multQ in Hq. 
       apply pred_plus_pr in Hq.
       revert Hq; apply (Trunc_ind _).
       intros (r,(s,(H1,(H2,H3)))).
       unfold OSn.  
       admit. (* ok but cumbersome *)

       apply IHM; trivial.
  - intros q Hq.
    apply rlpos. 
    simpl in Hq; 
    unfold semi_decide in Hq;
    destruct (decide (q < 0)); try trivial.  
    apply not_bot in Hq.     
    case Hq. 
+ unfold mon_opens. 
  intros U V HUV.
  intros q Hq. 
  unfold random_aux in *; simpl in *.
  induction M.
  - simpl in *. 
    trivial.
  - simpl.    
    simpl in Hq.     
    unfold pred_multQ in Hq. 
    unfold pred_multQ. 
    apply pred_plus_pr. 
    apply pred_plus_pr in Hq. 
    revert Hq; apply (Trunc_ind _). 
    intros (r,(s,(E1,(E2,E3)))).
    apply tr. 
    exists r, s.     
    repeat split; trivial. 
    revert E1. 
    apply RC_mon with Qle. 
    intros x y; apply (antisymmetry Qle). 
    intros x y; apply orders.le_or_lt.
    reflexivity.
    apply OpenFun_mon. 
    trivial.
    revert E2.
Admitted. 


