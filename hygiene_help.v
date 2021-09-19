Require Import Program.Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined DefsEquiv.

Definition hctx G := @hygiene obj (@ctxpred obj G).

Transparent hctx.

Require Import lib.

Lemma under_op (G : @context obj) : hincl (fun i => (i < length G)%coq_nat)
                         (fun j : nat => 
     (j < 0)%coq_nat \/
     (j >= 0)%coq_nat /\
     ((j - 0)%coq_nat < (length G))%coq_nat ).
  move => i Hi.  right. split; auto.
  (*Hint Rewrite <- minus_n_O : test.
autorewrite with test. works
but autorewrite with natlib loops?*)
  nat_rewrite. assumption.
Qed.

Lemma under_binder (G : @context obj) x : hincl (fun i => (i < length (x :: G))%coq_nat)
                         (fun j : nat => 
     (j < 1)%coq_nat \/
     (j >= 1)%coq_nat /\
     ((j - 1)%coq_nat < (length G))%coq_nat ).
  move => i Hi. destruct (i < 1) eqn: Hbool.
  left. apply/ltP: Hbool.
  right. assert (0 < i). move/negbT: Hbool. rewrite - leqNgt. apply.
  split. apply/leP. assumption.
  apply/ltP. rewrite minusE.
  Search (?n.-1 < ?m = (?n <= ?m)). rewrite ltn_subLR.
  move/ltP: Hi. auto. assumption.
Qed.
Lemma hygiene_pi G m1 m2: (hctx G) m1 ->
                               (hctx ((hyp_tm m1) :: G)) m2 ->
                               (hctx G) (pi m1 m2).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H1. repeat constructor.
  apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_karrow G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (karrow m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_arrow G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (arrow m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.



Lemma hygiene_lam G m: 
                               (hctx ((hyp_tp) :: G)) m ->
                               (hctx G) (lam m).
  unfold hctx. rewrite ! ctxpred_length. move => H1. repeat constructor.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_app G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (app m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_fut G m1: (hctx G) m1 ->
                               (hctx G) (fut m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_next G m1: (hctx G) m1 ->
                               (hctx G) (next m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_prev G m1: (hctx G) m1 ->
                               (hctx G) (prev m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_rec G m: (hctx (hyp_tp :: G)) m -> (hctx G (rec m)).
  unfold hctx. rewrite ! ctxpred_length. move => H1. repeat constructor.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1. Qed.

Lemma hygiene_triv G: (hctx G triv). repeat constructor. Qed.

Lemma hygiene_eqtype G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (eqtype m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_all G i k m: (hctx G) i -> (hctx G) k ->
                               (hctx ((hyp_tm k) :: G)) m ->
                               (hctx G) (all i k m).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H00 H1.
  repeat constructor; try (apply (hygiene_weaken _ _ _ _ (under_op _)); assumption).
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_exist G i k m: (hctx G) i -> (hctx G) k ->
                               (hctx ((hyp_tm k) :: G)) m ->
                               (hctx G) (exist i k m).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H00 H1.
  repeat constructor; try (apply (hygiene_weaken _ _ _ _ (under_op _)); assumption).
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_voidtp G: (hctx G voidtp). repeat constructor. Qed.

Lemma hygiene_unittp G: (hctx G unittp). repeat constructor. Qed.
Lemma hygiene_booltp G: (hctx G booltp). repeat constructor. Qed.
Lemma hygiene_btrue G: (hctx G btrue). repeat constructor. Qed.
Lemma hygiene_bfalse G: (hctx G bfalse). repeat constructor. Qed.

Lemma hygiene_bite G m1 m2 m3: (hctx G) m1 -> (hctx G) m2 ->
                               (hctx G) m3 ->
                               (hctx G) (bite m1 m2 m3).
  unfold hctx. rewrite ! ctxpred_length. 
  repeat constructor; try (apply (hygiene_weaken _ _ _ _ (under_op _)); assumption). Qed.

Lemma hygiene_prod G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (prod m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_sigma G m1 m2: (hctx G) m1 ->
                               (hctx ((hyp_tm m1) :: G)) m2 ->
                               (hctx G) (sigma m1 m2).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H1. repeat constructor.
  apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_ppair G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (ppair m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_ppi1 G m1: (hctx G) m1 ->
                               (hctx G) (ppi1 m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.
Lemma hygiene_ppi2 G m1: (hctx G) m1 ->
                               (hctx G) (ppi2 m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_wt G m1 m2: (hctx G) m1 ->
                               (hctx ((hyp_tm m1) :: G)) m2 ->
                               (hctx G) (wt m1 m2).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H1. repeat constructor.
  apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.


Lemma hygiene0 G x: (hctx (x::G) (var 0)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene_hint G x y: (hctx (x::y::G) (var 1)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene2 G x y z: (hctx (z::x::y::G) (var 2)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene3 G x y z a: (hctx (a::z::x::y::G) (var 3)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene_univ G m: (hctx G) m ->
                               (hctx G) (univ m).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Hint Resolve hygiene_pi hygiene_karrow hygiene_arrow hygiene_lam hygiene_app
     hygiene_fut hygiene_prev hygiene_next hygiene_rec hygiene_triv hygiene_eqtype
     hygiene_all hygiene_exist hygiene_voidtp hygiene_unittp hygiene_booltp
     hygiene_bfalse hygiene_btrue hygiene_bite hygiene_prod hygiene_sigma hygiene_ppair
     hygiene_ppi1 hygiene_ppi2 hygiene_wt hygiene0 hygiene_hint hygiene2 hygiene3 hygiene_univ: hygiene_hint.

Ltac hyg_solv := try (prove_the_hygiene; simpl; auto); eauto 50 with hygiene_hint.

Lemma hygiene_makesubseq G: (hctx G) make_subseq.
unfold make_subseq. hyg_solv. Qed.

Hint Resolve hygiene_makesubseq: hygiene_hint.

Lemma hygiene_moveapp G A m v: (hctx G) m ->
                               (hctx G) v ->
                               (hctx G) (move_app A m v).
  unfold move_app. move => Hm Hv.
  induction A; simpl; hyg_solv.
Qed.

Lemma hygiene_nat G: (hctx G) nattp.
  prove_the_hygiene. simpl. auto. Qed.

Lemma hygiene_nzero: forall G, (hctx G) nzero.
   unfold nzero. hyg_solv. Qed.
Hint Resolve hygiene_nat hygiene_nzero: hygiene_hint.

Lemma hygiene_U0: forall G, (hctx G) (univ nzero).
  intros. unfold U0. hyg_solv.
Qed.

Hint Resolve hygiene_U0: hygiene_hint.

Lemma hygiene_pw G: (hctx G) preworld. unfold preworld. hyg_solv.
Qed.

Hint Resolve hygiene_pw : hygiene_hint.

Lemma hygiene_theta G : (hctx G) theta.
  unfold theta. hyg_solv. Qed.
Hint Resolve hygiene_theta: hygiene_hint.

Lemma hygiene_minus G : (hctx G) minus.
  unfold minus. unfold minusbc. hyg_solv. Qed.
Hint Resolve hygiene_minus: hygiene_hint.

Lemma hygiene_sh1 G n x: (hctx G) n ->
                         hctx (x :: G) (subst sh1 n).
  intros. eapply hygiene_shift'.
  rewrite ctxpred_length.
  match goal with |- hygiene ?f ?n => suffices: hincl (ctxpred G) f end. 
  move => Hincl. apply (hygiene_weaken _ _ _ _ Hincl).
  assumption. rewrite ctxpred_length. move =>> Hi. simpl.
  omega. Qed.


Lemma hygiene_sh3 G n x y z: (hctx G) n ->
                         hctx (x :: y:: z::G) (subst (sh 3) n).
  intros. eapply hygiene_shift'.
  rewrite ctxpred_length.
  match goal with |- hygiene ?f ?n => suffices: hincl (ctxpred G) f end. 
  move => Hincl. apply (hygiene_weaken _ _ _ _ Hincl).
  assumption. rewrite ctxpred_length. move =>> Hi. simpl.
  omega. Qed.

Lemma hygiene_sh2 G n x y: (hctx G) n ->
                         hctx (x :: y:: G) (subst (sh 2) n).
  intros. eapply hygiene_shift'.
  rewrite ctxpred_length.
  match goal with |- hygiene ?f ?n => suffices: hincl (ctxpred G) f end. 
  move => Hincl. apply (hygiene_weaken _ _ _ _ Hincl).
  assumption. rewrite ctxpred_length. move =>> Hi. simpl.
  omega. Qed.

Lemma hygiene_sh4 G n x y z a: (hctx G) n ->
                         hctx (x :: y:: z:: a :: G) (subst (sh 4) n).
  intros. eapply hygiene_shift'.
  rewrite ctxpred_length.
  match goal with |- hygiene ?f ?n => suffices: hincl (ctxpred G) f end. 
  move => Hincl. apply (hygiene_weaken _ _ _ _ Hincl).
  assumption. rewrite ctxpred_length. move =>> Hi. simpl.
  omega. Qed.

Hint Resolve hygiene_sh1 hygiene_sh2 hygiene_sh3 hygiene_sh4: hygiene_hint.

Lemma hygiene_nsucc G n: (hctx G) n -> (hctx G) (nsucc n).
  intros. unfold nsucc. hyg_solv. Qed.

Hint Resolve hygiene_nsucc: hygiene_hint.

Lemma hygiene_ltb G : (hctx G) lt_b.
  intros. unfold lt_b. unfold if_z. hyg_solv. Qed.
Hint Resolve hygiene_ltb: hygiene_hint.

Lemma hygiene_world: forall G, (hctx G) world.
intros. unfold world. hyg_solv. Qed.  
Hint Resolve hygiene_world: hygiene_hint.


Lemma hygiene_leqtp: forall G, (hctx G) leqtp.
  intros. hyg_solv. Qed. 

Lemma hygiene_bind: forall G m1 m2, (hctx G) m1 -> (hctx G) m2 ->
                               (hctx G) (make_bind m1 m2).
  intros. hyg_solv. Qed.


Lemma hygiene_lttp: forall G, (hctx G) lttp.
  intros. hyg_solv. Qed.

Lemma hygiene_leq: forall G m1 m2, (hctx G) m1 -> (hctx G) m2 ->
                               (hctx G) (leq_t m1 m2).
  intros. hyg_solv. 
Qed.
Hint Resolve hygiene_bind hygiene_leqtp hygiene_lttp: hygiene_hint.

Lemma hygiene_subseq: forall G m1 m2, (hctx G) m1 -> (hctx G) m2 ->
                                 (hctx G) (subseq m1 m2).
  intros. unfold subseq. hyg_solv. Qed.

Hint Resolve hygiene_subseq: hygiene_hint.

Lemma hygiene_store: forall G m1 m2, (hctx G) m1 -> (hctx G) m2 ->
                               (hctx G) (store m1 m2).
  intros. unfold store. unfold gettype.
  rewrite - ! subst_sh_shift. hyg_solv.
  Admitted.

Hint Resolve hygiene_store: hygiene_hint.

