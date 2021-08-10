Require Import Program.Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined.

Definition hctx G := @hygiene False (@ctxpred False G).

Transparent hctx.

Require Import lib.

Lemma under_op (G : @context False) : hincl (fun i => (i < length G)%coq_nat)
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

Lemma under_binder (G : @context False) x : hincl (fun i => (i < length (x :: G))%coq_nat)
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



Lemma hygiene_lam G m0 m: 
                               (hctx ((hyp_tm m0) :: G)) m ->
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

Lemma hygiene_moveapp G A m v: (hctx G) m ->
                               (hctx G) v ->
                               (hctx G) (move_app A m v).
  unfold hctx. unfold move_app. rewrite ctxpred_length. move => Hm Hv.
  induction A; simpl.
  unfold hygiene. simpl.
