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

Lemma under_op (G : @context False) : hincl (fun i => i < length G)
                         (fun j : nat => 
     (j < 0)%coq_nat \/
     (j >= 0)%coq_nat /\
     ((j - 0)%coq_nat < (length G)%coq_nat ) ).
  move => i Hi.  right. split. auto. nat_lib.
  Search (?m >= ?n)%coq_nat.
  apply not_lt. intros contra. move/ltP : contra. auto.
  replace (i - 0)%coq_nat with i. assumption. 
  Search (?i = (?i - 0)%coq_nat). exact: (minus_n_O _).
Qed.

  Lemma hygiene_app G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (app m1 m2).
    unfold hctx. rewrite ctxpred_length. unfold app. repeat constructor.
    apply (hygiene_weaken _ _ _ _ (under_op _)).
  change (j <)



Lemma hygiene_moveapp G A m v: (hctx G) m ->
                               (hctx G) v ->
                               (hctx G) (move_app A m v).
  unfold hctx. unfold move_app. rewrite ctxpred_length. move => Hm Hv.
  induction A; simpl.
  unfold hygiene. simpl.
