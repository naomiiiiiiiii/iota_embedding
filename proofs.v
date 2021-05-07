From Coq.Lists Require Import List.
Require Import ssreflect.
From istari Require Import source subst_src rules_src help trans.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
Check context.

Theorem one: forall G D e T ebar w1 l1,
    of_m G e T -> tr D (oof (ppair w1 l1) world) ->
    trans e ebar -> 
         tr ((gamma_at G (ppair w1 l1)) ++ D) (oof (app ebar (subst (sh (length G)) l1))
                                                   (trans_type (ppair w1 l1) T) ).
  move => G D e T ebar w1 l1 Ds Dtrans.
  move : w1 l1 Dtrans. induction Ds; intros.
  10 : {
    inversion H; subst. simpl.
    eapply tr_compute; try (
      apply Relation.star_one; left;
      eapply reduce_app_beta; try apply reduce_id).
    4 : {
      unfold equiv.
      eapply Relation.star_refl.
    }
    4 : { unfold subst1. simpl.
      unfold equiv.
    }

  }
