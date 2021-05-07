Require Import ssreflect.
From mathcomp Require Import ssreflect.seq.
From istari Require Import source subst_src rules_src help trans.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
Check context.

Lemma tr_arrow_elim: forall G a b m n p q, 
      tr G (deq m n (pi a (subst sh1 b)))
      -> tr G (deq p q a) 
      -> tr G (deq (app m p) (app n q) b).
            Admitted.

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.

Lemma pw_kind: forall G,
      tr G (deq preworld preworld (kuniv nzero)). Admitted.

Lemma subseq_type: forall G w1 w2,
    tr G (oof w1 world) -> tr G (oof w2 world) ->
    tr G (oof (subseq w1 w2) (univ nzero)). Admitted.

Ltac simpsub1 :=
  unfold leq_t; unfold leqtp; unfold nattp; unfold preworld; unfold app3; unfold nzero; simpsub; simpl.

Lemma tr_weakening_append: forall G1 G2 J,
      tr G1 J ->
      tr (G2 ++ G1) (substj (sh (length G2)) J).
  intros. induction G2.
  simpl. simpsub. assumption.
  rewrite - app_comm_cons.
  rewrite - (app_nil_l (a:: G2 ++ G1)).
  suffices: (substctx sh1 nil = nil).
  move => Heq.
  rewrite - (Heq False).
  
  apply (tr_weakening (G2 ++ G1)).

Theorem one: forall G D e T ebar w1 l1,
    of_m G e T -> tr D (oof (ppair w1 l1) world) ->
    trans e ebar -> 
         tr ((gamma_at G (ppair w1 l1)) ++ D) (oof (app ebar (subst (sh (length G)) l1))
                                                   (trans_type
                                                      (subst (sh (length G))
                                                             (ppair w1 l1)) T) ).
  move => G D e T ebar w1 l1 Ds Dtrans.
  move : w1 l1 Dtrans. induction Ds; intros.
  10 : {
    inversion H; subst.
    eapply tr_arrow_elim.
    eapply tr_pi_intro. eapply nat_type.
    simpl. auto. simpsub.
    apply tr_all_intro.
    apply pw_kind.
    auto. simpsub. simpl.
    apply tr_pi_intro. simpsub. simpl.
    unfold nattp. simpsub. apply nat_type.
    eapply tr_eqtype_convert.
    eapply tr_eqtype_symmetry.
    eapply tr_arrow_pi_equal. rewrite subseq_subst.
    eapply tr_formation_weaken.
    apply subseq_type.
    simpsub.
    induction G. simpsub.
    repeat rewrite compose_sh_dot.
    apply (tr_weakening D).
    apply tr_hyp_tm.
    try prove_subst.
    repeat simpl.
    Opaque subst. Opaque sh1.
    auto.
    simpsub.
    simpl.
    eapply tr_pi_intro.
    (*eapply tr_compute; try (
      apply Relation.star_one; left;
      eapply reduce_app_beta; try apply reduce_id).
    4 : {
      unfold equiv.
      eapply Relation.star_refl.
    }
    4 : { unfold subst1. simpl.
      unfold equiv.
    }*)

  }
