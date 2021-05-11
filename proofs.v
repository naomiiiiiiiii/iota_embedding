Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
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

Lemma tr_weakening_append: forall (G1: context) G2 J,
      tr G1 J ->
      tr (G2 ++ G1) (substj (sh (size G2)) J).
 intros. induction G2.
 -  simpl. simpsub. assumption.
  - destruct J as [J1 J2]; subst.
  suffices: (tr (substctx sh1 [::] ++ cons a (G2 ++ G1))
                (substj (under (length [::]) sh1)
                        (substj (sh (size G2)) (deq J1 J2 t)))).
  move => Hdone.
  simpl in Hdone.
  rewrite (size_ncons 1).
  rewrite - plusE. 
  unfold substj.
  repeat rewrite subst_sh_shift.
  repeat rewrite - shift_sum.
  repeat rewrite subst_sh_shift in Hdone.
  rewrite cat_cons.
 apply (Hdone False). 
 intros.
 eapply tr_weakening.
 auto.
Qed.

Lemma split_world: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof w1 preworld). (*ask karl can't put a
                                                          conjunction here*)
Admitted.

Lemma size_cons: forall(T: Type) (a: T) (L: seq T),
    size (a:: L) = 1 + (size L). Admitted.
 
Lemma size_gamma_at: forall G w l,
    size (gamma_at G w l) = size G. Admitted.

  Theorem one: forall G D e T ebar w1 l1,
    of_m G e T -> tr D (oof (ppair w1 l1) world) ->
    trans e ebar -> 
         tr ((gamma_at G w1 l1) ++ D) (oof (app ebar (shift (size G) l1))
                                                   (trans_type
                                                      (shift (size G)
                                                             w1) (shift (size G)
                                                             l1)
                                                    T )).
  move => G D e T ebar w1 l1 Ds Dtrans.
  move : w1 l1 Dtrans. induction Ds; intros.
  10 : {
    simpl.
    eapply (tr_pi_elim _ nattp).
    inversion H; subst.
    eapply tr_pi_intro. eapply nat_type.
    apply tr_all_intro.
    apply pw_kind.
    rewrite subst_lam.
    simpsub. simpl.
    apply tr_pi_intro.  apply nat_type.
    eapply tr_eqtype_convert.
    eapply tr_eqtype_symmetry.
    eapply tr_arrow_pi_equal.
    eapply tr_formation_weaken.
    apply subseq_type.
    unfold world.
    eapply tr_eqtype_convert.
    eapply tr_eqtype_symmetry.
      eapply tr_prod_sigma_equal.
    eapply tr_formation_weaken; eapply tr_kuniv_weaken.
    eapply pw_kind. eapply nat_type.
    eapply tr_sigma_intro.
    simpl. rewrite shift_sum.
    remember (size ([:: hyp_tm nattp,
        hyp_tm preworld,
        hyp_tm nattp
      & gamma_at G w1 l1])) as sizel.
    suffices: sizel = (3 + size G)%coq_nat.
    move => Heq. repeat rewrite - Heq.
    suffices: 
  (tr
    [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp
      & gamma_at G w1 l1 ++ D]
    (substj (sh sizel) (deq w1 w1 preworld)) ).
    move => Hdone. unfold substj in Hdone. simpl in Hdone. repeat rewrite subst_pw subst_sh_shift in Hdone.  assumption.
    repeat rewrite - cat_cons. subst.
    apply tr_weakening_append. eapply split_world. apply Dtrans.
    subst. repeat rewrite size_cons. rewrite addnA.
    rewrite size_gamma_at. auto.
    (*w1 l1 have gone under inders, need to shift them
     should do w1 as a variable beign subbed in like l1 cuz then
     the subs get taken care of*)
    rewrite subseq_subst.
    simpsub.
    induction G. simpsub.
    repeat rewrite compose_sh_dot.
    auto.
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
