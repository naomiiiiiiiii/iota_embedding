Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import source subst_src rules_src help trans basic_types.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
Check context.

Lemma tr_arrow_elim: forall G a b m n p q, 
      tr G (deq m n (pi a (subst sh1 b)))
      -> tr G (deq p q a) 
      -> tr G (deq (app m p) (app n q) b).
            Admitted.

Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.
Hint Resolve nat_type. 

Lemma pw_kind: forall G,
      tr G (deq preworld preworld (kuniv nzero)). Admitted.

Lemma subseq_type: forall G w1 w2,
    tr G (oof w1 world) -> tr G (oof w2 world) ->
    tr G (oof (subseq w1 w2) (univ nzero)). Admitted.

Ltac simpsub1 :=
  unfold leq_t; unfold leqtp; unfold nattp; unfold preworld; unfold app3; unfold nzero; simpsub; simpl.

Lemma tr_weakening_append: forall (G1: context) G2 J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (G2 ++ G1) (
                       (deq (shift (size G2) J1)
                            (shift (size G2) J2)
                            (shift (size G2) t))).
 intros. induction G2.
 -  simpl. repeat rewrite - subst_sh_shift. simpsub. assumption.
 -
  suffices: (tr (substctx sh1 [::] ++ cons a (G2 ++ G1))
                (substj (under (length [::]) sh1)
                        (substj (sh (size G2)) (deq J1 J2 t)))).
  move => Hdone.
  simpl in Hdone.
  rewrite (size_ncons 1).
  rewrite - plusE. 
  repeat rewrite subst_sh_shift.
  repeat rewrite - shift_sum.
  repeat rewrite subst_sh_shift in Hdone.
  rewrite cat_cons.
 apply (Hdone False). 
 intros.
 eapply tr_weakening.
 simpl. repeat rewrite subst_sh_shift. assumption.
Qed.

Lemma store_type: forall W G,
    (tr G (oof W world)) -> tr G (oof (store W) U0).
Admitted.

Lemma bar_type: forall A G i,
    (tr G (oof A (univ i))) -> tr G (oof (laters A) (univ i)).
  Admitted.

Lemma sh_sum :
  forall m n t,
    @subst False (sh n) (subst (sh m) t) = @subst False (sh (n+m)) t.
  intros. repeat rewrite subst_sh_shift.
  rewrite shift_sum. auto. Qed.

Lemma world_pair: forall w l G, tr G (oof w preworld) ->
                           tr G (oof l nattp) ->
    tr G (oof (ppair w l) world).
intros.
    eapply tr_eqtype_convert.
    eapply tr_eqtype_symmetry.
      eapply tr_prod_sigma_equal.
    eapply tr_formation_weaken; eapply tr_kuniv_weaken.
    eapply pw_kind. eapply nat_type.
    eapply tr_sigma_intro; try assumption. rewrite subst_nat.
    apply nat_type. Qed.

  Lemma compm1_type : forall U A G,
    (tr G (oof U world)) -> (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
    tr G (oof (arrow (store U)
                         (laters (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let V := ppair v lv in
                                              prod (prod (subseq (subst (sh 2) U) V) (store V))
                                                   A
                                                    ))
                                    )
         )) U0). (*A should be substed by 2 here start here fix this in trans also*)
  move => U A G U_t A_t.
  assert ([:: hyp_tm nattp; hyp_tm preworld] ++ G=
  [:: hyp_tm nattp, hyp_tm preworld & G]) as Hseq.
  rewrite - cat1s. rewrite - catA.
  repeat rewrite cat1s. reflexivity.
assert (size [:: hyp_tm nattp; hyp_tm preworld] = 2) as Hsize. by auto. 
  assert (tr [:: hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 1) (var 0)) world)) as Hworld.
apply world_pair.
rewrite - (subst_pw (sh 2)).
    apply tr_hyp_tm. repeat constructor.
    rewrite - (subst_nat (sh 1)). 
    apply tr_hyp_tm.
    rewrite subst_nat.
    repeat constructor.
  eapply tr_arrow_formation_univ.
  apply store_type. assumption. apply bar_type.
  apply tr_exist_formation_univ.
  apply pw_kind. eapply tr_sigma_formation_univ.
  unfold nzero. simpsub. apply nat_U0.
  simpl.
    eapply tr_prod_formation_univ.
    eapply tr_prod_formation_univ. unfold nzero. simpl.
    apply subseq_type.
    rewrite - (subst_world (sh 2)).
    rewrite - Hsize. rewrite - Hseq. repeat rewrite subst_sh_shift.
apply tr_weakening_append. assumption. assumption.
    auto. unfold nzero. simpsub. apply store_type. auto.
    rewrite subst_nzero. apply A_t.
    auto. apply leq_refl. auto.
    Qed.

  Lemma trans_type_works : forall w l A G,
      (tr G (oof (ppair w l) world)) ->
      tr G (oof (trans_type w l A) U0).
    move => w l A G Du. move : w l G Du.
    induction A; intros; simpl; try apply nat_U0.
    +
  assert ([:: hyp_tm nattp; hyp_tm preworld] ++ G=
  [:: hyp_tm nattp, hyp_tm preworld & G]) as Hseq.
  rewrite - cat1s. rewrite - catA.
  repeat rewrite cat1s. reflexivity.
 assert (tr [:: hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 1) (var 0)) world)) as Hu.
     apply world_pair. 
        rewrite - (subst_pw (sh 2)).
      apply tr_hyp_tm; repeat constructor.
        rewrite - (subst_nat (sh 1)).
        apply tr_hyp_tm; repeat constructor.

        apply tr_all_formation_univ.
      apply pw_kind.
      apply tr_pi_formation_univ.
      rewrite subst_nzero. apply nat_U0.
      apply tr_arrow_formation_univ.
      repeat rewrite subst_nzero.
      apply subseq_type.
    - (*showing w, l world*)
      rewrite - (subst_world (sh 2)).
      rewrite subst_sh_shift. rewrite - Hseq.
      apply tr_weakening_append. assumption. assumption.
        apply tr_arrow_formation_univ.
        repeat rewrite subst_nzero.
        eapply IHA1; try assumption.
        eapply IHA2; try assumption.
        auto. apply leq_refl. auto.
      + simpsub. simpl. apply tr_all_formation_univ.
        unfold subst1. rewrite subst_pw.
        rewrite subst_nzero. apply pw_kind.
        apply tr_pi_formation_univ.
        repeat rewrite subst_nat.
        rewrite subst_nzero. apply nat_U0.
        apply tr_arrow_formation_univ.
        simpsub. simpl. unfold subseq. simpl.
        rewrite subst_prod.
        eapply tr_prod_formation_univ.
        (*need a lemma about leq start here*)
        rewrite
      apply world+
rewrite - (subst_pw (sh 2)).
    apply tr_hyp_tm. repeat constructor.
    rewrite - (subst_nat (sh 1)). 
    apply tr_hyp_tm.
    rewrite subst_nat.
    repeat constructor.
    
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
  move => G D e T ebar w1 l1 De Dw Dtrans.
  move : D w1 l1 ebar Dw Dtrans. induction De; intros.
  10 : {
(*Useful facts that will help us later*)
    remember (size ([:: hyp_tm nattp,
        hyp_tm preworld,
        hyp_tm nattp
        & gamma_at G w1 l1])) as sizel.
    assert (sizel = (3 + size G)%coq_nat) as Hsizel. subst.
    repeat rewrite size_cons. repeat rewrite addnA.
    rewrite size_gamma_at. auto.

    assert ([:: hyp_tm nattp; hyp_tm preworld; hyp_tm nattp] ++ (gamma_at G w1 l1) =
  [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp & (gamma_at G w1 l1) ]) as Hseq.
  rewrite - cat1s. rewrite - catA.
  repeat rewrite cat1s. reflexivity.
   assert (tr
    [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp
      & gamma_at G w1 l1 ++ D]
    (oof (ppair (var 1) (var 0)) world) ) as Hu.
   apply world_pair.
        rewrite - (subst_pw (sh 2)).
      apply tr_hyp_tm; repeat constructor.
        rewrite - (subst_nat (sh 1)).
        apply tr_hyp_tm; repeat constructor.
    (*actual proof*)
    simpl.
    eapply (tr_pi_elim _ nattp).
    inversion Dtrans; subst.
    remember (size ([:: hyp_tm nattp,
        hyp_tm preworld,
        hyp_tm nattp
        & gamma_at G w1 l1])) as sizel.
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
    apply subseq_type. (*to show subseqs
                        are the same type,
 need to show that the variables are both of type world*)

   +     rewrite shift_sum.
    apply world_pair. 
    repeat rewrite - cat_cons. rewrite - (subst_pw (sh sizel)).
    repeat rewrite - Hsizel.
    rewrite subst_sh_shift. subst.
    repeat rewrite - Hseq.
    apply tr_weakening_append; auto.
eapply split_world. apply Dw.
      rewrite - (subst_nat (sh 3)).
      apply tr_hyp_tm; repeat constructor.
      + assumption. 
        (*do a suffices somehow*)
suffices:
          tr [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp & gamma_at G w1 l1 ++ D]
    (oof
       (arrow (store (ppair (var 1) (var 0)))
          (laters
             (exist nzero preworld
                (sigma nattp
                   (let v := var 1 in
                    let lv := var 0 in
                    let V := ppair v lv in
                    prod (prod (subseq (subst (sh 2) (ppair (var 1) (var 0))) V) (store V))
                          (trans_type (var 1) (var 0) B)))))) U0).
simpsub. move => Hdone. 
eapply tr_formation_weaken. apply Hdone.
        apply compm1_type.
        assumption.
        (*when forming the type A -> B, the x: A doesnt bind
         when you're writing B
         but when forming an element of A -> B, the x: A does bind

         when forming the type A \times B, the x: A doesnt bind
         when forming a value of type A \times B, the x: A does bind*)
        simpsub.
      eapply tr_hyp_tm. constructor.
      repeat rewrite subst_nat. apply nat_type.
      (*start here*)
      apply arrow_kind_formation.
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
