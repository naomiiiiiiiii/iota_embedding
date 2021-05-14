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

Lemma kind_type: forall G K i,
    tr G (deq K K (kuniv i)) -> tr G (deqtype K K).
  Admitted.

Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.
Hint Resolve nat_U0. 

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.
Hint Resolve nat_type. 

Lemma world_type: forall G,
      tr G (deqtype world world). Admitted.
Hint Resolve world_type. 

Lemma pw_type2: forall G, tr G (deqtype (arrow (fut nattp) (univ nzero))
       (arrow (fut nattp) (univ nzero))). Admitted.

Lemma pw_kind1: forall G, tr G (deq
       (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
       (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
       (kuniv nzero) ).
Admitted.


Lemma pw_kind: forall G,
      tr G (deq preworld preworld (kuniv nzero)). Admitted.

Lemma pw_type: forall G,
      tr G (deqtype preworld preworld ). Admitted.

Lemma unfold_pw: forall G,
    tr G (deqtype preworld (arrow nattp
          (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))). Admitted.

Lemma split_world_elim2: forall W G,
    tr G (oof W world) -> tr G (oof (ppi2 W) nattp).
Admitted.

    Lemma split_world: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof w1 preworld). (*ask karl can't put a
                                                          conjunction here*)
    Admitted.


Lemma subseq_type: forall G w1 w2,
    tr G (oof w1 world) -> tr G (oof w2 world) ->
    tr G (oof (subseq w1 w2) (univ nzero)).
  intros. unfold subseq.
  rewrite - (subst_nzero (dot w2 id)).
  rewrite - subst_univ.
  eapply (tr_pi_elim _ world).
  rewrite - (subst_nzero (under 1 (dot w1 id)) ).
  rewrite - subst_univ.
  rewrite - (subst_world (dot w1 id)).
  rewrite - subst_pi.
  eapply (tr_pi_elim _ world).
  apply tr_pi_intro. apply world_type.
  apply tr_pi_intro. apply world_type.
  eapply tr_prod_formation_univ.
  eapply leq_type.
  eapply split_world_elim2.
  rewrite - (subst_world (sh 1)).
  eapply tr_hyp_tm. constructor.
  eapply split_world_elim2.
  rewrite - (subst_world (sh 2)).
  eapply tr_hyp_tm. repeat constructor.
  eapply tr_all_formation_univ.
  eapply tr_fut_kind_formation.
  apply pw_kind.
  apply zero_typed.
  eapply tr_pi_formation_univ.
  eapply tr_fut_formation_univ.
  apply nat_U0.
  repeat rewrite subst_nzero. apply zero_typed.
  repeat rewrite subst_nzero.
  eapply tr_pi_formation_univ. apply nat_U0.
  repeat rewrite subst_nzero. eapply tr_pi_formation_univ.
  apply leq_type.
  rewrite - (subst_nat (sh 1)).
  eapply tr_hyp_tm. repeat constructor.
  rewrite subst_ppi2. simpsub. simpl.
  eapply split_world_elim2.
  rewrite - (subst_world (sh 4)).
  eapply tr_hyp_tm. repeat constructor.
  repeat rewrite subst_nzero.
  eapply tr_eqtype_formation_univ.
  assert (forall V,
tr [:: hyp_tm
          (leq_t (var 0)
             (subst (sh 3) (ppi2 (var 0)))),
        hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld), hyp_tm world,
        hyp_tm world
        & G] (oof V world) ->

  tr
    [:: hyp_tm
          (leq_t (var 0)
             (subst (sh 3) (ppi2 (var 0)))),
        hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld), hyp_tm world,
        hyp_tm world
      & G]
    (oof
       (app3 (ppi1 V) 
          (var 1) (var 3) (var 2)) 
     (univ nzero))
         ) as Hworldapp.
  intros V Hvw.

  rewrite - (subst_nzero (dot (var 2) id)). (*start of the application proof,
                                              make this general for any
                                              (var 0) which gamma says is world*)
  rewrite - subst_univ.
  eapply (tr_pi_elim _ (fut nattp) ).
   simpsub. simpl.
  assert (forall s, pi (fut nattp) (univ nzero)
                     =  @subst False s (pi (fut nattp) (univ nzero))
         ) as sub1.
  auto.
  assert (forall s, @subst False s (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
                     = (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
         ) as sub2.
  auto.
  assert (forall s, arrow (fut nattp) (univ nzero)
                     =  @subst False s (arrow (fut nattp) (univ nzero))
         ) as sub3.
  auto.
  eapply tr_eqtype_convert.
  rewrite - (subst_U0 (sh 1)).
  eapply tr_arrow_pi_equal.
  eapply tr_fut_formation. eapply nat_type.
  eapply tr_univ_formation.
  apply zero_typed.
  rewrite (sub3 (dot (var 3) id)).
  eapply (tr_pi_elim _ (fut preworld)).
  eapply tr_eqtype_convert.
  rewrite (sub3 sh1).
  eapply tr_arrow_pi_equal.
  eapply tr_fut_formation. eapply pw_type.
  eapply pw_type2.
  assert (forall s, (arrow (fut preworld)
          (arrow (fut nattp) (univ nzero)))
               =  @subst False s (arrow (fut preworld)
          (arrow (fut nattp) (univ nzero)))
)
    as sub4.
  auto.
  eapply tr_eqtype_convert.
  eapply tr_eqtype_symmetry.
  eapply tr_arrow_karrow_equal.
  eapply tr_fut_formation. eapply pw_type.
  eapply pw_type2.
  rewrite - (sub2 (dot (var 1) id)).
  eapply (tr_pi_elim _ nattp).
  eapply tr_eqtype_convert.
  rewrite - (sub2 (sh1)).
  eapply tr_arrow_pi_equal.
  apply nat_type.
  eapply (kind_type _ _ _ (pw_kind1 _) ).
  eapply tr_eqtype_convert.
  apply unfold_pw.
  eapply (tr_sigma_elim1 _ _ nattp).
  (*assert (forall s, (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
               =  @subst False s (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
)
    as sub5.
  intros. auto.*)
  apply Hvw.
  (*assert (sigma preworld nattp = world) by auto. rewrite H.
  rewrite - {3}(subst_world (sh 5)).
  apply tr_hyp_tm. repeat constructor.*)
  rewrite - {3}(subst_nat (sh 2)).
  apply tr_hyp_tm. repeat constructor.
  rewrite - {2}(subst_pw (sh 4)).
  rewrite - subst_fut.
  apply tr_hyp_tm. repeat constructor.
  rewrite - {2}(subst_nat (sh 3)).
  rewrite - subst_fut.
  apply tr_hyp_tm. repeat constructor.
  simpsub. simpl.
apply Hworldapp. 
  rewrite - {3}(subst_world (sh 5)).
  apply tr_hyp_tm. repeat constructor.





  apply tr_hyp_tm. repeat constructor.
  apply tr_arrow_formation. apply nat_type.
  eapply (kind_type _ _ _ (pw_kind1 _) ).
  apply nat_type.
  eapply (kind_type _ _ _ (pw_kind _) ).
  repeat rewrite - (subst_world (sh 5)).

  eapply tr_eq
  rewrite (sub4 (dot (var 1) id)).
  eapply (tr_arrow_elim _ nattp).
  .
  eapply tr_arrow_formation.
  eapply tr_fut_formation. eapply nat_type.
  eapply tr_univ_formation.
  apply zero_typed.




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
   (* eapply tr_eqtype_convert.
    eapply tr_eqtype_symmetry.
      eapply tr_prod_sigma_equal.*)
    (*eapply tr_formation_weaken; eapply tr_kuniv_weaken.
    eapply pw_kind. eapply nat_type.*)
    eapply tr_sigma_intro; try assumption.     apply nat_type. Qed.

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

  Lemma hseq2: forall (T: Type) (x y: T)
                  (L: seq T), [:: x; y] ++ L=
                 [:: x, y & L].
intros.
  rewrite - cat1s. rewrite - catA.
  repeat rewrite cat1s. reflexivity. Qed.

  Lemma uworld: forall G,
      (tr [:: hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 1) (var 0)) world)). intros.
     apply world_pair. 
        rewrite - (subst_pw (sh 2)).
      apply tr_hyp_tm; repeat constructor.
        rewrite - (subst_nat (sh 1)).
        apply tr_hyp_tm; repeat constructor. Admitted.

  Hint Resolve uworld.

                        

  Lemma trans_type_works : forall w l A G,
      (tr G (oof (ppair w l) world)) ->
      tr G (oof (trans_type w l A) U0).
    move => w l A G Du.
  move : w l G Du.
    induction A; intros; simpl; try apply nat_U0.
    + (*arrow*)
        apply tr_all_formation_univ.
      apply pw_kind.
      apply tr_pi_formation_univ.
      rewrite subst_nzero. apply nat_U0.
      apply tr_arrow_formation_univ.
      repeat rewrite subst_nzero.
      apply subseq_type.
    - (*showing w, l world*)
      rewrite - (subst_world (sh 2)).
      rewrite subst_sh_shift. rewrite - hseq2.
      apply tr_weakening_append. assumption.
      apply uworld.
        apply tr_arrow_formation_univ; try auto.
        repeat rewrite subst_nzero.
        eapply IHA1; try assumption; try auto. 
        eapply IHA2; try assumption; try auto.
        auto. apply leq_refl. auto.
        (*comp type*)
      + unfold subst1. rewrite subst_all.
        apply tr_all_formation_univ.
        rewrite subst_pw.
        rewrite subst_nzero. apply pw_kind.
        rewrite subst_pi.
        apply tr_pi_formation_univ.
        repeat rewrite subst_nat.
        rewrite subst_nzero. apply nat_U0.
        rewrite subst_arrow.
        apply tr_arrow_formation_univ.
        (*showing the subseq part is a type,
         problematic coz of substitutions*)
        simpsub. simpl.
        rewrite subseq_subst. simpsub.
        repeat rewrite subst_nat.
        rewrite subst_nzero.



        unfold subseq. simpl.
        rewrite subst_prod.
        eapply tr_prod_formation_univ.
        (*need a lemma about leq start here*)
        rewrite subst_leq.
        apply leq_type.
    - simpsub.
      rewrite - subst_sh_shift. simpsub.
      rewrite - (subst_nat (dot
                              (ppi1
          (ppair (subst (sh 2) w)
             (subst (sh 2) l))) 
                id )).
      eapply (tr_sigma_elim2 _ preworld).
      rewrite - (subst_pw (sh 2)).
      simpsub.
      rewrite - hseq2.
      rewrite - (subst_nat (under 1 (sh 2) )).
      rewrite - (subst_sigma False (sh 2) ).
      repeat rewrite subst_nat. rewrite subst_pw.
      rewrite - (subst_ppair).
      repeat rewrite subst_sh_shift.
      apply tr_weakening_append. apply Du.
      simpsub. rewrite subst_nat.
      unfold subst1. rewrite subst_pw.
      rewrite - (subst_nat (dot
                              (ppi1
          (ppair (var 1)
             (var 0))) 
                id  )).
      eapply (tr_sigma_elim2 _ preworld).
      repeat rewrite subst_nat.
      apply uworld.
  + (*ref type*)
    rewrite subst_pi.
    apply tr_pi_formation_univ.
    repeat rewrite subst_nat.
    repeat rewrite subst_nzero.
    apply nat_U0.
    rewrite subst_pi. simpsub. simpl.
    apply tr_pi_formation_univ.
    repeat rewrite subst_nat.
    repeat rewrite subst_nzero.
    apply nat_U0.
    repeat rewrite subst_nzero.
    apply tr_all_formation_univ.
    simpsub.
    repeat rewrite subst_nat. unfold subst1. repeat rewrite subst_pw. rewrite subst_leq. simpsub.
    rewrite - subst_sh_shift. simpsub. rewrite subst_nzero.


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
