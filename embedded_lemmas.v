Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src help subst_help0 subst_help
     trans basic_types derived_rules.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
(*useful properties of the embedding*)

Hint Resolve tr_fut_intro: core.

Ltac var_solv0 := try (apply tr_hyp_tm; repeat constructor).
Ltac var_solv := unfold oof; match goal with |- tr ?G' (deq (var ?n) ?n' ?T) => try
                                 rewrite - (subst_nat (sh (n.+1))); try rewrite - (subst_pw (sh (n.+1))); var_solv0 end.

(*quick facts about worlds*)

(*preworlds can indeed be impredicatively quantified over *)
Lemma pw_kind: forall {G},
    tr G (deq preworld preworld (kuniv nzero)).
  intros. apply tr_rec_kind_formation.
  apply tr_arrow_kind_formation.
  auto. apply tr_karrow_kind_formation.
  apply tr_fut_kind_formation.
  simpl. rewrite - subst_kuniv.
  apply tr_hyp_tm. repeat constructor.
  auto.
  apply tr_arrow_kind_formation. apply tr_fut_formation_univ.
  rewrite subst_nzero. apply nat_U0. auto.
  apply tr_univ_kind_formation; auto. apply zero_typed. Qed.

Lemma pw_type: forall {G},
    tr G (deqtype preworld preworld ).
  intros. apply (kind_type pw_kind). Qed.

Hint Resolve pw_kind pw_type.

(*subtypes of preworld*)
Lemma pw_type2: forall {G}, tr G (deqtype (arrow (fut nattp) (univ nzero))
                                   (arrow (fut nattp) (univ nzero))).
  intros. apply tr_arrow_formation.
  apply tr_fut_formation. auto.
  apply tr_univ_formation. auto. Qed.

Lemma pw_type1: forall {G}, tr G (deqtype
       (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
       (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
  ).
  intros. apply tr_karrow_formation.
  apply tr_fut_formation. auto. apply pw_type2. Qed.

Lemma pw_app_typed2 G u l: tr G (oof u preworld) ->
                                    tr G (oof l nattp) ->
                                    tr G (deqtype (app u l)
                                                  (app u l)).
  Admitted.

Lemma pw_app_typed1 G u l v: tr G (oof u preworld) ->
                                    tr G (oof l nattp) ->
                                    tr G (oof v (fut preworld)) ->
                                    tr G (deqtype (app (app u l) v)
                                                       (app (app u l) v)).
  Admitted.
Lemma pw_app_typed G u l v i: tr G (oof u preworld) ->
                                    tr G (oof l nattp) ->
                                    tr G (oof v (fut preworld)) ->
                                    tr G (oof i (fut nattp)) ->
                                    tr G (deqtype (app (app (app u l) v) i)
                                                  (app (app (app u l) v) i)).
  Admitted.

Lemma unfold_pw: forall G,
    tr G (deqtype preworld (arrow nattp
          (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))). Admitted.

Lemma split_world_elim2: forall W G,
    tr G (oof W world) -> tr G (oof (ppi2 W) nattp).
Admitted.

Lemma split_world_elim1: forall W G,
    tr G (oof W world) -> tr G (oof (ppi1 W) preworld).
Admitted.

Lemma world_type: forall G,
      tr G (deqtype world world). Admitted.
Hint Resolve world_type. 

    Lemma split_world1: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof w1 preworld). (*ask karl can't put a
                                                          conjunction here*)
    Admitted.

    Lemma split_world2: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof l1 nattp). (*ask karl can't put a
                                                          conjunction here*)
    Admitted.

    Lemma nth_works: forall G w n,
        tr G (oof w world) -> tr G (oof n nattp) -> tr G (oof (nth w n)
                           (karrow (fut preworld) (arrow (fut nattp) U0))).
      intros. unfold nth. apply (tr_arrow_elim _ nattp); auto.
      do 2? constructor. auto.
      constructor. auto.
      apply tr_univ_formation. auto.
      eapply tr_eqtype_convert. apply unfold_pw.
      apply split_world_elim1. assumption.
      Qed.

(*longer facts about worlds*)
Lemma subseq_U0: forall G w1 w2,
    tr G (oof w1 world) -> tr G (oof w2 world) ->
    tr G (oof (subseq w1 w2) (univ nzero)).
  intros.
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
                     =  @ subst obj s (pi (fut nattp) (univ nzero))
         ) as sub1.
  auto.
  assert (forall s, @ subst obj s (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
                     = (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
         ) as sub2.
  auto.
  assert (forall s, arrow (fut nattp) (univ nzero)
                     =  @ subst obj s (arrow (fut nattp) (univ nzero))
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
               =  @ subst obj s (arrow (fut preworld)
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
  eapply pw_type1.
  eapply tr_eqtype_convert.
  apply unfold_pw.
  eapply (tr_sigma_elim1 _ _ nattp).
  (*assert (forall s, (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
               =  @ subst obj s (arrow nattp
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


unfold subseq.
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
apply Hworldapp. 
  rewrite - {3}(subst_world (sh 5)).
  apply tr_hyp_tm. repeat constructor.
simpsub. simpl. apply Hworldapp. 
  rewrite - {3}(subst_world (sh 6)).
  apply tr_hyp_tm. repeat constructor.
  auto.
  repeat rewrite subst_nzero. apply leq_refl. auto.
assumption. assumption.
Qed.

(*simple lemmas about well typedness of embedding*)
Lemma laters_type: forall A G i,
    (tr G (oof A (univ i))) -> tr G (oof (laters A) (univ i)).
  Admitted.
Hint Resolve laters_type.

Lemma bind_type: forall G A B M0 M1,
    tr G (oof M0 (laters A)) ->
    tr G (oof M1 (arrow A (laters B))) ->
    tr G (oof (make_bind M0 M1) (laters B)). Admitted.

Lemma ret_type: forall G A M0,
    tr G (oof M0 A) ->
    tr G (oof (ret_a M0) (laters A)). Admitted.

(*repeated patterns of proofs.v*)

Lemma world_pair: forall w l G, tr G (oof w preworld) ->
                           tr G (oof l nattp) ->
    tr G (oof (ppair w l) world).
  intros. eapply tr_sigma_intro; try assumption.
  apply nat_type. Qed.

Lemma uworld10: forall G,
      (tr [:: hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 1) (var 0)) world)). intros.
                                          apply world_pair; var_solv.
Qed.

Lemma uworld21: forall G x,
      (tr [:: x, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 2) (var 1)) world)). intros.
   apply world_pair; var_solv. Qed. 

Lemma uworld32: forall G x y,
      (tr [:: x, y, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 3) (var 2)) world)). intros.
   apply world_pair; var_solv. Qed. 

  Lemma uworld43: forall G x y z,
      (tr [:: x, y, z, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 4) (var 3)) world)). intros.
   apply world_pair; var_solv. Qed. 

  Lemma uworld65: forall G x y z a b,
      (tr [:: x, y, z, a, b, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 6) (var 5)) world)). intros.
   apply world_pair; var_solv. Qed. 

  Lemma uworld76: forall G x y z a b c,
      (tr [:: x, y, z, a, b, c, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 7) (var 6)) world)). intros.
   apply world_pair; var_solv. Qed. 

Lemma uworld87: forall G x y z a b c d,
      (tr [:: x, y, z, a, b, c, d, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 8) (var 7)) world)). intros.
   apply world_pair; var_solv. Qed. 

  Lemma uworld98: forall G x y z a b c d e,
                     (tr [:: x, y, z, a, b, c, d, e, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 9) (var 8)) world)). intros.
   apply world_pair; var_solv. Qed. 

  Lemma uworld109: forall G x y z a b c d e f,
                     (tr [:: x, y, z, a, b, c, d, e, f, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 10) (var 9)) world)). intros.
   apply world_pair; var_solv. Qed. 


  Hint Resolve uworld10 uworld32 uworld21 uworld43 uworld65 uworld76 uworld87 uworld98
  uworld109.

  Lemma store_U0: forall w l G,
    (tr G (oof (ppair w l) world)) -> tr G (oof (store w l) U0).
Admitted.

  Lemma store_type: forall w l G,
    (tr G (oof (ppair w l) world)) -> tr G (deqtype (store w l) (store w l)).
Admitted.

Lemma subseq_type: forall G w1 w2,
    tr G (oof w1 world) -> tr G (oof w2 world) ->
    tr G (deqtype (subseq w1 w2) (subseq w1 w2)).
Admitted.
Hint Resolve store_type subseq_type.


Lemma tr_karrow_intro: forall G a b m n,
    tr G (deqtype a a) ->
      tr G (deqtype b b)
      -> tr (cons (hyp_tm a) G) (deq m n (subst sh1 b))
      -> tr G (deq (lam m) (lam n) (karrow a b) ).
intros. eapply tr_eqtype_convert.
apply tr_arrow_karrow_equal; try assumption.
eapply tr_arrow_intro; try assumption. Qed.

Lemma pw_type3: forall {G}, tr G (deqtype (fut preworld)  (fut preworld)).
  Admitted.

Hint Resolve pw_type3 pw_type2 pw_type1: core.
Hint Resolve tr_fut_formation tr_fut_formation_univ: core.

(*an expression in one world can be moved to any accessible world
 should move this to embedded lemmas probably*)
 Lemma move_works: forall G w1 l1 w2 l2 T,
     tr G (oof (ppair w1 l1) world) ->
     tr G (oof (ppair w2 l2) world) ->
     tr G (oof (move T) (arrow (subseq (ppair w1 l1) (ppair w2 l2))
                               (arrow
                                  (trans_type w1 l1 T)
                                  (trans_type w2 l2 T)
                               )
                        )
          ).
 Admitted.


