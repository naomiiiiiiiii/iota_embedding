Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src help subst_help0 subst_help
     trans basic_types derived_rules.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
(*useful properties of the embedding*)

Hint Resolve tr_fut_intro: core.


Ltac var_solv := unfold oof; match goal with |- tr ?G' (deq (var ?n) ?n' ?T) =>
                                 try rewrite - (subst_nat (sh (n.+1))); try rewrite - (subst_pw (sh (n.+1)));
                                              try rewrite - ! subst_fut;
var_solv0 end.

(*
Ltac weak_prep := match goal with |- tr ?G (deq (subst (sh ?n) ?M) ?M' ?T) =>
                                  change T with (@subst obj (sh n) T)

                                       [:: hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld)
      & G] (oof (subst (sh 3) U1) world) *)
(*quick facts about worlds*)

Hint Rewrite <- sh_Gamma_at subst_sh_shift subst_consb subst_U0 subst_ret subst_ret_a subst_subseq subst_leq subst_leq
     subst_lttp subst_lt subst_nzero subst_nat subst_world subst_pw subst_world
     subst_nth subst_laters subst_picomp1 subst_picomp2 subst_picomp4
     subst_picomp3 subst_make_subseq subst_theta  subst_ltb subst_univ subst_cty subst_con subst_karrow subst_arrow subst_pi subst_clam subst_capp subst_ctlam subst_ctapp subst_lam subst_app subst_fut subst_cnext subst_cprev subst_next subst_prev subst_rec subst_equal subst_triv subst_eqtype subst_subtype subst_kuniv subst_all subst_exist subst_voidtp subst_unittp subst_cunit subst_booltp subst_btrue subst_bfalse subst_bite subst_prod subst_sigma subst_cpair subst_cpi1 subst_cpi2 subst_ppair subst_ppi1 subst_ppi2 subst_set subst_quotient subst_guard subst_wt subst_ext : inv_subst.

Ltac inv_subst :=
autounfold with subst1; autorewrite with inv_subst.
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
Lemma pw_app_typed G u u' l l' v v' i i': tr G (deq u u' preworld) ->
                                    tr G (deq l l' nattp) ->
                                    tr G (deq v v' (fut preworld)) ->
                                    tr G (deq i i' (fut nattp)) ->
                                    tr G (deqtype (app (app (app u l) v) i)
                                                  (app (app (app u' l') v') i')).
(* eapply tr_formation_weaken. unfold app3.
      apply pw_app_typed.
      eapply (tr_arrow_elim _ (fut nattp)); auto.
    apply tr_univ_formation. apply zero_typed.
    eapply (tr_karrow_elim _ (fut preworld)).
    constructor. auto.
    apply pw_type2.
    apply (tr_arrow_elim _ nattp); auto.
    apply (tr_eqtype_convert _#3 preworld ). apply unfold_pw.
    apply split_world_elim1.
    change world with (@subst obj (sh 3) world).
    rewrite ! subst_sh_shift. apply tr_weakening_append3.
    assumption. var_solv'. change (fut preworld) with
                               (@subst obj (sh 3) (fut preworld)).
    var_solv'. change (fut nattp) with (@subst obj (sh 2) (fut nattp)). var_solv'.
 *) Admitted.

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

Lemma world_pair: forall w l G, tr G (oof w preworld) ->
                           tr G (oof l nattp) ->
    tr G (oof (ppair w l) world).
  intros. eapply tr_sigma_intro; try assumption.
  apply nat_type. Qed.

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

    Lemma subseq_U01: forall G w1 l1 w2, tr G (oof w1 preworld) ->
                                    tr G (oof l1 nattp) ->
                                       tr G (oof w2 preworld) ->
                                   tr (hyp_tm (fut preworld) :: G) (oof
       (pi (fut nattp)
          (pi nattp
             (arrow
                (leq_t (var 0) (subst (sh 3) l1))
                (eqtype
                   (app
                      (app
                         (app (subst (sh 3) w1)
                            (var 0)) (var 2)) 
                      (var 1))
                   (app3  (subst (sh 3) w2)
                      (var 0) (var 2) 
                      (var 1)))))) U0).
intros.
  assert (forall v,
tr 
    [:: 
        hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld)
      & G]
(oof v preworld) ->

  tr
    [:: 
        hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld)
      & G]
    (oof
       (app3 v
          (var 0) (var 2) (var 1)) 
     (univ nzero))
         ) as Hworldapp.
  { intros v Hvw.
  rewrite - (subst_nzero (dot (var 1) id)). (*start of the application proof,
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
  rewrite (sub3 (dot (var 2) id)).
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
  rewrite - (sub2 (dot (var 0) id)).
  eapply (tr_pi_elim _ nattp).
  eapply tr_eqtype_convert.
  rewrite - (sub2 (sh1)).
  eapply tr_arrow_pi_equal.
  apply nat_type.
  eapply pw_type1.
  eapply tr_eqtype_convert.
  apply unfold_pw. assumption.
  (*assert (forall s, (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
               =  @ subst obj s (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
)
    as sub5.
  intros. auto.*)
  (*assert (sigma preworld nattp = world) by auto. rewrite H.
  rewrite - {3}(subst_world (sh 5)).
  apply tr_hyp_tm. repeat constructor.*)
  var_solv.
  rewrite - {2}(subst_pw (sh 3)).
  rewrite - subst_fut.
  apply tr_hyp_tm. repeat constructor.
  rewrite - {2}(subst_nat (sh 2)).
  rewrite - subst_fut.
  apply tr_hyp_tm. repeat constructor.
   }
  eapply tr_pi_formation_univ.
  eapply tr_fut_formation_univ.
  apply nat_U0.
  repeat rewrite subst_nzero. apply zero_typed.
  repeat rewrite subst_nzero.
  eapply tr_pi_formation_univ. apply nat_U0.
  repeat rewrite subst_nzero. eapply tr_arrow_formation_univ.
 apply leq_type; try var_solv'. 
 rewrite - (subst_nat (sh 3)) ! subst_sh_shift; apply tr_weakening_append3.
 assumption.
  eapply tr_eqtype_formation_univ; apply Hworldapp;
  rewrite - (subst_pw (sh 3)) ! subst_sh_shift; apply tr_weakening_append3; try assumption.
Qed.

(*longer facts about worlds*)
Lemma subseq_U0: forall G w1 l1 w2 l2,
tr G (oof w1 preworld) ->
                                    tr G (oof l1 nattp) ->
                                    tr G (oof w2 preworld) ->
                                    tr G (oof l2 nattp) ->
    tr G (oof (subseq w1 l1 w2 l2) (univ nzero)).
  intros.
unfold subseq.
 (* rewrite - (subst_nzero (dot w2 id)).
  rewrite - subst_univ.
 eapply (tr_pi_elim _ world).
  rewrite - (subst_nzero (under 1 (dot w1 id)) ).
  rewrite - subst_univ.
  rewrite - (subst_world (dot w1 id)).
  rewrite - subst_pi.
  eapply (tr_pi_elim _ world).
  apply tr_pi_intro. apply world_type.
  apply tr_pi_intro. apply world_type.  simpsub_bigs.*)
  eapply tr_prod_formation_univ.
  eapply leq_type; try assumption. 
  eapply tr_all_formation_univ.
  eapply tr_fut_kind_formation.
  apply pw_kind.
  apply zero_typed. eapply subseq_U01; try assumption; auto.
  apply zero_typed. apply leq_refl; auto.
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


(*repeated patterns of proofs.v*)


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

Lemma store_works: forall l1 G u1 u2 l2 s1 m1 i,
      tr G (oof u1 preworld) ->
      tr G (oof u2 preworld) ->
      tr G (oof l1 nattp) ->
      tr G (oof l2 nattp) ->
      tr G (oof s1 (store u1 l1)) ->
      tr G (oof m1 (subseq u1 l1 u2 l2)) ->
      tr G (oof i nattp) ->
      tr G (oof (app (app (app s1 l2) m1) i)
               (app (app (app u1 i) (next u2)) (next l2))
           ).
    Admitted.


Lemma subseq_type: forall G w1 l1 w2 l2,
    tr G (oof (ppair w1 l1) world) -> tr G (oof (ppair w2 l1) world) ->
    tr G (deqtype (subseq w1 l1 w2 l2) (subseq w1 l1 w2 l2)).
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

 Lemma move_works: forall G w1 l1 w2 l2 T,
     tr G (oof (ppair w1 l1) world) ->
     tr G (oof (ppair w2 l2) world) ->
     tr G (oof (move T) (arrow (subseq w1 l1 w2 l2)
                               (arrow
                                  (trans_type w1 l1 T)
                                  (trans_type w2 l2 T)
                               )
                        )
          ).
 Admitted.


Lemma subseq_refl: forall ( u l: term obj) (G: context),
     tr G (oof u preworld) ->
     tr G (oof l nattp) 
                         ->tr G (oof make_subseq 
                                    (subseq u l u l)).
  intros. unfold subseq. unfold make_subseq.
  apply tr_prod_intro.
  { apply leq_refl.
  assumption. }
 { apply tr_all_intro; auto.
  constructor. apply pw_kind. auto.
  simpsub_big.
  apply tr_pi_intro. constructor. auto.
    apply tr_pi_intro; auto.
  suffices : (tr
    [:: hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld)
      & G]
    (deqtype
       (app3 (subst (sh 3) u)
          (var 0) (var 2) (var 1))
       (app3 (subst (sh 3) u)
             (var 0) (var 2) (var 1)))).
  intros Hdeq.
    apply tr_arrow_intro.
    { weaken leq_type. var_solv'.
    change nattp with (@subst obj (sh 3) nattp).
    rewrite ! subst_sh_shift. apply tr_weakening_append3. assumption. }
    { eapply tr_eqtype_formation; assumption. }
    { change triv with (@subst obj sh1 triv). rewrite ! subst_sh_shift.
    apply tr_weakening_append1. rewrite - ! subst_sh_shift. assumption. }
    {
     Ltac subseq_pwapp n := (apply pw_app_typed; [
    change preworld with (@subst obj (sh n) preworld);
    rewrite ! subst_sh_shift; try apply tr_weakening_append3;
    try apply tr_weakening_append4;
    assumption | var_solv' |
    change (fut preworld) with
                               (@subst obj (sh n) (fut preworld));
    var_solv' | change (fut nattp) with (@subst obj (sh (n- 1)) (fut nattp)); var_solv']).
     subseq_pwapp 3.
 } }
Qed.


(*will have to induct on n1 here
 and lemmas for how leq_t computes*)
(*start here*)
Lemma leq_trans_app n2 G n1 n3 t1 t2:
  tr G (oof n1 nattp) ->
  tr G (oof n2 nattp) ->
  tr G (oof n3 nattp) ->
  tr G (oof t1 (leq_t n1 n2)) ->
  tr G (oof t2 (leq_t n2 n3)) ->
  tr G (oof (leq_trans_fn_app n1 n2 n3
                          t1 t2)
 (leq_t n1 n3)).
  intros. unfold leq_t. unfold leq_trans_fn_app.
  eapply (tr_arrow_elim _ (leq_t n2 n3)); try weaken leq_type; try assumption.
  eapply (tr_arrow_elim _ (leq_t n1 n2)); try apply tr_arrow_formation;
    try weaken leq_type; try assumption.
  match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
      (@subst1 obj n3
       (arrow (leq_t (subst sh1 n1) (subst sh1 n2))
          (arrow (leq_t (subst sh1 n2) (var 0))
                 (app (app leqtp (subst sh1 n1)) (var 0))))) end.
  2:{ simpsub_bigs. auto. } apply (tr_pi_elim _ nattp); try assumption.
  match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
      (@subst1 obj n2
       (pi nattp (arrow (leq_t (subst (sh 2) n1) (var 1))
          (arrow (leq_t (var 1) (var 0))
                 (app (app leqtp (subst (sh 2) n1)) (var 0)))))) end.
  2:{ simpsub_bigs. auto. } apply (tr_pi_elim _ nattp); try assumption.
  match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
      (@subst1 obj n1
(pi nattp (pi nattp (arrow (leq_t (var 2) (var 1))
          (arrow (leq_t (var 1) (var 0))
                 (app (app leqtp (var 2)) (var 0))))))) end.
  2:{ simpsub_bigs. auto. } apply (tr_pi_elim _ nattp); try assumption.
  apply leq_trans_help. Qed.

Lemma subseq_trans u2 M M' u1 l1 l2 u3 l3 G:
  tr G (oof u1 preworld) ->
  tr G (oof l1 nattp) ->
  tr G (oof u2 preworld) ->
  tr G (oof l2 nattp) ->
  tr G (oof u3 preworld) ->
  tr G (oof l3 nattp) ->
                         tr G (oof M (subseq u2 l2  u3 l3))
                         -> tr G (oof M' (subseq u1 l1 u2 l2))
                         ->tr G (oof (make_subseq_trans
                                       l1 l2 l3 M' M)
                                    (subseq u1 l1 u3 l3)).
  intros Hu1 Hl1 Hu2 Hl2 Hu3 Hl3 Hsub2 Hsub1. unfold subseq. 
  apply tr_prod_intro.
  {
    
    eapply leq_trans_app; try assumption; 
    eapply tr_prod_elim1;
      [apply Hsub1 | apply Hsub2].
  }
  {
    apply tr_all_intro; auto. constructor. auto. apply zero_typed.
    simpsub_bigs. repeat apply tr_pi_intro; auto. apply tr_arrow_intro.
    - weaken leq_type. var_solv'. 
      change nattp with (@subst obj (sh 3) nattp). rewrite ! subst_sh_shift.
      apply tr_weakening_append3.  assumption.
    - apply tr_eqtype_formation; subseq_pwapp 3.
    - unfold app3. simpsub_bigs. apply (tr_eqtype_transitivity _ _
          (app3
              (subst (sh 4) u2)
             (var 1) (var 3) 
             (var 2))
            ).
      { unfold subseq in Hsub1.
        eapply (deqtype_intro _#3
                             (app3 (shift 4 (ppi2 M')) (var 2) (var 1) (var 0))
               ).
        apply (tr_arrow_elim _
                                 (leq_t (var 1)  (subst (sh 4) l1))).
     { weaken leq_type.  var_solv'. 
      change nattp with (@subst obj (sh 4) nattp). rewrite ! subst_sh_shift.
      apply tr_weakening_append4.  assumption. }
     {apply tr_eqtype_formation; subseq_pwapp 4. }
     { match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 1)
                                    (arrow
          (leq_t (var 0) (subst (sh 5) l1))
          (eqtype
             (app
                (app
                   (app (subst (sh 5) u1)
                      (var 0)) (var 4)) 
                (var 3))
             (app3  (subst (sh 5) u2)
                   (var 0) (var 4) (var 3))))) end.
       2:{
         unfold app3. simpsub_bigs. auto.
       }
       eapply (tr_pi_elim _ nattp).
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 2)
       (pi nattp
          (arrow
             (leq_t (var 0) (subst (sh 6) l1))
             (eqtype
                (app
                   (app
                      (app (subst (sh 6) u1)
                         (var 0)) 
                      (var 5)) (var 1))
                (app3 (subst (sh 6) u2)
                   (var 0) (var 5) 
                   (var 1)))))) end .
       2:{ unfold app3. simpsub_bigs. auto. }
       eapply (tr_pi_elim _ (fut nattp)).
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 3)
       (pi (fut nattp)
          (pi nattp
             (arrow
                (leq_t (var 0) (subst (sh 7) l1))
                (eqtype
                   (app
                      (app
                         (app (subst (sh 7) u1)
                            (var 0)) 
                         (var 2)) (var 1))
                   (app3 (subst (sh 7) u2)
                      (var 0) (var 2) 
                      (var 1))))))) end.
       2:{ unfold app3. simpsub_bigs. auto. }
       apply (tr_all_elim _ nzero (fut preworld)); auto. 
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
           (shift 4
      (all nzero (fut preworld) (pi (fut nattp)
         (pi nattp
            (arrow
               (leq_t (var 0)
                  (subst (sh 3) l1))
               (eqtype
                  (app
                     (app
                        (app
                              (subst (sh 3) u1)
                           (var 0)) 
                        (var 2)) 
                     (var 1))
                  (app3
                     (subst (sh 3) u2)
                     (var 0) (var 2) 
                     (var 1)))))))) end.
       apply tr_weakening_append4. 
       eapply tr_prod_elim2. inv_subst. apply Hsub1.
       { unfold app3. simpsub_bigs.  auto. }
       var_solv. 
       var_solv0.
       replace (subst (sh 7) u1) with (subst (sh 3) (subst (sh 4) u1)).
       replace (subst (sh 7) l1) with (subst (sh 3) (subst (sh 4) l1)).
       replace (subst (sh 7) u2) with (subst (sh 3) (subst (sh 4) u2)).
       weaken subseq_U01; change preworld with (subst (sh 4) preworld);
         change nattp with (@subst obj (sh 4) nattp);
       rewrite ! subst_sh_shift;
       apply tr_weakening_append4; assumption.
       simpsub_bigs; auto.
       simpsub_bigs; auto.
       simpsub_bigs; auto.
       var_solv. var_solv. }
     replace (subst (sh 4) l1) with (subst (sh 1) (subst (sh 3) l1)). inv_subst.
     sh_var 1 1. inv_subst.
     var_solv. simpsub_bigs. auto. }
      {
unfold subseq in Hsub2.
        eapply (deqtype_intro _#3
                              (app3 (shift 4 (ppi2 M)) (var 2) (var 1)
  (*var 1 < l2*)                    (leq_trans_fn_app (var 1)
                                    (subst (sh 4) l1)
                                    (subst (sh 4) l2)
                                    (var 0) (ppi1 (subst (sh 4) M'))))). 
        apply (tr_arrow_elim _
                                 (leq_t (var 1) (subst (sh 4) l2))).
     { weaken leq_type.  var_solv'. 
      change nattp with (@subst obj (sh 4) nattp). rewrite ! subst_sh_shift.
      apply tr_weakening_append4.  assumption. }
     {apply tr_eqtype_formation; subseq_pwapp 4. }
     { match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 1)
                                    (arrow
          (leq_t (var 0) (subst (sh 5) l2))
          (eqtype
             (app
                (app
                   (app (subst (sh 5) u2)
                      (var 0)) (var 4)) 
                (var 3))
             (app3 (subst (sh 5) u3)
                   (var 0) (var 4) (var 3))))) end.
       2:{
         unfold app3. simpsub_bigs. auto.
       }
       eapply (tr_pi_elim _ nattp).
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 2)
       (pi nattp
          (arrow
             (leq_t (var 0) (subst (sh 6) l2))
             (eqtype
                (app
                   (app
                      (app (subst (sh 6) u2)
                         (var 0)) 
                      (var 5)) (var 1))
                (app3 (subst (sh 6) u3)
                   (var 0) (var 5) 
                   (var 1)))))) end .
       2:{ unfold app3. simpsub_bigs. auto. }
       eapply (tr_pi_elim _ (fut nattp)).
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 3)
       (pi (fut nattp)
          (pi nattp
             (arrow
                (leq_t (var 0) (subst (sh 7) l2))
                (eqtype
                   (app
                      (app
                         (app (subst (sh 7) u2)
                            (var 0)) 
                         (var 2)) (var 1))
                   (app3 (subst (sh 7) u3)
                      (var 0) (var 2) 
                      (var 1))))))) end.
       2:{ unfold app3. simpsub_bigs. auto. }
       apply (tr_all_elim _ nzero (fut preworld)); auto. 
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
           (shift 4
      (all nzero (fut preworld) (pi (fut nattp)
         (pi nattp
            (arrow
               (leq_t (var 0)
                  (subst (sh 3) l2))
               (eqtype
                  (app
                     (app
                        (app
                       
                              (subst (sh 3) u2)
                           (var 0)) 
                        (var 2)) 
                     (var 1))
                  (app3
                     (subst (sh 3) u3)
                     (var 0) (var 2) 
                     (var 1)))))))) end.
       apply tr_weakening_append4.
       eapply tr_prod_elim2. inv_subst. apply Hsub2.
       { unfold app3. simpsub_bigs.  auto. }
       var_solv. 
       var_solv0.
       replace (subst (sh 7) u2) with (subst (sh 3) (subst (sh 4) u2)).
       replace (subst (sh 7) l2) with (subst (sh 3) (subst (sh 4) l2)).
       replace (subst (sh 7) u3) with (subst (sh 3) (subst (sh 4) u3)).
       weaken subseq_U01; change preworld with (subst (sh 4) preworld);
         change nattp with (@subst obj (sh 4) nattp);
       rewrite ! subst_sh_shift;
       apply tr_weakening_append4; assumption.
       simpsub_bigs; auto.
       simpsub_bigs; auto.
       simpsub_bigs; auto.
       var_solv. var_solv. }
 (* replace (subst (sh 4) U2) with (subst (sh 1) (subst (sh 3) U2)). inv_subst. *)
     apply leq_trans_app; try (
                               change nattp with (@subst obj (sh 4) nattp);
                               rewrite ! subst_sh_shift;
                               apply tr_weakening_append4;
                               assumption); try var_solv.
     { sh_var 1 1. replace (subst (sh 4) l1) with (subst (sh 1) (subst (sh 3) l1)). inv_subst.
       var_solv.
     simpsub_bigs. auto. }
     { eapply tr_prod_elim1.
       match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
           (subst (sh 4) (subseq u1 l1 u2 l2)) end.
       rewrite ! subst_sh_shift. apply tr_weakening_append4. assumption.
       simpsub_bigs. reflexivity. } } } 
  Qed.
