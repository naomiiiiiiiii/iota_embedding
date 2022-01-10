Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import lemmas0 source subst_src rules_src help subst_help0 subst_help
     trans basic_types derived_rules.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined PageType.
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

Lemma unfold_pw: forall G,
    tr G (deqtype preworld (arrow nattp
                                  (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))).
  intros. unfold preworld.
  apply tr_rec_unroll.
  apply tr_arrow_formation; auto.
  apply tr_karrow_formation.
  apply tr_fut_formation.
  simpl. 
  apply tr_hyp_tp. repeat constructor.
  apply tr_arrow_formation; auto.
  apply tr_fut_formation; auto. Qed.

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


Lemma pw_app_typed2 G u u' l l': tr G (deq u u' preworld) ->
                                    tr G (deq l l' nattp) ->
                                    tr G (deq  (app u l) (app u' l')
       (karrow (fut preworld)
               (arrow (fut nattp) (univ nzero)))).
  intros. apply (tr_arrow_elim _ nattp); auto.
  apply pw_type1.
  eapply tr_eqtype_convert. 
  apply unfold_pw. assumption. Qed.

Lemma pw_app_typed G u u' l l' v v' i i': tr G (deq u u' preworld) ->
                                    tr G (deq l l' nattp) ->
                                    tr G (deq v v' (fut preworld)) ->
                                    tr G (deq i i' (fut nattp)) ->
                                    tr G (deqtype (app (app (app u l) v) i)
                                                  (app (app (app u' l') v') i')).
  intros. apply (tr_formation_weaken _ nzero).
  apply (tr_arrow_elim _ (fut nattp)); auto.
  apply tr_fut_formation. auto.
  apply (tr_karrow_elim _ (fut preworld)); auto.
  apply tr_fut_formation. auto.
  apply tr_arrow_formation; auto.
  apply tr_fut_formation. auto. apply pw_app_typed2; assumption. Qed.



Lemma world_type: forall G,
    tr G (deqtype world world).
unfold world. intros. apply tr_sigma_formation; auto.
Qed.

Lemma world_pair: forall w l G, tr G (oof w preworld) ->
                           tr G (oof l nattp) ->
    tr G (oof (ppair w l) world).
  intros. eapply tr_sigma_intro; try assumption.
  apply nat_type. Qed.

    Lemma split_world1: forall w1 l1 G,
    tr G (oof (ppair w1 l1) world) -> tr G (oof w1 preworld).
      intros.
      eapply tr_compute; try 
      (apply (equiv_symm _ (ppi1 (ppair w1 l1))); apply reduce_equiv;
       apply reduce_ppi1_beta; apply reduce_id); try apply equiv_refl.
      eapply tr_sigma_elim1. apply H.
Qed.

    Lemma split_world2: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof l1 nattp). (*ask karl can't put a
                                                          conjunction here*)
      intros.
      eapply tr_compute; try 
      (apply (equiv_symm _ (ppi2 (ppair w1 l1))); apply reduce_equiv;
       apply reduce_ppi2_beta; apply reduce_id); try apply equiv_refl.
      change nattp with (subst1 (ppi1 (ppair w1 l1)) nattp).
      eapply tr_sigma_elim2. apply H. Qed.

    Lemma nth_works: forall G w n,
        tr G (oof w world) -> tr G (oof n nattp) -> tr G (oof (nth w n)
                           (karrow (fut preworld) (arrow (fut nattp) U0))).
      intros G w n Hw Hn. unfold nth. apply (tr_arrow_elim _ nattp); auto.
      do 2? constructor. auto.
      constructor. auto.
      apply tr_univ_formation. auto.
      eapply tr_eqtype_convert. apply unfold_pw.
      eapply tr_sigma_elim1. apply Hw. 
      Qed.

    Lemma subseq_U01: forall G w1 l1 w2, tr G (oof w1 preworld) ->
                                    tr G (oof l1 nattp) ->
                                       tr G (oof w2 preworld) ->
                                   tr (hyp_tm (fut preworld) :: G) (oof
       (pi (fut nattp)
          (pi nattp
             (arrow
                (lt_t (var 0) (subst (sh 3) l1))
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
 apply lt_type; try var_solv'. 
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
  apply zero_typed.
  eapply subseq_U01; try assumption; auto.
  apply zero_typed. apply leq_refl; auto.
Qed.

(*simple lemmas about well typedness of embedding*)
Lemma laters_type: forall A G,
    (tr G (oof A (univ nzero))) -> tr G (oof (laters A) (univ nzero)).
  intros. unfold laters. unfold plus.
  apply tr_rec_formation_univ. apply tr_sigma_formation_univ; auto.
  simpsub. apply tr_booltp_formation.
  simpsub.
  change (univ nzero) with (@subst1 obj (var 0) (univ nzero)).
  apply tr_booltp_elim. rewrite - (@subst_booltp obj (sh 1)). var_solv.
  simpsub_bigs. change (univ nzero) with (@subst obj (sh 2) (univ nzero)).
  rewrite ! subst_sh_shift. apply tr_weakening_append2. assumption.
  simpsub. constructor. simpl. change (univ nzero) with
(@subst obj (sh 2) (univ nzero)). var_solv. auto. auto. Qed.

  Hint Resolve laters_type.
(* dont use theta, y comb special
Definition bind : term obj := app theta
   (lam   ( (*f := 0*)
      lam ( (*f:= 1, x : laters A := 0*)
          lam ( (*f:= 2, x := 1, g : A -> laters B := 0 *)
              let f := (var 2) in
              let x := (var 1) in
              let g := (var 0) in
              let y := ppi2 x in
         bite (ppi1 x) (app g y) (*y : A*)
              (let y' := prev y in (*y : |> laters A*)
               let f' := prev f in
               inr (next (app (app f' y') g))) )
        ))).

Definition make_bind E1 E2 := app (app bind E1) E2. *)

  Lemma inl_plus_typ: forall G A B m,
    tr G (oof m A) ->
    tr G (deqtype A A) ->
    tr G (deqtype B B) ->
    tr G (oof (inl m) (plus A B)).
  intros. unfold plus. unfold inl.
  apply tr_sigma_intro. constructor.
  simpsub_bigs.
  eapply tr_compute; try apply H.
  apply reduce_equiv. apply reduce_bite_beta1.
  apply reduce_id.
  apply equiv_refl. apply equiv_refl.
   apply tr_booltp_elim_eqtype; try ( 
    unfold deqtype;
    sh_var 1 1;
    change triv with (@shift obj 1 triv); inv_subst;
    rewrite ! subst_sh_shift; apply tr_weakening_append1;
    auto).
  change booltp with (@subst obj (sh 1) booltp).
  var_solv0. Qed.

Lemma plus_typed: forall G A B,
    tr G (deqtype A A) ->
    tr G (deqtype B B) ->
    tr G (oof_t (plus A B)).
intros. 
    unfold plus.
    apply tr_sigma_formation.
    weaken tr_booltp_formation.
    constructor; try (change booltp with (@subst obj (sh 1) booltp); var_solv0); try (
    unfold deqtype; simpsub_bigs; inv_subst;
    change triv with (@shift obj 1 triv);
    rewrite subst_sh_shift; apply tr_weakening_append1; auto).
Qed.

Lemma inr_plus_typ: forall G A B m,
    tr G (oof m B) ->
    tr G (deqtype A A) ->
    tr G (deqtype B B) ->
    tr G (oof (inr m) (plus A B)).
  intros. unfold plus. unfold inr.
  apply tr_sigma_intro. constructor.
  simpsub_bigs.
  eapply tr_compute; try apply H.
  apply reduce_equiv. apply reduce_bite_beta2.
  apply reduce_id.
  apply equiv_refl. apply equiv_refl.
   apply tr_booltp_elim_eqtype; try ( 
    unfold deqtype;
    sh_var 1 1;
    change triv with (@shift obj 1 triv); inv_subst;
    rewrite ! subst_sh_shift; apply tr_weakening_append1;
    auto).
  change booltp with (@subst obj (sh 1) booltp).
  var_solv0. Qed.

(*start here this is pasically ret, redefine ret to be this*)
Lemma inl_laters_type: forall G A m,
    tr (promote G) (oof_t A) ->
    tr G (oof m A) ->
    tr G (oof (inl m) (laters A)).
  intros. unfold laters.
  eapply tr_eqtype_convert.
  - eapply tr_eqtype_symmetry.
    apply tr_rec_unroll.
 - apply plus_typed. 
    unfold deqtype. change triv with (@shift obj 1 triv).
    inv_subst. rewrite ! subst_sh_shift. apply tr_weakening_append1.
    apply (tr_inhabitation_formation _ m m). auto.
    constructor. simpl.
    apply tr_hyp_tp. apply Sequence.index_0.
    simpsub_bigs.
    apply inl_plus_typ. auto.
    apply (tr_inhabitation_formation _ m m). auto.
    constructor.
    constructor. apply plus_typed.
    unfold deqtype. inv_subst.
    change triv with (@shift obj 1 triv).
    rewrite ! subst_sh_shift. apply tr_weakening_append1. auto.
    constructor.
    apply tr_hyp_tp. apply Sequence.index_0. Qed.

Lemma inr_laters_type: forall G A m,
    tr G (oof m (fut (laters A))) ->
    tr (promote G) (oof A U0) ->
    tr G (oof A U0) ->
    tr G (oof (inr m) (laters A)).
  intros. unfold laters.
  eapply tr_eqtype_convert.
  eapply tr_eqtype_symmetry.
  - apply tr_rec_unroll.
  - apply plus_typed. 
    unfold deqtype. change triv with (@shift obj 1 triv).
    inv_subst. rewrite ! subst_sh_shift. apply tr_weakening_append1.
    weaken H1.
     constructor.
    apply tr_hyp_tp. apply Sequence.index_0.
  - simpsub_bigs. apply inr_plus_typ. unfold laters in H.
    rewrite subst_sh_shift. auto.
  - weaken H1. constructor. 
    match goal with |- tr ?G (deqtype ?T ?T) =>
                    replace T with (laters A) end.
    2: {
      unfold laters. simpsub_bigs. auto.
    }
    weaken laters_type. apply H0. Qed.

Lemma yc_typed G A: tr G (deqtype A A) ->
                    tr G (oof Yc (arrow (arrow (fut A) A)
                                        A
                         )).
  Admitted.

Lemma tr_weakening_append5: forall G1 x y z a b J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (x::y::z::a::b::G1) (
                       (deq (shift 5 J1)
                            (shift 5 J2)
                            (shift 5 t))).
Admitted.



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

  Lemma store_U0: forall w l G, tr G (oof w preworld) ->
                           tr G (oof l nattp) ->
                           tr G (oof (store w l) U0).
Admitted.

  Lemma store_type1: forall w l G,
tr G (oof w preworld) ->
 tr G (oof l nattp) ->
 tr (hyp_tm preworld ::G) (oof_t (pi nattp (*v = 1, l v= 0*)
                 (arrow (subseq (shift 2 w) (shift 2 l) (var 1) (var 0))
                        (gettype (shift 2 w) (var 1) (var 0))))).
  Admitted.


    Lemma store_type: forall w l G,
   tr G (oof w preworld) ->
   tr G (oof l nattp) ->
 tr G (deqtype (store w l) (store w l)).
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
      tr G (oof w1 preworld) ->
      tr G (oof w2 preworld) ->
      tr G (oof l1 nattp) ->
      tr G (oof l2 nattp) ->
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
    { weaken lt_type. var_solv'.
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
    - weaken lt_type. var_solv'. 
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
                                 (lt_t (var 1)  (subst (sh 4) l1))).
     { weaken lt_type.  var_solv'. 
      change nattp with (@subst obj (sh 4) nattp). rewrite ! subst_sh_shift.
      apply tr_weakening_append4.  assumption. }
     {apply tr_eqtype_formation; subseq_pwapp 4. } 
     { match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 1)
                                    (arrow
          (lt_t (var 0) (subst (sh 5) l1))
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
             (lt_t (var 0) (subst (sh 6) l1))
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
                (lt_t (var 0) (subst (sh 7) l1))
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
               (lt_t (var 0)
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
  (*var 1 < l2*)                    (lt_trans_fn_app (var 1)
                                    (subst (sh 4) l1)
                                    (subst (sh 4) l2)
                                    (var 0) (ppi1 (subst (sh 4) M'))))). 
        apply (tr_arrow_elim _
                                 (lt_t (var 1) (subst (sh 4) l2))).
     { weaken lt_type.  var_solv'. 
      change nattp with (@subst obj (sh 4) nattp). rewrite ! subst_sh_shift.
      apply tr_weakening_append4.  assumption. }
     {apply tr_eqtype_formation; subseq_pwapp 4. }
     { match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with
                                    (@subst1 obj (var 1)
                                    (arrow
          (lt_t (var 0) (subst (sh 5) l2))
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
             (lt_t (var 0) (subst (sh 6) l2))
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
                (lt_t (var 0) (subst (sh 7) l2))
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
               (lt_t (var 0)
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
     apply lt_trans_app; try (
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
Lemma bind_type G A B M0 M1 :
    tr G (oof A U0) ->
    tr (promote G) (oof A U0) ->
    tr G (oof B U0) ->
    tr (promote G) (oof B U0) ->
    tr G (oof M0 (laters A)) ->
    tr G (oof M1 (arrow A (laters B))) ->
    tr G (oof (make_bind M0 M1) (laters B)).
  intros Ha Ha1 Hb Hb1 Hm0 Hm1.
  unfold make_bind. unfold bind. 
  apply (tr_arrow_elim _ (arrow A (laters B))); auto.
  { apply tr_arrow_formation; auto. weaken Ha. weaken laters_type; auto.
  }
  { weaken laters_type; auto. }
  apply (tr_arrow_elim _ (laters A) ); auto.
  { weaken laters_type; auto. }
  { repeat apply tr_arrow_formation; try weaken Ha; try weaken laters_type; auto.
  } 
  apply (tr_arrow_elim _
                       (arrow
                          (fut ((arrow (laters A)
                                       (arrow (arrow A (laters B)) (laters B)))))
                          ((arrow (laters A)
                                       (arrow (arrow A (laters B)) (laters B)))))
        ).
  {  
    repeat apply tr_arrow_formation; try apply tr_fut_formation;
      repeat apply tr_arrow_formation; try weaken Ha;
      try weaken Ha1; try weaken Hb1; try weaken laters_type; auto.
  }
   { repeat apply tr_arrow_formation; try weaken Ha;
       try weaken Ha1; try weaken Hb1; try weaken laters_type; auto. }
   apply yc_typed.
   { repeat apply tr_arrow_formation; try weaken Ha;
       try weaken Ha1; try weaken Hb1; try weaken laters_type; auto. }
   apply tr_arrow_intro.
   { try apply tr_fut_formation;
      repeat apply tr_arrow_formation; try weaken Ha;
      try weaken Ha1; try weaken Hb1; try weaken laters_type; auto.
  }
      { repeat apply tr_arrow_formation; try weaken Ha;
          try weaken Ha1; try weaken Hb1; try weaken laters_type; auto. }
      simpsub.
   apply tr_arrow_intro; try (unfold deqtype; change triv with (@subst obj sh1 triv); inv_subst;
   rewrite ! subst_sh_shift; apply tr_weakening_append1). try weaken laters_type; auto.
      { repeat apply tr_arrow_formation; try weaken Ha;
          try weaken Ha1; try weaken Hb1; try weaken laters_type; auto. }
      simpsub. simpl.
      apply tr_arrow_intro;
        unfold deqtype; try (change triv with (@subst obj (sh 2) triv); inv_subst;
                                          rewrite ! subst_sh_shift; apply tr_weakening_append2).
      { repeat apply tr_arrow_formation; try weaken Ha;
          try weaken Ha1; try weaken Hb1; try weaken laters_type; auto. }
      { repeat apply tr_arrow_formation; try weaken Ha;
          try weaken Ha1; try weaken Hb1; try weaken laters_type; auto. }
      simpsub_big. unfold laters at 1. unfold plus at 1.
      rewrite make_app1.
      eapply tr_eqtype_convert_hyp. apply tr_rec_unroll.
       {apply tr_sigma_formation. weaken tr_booltp_formation.
       apply tr_booltp_elim_eqtype. change booltp with (@subst obj sh1 booltp).
       var_solv. simpsub_bigs.  unfold deqtype. inv_subst.
       rewrite ! subst_sh_shift.
   change triv with (@shift obj 3 triv). 
   apply tr_weakening_append3. weaken Ha.
   simpsub. apply tr_fut_formation. simpl. apply tr_hyp_tp. constructor.
  apply Sequence.index_0. 
      }
      simpsub_bigs.
      match goal with |- tr ?G (deq ?M ?M ?T) => change M with 
          (@subst obj (under 1 (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)))
                  (bite (var 2)
                        (app (var 0) (var 1))
          (inr
             (next
                (app
                   (app
                     (prev
                     (var 3))
                     (prev
                     (var 1)))
                   (var 0)))))
          ) end.
      rewrite make_app1.
      apply tr_sigma_eta_hyp.
      simpsub_bigs.
          change (inr
             (next
                (app
                   (app (prev (var 3)) (prev (var 1)))
                   (var 0)))) with
              (@subst obj (under 2 sh1)
            (inr (next
                (app
                   (app (prev (var 2)) (prev (var 1)))
                   (var 0))))).
          change (app (var 0) (var 1)) with
              (@subst obj (under 2 sh1)
                      (app (var 0) (var 1))
              ). rewrite make_app2.
replace 
              (rec
                 (sigma booltp
                    (bite (var 0) (subst (sh 5) B)
                          (fut (var 1))))) with
    (laters (subst (sh 3) B)).
replace (rec (plus (subst (sh 3) A)
                       (fut (var 0)))) with (laters (subst (sh 2) A)).
          apply tr_booltp_eta_hyp.
          {simpsub_bigs.
           rewrite make_app1. eapply tr_compute_hyp.
           { constructor. apply reduce_equiv. apply reduce_bite_beta1. apply reduce_id.
           } apply (tr_arrow_elim _ (subst (sh 3) A)).
           { unfold deqtype. inv_subst.
       rewrite ! subst_sh_shift.
   change triv with (@shift obj 3 triv). 
   apply tr_weakening_append3. weaken Ha. }
           {weaken laters_type. change (univ nzero) with
                                    (@subst obj (sh 3) (univ nzero)).
            rewrite ! subst_sh_shift. apply tr_weakening_append3. assumption. }
        rewrite - ! (sh_sum 2 1).  inv_subst. var_solv.
        rewrite - ! (sh_sum 1 2).  inv_subst. var_solv. }
          simpsub_bigs.
           match goal with |- tr ?G (deq ?M ?M ?T) =>
                            change M with (inr ( subst1 (prev (var 2))
                                                (next
             (app (app (var 0) (prev (var 2)))
                (var 1))))) 
           end.
           apply inr_laters_type.
           match goal with |- tr ?G (oof ?M ?T) => replace T with
               (subst1 (prev (var 2))
                       (fut (laters (subst (sh 4) B)))
               ) end.
           2:{ simpsub_bigs. auto.  }
           eapply (tr_fut_elim _#3
             (subst (sh 3) 
             (arrow (laters A)
                (arrow (arrow A (laters B))
                   (laters B))))).
           { inv_subst. var_solv. }
           { simpsub_bigs.
             repeat apply tr_arrow_formation; try weaken laters_type;
               change (univ nzero) with (@subst obj (sh 3) (univ nzero));
               rewrite ! subst_sh_shift; try apply tr_weakening_append3;
                 try assumption.
             unfold deqtype. change triv with (@shift obj 3 triv).
             inv_subst. rewrite ! subst_sh_shift.
             apply tr_weakening_append3. weaken Ha1. }
           match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
               (subst1 (prev (var 2))
                       (fut (laters (subst (sh 5) B))));
                change M with (@subst1 obj (prev (var 2))
       (next
          (app (app (var 1) (var 0)) (var 2)))
                               
               ) end.
           rewrite make_app2. eapply tr_compute_hyp.
           {constructor. apply reduce_equiv. apply reduce_bite_beta2. apply reduce_id. }
           eapply (tr_fut_elim _#3 (laters (subst (sh 4) A))).
           { rewrite - (sh_sum 1 3). inv_subst. var_solv. }
           {simpl.  unfold deqtype. inv_subst.
       rewrite ! subst_sh_shift.
   change triv with (@shift obj 4 triv). 
   apply tr_weakening_append4. weaken laters_type. apply Ha1. }
           { constructor. simpl. simpsub_bigs.
             apply (tr_arrow_elim _ (arrow (subst (sh 5) A)
                   (laters (subst (sh 5) B)))).
           { 
             repeat apply tr_arrow_formation; try weaken laters_type;
               change (univ nzero) with (@subst obj (sh 5) (univ nzero));
               rewrite ! subst_sh_shift; try apply tr_weakening_append5;
                 try assumption.
             unfold deqtype. change triv with (@shift obj 5 triv).
             inv_subst. rewrite ! subst_sh_shift.
             apply tr_weakening_append5. weaken Ha1. }
           { weaken laters_type;
               change (univ nzero) with (@subst obj (sh 5) (univ nzero));
               rewrite ! subst_sh_shift; try apply tr_weakening_append5;
                 try assumption.
           }
           {
             apply (tr_arrow_elim _ (laters (subst (sh 5) A))).
           { weaken laters_type;
               change (univ nzero) with (@subst obj (sh 5) (univ nzero));
               rewrite ! subst_sh_shift; try apply tr_weakening_append5;
                 try assumption.
           }
           { 
             repeat apply tr_arrow_formation; try weaken laters_type;
               change (univ nzero) with (@subst obj (sh 5) (univ nzero));
               rewrite ! subst_sh_shift; try apply tr_weakening_append5;
                 try assumption.
             unfold deqtype. change triv with (@shift obj 5 triv).
             inv_subst. rewrite ! subst_sh_shift.
             apply tr_weakening_append5. weaken Ha1. }
           rewrite - ! (sh_sum 3 2). inv_subst. var_solv.
           rewrite - ! (sh_sum 4 1). inv_subst. var_solv. }
           rewrite - ! (sh_sum 2 3). inv_subst. var_solv. }
           simpsub_bigs. auto.
           simpl.
               change U0 with (@subst obj (sh 3) (univ nzero));
               rewrite ! subst_sh_shift; apply tr_weakening_append3;
                  assumption.
               change U0 with (@subst obj (sh 3) (univ nzero));
               rewrite ! subst_sh_shift; apply tr_weakening_append3;
                  assumption.
           unfold laters. simpsub_bigs. auto.
           unfold laters. unfold plus. simpsub_bigs. auto. Qed.
(*repeated patterns of proofs.v*)
