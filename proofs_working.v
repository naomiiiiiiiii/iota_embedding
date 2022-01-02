Require Import Program Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences.
From istari Require Import Rules Defined DefsEquiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma size_Gamma_at: forall w l G,
    size (Gamma_at_ctx G w l) = size G.
  intros. induction G. auto.
  simpl. rewrite IHG. auto. Qed.

Lemma shift_trans_type : forall w l A s ,
    (shift s (trans_type w l A)) = (trans_type                                 
                                            (shift s w)
                                            (shift s l) A).
  intros.
  rewrite - ! subst_sh_shift. change (sh s) with (@under obj 0 (sh s)).
  apply sh_under_trans_type.
 Qed.





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




(*need another lemma showing that trans is total probably*)

Lemma gettype_typed: forall G w v lv, tr G (oof w preworld) -> tr (promote G) (oof (ppair v lv) world) -> tr G (deqtype (gettype w v lv) (gettype w v lv)). 
 intros. unfold gettype.
  constructor; auto. 
  apply pw_app_typed; try var_solv; change preworld with (shift 1 preworld).
  apply tr_weakening_append1. auto. constructor. simpl.
  apply tr_weakening_append1.
  eapply split_world1. apply H0.
  constructor. simpl. change nattp with (@shift obj 1 nattp).
  apply tr_weakening_append1.
  eapply split_world2. apply H0.
  Qed.

(*
Lemma sh_succ m n: @ subst obj (sh n.+1) m = (subst sh1 (subst (sh n) m)).
simpsub. rewrite plusE. rewrite addn1. auto. Qed.

Lemma sh0 m: @ subst obj (sh 0) m = m.
  simpsub. auto. Qed.
Hint Rewrite sh_succ sh0: hygiene_hint.



Goal (@ var obj 10) = (var 0).
  var_nf 10. autorewrite with hygiene_hint. Abort. *)

Lemma moveapp_works : forall T G w1 l1 w2 l2 m v,
      tr G (oof w1 preworld) ->
      tr G (oof w2 preworld) ->
      tr G (oof l1 nattp) ->
      tr G (oof l2 nattp) ->
     tr G (oof m (subseq w1 l1  w2 l2)) ->
     tr G (oof v (trans_type w1 l1 T)) -> (*it's the occurence of T in this line?!
                                          ask karl*)
     tr G (oof (move_app T m v) (trans_type w2 l2 T)).
  intros. unfold move_app.
  eapply tr_arrow_elim; try apply H4; try (weaken trans_type_works; auto).
  eapply tr_arrow_elim; try apply H3; try (apply subseq_type; auto).
  eapply tr_arrow_formation; try (weaken trans_type_works; auto).
  apply move_works; auto.
  Qed.



(*
clam, capp are for points in spaces (kinds)
isomorphism between normally constructed terms of kinds and points in spaces (whole point of semantics)
he has istari code for converting from normal terms (of kinds) to the points


no jugement for typing the points in spaces

syntactic rules for istari but interpretation (semantics) uses them


con, cty establish relationship between constructors and 
 *)


(*
Goal (@ subst1 obj nattp (var 0)) = nattp.
  unfold subst1. simpl (subst (dot ?x1 ?s) ?x2). cbn - [ nattp].
  cbn [traverse]. *)

Lemma ref1_type: forall A G w1 i,
      (tr G (oof w1 preworld)) ->
      (tr G (oof i nattp)) ->
      (tr [:: hyp_tm nattp, hyp_tm preworld & (promote G)] (oof A U0)) ->
      tr  [:: hyp_tm preworld & G] (oof
             (pi nattp
                (eqtype
                   (app
                      (app
                         (app (subst (sh 2) w1) (subst (sh 2) i))
                         (next (var 1))) 
                      (next (var 0)))
                   (fut A))) U0). intros. 
      apply tr_pi_formation_univ; auto.
      apply tr_eqtype_formation_univ.
      eapply (tr_arrow_elim _ (fut nattp) ). constructor; auto.
      apply tr_univ_formation.  auto.
      apply (tr_karrow_elim _ (fut preworld)).
      eapply kind_type. apply tr_fut_kind_formation. apply pw_kind. auto.
      apply tr_arrow_formation. constructor; auto.
      apply tr_univ_formation. auto. apply (tr_arrow_elim _ nattp); auto.
      eapply tr_eqtype_convert; try apply unfold_pw.
      rewrite ! subst_sh_shift. change preworld with (shift 2 preworld).
      apply tr_weakening_append2. auto.
      rewrite ! subst_sh_shift. change nattp with (@shift obj 2 nattp).
      apply tr_weakening_append2. auto.
      constructor.
      var_solv.
      constructor.
      var_solv.
      apply tr_fut_formation_univ. simpsub_big.
      simpl. assumption.
      auto.
      Qed.

Lemma ref0_type: forall A G w1 l1,
      (tr G (oof (ppair w1 l1) world)) ->
      (tr [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp & (promote G)]
          (oof A U0)) ->
      tr ((hyp_tm nattp) :: G) (oof
(prod (lt_t (var 0) (shift 1 l1))
          (all nzero preworld
             (pi nattp
                (eqtype
                   (app
                      (app
                         (app (subst (sh 3) w1) (var 2))
                         (next (var 1))) 
                      (next (var 0)))
                   (fut A))))) U0).
  intros.
      eapply tr_prod_formation_univ. apply lt_type.
      rewrite - (subst_nat sh1). var_solv.
      rewrite - (subst_nat sh1) ! subst_sh_shift.
      apply tr_weakening_append1. 
    eapply split_world2. apply H.
    apply tr_all_formation_univ. apply pw_kind.
    sh_var 2 4.
    replace (subst (sh 3) w1) with (subst (sh 2) (subst (sh 1) w1)).
    rewrite - ! subst_sh_shift. apply ref1_type.
    change preworld with (shift 1 preworld). rewrite subst_sh_shift.
    apply tr_weakening_append1.
    eapply split_world1; apply H.
    var_solv.
    simpl.
    apply H0. simpsubs. auto.
    auto. apply leq_refl. auto. Qed.


Hint Rewrite <- subst_ppair subst_nsucc: inv_subst.



 


Lemma apply_IH: forall A Et G G' w l g,
      tr [::]
                (oof Et
                   (all nzero preworld
                      (pi nattp
                         (arrow
                            (Gamma_at G (var 1) (var 0))
                            (trans_type (var 1) (var 0) A))))) ->
      tr G' (oof w preworld) ->
      tr G' (oof l nattp) ->
      tr G' (oof g (Gamma_at G w l)) ->
      tr G' (oof (app (app (subst (sh (size G')) Et) l) g)
          (trans_type w l A)).
intros.
apply (tr_arrow_elim _ (Gamma_at G w l)).
apply Gamma_at_type; auto. 
weaken trans_type_works; assumption.
match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
                   (subst1 l (arrow (Gamma_at G (shift 1 w) (var 0))
                                          (trans_type (shift 1 w) (var 0) A))) end.
               2: { simpsub. unfold subst1 at 1.
                    rewrite subst1_Gamma_at subst1_trans_type. simpsub_bigs. auto.
               }
               apply (tr_pi_elim _ nattp).
               match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
                   (subst1 w (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                          (trans_type (var 1) (var 0) A)))) end.
               2: { unfold subst1. rewrite subst_pi subst_arrow. 
                    rewrite subst1_under_Gamma_at subst1_under_trans_type.
                    simpsub_bigs. auto.
               }
               apply (tr_all_elim _ nzero preworld).
               match goal with |- tr ?G' (deq ?M ?M ?T) =>
                               rewrite - {1} (cats0 G'); replace T with
                                                         (subst (sh (size G')) T) end.
               2: {rewrite subst_all subst_pi subst_arrow.
                   rewrite under_sum sh_under_Gamma_at sh_under_trans_type.
                   simpsub_bigs. auto.
               }
               rewrite ! subst_sh_shift. apply tr_weakening_append.
               assumption. assumption.
               sh_var 1 1.
               apply trans_type_works1; try var_solv.
               assumption. assumption.
Qed.


Lemma subst_make_subseq_trans: forall s a b c d e, (subst s (make_subseq_trans a b c d e)) = (make_subseq_trans
                                                                                 (subst s a)
                                                                                 (subst s b)
                                                                                 (subst s c)
                                                                                 (subst s d)
                                                                                 (subst s e)
                                                                                        ).
  intros. unfold make_subseq_trans. unfold leq_trans_fn_app. unfold leq_trans_fn. simpsub. auto. Qed.

Hint Rewrite subst_make_subseq_trans: core subst1.
Hint Rewrite <- subst_make_subseq_trans : inv_subst.


Theorem two_working: forall G e T ebar,
    trans G e T ebar ->
    tr [::] (oof ebar
                (all nzero preworld (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                                     (trans_type (var 1) (var 0) T))))
           ).
  (*gamma can be part of D, don't even need to move gamma (var 5) over i think*)
  move => G e T ebar Dtrans. induction Dtrans; intros.
  4:{
    apply comp_front.
    simpsub_bigs.  simpsub_bigs. apply inr_laters_type.
    2:{ simpl. sh_var 2 5. inv_subst. apply compm3_type; try var_solv; auto.
        apply trans_type_works; try var_solv.
    }
    2:{ simpl. sh_var 2 5. inv_subst. apply compm3_type; auto; try var_solv.
        apply trans_type_works; try var_solv; auto.
    }

remember (move_app (reftp_m A) (var 1) (app (app (subst (sh 7) Rt) (var 5)) (var 4))) as Ru1.
remember (ppi1 Ru1) as i.
remember (ppi2 (ppi2 Ru1))  as p.
remember (app (app (app (var 0) (var 2)) make_subseq) i) as e.
remember 
    [:: hyp_tm (store (var 2) (var 1));
        hyp_tm
          (subseq (var 4) (var 3)
             (var 1) (var 0));
        hyp_tm nattp; hyp_tm preworld;
        hyp_tm (Gamma_at G (var 1) (var 0));
        hyp_tm nattp; hyp_tm preworld] as G'.
assert (tr G' (oof Ru1 (trans_type (var 3) (var 2) (reftp_m A)))) as Hru1.
      subst.
      apply (@moveapp_works _ _ (var 6) (var 5)); auto; try var_solv.
      (*m : W <= U1*)
       sh_var 2 6.
      inv_subst. var_solv.
      eapply apply_IH; try apply IHDtrans; try var_solv.
      sh_var 5 6.
      inv_subst. var_solv0.
    - assert (tr G' (oof i nattp)) as Hi.
    (*i : nat*) subst.
      eapply (tr_sigma_elim1 _ _
            (prod (lt_t (var 0) (subst sh1 (var 2)))
                (all nzero preworld (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := (shift 3 (var 3)) in
            let l1 := (shift 3 (var 2)) in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (app w i) (next v)) (next lv))
                 (fut (trans_type v lv A))
                      )
             )))). assumption.
    - assert (tr G' (oof p (subst1 i 
                (all nzero preworld (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := (shift 3 (var 3)) in
            let l1 := (@shift obj 3 (var 2)) in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (app w i) (next v)) (next lv))
                 (fut (trans_type v lv A))
                      )
             ))))) as Hp. subst p.
      eapply (tr_prod_elim2 _ (subst1 i (lt_t (var 0) (subst sh1 (var 2))))).
      inv_subst. subst i. eapply tr_sigma_elim2. apply Hru1.
      match goal with |- tr ?G (oof ?M ?T) =>
                      replace M with
          (subst1 (prev e)
       (next
          (inl
             (ppair (var 3)
                (ppair
                   (ppair make_subseq
                      (var 1)) 
                   (var 0))))
          ));
                        replace T with
                            (subst1 (prev e)
       (fut
          (laters
             (exist nzero preworld
                (sigma nattp
                   (prod
                      (prod
                         (subseq
                            (var 6) 
                            (var 5)
                            (var 1) 
                            (var 0))
                         (store 
                            (var 1) 
                            (var 0)))
                      (trans_type 
                         (var 1) 
                         (var 0) A))))))) end.
      subst G'. 
      apply (tr_fut_elim _#3 (trans_type (var 3) (var 2) A) ).
      (*s l1 m i: fut A @ u1*)
      subst e. 
      eapply (tr_eqtype_convert _ _ _
               (app (app (app (var 3) i) (next (var 3))) (next (var 2)))).
      (*convert from fut A @ u1 to u1 i u1 l1*)
        simpsubin_bigs Hp. 
        apply (deqtype_intro _ _ _ (app p (var 2))
                             (app p (var 2))
                                        ).
        match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
       (subst1 (var 2) (eqtype
          (app
             (app (app (var 4) (shift 1 i))
                (next (var 4))) 
             (next (var 0)))
          (fut (trans_type (var 4) (var 0) A)))) end.
        2:{
          subst. simpsub_bigs. rewrite fold_subst1 subst1_trans_type. simpsub_bigs. auto.
        }
        apply (tr_pi_elim _ nattp).
        match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
       (subst1 (var 3) 
       (pi nattp
          (eqtype
             (app
                (app (app (var 5) (shift 2 i))
                   (next (var 1)))
                (next (var 0)))
             (fut (trans_type (var 1) (var 0) A))))) end.
        eapply (tr_all_elim _ nzero preworld).
        move : Hp. simpl. simpsubs.
        replace (dot (var 0)
                         (dot (var 1)
                              (dot (subst (sh 2) i) (sh 2)))) with
            (under 2 (dot i id)).
        2:{
          simpsub_bigs. auto.
        } rewrite subst1_under_trans_type. simpsub_bigs.
        apply; auto; try var_solv. var_solv.
        sh_var 2 5. rewrite - ! subst_sh_shift.
        weaken ref1_type; try var_solv. assumption.
        apply trans_type_works; try var_solv; auto.
        simpsub_bigs. auto.
        change (dot (var 0) (dot (var 4) sh1)) with
            (@under obj 1 (dot (var 3) id)).
        rewrite subst1_under_trans_type.
        simpsub_bigs. auto. var_solv.
        (*s l1 m i: u1 i u1 l1*)
        eapply (@store_works (var 2)); try var_solv.
        sh_var 1 3. rewrite - ! subst_sh_shift - ! (subst_store _ _ (sh 1)).
        var_solv0.
        apply subseq_refl; auto; try var_solv. assumption.
        weaken trans_type_works; try var_solv; auto.
        (*pair : laters*)
        apply tr_fut_intro. simpl.
        apply inl_laters_type. simpl.
      * sh_var 2 6. inv_subst. weaken compm3_type; auto; try var_solv.
        apply trans_type_works; auto; try var_solv.
        apply (tr_exist_intro _ _ _ _ (var 4)); auto; try var_solv.
        simpsub_bigs.
        apply tr_sigma_intro; auto; try var_solv.
        simpsub_bigs.
        apply tr_prod_intro; auto.
        apply tr_prod_intro; auto.
        apply subseq_refl; try var_solv.
        sh_var 2 4. rewrite - ! subst_sh_shift - ! (subst_store _ _ (sh 2)).
        var_solv.
       replace (subst (dot (var 3) (dot (var 4) id))
              (trans_type (var 1) (var 0) A)) with
       (subst (dot (var 4) id) (subst (dot (var 4) id)
                                      (trans_type (var 1) (var 0) A))).
       2:{ simpsub_bigs. auto.
       }
       rewrite ! fold_subst1 ! subst1_trans_type.
       simpsub_bigs. sh_var 1 4. rewrite - ! subst_sh_shift.
    rewrite -  (sh_trans_type (var 3)).
    var_solv0. 
    weaken compm5_type; auto; try var_solv.
    change (dot (var 0) (dot (var 5) sh1)) with
        (@under obj 1 (dot (var 4) id)).
    rewrite subst1_under_trans_type. simpsub_bigs.
    apply trans_type_works; try var_solv.
    sh_var 2 6. inv_subst. weaken compm4_type; auto; try var_solv.
    apply trans_type_works; auto; try var_solv.
simpsub_type; auto.
simpsub_bigs; auto.
simpsub_type; auto.
  }
   4: { 
       (*ap case*) 
 apply tr_all_intro; auto. simpsub_bigs.
       apply tr_pi_intro; auto.
       apply tr_arrow_intro; auto.
       apply Gamma_at_type; auto; try var_solv.
       weaken trans_type_works; auto; try var_solv.
       rewrite sh_trans_type.  simpsub_bigs.
       apply (tr_arrow_elim _ (trans_type (var 2) (var 1) Targ)); try (weaken trans_type_works; auto); try var_solv.
       apply (tr_arrow_elim _
                            (subseq (var 2) (var 1)
                            (var 2) (var 1)
                            )
             ).
       apply subseq_type; auto; try var_solv.
       apply tr_arrow_formation; try (weaken trans_type_works; auto);
       try var_solv.
       match goal with |- tr ?G (deq ?M ?M ?T) =>
                       replace T with
          ( subst1 (var 1)
       (arrow
          (subseq (var 3) (var 2) (var 3) (var 0))
          (arrow (trans_type (var 3) (var 0) Targ)
                 (trans_type (var 3) (var 0) T2)))) end.

     2: {
         simpsub_bigs. rewrite fold_subst1 ! subst1_trans_type. simpsubs.
         auto.
       }
       apply (tr_pi_elim _ nattp); try var_solv.
       match goal with |- tr ?G (deq ?M ?M ?T) =>
                       replace T with
       (subst1 (var 2) (pi nattp
          (arrow
             (subseq (var 4) (var 3)
                 (var 1) (var 0))
             (arrow
                (trans_type (var 1) (var 0) Targ)
                (trans_type (var 1) (var 0) T2))))) end.
       2: {
         simpsub_bigs.
         change (dot (var 0) (dot (var 3) sh1)) with
             (@under obj 1 (dot (var 2) id)).
         rewrite ! subst1_under_trans_type. simpsubs.
         auto.
       }
       apply (tr_all_elim _ nzero preworld).
       match goal with |- tr ?G (deq ?M ?M ?T) =>
                       change T with (trans_type (var 2) (var 1)
                                                  (arrow_m Targ T2)) end.
       eapply apply_IH; auto; try var_solv. apply IHDtrans1.
       sh_var 1 2. inv_subst. var_solv0. var_solv.
       apply tr_pi_formation; auto; try var_solv.
       apply tr_arrow_formation; try (weaken trans_type_works; auto); try var_solv.
       apply subseq_type; auto; try var_solv.
       apply tr_arrow_formation; try (weaken trans_type_works; auto); try var_solv.
       apply subseq_refl; auto; try var_solv.
       eapply apply_IH; auto; try var_solv. apply IHDtrans2.
       sh_var 1 2. inv_subst. var_solv0. 
  }
  4: { (*arrow case*)
    assert (tr [:: hyp_tm nattp; hyp_tm preworld; hyp_tm nattp; hyp_tm preworld]
    (deqtype
             (arrow
                (subseq  (var 3) (var 2)
                   (var 1) (var 0))
                (arrow (trans_type (var 1) (var 0) Targ)
                   (trans_type (var 1) (var 0) T2)))
             (arrow
                (subseq (var 3) (var 2)
         (var 1) (var 0))
                (arrow (trans_type (var 1) (var 0) Targ)
                       (trans_type (var 1) (var 0) T2))))) as Htyp1.
    apply tr_arrow_formation; auto.
    apply subseq_type; auto; try var_solv.
    apply tr_arrow_formation; try (weaken trans_type_works; try var_solv; auto).
    assert (
  tr
    [:: hyp_tm nattp; hyp_tm preworld;
        hyp_tm (Gamma_at G (var 1) (var 0)); 
       hyp_tm nattp; hyp_tm preworld]
    (deqtype
       (arrow (trans_type (var 1) (var 0) Targ)
          (trans_type (var 1) (var 0) T2))
       (arrow (trans_type (var 1) (var 0) Targ)
          (trans_type (var 1) (var 0) T2)))
      ) as Htyp2.
    apply tr_arrow_formation; auto;
      try (weaken trans_type_works; try var_solv; auto).
        apply tr_all_intro; auto. simpsub_bigs. 
       apply tr_pi_intro; auto.
       apply tr_arrow_intro; auto.
       apply Gamma_at_type; auto; try var_solv.
       apply tr_all_formation; auto.
       apply tr_pi_formation; auto.
       simpsub_bigs.
       change (dot (var 0) (dot (var 1) (sh 3))) with
           (@under obj 2 (sh 1)). rewrite ! sh_under_trans_type.
        apply tr_all_intro; auto. simpsub_bigs.
        apply tr_pi_intro; auto.
        apply tr_arrow_intro; auto.
        simpsub_bigs.
        apply subseq_type; try var_solv.
        simpsub_bigs.
        rewrite ! sh_trans_type. simpsub_bigs.
        apply tr_arrow_intro; try (weaken trans_type_works; try var_solv; auto).
        rewrite ! sh_trans_type. simpsub_bigs.
        eapply apply_IH; auto; try var_solv.
        apply IHDtrans. 
        apply Gamma_at_intro; try var_solv.
        eapply (move_gamma_works _ _ (var 6) (var 5)); try var_solv. 
        sh_var 2 6. inv_subst. var_solv0.
        sh_var 5 6. inv_subst. var_solv0.
        sh_var 1 3. rewrite - ! subst_sh_shift - ! sh_trans_type.
        var_solv0. rewrite ! sh_trans_type. simpsubs.
        apply Sequence.index_0.
  }
  4:{ (*ret case*)
    simpl. apply comp_front.
    simpsub_bigs. simpsub_bigs.
    apply inl_laters_type.
   * sh_var 2 6. inv_subst. simpl. weaken compm3_type; try var_solv; auto.
        apply trans_type_works; auto; try var_solv.
  * apply (tr_exist_intro _#4 (var 3)); auto; try var_solv.
    simpsub_bigs.
       change (dot (var 0) (dot (var 4) (sh1))) with
           (@under obj 1 (dot (var 3) id)).
       rewrite ! subst1_under_trans_type.
    apply tr_sigma_intro; try var_solv.
    simpsub_bigs. rewrite fold_subst1 subst1_trans_type.
    simpsub_bigs. apply tr_prod_intro.
    apply tr_prod_intro.
    apply subseq_refl; auto; try var_solv.
    sh_var 1 3. inv_subst. rewrite - ! (subst_store _ _ (sh 1)).
    var_solv0.
    eapply (@moveapp_works _ _ (var 6) (var 5)); auto; try var_solv.
    sh_var 2 6. inv_subst. var_solv0.
    eapply apply_IH; try apply IHDtrans; auto; try var_solv.
    sh_var 5 6. inv_subst. var_solv0.
    weaken compm5_type; try var_solv; auto; try var_solv.
    apply trans_type_works; try var_solv; simpsubs; try var_solv.
    sh_var 2 5. inv_subst. weaken compm4_type; try var_solv; auto.
    apply trans_type_works; try var_solv; auto.
  }
  3: {
    apply comp_front.
    simpsub_bigs.  simpsub_bigs.
    apply inl_laters_type.
    sh_var 2 5. inv_subst. 
    simpl. weaken compm3_type; try var_solv; auto. apply tr_unittp_formation.
    (*l1 = var 2 = pw*)
    apply (tr_exist_intro _ nzero preworld _ (var 3)); auto.
    var_solv.
    simpsub_bigs. constructor; try var_solv. (*l1 : nat*)
    simpsub_bigs.
    apply tr_prod_intro.
    - apply tr_prod_intro.
      + (*U1 <= U1*)
        apply subseq_refl; try var_solv; auto.
      + (*lam : store u1*)unfold store. apply tr_all_intro; auto. simpsub_bigs.
        apply tr_pi_intro; auto.
        apply tr_arrow_intro; auto. apply subseq_type; auto; try
 var_solv.
        apply gettype_typed; simpl; try var_solv; auto.
        unfold gettype.
        simpsub_bigs. apply tr_pi_intro; auto.
        (*case on whether index = i size u*)
        remember (move_app (reftp_m A) 
                   (var 5)
                   (app
                      (app (subst (sh 11) Rt)
                         (var 9)) 
                      (var 8))) as Ru1.
        remember (ppi1 Ru1) as i.
        remember (ppi2 (ppi2 Ru1))  as p.
        match goal with |- tr ?G' (@ deq obj ?M ?M ?T) =>
                        remember G' as G'' end.
    - assert (tr G'' (oof Ru1 (trans_type (var 7) (var 6) (reftp_m A)))) as Hru1.
      subst.
      apply (@moveapp_works _ _ (var 10) (var 9)); auto; try var_solv.
      (*m : W <= U1*)
      sh_var 6 10.
      inv_subst. var_solv0.
      eapply apply_IH; try apply IHDtrans1; try var_solv.
      sh_var 9 10.
      inv_subst. var_solv0.
    - assert (tr G'' (oof i nattp)) as Hi.
    (*i : nat*) subst.
      eapply (tr_sigma_elim1 _ _
            (prod (lt_t (var 0) (subst sh1 (var 6)))
                (all nzero preworld (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := (shift 3 (var 7)) in
            let l1 := (shift 3 (var 6)) in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (app w i) (next v)) (next lv))
                 (fut (trans_type v lv A))
                      )
             )))). assumption.
    - assert (tr G'' (oof p (subst1 i 
                (all nzero preworld (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := (shift 3 (var 7)) in
            let l1 := (@shift obj 3 (var 6)) in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (app w i) (next v)) (next lv))
                 (fut (trans_type v lv A))
                      )
             ))))) as Hp. subst p.
      eapply (tr_prod_elim2 _ (subst1 i (lt_t (var 0) (subst sh1 (var 6))))).
      inv_subst. subst i. eapply tr_sigma_elim2. apply Hru1.
      (*casing on i = j with lambda trick
      suffices: tr G'' (deq
      (lam (bite (app (app eq_b (var 1)) i)
          (next
             (move_app A make_subseq
                (app (app (subst (sh 12) Et) (var 10)) (var 5))))
          (app (app (app (var 5) (var 3)) make_subseq) (var 1))))
      (lam (bite (app (app eq_b (var 1)) i)
          (next
             (move_app A make_subseq
                (app (app (subst (sh 12) Et) (var 10)) (var 5))))
          (app (app (app (var 5) (var 3)) make_subseq) (var 1))))
      (arrow (equal (app (app eq_b (var 0)) i) (app (app eq_b (var 0)) i) booltp)
             (app (app (app (var 7) (var 0)) (next (var 3)))
                  (next (var 2))))).
        intros Hlam. 
        suffices: (tr G'' (oof triv (equal booltp (app (app eq_b (var 0)) i)
                                           (app (app eq_b (var 0)) i)))). 
        intros Harg. *) match goal with |- tr ?G (deq ?M ?M ?T) =>
replace M with 
    (subst1 triv
(bite (app (eq_b (var 1)) (shift 1 i))
                    (next
                       (move_app A 
                (make_subseq_trans (var 10) (var 7) 
                   (var 3) (var 6) (var 2))

                          (app
                             (app (subst (sh 12) Et)
                                (var 10)) 
                             (var 9))))
                    (app
                       (app (app (var 5) (var 3))
                          (var 2)) 
                       (var 1)))) end.
2:{ subst. simpsub_bigs. auto.
     } 
        eapply (tr_compute _ _ _ _ 
           ( app 
              (lam
                 (bite (app (eq_b (var 1)) (shift 1 i))
                    (next
                       (move_app A 
                (make_subseq_trans 
                   (var 10) (var 7) 
                   (var 3) (var 6) 
                   (var 2))

                          (app
                             (app (subst (sh 12) Et)
                                (var 10)) 
                             (var 9))))
                    (app
                       (app (app (var 5) (var 3))
                          (var 2)) 
                       (var 1)))) triv)).
        apply equiv_refl.
        apply equiv_symm.
        apply reduce_equiv.
apply reduce_app_beta; apply reduce_id.
        apply equiv_symm.
        apply reduce_equiv.
        apply reduce_app_beta; apply reduce_id.
        apply (tr_arrow_elim _
                 (equal booltp (app (eq_b (var 0)) i)
                    (app (eq_b (var 0)) i))).
        apply tr_equal_formation. weaken tr_booltp_formation.
        apply eqapp_typed; auto. subst. var_solv.
        apply eqapp_typed. subst; var_solv. assumption.
        subst.
        apply pw_app_typed; try apply tr_fut_intro; try var_solv.
        match goal with |- tr ?G' (@ deq obj ?M ?M ?T) => replace M with
            (subst1 (app (eq_b (var 0))  i)
                    ( lam (
                      bite (var 1)
          (next
             (move_app A 
                   (make_subseq_trans (var 11) 
                      (var 8) (var 4) (var 7) 
                      (var 3))

                (app
                   (app (subst (sh 13) Et)
                      (var 11)) 
                   (var 10))))
          (app
             (app (app (var 6) (var 4))
                  (var 3)) (var 2))))
            );
  replace T with (
       subst1 (app (eq_b (var 0)) i)
       (arrow
          (equal booltp (var 0)
             (app (eq_b (var 1)) (shift 1 i)))
       (shift 1 (app (app (app (var 7) (var 0)) (next (var 3)))
                     (next (var 2)))))) end. 
        2: { simpsub_bigs. auto.
     }
        2: { unfold subst1. simpsub_bigs. auto.
     }
        rewrite fold_substj.
        eapply (tr_generalize _ booltp).
        apply eqapp_typed; try (subst; var_solv). assumption.
        apply tr_arrow_intro.
        apply tr_equal_formation. weaken tr_booltp_formation.
        rewrite - (@subst_booltp obj (sh 1)). var_solv0.
        apply eqapp_typed; auto. subst. var_solv.
        rewrite - (subst_nat (sh 1)) subst_sh_shift.
        apply tr_weakening_append1. assumption.
        unfold deqtype.
        change triv with (@shift obj 1 triv).
        inv_subst. rewrite ! subst_sh_shift.
        apply tr_weakening_append1. 
        apply pw_app_typed; subst;
          try apply tr_fut_intro; try var_solv.
        simpsub. (*make a template for this casing reasoning*)
        rewrite - cat1s.
        match goal with |- tr ?G (deq ?M ?M ?T) =>
      replace M with  (bite (var 1)
         (subst (under 1 sh1) (next
             (move_app A 
                (make_subseq_trans (var 10) 
                   (var 7) (var 3) (var 6) (var 2))

                (app (app (subst (sh 12) Et) (var 10)) (var 9)))))
         (subst (under 1 sh1) (app (app (app (var 5) (var 3)) (var 2))
                                   (var 1)))) end.
        2:{
          simpsub_bigs. auto.
        }
        apply tr_booltp_eta_hyp.
      + (*i= j *) simpsub_bigs. simpsub_bigs.
        eapply (tr_eqtype_convert _ _ _ 
                                  (app (app (app (var 8) (shift 1 i)) (next (var 4))) (next (var 3)))).
        (*convert from u1 j u2 l2 to u1 i u2 l2*)
        apply pw_app_typed; try apply tr_fut_intro; try (subst; var_solv).
        apply tr_symmetry. apply eqb_P.
        subst; var_solv.
        rewrite - (subst_nat (sh 1)) subst_sh_shift.
        apply tr_weakening_append1. assumption.
        apply tr_symmetry.
       apply (deq_intro _#4 (var 0) (var 0)).
        match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
            (subst (sh 1)
       (equal booltp btrue (app (eq_b (var 0)) i))) end.
        var_solv0. simpsub_bigs. auto. 
        (*convert from u1 i u2 l2 to |>(A @ u2, l2)*)
        eapply (tr_eqtype_convert _ _ _
                                  (fut (trans_type (var 4) (var 3) A))).
        simpsubin_bigs Hp.
        apply tr_eqtype_symmetry. apply (deqtype_intro _ _ _
                                                       (app (shift 1 p) (var 3))
                                                       (app (shift 1 p) (var 3))
                                        ).
        match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
       (subst1 (var 3) (eqtype
          (app
             (app (app (var 9) (shift 2 i))
                (next (var 5))) 
             (next (var 0)))
          (fut (trans_type (var 5) (var 0) A)))) end.
        2:{
          simpsub_bigs. rewrite fold_subst1 subst1_trans_type. simpsub_bigs. auto.
        }
        apply (tr_pi_elim _ nattp).
        match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
       (subst1 (var 4) 
       (pi nattp
          (eqtype
             (app
                (app (app (var 10) (shift 3 i))
                   (next (var 1)))
                (next (var 0)))
             (fut (trans_type (var 1) (var 0) A))))) end.
        eapply (tr_all_elim _ nzero preworld).
        move : Hp. simpl. simpsubs.
        replace (dot (var 0)
                         (dot (var 1)
                              (dot (subst (sh 2) i) (sh 2)))) with
            (under 2 (dot i id)).
        2:{
          simpsub_bigs. auto.
        } rewrite subst1_under_trans_type. simpsub_bigs.
        move => Hp. 
        match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
       (shift 1 
       (all nzero preworld (pi nattp
          (eqtype
             (app
                (app (app (var 9) (subst (sh 2) i))
                   (next (var 1)))
                (next (var 0)))
             (fut (trans_type (var 1) (var 0) A)))))) end.
        2: {
          simpsub_bigs. auto.
          replace (dot (var 0) (dot (var 1) (sh 3))) with
              (@under obj 2 (sh 1)).
          2:{
            simpsubs. auto.
          } rewrite sh_under_trans_type. auto. }
        rewrite ! subst_sh_shift. apply tr_weakening_append1.
        rewrite - subst_sh_shift. assumption.
        subst; var_solv.
sh_var 1 10. replace (shift 3 i) with (shift 1 (shift 2 i)).
weaken ref2_type; try (subst; var_solv).
rewrite - (subst_nat (sh 2)) subst_sh_shift. apply tr_weakening_append2. assumption.
simpsub_bigs. auto.
simpsub_bigs. auto.
replace (dot (var 0) (dot (var 5) sh1)) with (@under obj 1 (dot (var 4) id)).
2:{
simpsub. auto.
} 
rewrite subst1_under_trans_type. simpsub_bigs. auto.
subst; var_solv.
(*show move (Et @ u l) : A @ U2*)
subst.
constructor. apply (@moveapp_works _ _ (var 11) (var 10)); auto; try var_solv. simpl. 
(*U <= U2*) 
apply (subseq_trans (var 8)); auto; try var_solv.
sh_var 3 8. inv_subst. rewrite subst_sh_shift. var_solv.
sh_var 7 11. inv_subst. rewrite subst_sh_shift. var_solv.
eapply apply_IH; try apply IHDtrans2; try var_solv.
sh_var 10 11. inv_subst. rewrite subst_sh_shift. var_solv.
      + (*i != j *) simpsub_bigs. simpsub_bigs. subst.
        eapply (@store_works (var 7)); try (subst; var_solv).
        sh_var 6 8. inv_subst. rewrite - subst_store.
        var_solv0.
        sh_var 3 8. inv_subst. 
        var_solv0.
        simpsub_bigs. auto.
        constructor. apply eqapp_typed; try (subst; var_solv). assumption.
        constructor.
        weaken compm5_type; try var_solv; auto.
        simpsub_bigs. constructor.
        sh_var 2 5. rewrite - ! subst_sh_shift. weaken compm4_type; try var_solv; auto.
constructor. }
(*ref case*)
  2: { apply comp_front. (*is a valid intro form for comp type*)
       simpsub_bigs. simpsubs.
       apply inl_laters_type. 
         { simpsub_bigs.
         sh_var 2 5. inv_subst.
         weaken compm3_type; try var_solv; auto.
              match goal with |- tr ?G (oof ?T U0) =>
                              replace T with (trans_type (var 1)
                                             (var 0) (reftp_m A)) end.
              apply trans_type_works; try var_solv; auto.
              simpsub_bigs. simpsub_bigs. auto. }
       remember (lam
                (lam
                   (subst1 (prev ((var 0)))
                      (subst1 (prev ((var 2)))
                              (fut (trans_type ((var 0)) ((var 1)) A)))))) as x.
       assert (x = lam
    (lam (fut (trans_type (prev (var 1)) (prev (var 0)) A)))) as Heq1x. subst x.
       unfold subst1. rewrite ! subst_fut ! fold_subst1 ! subst1_trans_type.
               do 2 simpsubs. auto. 
         remember (cons_b ((var 3)) ((var 2)) x) as u1. (*u1 = u::A*)
         remember (ppair u1 (nsucc (var 2))) as U1.
        - (*u1 : preworld*)
         match goal with |- tr ?D' ?J => assert (forall G', tr G' (oof x (karrow (fut preworld)
                                                                    (arrow (fut nattp) U0)
                                              ))) as Hx end. 
         subst x. move =>>. apply tr_karrow_intro; try assumption; auto.
         simpsub_big_T.
         apply tr_arrow_intro; try assumption; auto.
         simpsub_big_T. change (univ nzero) with (@ subst1 obj (prev (var 0)) (univ nzero)).
         apply (tr_fut_elim _ _ _ nattp). var_solv. inv_subst. auto.
         change (univ nzero) with (@ subst1 obj (prev (var 2)) (univ nzero)).
         apply (tr_fut_elim _ _ _ preworld). var_solv. inv_subst. auto.
         constructor. apply trans_type_works; try var_solv; auto.
         auto.
         match goal with |- tr (?a::?b::?G') ?J => assert (forall x y, tr (x::y::G') (oof u1 preworld))
                           as Hu1 end.
         intros. subst. apply consb_typed; try assumption; try var_solv; auto.
        - (*U1 : world*) 
         match goal with |- tr ?G' ?J => assert (tr G' (oof U1 world)) as HU1 end.
         subst. apply world_pair; try (apply Hu1); apply nsucc_nat; var_solv; auto. subst U1.
         (*new reference is at world U1*)
         eapply (tr_exist_intro _ _ _ _ u1); auto.
         2: { sh_var 2 5. rewrite - ! subst_sh_shift.
              comptype; try var_solv.
              match goal with |- tr ?G (oof ?T U0) =>
                              replace T with (trans_type (var 1)
                                             (var 0) (reftp_m A)) end.
              apply trans_type_works; try var_solv; auto. simpl. simpsub_bigs. auto. 
         }
         simpsub_bigs. simpsub_type; auto.
         (*split up nat from pair*)
         apply tr_sigma_intro. apply nsucc_nat. var_solv.
         (*<p1, <l, <*, \_:nat.*>>>: <u, l> <= <u1, l1> x storeU1 x ref(A)@U1) *)
         (*7862 has appeared here, wasnt there at start of ref*)
         simpsub_bigs.
         (*showing U <= U1*)
         + assert (tr [:: hyp_tm (store (var 2) (var 1));
                       hyp_tm (subseq (var 4) (var 3) (var 1) (var 0)); hyp_tm nattp; hyp_tm preworld; hyp_tm (Gamma_at G (var 1) (var 0)); hyp_tm nattp; hyp_tm preworld]
                    (deq make_subseq make_subseq
                         (subseq  (var 3) (var 2) u1 (nsucc (var 2)))))
             as HUsubU1. (*m1*)
           subst. apply consb_subseq; try (apply Hx); try var_solv.
           apply tr_prod_intro; try assumption.
           apply tr_prod_intro. assumption.
           (*showing the new store is a store at U1*)
           subst u1. unfold store.
           apply tr_all_intro; auto. simpsub_bigs.
      apply tr_pi_intro; auto. apply tr_arrow_intro; auto. apply subseq_type; auto.
      (*ltac for showing (sh 2 U1) to be a world in context grown by 2*)
      Ltac u1_pw2 := sh_var 2 5; inv_subst; match goal with |- tr (?a::?b::?G') ?J => change (a::b::G') with ([::a; b] ++ G') end; rewrite - (subst_pw (sh 2)) ! subst_sh_shift; apply tr_weakening_append.
      apply world_pair. u1_pw2. apply Hu1. apply nsucc_nat; var_solv. 
      2: { unfold gettype. simpsub_bigs. apply tr_pi_intro; auto.
           eapply (tr_compute _ _ _ _ _ _ _ reduce_consb); try (apply equiv_refl).
(*match goal with |- tr ?G' (@ deq obj ?M ?M ?T) => change M with M end.
  literally what ask karl
 *)
(*case on whether index is < l = size u*) 
match goal with |- tr ?G' (@ deq obj ?M ?M ?T) => replace M with 
       (subst1 (ltb_app (var 0) (var 6)) (bite (var 0)
          (app
             (app (app (var 5) (var 3))
                (make_subseq_trans 
                   (var 7) (nsucc (var 7))
                   (var 3) make_subseq 
                   (var 2))) (var 1)) 
          (next
             (move_app A 
                (make_subseq_trans 
                   (var 10) (var 7) 
                   (var 3) (var 6)
                   (make_subseq_trans 
                      (var 7) (nsucc (var 7))
                      (var 3) make_subseq
                      (var 2)))
                (app
                   (app (subst (sh 12) Et)
                      (var 10)) 
                   (var 9)))))); replace T with
(subst1 (ltb_app (var 0) (var 6))
       (app
          (app
             (bite
               (var 0) 
                (app (var 8) (var 1))
                (shift 5 x))
             (next (var 4)))
          (next (var 3))))
end.
2, 4: (simpsub_bigs; auto). rewrite fold_substj.
eapply (tr_generalize _ booltp).
apply ltapp_typed; try var_solv.
match goal with |- tr ?G (deq (bite ?M1 ?M2 ?M3) ?M4 ?T) =>
change M2 with
    (subst sh1 
          (app
             (app (app (var 4) (var 2))
                (make_subseq_trans 
                   (var 6) (nsucc (var 6))
                   (var 2) make_subseq 
                   (var 1))) (var 0)));
  replace M3 with
         (subst sh1 (next
             (move_app A
                (make_subseq_trans 
                   (var 9) (var 6) 
                   (var 2) (var 5)
                   (make_subseq_trans 
                      (var 6) (nsucc (var 6))
                      (var 2) make_subseq
                      (var 1)))
                (app
                   (app (subst (sh 11) Et)
                      (var 9)) 
                   (var 8))))) end.

2: { simpsub_bigs. auto. }
     apply tr_booltp_eta_hyp0.
           - (*case: i < l*)
             simpsub_bigs. (*beta reduce the type*)
             match goal with |- (tr ?G' (deq ?M ?M ?T)) => assert (equiv T
                                                                       (app (app (app (var 7) (var 0)) (next (var 3))) (next (var 2)))) as HeqT end.
             + do 2 (apply equiv_app; try apply equiv_refl). apply reduce_equiv.
               apply reduce_bite_beta1; apply reduce_id.
             eapply (tr_compute _ _ _ _ _ _ _ HeqT);
               try (apply equiv_refl). clear HeqT.
             match goal with |- tr ?G' (deq ?M ?M ?T) => change T with
                 (@ subst1 obj (var 0) (app (app (app (var 8) (var 0)) (next (var 4)))
                                     (next (var 3)))) end.
             apply (tr_pi_elim _ nattp); auto.
             (*showing 4: store(U)*)
             apply (tr_arrow_elim _ (subseq (ppair (var 7) (var 6)) (ppair (var 3) (var 2)))).
             apply subseq_type; auto.
             apply tr_pi_formation; auto.
             apply pw_app_typed; try apply tr_fut_intro; try var_solv.
             match goal with |- tr ?G' (deq ?M ?M ?T) => change T with
                 (@ subst1 obj (var 2) (arrow (subseq (ppair (var 8) (var 7)) (ppair (var 4) (var 0)))
                                           (pi nattp
                                               (app (app (app (var 9) (var 0)) (next (var 5)))
                                                    (next (var 1)))))) end.
             apply (tr_pi_elim _ nattp); auto.
             match goal with |- tr ?G' (deq ?M ?M ?T) =>
                             change T with
                 (subst1 (var 3) (pi nattp (arrow
                                              (subseq
                                                 (ppair (var 9) (var 8))
                                                 (ppair (var 1) (var 0)))
                                              (pi nattp (app (app (app (var 10)
                                                                       (var 0))
                                                                  (next (var 2)))
                                                             (next (var 1))))))
                 ) end.
             eapply (tr_all_elim _ nzero preworld).
             match goal with |- tr ?G' (deq ?M ?M ?T) =>
                             change T with
       (subst (sh 5) (all nzero preworld
          (pi nattp
             (arrow
                (subseq
                   (ppair (var 4) (var 3))
                   (ppair (var 1) (var 0)))
                (pi nattp
                   (app
                      (app
                         (app (var 5) (var 0))
                         (next (var 2)))
                      (next (var 1)))))))) end.
             var_solv0. var_solv.
             sh_var 1 10. inv_subst. rewrite ! subst_sh_shift. apply store_type1; auto. var_solv.
             (*showing U <= U2*)
             + simpsub_bigs. eapply (@subseq_trans (var 1) make_subseq _
                                                  (ppair ((cons_b (var 7) (var 6) (shift 4 x)))
                                                   (nsucc (var 6)))).
               * (*U1 <= U2*)
                 replace (shift 4 x) with (shift 2 (shift 2 x)). sh_var 2 7.
               inv_subst. var_solv0. unfold cons_b. simpsub_big. apply Sequence.index_0. simpsub_big. auto.
               * (*U<= U1*) 
                 sh_var 4 7. inv_subst. rewrite make_app4.
                 rewrite - (subst_make_subseq (sh 4)) ! subst_sh_shift.
                 apply tr_weakening_append. assumption.
                 var_solv.
           - (*i >= l*)
             Hint Unfold subst1 : subst1.
             simpsub_bigs. 
             + (*beta reduce the type*)
               remember (app (app (subst (sh 4) x) (next (var 3))) (next (var 2))) as T0.
               remember (app (subst1 (next (var 3)) (lam (fut (trans_type (prev (var 1)) (prev (var 0)) A)))) (next (var 2))) as T1.
               remember (subst1 (next (var 2))
                         (fut (trans_type (prev (next (var 4))) (prev (var 0)) A))) as T2.
               match goal with |- (tr ?G' (deq ?M ?M ?T)) => assert (equiv T T0) as Heq0 end.
             subst. do 2 (apply equiv_app; try apply equiv_refl). apply reduce_equiv.
             apply reduce_bite_beta2; apply reduce_id.
             assert (equiv T0 T1) as Heq1.
             subst. rewrite Heq1x. apply equiv_app; try apply equiv_refl.
             apply reduce_equiv. rewrite subst_lam.
             apply reduce_app_beta; [simpsub_bigs; rewrite subst_trans_type; auto | ..];
               apply reduce_id.
             unfold subst1 in HeqT1.
             rewrite subst_lam subst_fut subst1_under_trans_type in HeqT1.
             simpsubin_bigs HeqT1.
             assert (equiv T1 T2) as Heq2.
             subst. apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
             assert (equiv T2 (fut (trans_type (var 3) (var 2) A))) as Heq3.
             subst. simpsub. rewrite subst1_trans_type. do 2 simpsubs. apply equiv_fut.
             apply trans_type_equiv; apply reduce_equiv; constructor; apply reduce_id.
    move : (equiv_trans _#4 (equiv_trans _#4 ( equiv_trans _#4 Heq0 Heq1) Heq2) Heq3)
             => HeqT.
             eapply (tr_compute _ _ _ _ _ _ _ HeqT);
               try (apply equiv_refl).
             clear T0 T1 T2 HeqT0 HeqT1 HeqT2 Heq0 Heq1 Heq2 Heq3 HeqT.
             apply tr_fut_intro. simpl.
             - (*showing next(move A (m2 o m1 o m) (e @W)) : |>(T @ U2) *)
               apply (@moveapp_works _ _ (var 10) (var 9) (var 3) (var 2)); try (apply world_pair; var_solv).
             assert (forall w l x, cons_b w l x = lam (let i := (var 0) in
                                                  bite (ltb_app i (shift 1 l)) (app (shift 1 w) i) (shift 1 x))) as fold_consb. auto.
             remember (cons_b (var 3) (var 2) x) as u1.
             replace (lam (bite (ltb_app (var 0) (var 5))
                                 (app (var 6) (var 0))
                                 (subst (sh 3) x))) with (shift 2 u1);
               last by subst; unfold cons_b; simpsub_bigs; auto.
             (*showing m2 o m1 o m : W <= U2*)
             match goal with |- tr ?G' ?J =>
                             suffices: (Datatypes.prod (tr G' (oof make_subseq
                                                   (subseq (ppair (var 10) (var 9))
                                                           (ppair (shift 4 u1) (nsucc (var 6)))
                                       )))
                                       (tr G' (oof (var 1)
                                                   (subseq (ppair (shift 4 u1) (nsucc (var 6)))
                                                           (ppair (var 3) (var 2)))
                                       ))) end.
             move => [Hsub1 Hsub2]. apply (subseq_trans _ _ _ _ _ _ Hsub2 Hsub1). split.
             (*showing m1 o m : W <= U1*)
             match goal with |- tr ?G' ?J =>
                             suffices: (Datatypes.prod (tr G' (oof (var 5)
                                                   (subseq (ppair (var 10) (var 9))
                                                           (ppair (var 7) (var 6)))
                                       ))
                                       (tr G' (oof make_subseq
                                                   (subseq (ppair (var 7) (var 6))
                                                           (ppair (shift 4 u1) (nsucc (var 6)))
                                       )))) end.
             move => [Hsub11 Hsub12]. apply (subseq_trans _ _ _ _ _ _ Hsub12 Hsub11). split.
             (*showing m: W <= U*)
             sh_var 5 10. inv_subst. rewrite ! subst_sh_shift make_app5.
             apply tr_weakening_append. sh_var 1 5. inv_subst. var_solv.
             (*showing m1: U <= U1*)
             simpl. rewrite - (subst_sh_shift _ 4). sh_var 4 7. inv_subst. rewrite make_app4.
             rewrite - (subst_make_subseq (sh 4)) ! subst_sh_shift.
             apply tr_weakening_append. assumption.
             (*showing m2: U1 <= U2*)
             replace (shift 4 u1) with (shift 2 (shift 2 u1)); last by
             simpsub_bigs; auto. sh_var 2 6.
             inv_subst. rewrite make_app2. subst. var_solv.
             - (*showing Et l G : A@W*)
               apply (tr_arrow_elim _ (Gamma_at G (var 10) (var 9))); auto.
               apply Gamma_at_type; try var_solv; auto. trans_type.
               match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
                   (subst1 (var 9) (arrow (Gamma_at G (var 11) (var 0))
                                          (trans_type (var 11) (var 0) A))) end.
               2: { simpsub. unfold subst1 at 1.
                    rewrite subst1_Gamma_at subst1_trans_type. simpsub. auto.
               }
               apply (tr_pi_elim _ nattp).
               match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
                   (subst1 (var 10) (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                          (trans_type (var 1) (var 0) A)))) end.
               2: { unfold subst1. rewrite subst_pi subst_arrow. 
                    rewrite subst1_under_Gamma_at subst1_under_trans_type.
                    simpsub_bigs. auto.
               }
               apply (tr_all_elim _ nzero preworld); try var_solv.
               match goal with |- tr ?G' (deq ?M ?M ?T) =>
                               rewrite - (cats0 G'); replace T with
                                                         (subst (sh 11) T) end.
               2: {rewrite subst_all subst_pi subst_arrow.
                   rewrite under_sum sh_under_Gamma_at sh_under_trans_type.
                   simpsub_bigs. auto.
               }
               rewrite ! subst_sh_shift. apply tr_weakening_append.
               apply IHDtrans. change (var 1) with (@ shift obj 1 (var 0)).
               apply trans_type_works; try var_solv1; var_solv. var_solv.
               sh_var 9 10. inv_subst. var_solv0.
               simpsub_bigs. auto.
      }
      { (*small typing goal*)
                 apply gettype_typed. sh_var 2 5. rewrite - ! subst_sh_shift - subst_consb - (subst_pw (sh 2)) ! subst_sh_shift make_app2.
                 apply tr_weakening_append. apply Hu1. simpl. auto.
      }
      { (*2: ref A*)
                 change (dot (var 0) (dot (var 1) (dot (var 2)
                                                       (dot (nsucc (var 5))
                                                            (sh 3))))) with
                     (@ under obj 3 (dot (nsucc (var 2)) id)).
                 rewrite subst1_under_trans_type.
                 simpsub_bigs.
                 constructor. var_solv.
                 simpsub_bigs. apply tr_prod_intro. apply nsucc_lt. var_solv.
                 { (*\lv.<> : (U1 v lv)[l] = |> tau @ <v, lv>*)
                   constructor; auto.
                   change (dot (var 0) (dot (var 1)
                                       (dot (var 4) (sh 2))))
                     with (@under obj 2 (dot (var 2) id)).
                   rewrite subst1_under_trans_type.
                   simpsub_bigs.
                   constructor; auto.
                   (*(U1 v lv)[l] = |> tau @ <v, lv> *)
                   subst u1. simpsub_bigs.
                   rewrite Heq1x. simpsub_type; auto. 
                   eapply tr_eqtype_transitivity.
                   -(*(U1 v lv)[l] = subst1 subst1 x*)
                     eapply tr_formation_weaken.
                     apply reduce_consb_end; try var_solv; try
                                                             (constructor ; var_solv); auto.
                     rewrite - Heq1x. apply Hx.
                     unfold subst1. rewrite ! subst_fut ! fold_subst1
                                            subst1_under_trans_type subst1_trans_type.
                     simpsub.
                     eapply tr_compute.
                     (*next prev -> now *)
                     eapply equiv_eqtype; first by (apply equiv_fut; apply trans_type_equiv;
                     (apply reduce_equiv; apply reduce_prev_beta; apply reduce_id)).
                     apply equiv_refl.
                     apply equiv_refl.
                     apply equiv_refl.
                     constructor. weaken trans_type_works; try var_solv; auto.
                     simpl. auto. }
                   change (nsucc (var 3)) with (@shift obj 1 (nsucc (var 2))).
                   weaken ref0_type; auto. apply trans_type_works; try var_solv; auto.
}
(*bind ref*) 
replace 
          (sigma nattp
             (prod (ltpagetp (var 0) (var 1))
                (all nzero preworld
                   (pi nattp
                      (eqtype
                         (app
                            (app
                               (app
                                 (subst (sh 4) u1)
                                 (var 2))
                               (next (var 1)))
                            (next (var 0)))
                         (fut
                            (trans_type 
                               (var 1) 
                               (var 0) A))))))) with
    (trans_type (shift 1 u1) (var 0) (reftp_m A)).
      2: {
simpl. simpsub_bigs. auto.
      }
      weaken compm5_type; try var_solv; auto; try apply trans_type_works; try var_solv; apply world_pair; try var_solv;
      rewrite - (subst_pw sh1) ! subst_sh_shift;
      apply tr_weakening_append1; auto.
  }
{ apply comp_front.
    simpsub. rewrite subst_bind.
    simpsub_big. simpl.
    eapply (bind_type _
                      (exist nzero preworld (
                                          sigma nattp (*l1 = 6 u := 5, l := 4, v= 1, lv := 0*)
                                          (let u := Syntax.var 5 in
                                              let l := Syntax.var 4 in
                                              let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let U := ppair u l in
                                              let V := ppair v lv in
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq U V) (store v lv))
                                                     (trans_type v lv A))))
           ).
    (*at make_bind*)
  replace (@ ppair obj (var 5) (var 4)) with (@ subst obj (sh 2) (ppair (var 3) (var 2))); auto. 
    eapply (tr_arrow_elim _  (store (var 3) (var 2))); auto.
- 
  simpl.
  sh_var 2 5. rewrite - ! subst_sh_shift - ! subst_ppair.
              comptype.
  (*engage Et1 *)
  eapply tr_arrow_elim.
  apply (subseq_type _
                     (ppair (var 6) (var 5))
                     (ppair (var 3) (var 2))); auto. simpl.
  comptype. simpl. 
replace 
       (arrow
          (subseq (ppair (var 6) (var 5))
             (ppair (var 3) (var 2)))
          (arrow
             (store (var 3) (var 2))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (prod
                         (prod
                            (subseq
                              (ppair 
                              (var 5) 
                              (var 4))
                              (ppair 
                              (var 1) 
                              (var 0)))
                            (store
                              (var 1) 
                              (var 0)))
                         (trans_type 
                            (var 1) 
                            (var 0) A)))))))
 with
(subst1 (var 2) 
       (arrow
          (subseq (ppair (var 7) (var 6))
             (ppair (var 4) (var 0)))
          (arrow (store (var 4) (var 0))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (prod
                         (prod
                            (subseq (ppair (var 6) (var 2))
                               (ppair (var 1) (var 0)))
                            (store (var 1) (var 0)))
                         (trans_type (var 1) (var 0) A)))))))).
2: {
 simpsub_type; auto.
}
eapply (tr_pi_elim _ nattp).
(*add the forall*)
  replace 
       (pi nattp
          (arrow
             (subseq (ppair (var 7) (var 6))
                (ppair (var 4) (var 0)))
             (arrow
                (store (var 4) (var 0))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq
                                (ppair 
                                (var 6) 
                                (var 2))
                                (ppair 
                                (var 1) 
                                (var 0)))
                               (store
                                (var 1) 
                                (var 0)))
                            (trans_type 
                               (var 1) 
                               (var 0) A))))))))
 with
(subst1 (var 3) (pi nattp
          (arrow
             (subseq (ppair (var 8) (var 7))
                (ppair (var 1) (var 0)))
             (arrow (store (var 1) (var 0))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq (ppair (var 3) (var 2))
                                  (ppair (var 1) (var 0)))
                               (store (var 1) (var 0)))
                            (trans_type (var 1) (var 0) A))))))))).
  2: {
     simpsub_type; auto. }
  eapply (tr_all_elim _ nzero preworld).
  (*put the g back on*)
match goal with |- tr ?G (deq ?M ?M ?T) =>
                replace T with
    (trans_type (var 6) (var 5) (comp_m A)) end.
eapply tr_arrow_elim. apply (@Gamma_at_type _ G); auto. 
weaken trans_type_works; try var_solv; auto.
simpl. simpsub_type; auto. simpsub. simpl.
(*have to get type in the form subst1 lv type
 for the pi elim rule*)
replace (arrow (Gamma_at G (var 6) (var 5))
          (all nzero preworld
             (pi nattp
                (arrow
                   (subseq (ppair (var 8) (var 7)) (ppair (var 1) (var 0)))
                   (arrow (store (var 1) (var 0))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (var 1) (var 0)))
                                  (trans_type (var 1) (var 0) A)))))))))) with
    (subst1 (var 5)
(arrow (Gamma_at G (var 7) (var 0))
          (all nzero preworld
             (pi nattp
                (arrow
                   (subseq (ppair (var 9) (var 2)) (ppair (var 1) (var 0)))
                   (arrow (store (var 1) (var 0))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (var 1) (var 0)))
                                  (trans_type (var 1) (var 0) A)))))))))
    )).
2: {  simpsub_type; auto. rewrite subst1_Gamma_at; auto. }
apply (tr_pi_elim _ nattp).
match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
    (subst1 (var 6)
       (pi nattp
          (arrow (Gamma_at G (var 1) (var 0))
             (all nzero preworld
                (pi nattp
                   (arrow
                      (subseq (ppair (var 3) (var 2))
                         (ppair (var 1) (var 0)))
                      (arrow (store (var 1) (var 0))
                         (laters
                            (exist nzero preworld
                               (sigma nattp
                                  (prod
                                     (prod
                                        (subseq
                                         (ppair (var 3) (var 2))
                                         (ppair (var 1) (var 0)))
                                        (store (var 1) (var 0)))
                                     (trans_type 
                                        (var 1) 
                                        (var 0) A)))))))))))) end.
2: {  simpsub_type; auto.
     change (dot (var 0) (dot (var 7) sh1)) with
(@ under obj 1 (dot (var 6) id)). rewrite subst1_under_Gamma_at. auto.
}
eapply (tr_all_elim _ nzero preworld). 
match goal with |- tr ?G (deq ?M ?M ?T) =>
               (replace T with
                    (shift 7 T)) end.
2: {  simpsub_type; auto. 
change (dot (var 0)
            (dot (var 1) (sh 9))) with (@ under obj 2 (sh 7)).
rewrite sh_under_Gamma_at. simpsub. auto. }
match goal with |- tr ?G' ?J => rewrite - (cats0 G'); change (sh 7)
with (@ sh obj (size G')); rewrite ! subst_sh_shift
end. apply tr_weakening_append.
match goal with |- tr ?G (deq ?M ?M (all _ _ (pi _ (arrow _ ?T)))
                        ) =>
                replace T with (trans_type (var 1) (var 0) (comp_m A)) end.
eapply IHDtrans1; try assumption. simpsub_type; auto.
eapply split_world1; auto.
match goal with |- tr ?G (deqtype (pi _ (arrow _ ?T)) ?J
                        ) =>
                replace T with
    (trans_type (var 1) (var 0) (comp_m A)) end.
change (var 1) with (@ shift obj 1 (var 0)).
apply trans_type_works; try var_solv1; auto.
var_solv.
simpsub_type; auto.
var_solv. replace (Gamma_at G (var 6) (var 5)) with
              (shift 5 (Gamma_at G (var 1) (var 0))). rewrite - subst_sh_shift.
try (apply tr_hyp_tm; repeat constructor).
rewrite - subst_sh_shift. change (sh 5) with (@ under obj 0 (sh 5)).
rewrite sh_under_Gamma_at. auto.
simpsub_type; auto. var_solv. eapply tr_formation_weaken; apply compm0_type.
apply world_pair; var_solv. apply trans_type_works; try var_solv; auto. var_solv.
replace (subseq (ppair (var 6) (var 5))
                (ppair (var 3) (var 2))) with (subst (sh 2)
(subseq (ppair (var 4) (var 3)) (ppair (var 1) (var 0)))); auto.
apply tr_hyp_tm; repeat constructor.
replace (store (var 3) (var 2))
  with (subst (sh 1) (store (var 2) (var 1))); auto.
apply tr_hyp_tm; repeat constructor.
(*done with et1, ramping up to et2*)
- simpl.
 rewrite subst_bind.
 simpsub_big.  
 apply tr_arrow_intro; try (sh_var 2 5; rewrite - ! subst_sh_shift - ! subst_ppair;
 comptype). simpsub_big. simpl.
 (*type of Et2 depends on v so need to get v out before applying bind_type*)
 match goal with |- tr ?G' (deq ?M ?M ?T) => replace M with
     (subst1 (var 0) 
       (make_bind (app
          (app
             (app
                (app
                   (app (subst (sh 9) Et2)
                      (ppi1 (var 0)))
                   (ppair (picomp4 (var 0))
                      (move_gamma G make_subseq (var 6))))
                (ppi1 (var 0))) make_subseq)
          (picomp3 (var 0)))
          (lam
               (ret_a (ppair (picomp1 (var 0))
                      (ppair (ppair make_subseq (*z2 \circ z1*)
                       (picomp3 (var 0))) (picomp4 (var 0)))                         
                                                        ))
     ))) end.
 2 : {
unfold subst1. rewrite subst_bind. simpsub_big. auto. 
 }
(*get v and lv separate*)
 eapply (tr_exist_elim _ (subst (sh 1) nzero)
                         (subst (sh 1) preworld)
             (subst (under 1 (sh 1)) (sigma nattp
                (prod
                   (prod
                      (subseq (ppair (var 5) (var 4))
                         (ppair (var 1) (var 0)))
                      (store (var 1) (var 0)))
                   (trans_type (var 1) (var 0) A)))) ).
 rewrite - subst_exist; auto.
 - var_solv0. simpsub; apply pw_type.
 - simpsub_big. simpl. replace (ppair (var 6) (var 5)) with
                        (@ subst obj (sh 2) (ppair (var 4) (var 3))); auto. comptype. simpsub_type; try apply trans_type_works; try var_solv; auto.
(*at make_bind*)
 rewrite subst_bind. simpsub_big. simpl.
 eapply (bind_type  _
                      (exist nzero preworld (
                                          sigma nattp                                           (let v := Syntax.var 3 in
                                              let lv := ppi1 (Syntax.var 2) in
                                              let v1 := Syntax.var 1 in
                                              let lv1 := Syntax.var 0 in
                                              let V := ppair v lv in
                                              let V1 := ppair v1 lv1 in
                                      prod (prod (subseq V V1) (store v1 lv1))
                                                     (trans_type v1 lv1 B))))
        ) .
(*engage Et2*)
 (*pop the store off*)
eapply (tr_arrow_elim _ (store (var 1) (picomp1 (var 0)))); simpl; auto.
- replace (ppair (var 3) (ppi1 (var 2))) with
    (@ subst obj (sh 2) (ppair (var 1) (ppi1 (var 0)))); auto. comptype.
-
  eapply (tr_arrow_elim _
                        (subseq (ppair (var 1) (picomp1 (var 0)))
                                (ppair (var 1) (picomp1 (var 0)))
                        )). apply subseq_type; auto.
    +   replace (ppair (var 3) (ppi1 (var 2))) with
    (@ subst obj (sh 2) (ppair (var 1) (ppi1 (var 0)))); auto. comptype.
        match goal with |- tr ?G' (deq ?M ?M ?T) =>
                        replace T with 
       (subst1 (ppi1 (var 0)) (arrow
          (subseq (ppair (var 2) (ppi1 (var 1)))
             (ppair (var 2) (var 0)))
          (arrow
             (store (var 2) (var 0))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (prod
                         (prod
                            (subseq
                               (ppair 
                                  (var 4) 
                                   (var 2))
                               (ppair (var 1) (var 0)))
                            (store (var 1) (var 0)))
                         (trans_type (var 1) (var 0) B)))))))) end.
        2: {
simpsub_type; auto. }
apply (tr_pi_elim _ nattp).
(*add the forall*)
        match goal with |- tr ?G' (deq ?M ?M ?T) =>
                        replace T with
       (subst1 (var 1) (pi nattp
          (arrow
             (subseq (ppair (var 3) (ppi1 (var 2)))
                (ppair (var 1) (var 0)))
             (arrow (store (var 1) (var 0))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq
                                  (ppair (var 3) (var 2))
                                  (ppair (var 1) (var 0)))
                               (store (var 1) (var 0)))
                            (trans_type (var 1) (var 0) B))))))))) end.
        2: { simpsub_type; auto.
        }
eapply (tr_all_elim _ nzero preworld).
        apply (tr_arrow_elim _
                             (Gamma_at (A::G) (var 1) (ppi1 (var 0)))).
        apply Gamma_at_type; try var_solv; try var_solv.
        rewrite (subst_trans_type _ _ A); auto.
match goal with |- tr ?G (deqtype ?M ?M) =>
                replace M with
    (trans_type (var 1) (ppi1 (var 0)) (comp_m B)) end.
2: {
simpl. simpsub_type; auto. 
} weaken trans_type_works; try var_solv; auto.
(*have to get type in the form subst1 lv type
 for the pi elim rule*)
match goal with |- (tr ?G' (deq ?M ?M ?T)) =>
                replace T with
    (subst1 (ppi1 (var 0)) 
(arrow (Gamma_at (A::G) (var 2) (var 0))
          (all nzero preworld
             (pi nattp
                (arrow
                   (subseq (ppair (var 4) (var 2))
                           (ppair (var 1) (var 0)))
                   (arrow (store (var 1) (var 0))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (var 1) (var 0)))
                                  (trans_type (var 1) (var 0) B)))))))))
    )) end.
2: { simpsub_big. 
     rewrite subst1_Gamma_at. simpsub_type; auto. }
apply (tr_pi_elim _ nattp).
(*once and forall*)
match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
    (subst1 (var 1)
       (pi nattp
          (arrow (Gamma_at (A::G) (var 1) (var 0))
             (all nzero preworld
                (pi nattp
                   (arrow
                      (subseq (ppair (var 3) (var 2))
                         (ppair (var 1) (var 0)))
                      (arrow (store (var 1) (var 0))
                         (laters
                            (exist nzero preworld
                               (sigma nattp
                                  (prod
                                     (prod
                                        (subseq
                                         (ppair (var 3) (var 2))
                                         (ppair (var 1) (var 0)))
                                        (store (var 1) (var 0)))                                     (trans_type 
                                        (var 1) 
                                        (var 0) B)))))))))))) end.
2: {  simpsub_big; auto.
     change (dot (var 0) (dot (var (1 + 1)%coq_nat) sh1)) with
(@ under obj 1 (dot (var 1) id)). rewrite subst1_under_Gamma_at. simpsub_type; auto.
}
eapply (tr_all_elim _ nzero preworld).
match goal with |- tr ?G' ?J => rewrite - (cats0 G'); change (sh 10)
with (@ sh obj (size G')); rewrite ! subst_sh_shift
end.
match goal with |- tr ?G (deq ?M ?M ?T) =>
                replace T with (shift 10 T) end.
2: {
simpsub_type; auto. rewrite subst_Gamma_at; auto. simpsub_type; auto.
}
apply tr_weakening_append.
match goal with |- tr ?G (deq ?M ?M (all _ _ (pi _ (arrow _ ?T)))
                        ) => replace T with (trans_type (var 1) (var 0) (comp_m B)) end.
2: {
simpsub_type; auto. 
}
eapply IHDtrans2; try assumption; try var_solv; auto.
var_solv.
match goal with |- tr ?G (deqtype (pi _ (arrow _ ?T))
                                 ?T')
                         => replace T with (trans_type (var 1) (var 0) (comp_m B)) end.
2: {
simpsub_type; auto. 
}
change (var 1) with (@ shift obj 1 (var 0)).
apply trans_type_works; try var_solv1; auto. var_solv. auto.
simpl. apply Gamma_at_intro; try var_solv; auto.
eapply (move_gamma_works _ _ (var 9) (var 8)); auto.
eapply (subseq_trans (picomp2 (var 0)) (var 4)
                          _ (ppair (var 6) (var 5))); auto.
match goal with |- tr ?G' (oof ?M ?T) =>
                replace T with
    (subst (sh 5) (subseq (ppair (var 4) (var 3))
                    (ppair (var 1) (var 0))
            )) end.
2: {simpsub_big. auto. }
var_solv0.
match goal with |- tr ?G' (oof ?M ?T) =>
                (replace T with
    (subst (sh 8) (Gamma_at G (var 1) (var 0))
                )) end.
2: { change (sh 8) with (@ under obj 0 (sh 8)).
     rewrite sh_under_Gamma_at. auto. }
var_solv0. simpsub_type; auto. 
var_solv. eapply tr_formation_weaken; apply compm0_type.
match goal with |- tr (?y::(?x::?G')) (oof ?M world) =>                 
           (change M with
                (@subst
                   obj (sh 2) (ppair (var 1) (ppi1 (var 0)))
           ); change (y::x::G') with ([:: y; x] ++ G'))
end.
rewrite - (subst_world (sh 2)) ! subst_sh_shift. apply tr_weakening_append; auto.
apply trans_type_works; try var_solv; auto. auto.
apply subseq_refl; try var_solv; auto.
var_solv0.
simpsub_type; auto. 
- apply tr_arrow_intro; auto.
  + simpl. change (ppair (var 3) (ppi1 (var 2))) with
             (@ subst obj (sh 2) (ppair (var 1) (ppi1 (var 0)))).
comptype.
rewrite ! subst_trans_type; auto.
change (ppair (var 8) (var 7)) with
             (@ subst obj (sh 2) (ppair (var 6) (var 5))).
comptype.
  + simpsub_type; auto. apply inl_laters_type.
    { sh_var 2 9. inv_subst. weaken compm3_type; try var_solv; auto.
      apply world_pair; var_solv. apply trans_type_works; try var_solv; auto.
    }
    match goal with |- (tr ?G' (oof ?M ?T)) => change M with
        (subst1 (var 0)
       (ppair (ppi1 (var 0))
          (ppair
             (ppair make_subseq
                (picomp3 (var 0)))
             (picomp4 (var 0)))))
        end.
    (*split up the most recent existential hypothesis*)
 eapply (tr_exist_elim _ (subst (sh 1) nzero)
                         (subst (sh 1) preworld)
             (subst (under 1 (sh 1)) (sigma nattp
                (prod
                   (prod
                      (subseq (ppair (var 3) (ppi1 (var 2)))
                         (ppair (var 1) (var 0)))
                      (store (var 1) (var 0)))
                   (trans_type (var 1) (var 0) B)))) ); auto.
 rewrite - subst_exist. var_solv0.
    * simpsub_big. simpl.
 change (ppair (var 4) (ppi1 (var 3))) with
     (@ subst obj (sh 2) (ppair (var 2) (ppi1 (var 1)))). comptype.
match goal with |- tr (?x::?G') (oof ?M world) =>                 
           (change M with
                (@subst
                   obj (sh 1) (ppair (var 1) (ppi1 (var 0)))
           ); change (x::G') with ([:: x] ++ G'))
end.
rewrite - (subst_world (sh 1)) ! subst_sh_shift. apply tr_weakening_append; auto. rewrite ! subst_trans_type; auto. apply trans_type_works; try var_solv; auto.
simpsub_type; auto. rewrite ! subst_trans_type; auto.
apply (tr_exist_intro _ _ _ _ (var 1)); auto.
    * var_solv.
      simpsub_big; auto. simpl.
      change (dot (var 0) (dot (var 2) sh1))  with (@ under obj 1 (dot (var 1) id)). rewrite ! subst1_under_trans_type; auto. simpsub. simpl.
      apply tr_sigma_intro; auto.
- simpsub_big. simpl. apply tr_prod_intro.
  + apply tr_prod_intro.
    eapply (subseq_trans (picomp2 (var 0)) (picomp2 (var 3))
                         _ (ppair (var 4) (
                                     ppi1 (var 3)))); auto.
sh_var 3 9.
rewrite - ! subst_sh_shift.
rewrite - ! subst_picomp2 - ! subst_ppi1 - ! subst_ppair - !
                                                             subst_subseq ! subst_sh_shift.
rewrite make_app3.
apply tr_weakening_append; auto.
auto. repeat fold (@subst1 False).
rewrite fold_subst1 subst1_trans_type.
simpsub_big. simpl. apply picomp4_works.
weaken compm5_type; try var_solv; auto; try apply trans_type_works; try var_solv; try (apply world_pair; var_solv).
intros.
sh_var 2 11. rewrite - ! subst_sh_shift - ! subst_ppair.
weaken compm4_type; try var_solv; auto. apply trans_type_works; try var_solv; auto.
}
Unshelve. apply nat. 
Unshelve. apply nat. 
Qed.


Theorem one: forall G e A ebar w1 l1,
    of_m G e A ->
    tr [::] (oof (ppair w1 l1) world) ->
    trans G e A ebar -> 
    tr (Gamma_at_ctx G w1 l1) (oof (app (app (shift (size G) ebar)
                                             (shift (size G) l1))
                                        (gamma_at G))
                                     (trans_type (shift (size G) w1) (shift (size G) l1) A)).
  move => G e A ebar w1 l1 He Hwl Htrans.
  eapply (tr_arrow_elim _ (Gamma_at G (shift (size G) w1) (shift (size G) l1))).
  apply Gamma_at_type.
  rewrite - ! subst_sh_shift - subst_ppair - (subst_world (sh (size G))) - (size_Gamma_at w1 l1) ! subst_sh_shift - {1} (cats0 (Gamma_at_ctx G w1 l1)).
  apply (tr_weakening_append [::]).
  auto.
  rewrite - (cats0 (Gamma_at_ctx G w1 l1)) - (size_Gamma_at w1 l1) - shift_trans_type.
  apply (tr_weakening_appendt [::]).
  weaken trans_type_works; try var_solv; auto.
  match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
       (subst1 (shift (size G) l1) (arrow
          (Gamma_at G
             (shift 
                (size G + 1) w1) (var 0))
          (trans_type
             (shift 
                (size G + 1) w1)
             (var 0) A))) end.
  2: {
    simpsub_bigs.
    rewrite subst1_Gamma_at fold_subst1 subst1_trans_type.
    simpsub_big.
    replace (size G + 1) with ((size G).+1). 
    rewrite compose_sh_dot.
    simpsub_bigs.
    rewrite plusE.
    replace (size G + 0) with (size G).
    auto.
    rewrite addn0. auto.
    rewrite addn1. auto.
  }
  apply (tr_pi_elim _ nattp).
  match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
      (subst1 (shift (size G) w1)
       (pi nattp
          (arrow (Gamma_at G (var 1) (var 0))
                 (trans_type (var 1) (var 0) A)))) end.
  2: {
    unfold subst1. rewrite subst_pi subst_arrow.
    rewrite subst1_under_Gamma_at subst1_under_trans_type.
    simpsub_big.
    rewrite plusE. auto.
  }
  eapply (tr_all_elim _ nzero preworld). 
  match goal with |- tr ?G' (deq ?M ?M ?T) => replace T with
      (shift (size G) T) end. 
  2: {
    rewrite - subst_sh_shift subst_all subst_pi subst_arrow under_sum.
    rewrite sh_under_Gamma_at sh_under_trans_type.
    simpsub_bigs. auto.
  }
  rewrite - (cats0 (Gamma_at_ctx G w1 l1)) - (size_Gamma_at w1 l1).
  apply tr_weakening_append. eapply two_working. apply Htrans. 
  + rewrite - (cats0 (Gamma_at_ctx G w1 l1))  - (subst_pw (sh (size G)))
  - (size_Gamma_at w1 l1) subst_sh_shift.
  apply tr_weakening_append. eapply split_world1. apply Hwl.
  change (var 1) with (@shift obj 1 (var 0)).
  apply trans_type_works; try var_solv1. var_solv.
  + rewrite - (cats0 (Gamma_at_ctx G w1 l1))  - (subst_nat (sh (size G)))
  - (size_Gamma_at w1 l1) subst_sh_shift.
  apply tr_weakening_append. eapply split_world2. apply Hwl.
  change (var 1) with (@shift obj 1 (var 0)).
  apply gamma_at_typed. auto.
Qed.
