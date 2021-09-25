Require Import Program Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans hygiene_help derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences.
From istari Require Import Rules Defined DefsEquiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
Lemma silly: forall n m, (n + 1) = m \/ (n + 1) = 2.
 move=> + m.*)


Check True.

(*crucial lemmas leading up to the final theorem (one) showing
 well-typedness of the translation *)
Ltac var_nf_help cap var_num := match (eval compute in (leq var_num cap)) with
                          true => (change (@ var obj var_num) with (subst (sh var_num) (@ var obj 0)));
                                                              var_nf_help cap var_num.+1
                        | false => auto
                          (*change (@ var obj 9) with
                              (shift sh_amt (@ var obj 6))*)

                                       end.
(*sh_var amt cap rewrites (Var i) as (shift sh_amt (var (i - sh_amt)))
 for any i <= cap*)
Ltac var_nf cap := var_nf_help cap 1.


Lemma gettype_typed: forall G w v lv, tr G (oof w preworld) -> tr G (oof (ppair v lv) world) -> tr G (deqtype (gettype w v lv) (gettype w v lv)).
  Admitted.

Lemma types_hygienic: forall G A, tr G (deqtype A A) ->
                                hygiene (ctxpred G) A.
Admitted.


Lemma trans_hygenic G E A Et: trans G E A Et -> (hctx [::]) Et.
Admitted.

Lemma trans_types_hygienic G w l A: (hctx G w) -> (hctx G l) ->
    (hctx G) (trans_type w l A).
Admitted.

Hint Resolve trans_hygenic trans_types_hygienic: hygiene_hint.

Lemma sh_succ m n: @ subst obj (sh n.+1) m = (subst sh1 (subst (sh n) m)).
simpsub. rewrite plusE. rewrite addn1. auto. Qed.

Lemma sh0 m: @ subst obj (sh 0) m = m.
  simpsub. auto. Qed.
Hint Rewrite sh_succ sh0: hygiene_hint.



Goal (@ var obj 10) = (var 0).
  var_nf 10. autorewrite with hygiene_hint. Abort.

Lemma moveapp_works {T}: forall G w1 l1 w2 l2 m v,
     tr G (oof (ppair w1 l1) world) ->
     tr G (oof (ppair w2 l2) world) ->
     tr G (oof m (subseq (ppair w1 l1) (ppair w2 l2))) ->
     tr G (oof v (trans_type w1 l1 T)) -> (*it's the occurence of T in this line?!
                                          ask karl*)
     tr G (oof (move_app T m v) (trans_type w2 l2 T)).
Admitted.


(*
clam, capp are for points in spaces (kinds)
isomorphism between normally constructed terms of kinds and points in spaces (whole point of semantics)
he has istari code for converting from normal terms (of kinds) to the points


no jugement for typing the points in spaces

syntactic rules for istari but interpretation (semantics) uses them


con, cty establish relationship between constructors and 
 *)




 Lemma equiv_trans {m1 m2 m3} : @ equiv obj m1 m2 -> equiv m2 m3 -> equiv m1 m3.
  apply equiv_trans. Qed.

Ltac hyg_solv_big := var_nf 15; autorewrite with hygiene_hint; hyg_solv.

(*
Goal (@ subst1 obj nattp (var 0)) = nattp.
  unfold subst1. simpl (subst (dot ?x1 ?s) ?x2). cbn - [ nattp].
  cbn [traverse]. *)

Lemma ref_type1 G w1 i A:
  tr G (oof w1 preworld) -> tr G (oof A U0) ->
  tr G (oof i nattp) ->
      tr G (oof (all nzero preworld
           (pi nattp 
               ( let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (app (subst (sh 2) w1) (subst (sh 2 ) i)) (next v)) (next lv))
                 (fut A) ))) U0).
Admitted.

Theorem two: forall G e T ebar,
    trans G e T ebar ->
    tr [::] (oof ebar
                (all nzero preworld (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                                     (trans_type (var 1) (var 0) T))))
           ).
  (*gamma can be part of D, don't even need to move gamma (var 5) over i think*)
  move => G e T ebar Dtrans. induction Dtrans; intros.
(*ref case*)
  2: { apply comp_front. (*is a valid intro form for comp type*)
       simpsub_bigs. simpsubs.
       apply ret_type.
       remember (lam
                (lam
                   (subst1 (prev ((var 0)))
                      (subst1 (prev ((var 2)))
                              (fut (trans_type ((var 0)) ((var 1)) A)))))) as x.
         remember (cons_b ((var 3)) ((var 2)) x) as u1. (*u1 = u::A*)
         remember (ppair u1 (nsucc (var 2))) as U1.
        - (*u1 : preworld*)
         match goal with |- tr ?D' ?J => assert (forall G', tr G' (oof x (karrow (fut preworld)
                                                                    (arrow (fut nattp) U0)
                                              ))) as Hx end. 
         subst x. move =>>. apply tr_karrow_intro; try assumption; auto.
         simpsub_big_T.
         apply tr_arrow_intro; try assumption; auto.
         apply tr_univ_formation; auto.
         simpsub_big_T. change (univ nzero) with (@ subst1 obj (prev (var 0)) (univ nzero)).
         apply (tr_fut_elim _ _ _ nattp). var_solv. inv_subst. var_solv. auto.
         change (univ nzero) with (@ subst1 obj (prev (var 2)) (univ nzero)).
         apply (tr_fut_elim _ _ _ preworld). var_solv. inv_subst. var_solv. auto.
         constructor. apply trans_type_works; auto. apply world_pair; var_solv.
         auto.
         match goal with |- tr (?a::?b::?G') ?J => assert (forall x y, tr (x::y::G') (oof u1 preworld))
                           as Hu1 end.
         intros. subst. apply consb_typed; try assumption; try var_solv; auto.
        - (*U1 : world*)
         match goal with |- tr ?G' ?J => assert (tr G' (oof U1 world)) as HU1 end.
         subst. apply world_pair; try (apply Hu1); apply nsucc_nat; var_solv; auto. subst U1.
         (*new reference is at world U1*)
         eapply (tr_exist_intro _ _ _ _ u1); auto.
         2: { sh_var 2 5. rewrite - ! subst_sh_shift - ! subst_ppair.
              comptype.
              match goal with |- tr ?G (oof ?T U0) =>
                              replace T with (trans_type (var 1)
                                             (var 0) (reftp_m A)) end.
              apply trans_type_works; auto. simpl. simpsub_bigs. auto. 
         }
         simpsub_bigs. simpsub_type; auto.
         (*split up nat from pair*)
         apply tr_sigma_intro. apply nsucc_nat. var_solv.
         (*<p1, <l, <*, \_:nat.*>>>: <u, l> <= <u1, l1> x storeU1 x ref(A)@U1) *)
         (*7862 has appeared here, wasnt there at start of ref*)
         simpsub_bigs.
         (*showing U <= U1*)
         + assert (tr [:: hyp_tm (store (var 2) (var 1)); hyp_tm (subseq (ppair (var 4) (var 3)) (ppair (var 1) (var 0))); hyp_tm nattp; hyp_tm preworld; hyp_tm (Gamma_at G (var 1) (var 0)); hyp_tm nattp; hyp_tm preworld]
                    (deq make_subseq make_subseq
                         (subseq (ppair (var 3) (var 2)) (ppair u1 (nsucc (var 2))))))
             as HUsubU1.
           subst. apply consb_subseq; try (apply Hx); try var_solv.
           repeat (apply tr_prod_intro); try assumption.
           (*showing the new store is a store at U1*)
      subst u1. unfold store. apply tr_all_intro; auto. simpsub_bigs.
      apply tr_pi_intro; auto. apply tr_arrow_intro; auto. apply subseq_type; auto.
      (*ltac for showing (sh 2 U1) to be a world in context grown by 2*)
      Hint Rewrite <- subst_ppair subst_nsucc: inv_subst.
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
                make_subseq) 
             (var 1))
          (next
             (move_app A make_subseq
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
change (app (app (app (var 5) (var 3)) make_subseq) (var 1)) with
    (subst sh1 (app (app (app (var 4) (var 2)) make_subseq) (var 0))).
replace (next (move_app A make_subseq (app (app (subst (sh 12) Et) (var 10)) (var 9)))) with
    (subst sh1 (next (move_app A make_subseq (app (app (subst (sh 11) Et) (var 9)) (var 8))))).
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
             subst. rewrite ! subst_lam. apply equiv_app; try apply equiv_refl.
             apply reduce_equiv. apply reduce_app_beta;
               [unfold subst1; rewrite ! subst_fut ! fold_subst1 ! subst1_trans_type;
               do 2 simpsubs; rewrite subst_trans_type; auto | ..]; apply reduce_id.
             unfold subst1 in HeqT1.
             rewrite subst_lam subst_fut subst1_under_trans_type in HeqT1.
             simpsubin_bigs HeqT1.
             assert (equiv T1 T2) as Heq2.
             subst. apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
             assert (equiv T2 (fut (trans_type (var 3) (var 2) A))) as Heq3.
             subst. simpsub. rewrite subst1_trans_type. do 2 simpsubs. apply equiv_fut.
             apply trans_type_equiv; apply reduce_equiv; constructor; apply reduce_id.
             move : (equiv_trans (equiv_trans (equiv_trans Heq0 Heq1) Heq2) Heq3) => HeqT.
             eapply (tr_compute _ _ _ _ _ _ _ HeqT);
               try (apply equiv_refl).
             clear T0 T1 T2 HeqT0 HeqT1 HeqT2 Heq0 Heq1 Heq2 Heq3 HeqT.
             apply tr_fut_intro. simpl.
             - (*showing next(move A (m2 o m1 o m) (e @W)) : |>(T @ U2) *)
               apply (@moveapp_works _ _ (var 10) (var 9) (var 3) (var 2)); try (apply world_pair; var_solv).
             assert (forall w l x, cons_b w l x = lam (let i := (var 0) in
                                                  bite (app (app lt_b i) (shift 1 l)) (app (shift 1 w) i) (shift 1 x))) as fold_consb. auto.
             remember (cons_b (var 3) (var 2) x) as u1.
             replace (lam (bite (app (app lt_b (var 0)) (var 5))
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
               apply Gamma_at_type; auto. trans_type.
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
               apply trans_type_works1; var_solv. var_solv.
               sh_var 9 10. inv_subst. var_solv0.
               simpsub_bigs. auto.
      }
      { (*small typing goal*)
                 apply gettype_typed. sh_var 2 5. rewrite - ! subst_sh_shift - subst_consb - (subst_pw (sh 2)) ! subst_sh_shift make_app2.
                 apply tr_weakening_append. apply Hu1. auto.
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
                   eapply tr_compute.
                   {   (*start here move this out.*)
  apply equiv_eqtype.
  eapply equiv_trans.
  apply reduce_consb. apply equiv_app. apply equiv_app.
  apply equiv_bite. eapply ltb_false.
  apply equiv_refl.
                     }
                   do 2 (apply equiv_refl).
                   apply equiv_refl. (*start here clean this up*)
                   match goal with tr ?G (deq triv triv ?T) =>
                                   assert (equiv T
       (eqtype
          (app (app (bite (ltb_app (var 4) (var 4)) (app (var 5) (var 4))
                          (subst (sh 2) x)) v) lv).
                       (next (obj 0)))
          (fut (trans_type (obj 1) (obj 0) A))))
                                          )



                   unfold cons_b.
                 }


                 subst. unfold subst1.
                 rewrite ! subst_fut ! fold_subst1 ! subst1_trans_type.
                 simpsub_bigs.
                 constructor. var_solv. simpsub_bigs.
                 rewrite ! subst_trans_type; auto.
                 apply tr_prod_intro. weaken lt_type. var_solv.
                 apply nsucc_nat; var_solv. (*typing goal*)
                 match goal with |- tr ?G (deqtype ?T ?T) => replace T with
       (shift 2 (all nzero preworld
          (pi nattp
             (eqtype
                (app
                   (app
                      (app
                         (cons_b (var 3) 
                            (var 2)
                            (lam
                               (lam
                                  (fut
                                   (trans_type
                                   (prev (var 1))
                                   (prev (var 0)) A)))))
                         (var 2)) 
                      (next (var 1)))
                   (next (var 0)))
                (fut
                   (trans_type (var 1) (var 0) A)))))) end.
                 2: {
                   simpsub_bigs. rewrite ! subst_trans_type; auto.
                 }
                 eapply (tr_formation_weaken _ nzero).
                 rewrite make_app2 - (subst_U0 (sh 2)) subst_sh_shift.
                 apply tr_weakening_append.
                 replace (cons_b (var 3) (var 2)
                            (lam
                               (lam
                                  (fut
                                   (trans_type
                                   (prev (var 1))
                                   (prev (var 0)) A))))) with
                     (subst (sh 2) (cons_b (var 1) (var 0)
                            (lam
                               (lam
                                  (fut
                                   (trans_type
                                   (prev (var 1))
                                   (prev (var 0)) A)))))). sh_var 2 2.
                 rewrite - subst_sh_shift.
                 eapply ref_type1. apply consb_typed; try var_solv.
                 unfold subst1 in Hx. rewrite ! subst_fut ! fold_subst1
                                              ! subst1_trans_type in Hx.
                 do 2 simpsubin Hx.
                 apply Hx.
                 apply trans_type_works; auto. var_solv. simpsub_bigs.
                 rewrite subst_trans_type; auto.
                 (*2 < succ 2 *)

                 2: { apply trans_ty

                 }

                 eapply ref_type1.
                 assumption.
                 subst. unfold subst1.
                 change (dot (var 0)
                         (dot (var 1)
                            (dot (var 4)
                               (dot 
                                  (nsucc (var 4))
                                  (sh 2))))) with
                     (under )

rewrite ! subst_fut ! fold_subst1 ! subst1_trans_type.
                ! sh_under_trans_type. do 2 simpsubs.


                 weaken ref_type1.

                 1: { apply comp_front.
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
weaken trans_type_works; auto.
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
apply trans_type_works1; auto.
var_solv.
simpsub_type; auto.
var_solv. replace (Gamma_at G (var 6) (var 5)) with
              (shift 5 (Gamma_at G (var 1) (var 0))). rewrite - subst_sh_shift.
try (apply tr_hyp_tm; repeat constructor).
rewrite - subst_sh_shift. change (sh 5) with (@ under obj 0 (sh 5)).
rewrite sh_under_Gamma_at. auto.
simpsub_type; auto. var_solv. eapply tr_formation_weaken; apply compm0_type.
apply world_pair; var_solv. apply trans_type_works; auto. var_solv.
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
                        (@ subst obj (sh 2) (ppair (var 4) (var 3))); auto. comptype. simpsub_type; try apply trans_type_works; auto.
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
        apply Gamma_at_type; try var_solv.
        rewrite (subst_trans_type _ _ A); auto.
match goal with |- tr ?G (deqtype ?M ?M) =>
                replace M with
    (trans_type (var 1) (ppi1 (var 0)) (comp_m B)) end.
2: {
simpl. simpsub_type; auto. 
} weaken trans_type_works; auto.
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
apply trans_type_works1; auto. var_solv. auto.
simpl. apply Gamma_at_intro; auto.
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
                   False (sh 2) (ppair (var 1) (ppi1 (var 0)))
           ); change (y::x::G') with ([:: y; x] ++ G'))
end.
rewrite - (subst_world (sh 2)) ! subst_sh_shift. apply tr_weakening_append; auto.
apply trans_type_works; auto. auto.
apply sub_refl; auto.
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
  + simpsub_type; auto. apply ret_type.
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
                   False (sh 1) (ppair (var 1) (ppi1 (var 0)))
           ); change (x::G') with ([:: x] ++ G'))
end.
rewrite - (subst_world (sh 1)) ! subst_sh_shift. apply tr_weakening_append; auto. rewrite ! subst_trans_type; auto. apply trans_type_works; auto.
simpsub_type; auto. rewrite ! subst_trans_type; auto.
apply (tr_exist_intro _ _ _ _ (var 1)); auto.
    * var_solv.
      simpsub_big; auto. simpl.
      change (dot (var 0) (dot (var 2) sh1))  with (@ under obj 1 (dot (var 1) id)). rewrite ! subst1_under_trans_type; auto. simpsub. simpl.
      apply tr_sigma_intro; auto.
- simpsub_big. simpl. apply tr_prod_intro.
  * constructor. apply subseq_type; auto. apply store_type; auto.
    fold (@ subst1 obj (ppi1 (var 0))).
    rewrite subst1_trans_type. simpsub_big. simpl.
    eapply tr_formation_weaken. apply trans_type_works. auto.
    + apply tr_prod_intro. apply subseq_type; auto. apply store_type; auto.
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
weaken compm5_type; auto; try apply trans_type_works; try (apply world_pair; var_solv).
intros.
sh_var 2 11. rewrite - ! subst_sh_shift - ! subst_ppair.
weaken compm4_type; auto. apply trans_type_works; auto.
}

Theorem onef: forall G e T ebar w1 l1,
    of_m G e T ->
    tr [::] (oof (ppair w1 l1) world) ->
    trans G e ebar -> 
    tr (Gamma_at_ctx G w1 l1) (oof (app (app ebar l1) 
              (arrow (Gamma_at G w1 l1) (trans_type w1 l1 T))).
