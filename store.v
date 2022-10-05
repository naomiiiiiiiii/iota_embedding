
      subst u1. unfold store. apply tr_all_intro; auto. simpsub_bigs.
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
             move : (equiv_trans (equiv_trans (equiv_trans Heq0 Heq1) Heq2) Heq3) => HeqT.
             eapply (tr_compute _ _ _ _ _ _ _ HeqT);
               try (apply equiv_refl).
             clear T0 T1 T2 HeqT0 HeqT1 HeqT2 Heq0 Heq1 Heq2 Heq3 HeqT.
             apply tr_fut_intro. simpl.
