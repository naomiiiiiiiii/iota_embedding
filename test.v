
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
  replace (@ppair False (var 5) (var 4)) with (@subst False (sh 2) (ppair (var 3) (var 2))); auto. 
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
(@under False 1 (dot (var 6) id)). rewrite subst1_under_Gamma_at. auto.
}
eapply (tr_all_elim _ nzero preworld). 
match goal with |- tr ?G (deq ?M ?M ?T) =>
               (replace T with
                    (shift 7 T)) end.
2: {  simpsub_type; auto. 
change (dot (var 0)
            (dot (var 1) (sh 9))) with (@under False 2 (sh 7)).
rewrite sh_under_Gamma_at. simpsub. auto. }
match goal with |- tr ?G' ?J => rewrite - (cats0 G'); change (sh 7)
with (@sh False (size G')); rewrite ! subst_sh_shift
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
change (var 1) with (@shift False 1 (var 0)).
apply trans_type_works1; auto.
var_solv.
simpsub_type; auto.
var_solv. replace (Gamma_at G (var 6) (var 5)) with
              (shift 5 (Gamma_at G (var 1) (var 0))). rewrite - subst_sh_shift.
try (apply tr_hyp_tm; repeat constructor).
rewrite - subst_sh_shift. change (sh 5) with (@under False 0 (sh 5)).
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
                        (@subst False (sh 2) (ppair (var 4) (var 3))); auto. comptype. simpsub_type; try apply trans_type_works; auto.
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
    (@subst False (sh 2) (ppair (var 1) (ppi1 (var 0)))); auto. comptype.
-
  eapply (tr_arrow_elim _
                        (subseq (ppair (var 1) (picomp1 (var 0)))
                                (ppair (var 1) (picomp1 (var 0)))
                        )). apply subseq_type; auto.
    +   replace (ppair (var 3) (ppi1 (var 2))) with
    (@subst False (sh 2) (ppair (var 1) (ppi1 (var 0)))); auto. comptype.
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
(@under False 1 (dot (var 1) id)). rewrite subst1_under_Gamma_at. simpsub_type; auto.
}
eapply (tr_all_elim _ nzero preworld).
match goal with |- tr ?G' ?J => rewrite - (cats0 G'); change (sh 10)
with (@sh False (size G')); rewrite ! subst_sh_shift
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
change (var 1) with (@shift False 1 (var 0)).
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
2: { change (sh 8) with (@under False 0 (sh 8)).
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
             (@subst False (sh 2) (ppair (var 1) (ppi1 (var 0)))).
comptype.
rewrite ! subst_trans_type; auto.
change (ppair (var 8) (var 7)) with
             (@subst False (sh 2) (ppair (var 6) (var 5))).
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
     (@subst False (sh 2) (ppair (var 2) (ppi1 (var 1)))). comptype.
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
      change (dot (var 0) (dot (var 2) sh1))  with (@under False 1 (dot (var 1) id)). rewrite ! subst1_under_trans_type; auto. simpsub. simpl.
      apply tr_sigma_intro; auto.
- simpsub_big. simpl. apply tr_prod_intro.
  * constructor. apply subseq_type; auto. apply store_type; auto.
    fold (@subst1 False (ppi1 (var 0))).
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
3 focused subgoals
(shelved: 1) (ID 4047)
  
  G : source.context
  E : source.term
  Et : term False
  A : source.term
  o : of_m G (ref_m E) (comp_m (reftp_m A))
  Dtrans : trans G E A Et
  IHDtrans : tr [::]
               (oof Et
                  (all nzero preworld
                     (pi nattp
                        (arrow
                           (Gamma_at G
                             (False 1)
                             (False 0))
                           (trans_type
                             (False 1)
                             (False 0) A)))))
  x : term False
  Heqx : x =
         lam
           (lam
              (subst1 (prev (False 0))
                 (subst1 (prev (False 2))
                    (fut
                       (trans_type 
                          (False 0) 
                          (False 1) A)))))
  Hx : tr
         [:: hyp_tm
               (store (False 2) (False 1));
             hyp_tm
               (subseq
                  (ppair (False 4) (False 3))
                  (ppair (False 1) (False 0)));
             hyp_tm nattp; hyp_tm preworld;
             hyp_tm
               (Gamma_at G (False 1)
                  (False 0)); 
            hyp_tm nattp; hyp_tm preworld]
         (oof x
            (karrow (fut preworld)
               (arrow (fut nattp) U0)))
  HUsubU1 : tr
              [:: hyp_tm
                    (store (False 2)
                       (False 1));
                  hyp_tm
                    (subseq
                       (ppair 
                          (False 4) 
                          (False 3))
                       (ppair 
                          (False 1) 
                          (False 0)));
                  hyp_tm nattp;
                  hyp_tm preworld;
                  hyp_tm
                    (Gamma_at G 
                       (False 1) 
                       (False 0));
                  hyp_tm nattp;
                  hyp_tm preworld]
              (deq make_subseq make_subseq
                 (subseq
                    (ppair (False 3)
                       (False 2))
                    (ppair
                       (cons_b 
                          (False 3) 
                          (False 2) x)
                       (nsucc (False 2)))))
  HU1 : tr
          [:: hyp_tm
                (store (False 2) (False 1));
              hyp_tm
                (subseq
                   (ppair (False 4) (False 3))
                   (ppair (False 1) (False 0)));
              hyp_tm nattp; hyp_tm preworld;
              hyp_tm
                (Gamma_at G (False 1)
                   (False 0)); 
             hyp_tm nattp; hyp_tm preworld]
          (oof
             (ppair
                (cons_b (False 3) (False 2) x)
                (nsucc (False 2))) world)
  Hu1 : tr
          [:: hyp_tm
                (store (False 2) (False 1));
              hyp_tm
                (subseq
                   (ppair (False 4) (False 3))
                   (ppair (False 1) (False 0)));
              hyp_tm nattp; hyp_tm preworld;
              hyp_tm
                (Gamma_at G (False 1)
                   (False 0)); 
             hyp_tm nattp; hyp_tm preworld]
          (oof (cons_b (False 3) (False 2) x)
             preworld)
  T0 : term False
  HeqT0 : T0 =
          app
            (app (subst (sh 4) x)
               (next (False 3)))
            (next (False 2))
  T1 : term False
  T2 : termx False
  HeqT2 : T2 =
          subst1 (next (False 2))
            (fut
               (trans_type
                  (prev (next (False 4)))
                  (prev (False 0)) A))
  Heq0 : equiv
           (app
              (app
                 (bite bfalse
                    (app (False 7) (False 0))
                    (subst (sh 4) x))
                 (next (False 3)))
              (next (False 2))) T0
  Heq1 : equiv T0 T1
  HeqT1 : T1 =
          app
            (lam
               (fut
                  (trans_type
                     (prev
                        (next
                           (False
                             (1 + 3)%coq_nat)))
                     (prev (False 0)) A)))
            (next (False 2))
  Heq2 : equiv T1 T2
  Heq3 : equiv T2
           (fut
              (trans_type (False 3) 
                 (False 2) A))
  HeqT : equiv
           (app
              (app
                 (bite bfalse
                    (app (False 7) (False 0))
                    (subst (sh 4) x))
                 (next (False 3)))
              (next (False 2)))
           (fut
              (trans_type (False 3) 
                 (False 2) A))
  ============================
  hygiene
    (ctxpred
       [:: hyp_tm nattp;
           hyp_tm
             (subseq
                (ppair
                   (lam
                      (bite
                         (app
                            (app lt_b
                             (False 0))
                            (False 5))
                         (app 
                            (False 6)
                            (False 0))
                         (subst (sh 3) x)))
                   (nsucc (False 4)))
                (ppair (False 1) (False 0)));
           hyp_tm nattp; hyp_tm preworld;
           hyp_tm
             (all nzero preworld
                (pi nattp
                   (arrow
                      (subseq
                         (ppair 
                            (False 4)
                            (False 3))
                         (ppair 
                            (False 1)
                            (False 0)))
                      (pi nattp
                         (app
                            (app
                             (app 
                             (False 5)
                             (False 0))
                             (next (False 2)))
                            (next (False 1)))))));
           hyp_tm
             (subseq
                (ppair (False 4) (False 3))
                (ppair (False 1) (False 0)));
           hyp_tm nattp; hyp_tm preworld;
           hyp_tm
             (Gamma_at G (False 1) (False 0));
           hyp_tm nattp; hyp_tm preworld])
    (next
       (move_app A make_subseq
          (app
             (app (subst (sh 11) Et)
                (False 9)) (False 8)))) /\
  hygiene
    (ctxpred
       [:: hyp_tm nattp;
           hyp_tm
             (subseq
                (ppair
                   (lam
                      (bite
                         (app
                            (app lt_b
                             (False 0))
                            (False 5))
                         (app 
                            (False 6)
                            (False 0))
                         (subst (sh 3) x)))
                   (nsucc (False 4)))
                (ppair (False 1) (False 0)));
           hyp_tm nattp; hyp_tm preworld;
           hyp_tm
             (all nzero preworld
                (pi nattp
                   (arrow
                      (subseq
                         (ppair 
                            (False 4)
                            (False 3))
                         (ppair 
                            (False 1)
                            (False 0)))
                      (pi nattp
                         (app
                            (app
                             (app 
                             (False 5)
                             (False 0))
                             (next (False 2)))
                            (next (False 1)))))));
           hyp_tm
             (subseq
                (ppair (False 4) (False 3))
                (ppair (False 1) (False 0)));
           hyp_tm nattp; hyp_tm preworld;
           hyp_tm
             (Gamma_at G (False 1) (False 0));
           hyp_tm nattp; hyp_tm preworld])
    (app
       (app
          (bite bfalse
             (app (False 7) (False 0))
             (subst (sh 4) x))
          (next (False 3))) (next (False 2)))

subgoal 2 (ID 2656) is:
 subst1 (ltb_app (False 0) (False 6))
   (bite (False 0)
      (app
         (app (app (False 5) (False 3))
            make_subseq) (False 1))
      (next
         (move_app A make_subseq
            (app
               (app (subst (sh 12) Et)
                  (False 10)) 
               (False 9))))) =
 bite (app (app lt_b (False 0)) (False 6))
   (app
      (app (app (False 4) (False 2))
         make_subseq) (False 0))
   (next
      (move_app A make_subseq
         (app
            (app (subst (sh 11) Et) (False 9))
            (False 8))))
subgoal 3 (ID 2316) is:
 hygiene
   (ctxpred
      [:: hyp_tm nattp;
          hyp_tm
            (subseq
               (ppair
                  (lam
                     (bite
                        (app
                           (app lt_b
                             (False 0))
                           (shift 1 (False 4)))
                        (app
                           (shift 1 (False 5))
                           (False 0))
                        (shift 1
                           (subst (sh 2) x))))
                  (nsucc (False 4)))
               (ppair (False 1) (False 0)));
          hyp_tm nattp; hyp_tm preworld;
          hyp_tm
            (all nzero preworld
               (pi nattp
                  (arrow
                     (subseq
                        (ppair 
                           (False 4)
                           (False 3))
                        (ppair 
                           (False 1)
                           (False 0)))
                     (pi nattp
                        (app
                           (app
                             (app 
                             (False 5)
                             (False 0))
                             (next (False 2)))
                           (next (False 1)))))));
          hyp_tm
            (subseq
               (ppair (False 4) (False 3))
               (ppair (False 1) (False 0)));
          hyp_tm nattp; hyp_tm preworld;
          hyp_tm
            (Gamma_at G (False 1) (False 0));
          hyp_tm nattp; hyp_tm preworld])
   (bite (app (app lt_b (False 0)) (False 6))
      (app
         (app (app (False 4) (False 2))
            make_subseq) (False 0))
      (next
         (move_app A make_subseq
            (app
               (app (subst (sh 11) Et)
                  (False 9)) (False 8))))) /\
 hygiene
   (ctxpred
      [:: hyp_tm nattp;
          hyp_tm
            (subseq
               (ppair
                  (lam
                     (bite
                        (app
                           (app lt_b
                             (False 0))
                           (shift 1 (False 4)))
                        (app
                           (shift 1 (False 5))
                           (False 0))
                        (shift 1
                           (subst (sh 2) x))))
                  (nsucc (False 4)))
               (ppair (False 1) (False 0)));
          hyp_tm nattp; hyp_tm preworld;
          hyp_tm
            (all nzero preworld
               (pi nattp
                  (arrow
                     (subseq
                        (ppair 
                           (False 4)
                           (False 3))
                        (ppair 
                           (False 1)
                           (False 0)))
                     (pi nattp
                        (app
                           (app
                             (app 
                             (False 5)
                             (False 0))
                             (next (False 2)))
                           (next (False 1)))))));
          hyp_tm
            (subseq
               (ppair (False 4) (False 3))
               (ppair (False 1) (False 0)));
          hyp_tm nattp; hyp_tm preworld;
          hyp_tm
            (Gamma_at G (False 1) (False 0));
          hyp_tm nattp; hyp_tm preworld])
   (app
      (app
         (app
            (lam
               (bite
                  (app (app lt_b (False 0))
                     (shift 1 (False 6)))
                  (app (shift 1 (False 7))
                     (False 0))
                  (shift 1 (subst (sh 4) x))))
            (False 0)) (next (False 3)))
      (next (False 2)))
