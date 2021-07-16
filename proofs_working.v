Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
(*crucial lemmas leading up to the final theorem (one) showing
 well-typedness of the translation*)


Ltac trans_type := weaken trans_type_works; auto.

 Lemma move_gamma_works: forall D G w1 l1 w2 l2 m gamma,
    tr D (oof (ppair w1 l1) world) ->
    tr D (oof (ppair w2 l2) world) ->
     tr D (oof m (subseq (ppair w1 l1) (ppair w2 l2))) ->
     tr D (oof gamma (Gamma_at G w1 l1)) ->
     tr D (oof (move_gamma G m gamma) (Gamma_at G w2 l2)).
  move => D G. move: D. induction G; simpl; move => D w1 l1 w2 l2 m gamma
                                                  Hw1 Hw2 Hsub Hg; auto.
  (*IS*)
   apply tr_prod_intro.
  - (*show product type is well formed*)
    weaken trans_type_works; auto.
    apply Gamma_at_type; auto.
  - (*pi1*)
    unfold move_app.
    (apply (tr_arrow_elim _ (trans_type w1 l1 a))); try trans_type.
    apply (tr_arrow_elim _ (subseq (ppair w1 l1)
                                   (ppair w2 l2)
                           )
          ).
    apply subseq_type; auto.
    apply tr_arrow_formation; try trans_type.
    apply move_works; auto. auto.
    eapply tr_prod_elim1. apply Hg.
  - (*pi2*)
    eapply IHG. apply Hw1. apply Hw2. auto.
    eapply tr_prod_elim2. apply Hg.
    Qed.

Lemma sub_refl: forall ( U: term False) (G: context),
                         tr G (oof U world)
                         ->tr G (oof make_subseq 
                                    (subseq U U)).
 Admitted.

 Theorem two: forall G e T ebar,
    trans G e T ebar -> 
    tr [::] (oof ebar
                (all nzero preworld (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                                     (trans_type (var 1) (var 0) T))))
           ).
  (*gamma can be part of D, don't even need to move gamma (var 5) over i think*)
  move => G e T ebar Dtrans. induction Dtrans; intros.
(*pop them all off*)
  1: {
    constructor; auto.
simpsub_big. simpl. apply tr_pi_intro; auto.
apply tr_arrow_intro; auto.
apply Gamma_at_type; auto. 
match goal with |- tr ?G (deqtype ?A ?A) =>
               (change A with
(trans_type (var 1) (var 0) (comp_m B))) end; auto.
weaken trans_type_works; auto. (*have popped off G*)
simpsub_big. simpl. constructor; auto; simpsub_big; simpl.
constructor; auto.
apply tr_arrow_intro; auto.
weaken compm1_type; auto.
 rewrite subst_trans_type; auto.
    apply trans_type_works; auto.
    (*pop off the store*)
   simpsub_big. simpl. apply tr_arrow_intro; auto.
    eapply tr_formation_weaken. 
    replace (@ppair False (var 4) (var 3)) with (@subst False (sh 2) (ppair (var 2) (var 1))); auto.
    apply compm2_type; auto.
    rewrite subst_trans_type. apply trans_type_works. auto.
    simpsub. auto. rewrite subst_bind.
    simpsub_big.
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
                                                    prod (prod (subseq U V) (store V))
                                                     (trans_type v lv A))))
           ).
    (*at make_bind*)
  replace (@ppair False (var 5) (var 4)) with (@subst False (sh 2) (ppair (var 3) (var 2))); auto. 
    eapply (tr_arrow_elim _  (store (ppair (var 3)
                                                   (var 2)
           ))); auto.
- 
  simpl.
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
             (store (ppair (var 3) (var 2)))
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
                              (ppair 
                              (var 1) 
                              (var 0))))
                         (trans_type 
                            (var 1) 
                            (var 0) A)))))))
 with
(subst1 (var 2) 
       (arrow
          (subseq (ppair (var 7) (var 6))
             (ppair (var 4) (var 0)))
          (arrow (store (ppair (var 4) (var 0)))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (prod
                         (prod
                            (subseq (ppair (var 6) (var 2))
                               (ppair (var 1) (var 0)))
                            (store (ppair (var 1) (var 0))))
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
                (store (ppair (var 4) (var 0)))
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
                                (ppair 
                                (var 1) 
                                (var 0))))
                            (trans_type 
                               (var 1) 
                               (var 0) A))))))))
 with
(subst1 (var 3) (pi nattp
          (arrow
             (subseq (ppair (var 8) (var 7))
                (ppair (var 1) (var 0)))
             (arrow (store (ppair (var 1) (var 0)))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq (ppair (var 3) (var 2))
                                  (ppair (var 1) (var 0)))
                               (store (ppair (var 1) (var 0))))
                            (trans_type (var 1) (var 0) A))))))))).
  2: {
     simpsub_type; auto. }
  eapply (tr_all_elim _ nzero preworld).
  (*put the g back on*)
match goal with |- tr ?G (deq ?M ?M ?T) =>
                replace T with
    (trans_type (var 6) (var 5) (comp_m A)) end.
eapply tr_arrow_elim. apply (@Gamma_at_type _ G); auto. (*start here replace the replaces with match*)
weaken trans_type_works; auto.
simpl. simpsub_type; auto. simpsub. simpl.
(*have to get type in the form subst1 lv type
 for the pi elim rule*)
replace (arrow (Gamma_at G (var 6) (var 5))
          (all nzero preworld
             (pi nattp
                (arrow
                   (subseq (ppair (var 8) (var 7)) (ppair (var 1) (var 0)))
                   (arrow (store (ppair (var 1) (var 0)))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (ppair (var 1) (var 0))))
                                  (trans_type (var 1) (var 0) A)))))))))) with
    (subst1 (var 5)
(arrow (Gamma_at G (var 7) (var 0))
          (all nzero preworld
             (pi nattp
                (arrow
                   (subseq (ppair (var 9) (var 2)) (ppair (var 1) (var 0)))
                   (arrow (store (ppair (var 1) (var 0)))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (ppair (var 1) (var 0))))
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
                      (arrow (store (ppair (var 1) (var 0)))
                         (laters
                            (exist nzero preworld
                               (sigma nattp
                                  (prod
                                     (prod
                                        (subseq
                                         (ppair (var 3) (var 2))
                                         (ppair (var 1) (var 0)))
                                        (store
                                         (ppair (var 1) (var 0))))
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
apply trans_type_works2; auto.
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
replace (store (ppair (var 3) (var 2)))
  with (subst (sh 1) (store (ppair (var 2) (var 1)))); auto.
apply tr_hyp_tm; repeat constructor.
(*done with et1, ramping up to et2*)
- simpl.
 rewrite subst_bind.
 simpsub_big. rewrite subst_trans_type; auto. unfold make_subseq. simpsub. fold make_subseq.
 apply tr_arrow_intro; try comptype. simpsub_big. simpl.
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
                      (store (ppair (var 1) (var 0))))
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
                                      prod (prod (subseq V V1) (store V1))
                                                     (trans_type v1 lv1 B))))
        ) .
(*engage Et2*)
 (*pop the store off*)
eapply (tr_arrow_elim _ (store (ppair (var 1) (picomp1 (var 0))))); simpl; auto.
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
             (store (ppair (var 2) (var 0)))
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
                            (store
                               (ppair (var 1) (var 0))))
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
             (arrow (store (ppair (var 1) (var 0)))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq
                                  (ppair (var 3) (var 2))
                                  (ppair (var 1) (var 0)))
                               (store
                                  (ppair (var 1) (var 0))))
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
                   (arrow (store (ppair (var 1) (var 0)))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (ppair (var 1) (var 0))))
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
                      (arrow (store (ppair (var 1) (var 0)))
                         (laters
                            (exist nzero preworld
                               (sigma nattp
                                  (prod
                                     (prod
                                        (subseq
                                         (ppair (var 3) (var 2))
                                         (ppair (var 1) (var 0)))
                                        (store
                                         (ppair (var 1) (var 0))))
                                     (trans_type 
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
apply trans_type_works2; auto. var_solv. auto.
simpl. apply Gamma_at_intro; auto.
eapply (move_gamma_works _ _ (var 9) (var 8)); auto.
eapply (compose_sub_works (picomp2 (var 0)) (var 4)
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
                      (store (ppair (var 1) (var 0))))
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
eapply (compose_sub_works (picomp2 (var 0)) (picomp2 (var 3))
                          _ (ppair (var 4) (
                                     ppi1 (var 3)))); auto.
sh_var 3 9.
rewrite - ! subst_sh_shift.
rewrite - ! subst_picomp2 - ! subst_ppi1 - ! subst_ppair - !
                                                             subst_subseq ! subst_sh_shift.
match goal with |- tr (?x::?y::?z::?G') ?J =>                 
         change (?x::?y::?z::G') with ([:: x; y; z] ++ G')
end.
apply tr_weakening_append; auto.
auto. repeat fold (@subst1 False).
(*start here bring that guy out*)
rewrite fold_subst1 subst1_trans_type.
simpsub_big. simpl. apply picomp4_works.
weaken compm5_type; auto; try apply trans_type_works; try (apply world_pair; var_solv).
intros.
sh_var 2 11. rewrite - ! subst_sh_shift - ! subst_ppair.
weaken compm4_type; auto. apply trans_type_works; auto.
}
  1: {
    constructor; auto.
simpsub_bigs. simpl. apply tr_pi_intro; auto.
apply tr_arrow_intro; auto.
apply Gamma_at_type; auto. 
match goal with |- tr ?G (deqtype ?A ?A) =>
               (change A with
(trans_type (var 1) (var 0) (comp_m B))) end; auto.
weaken trans_type_works; auto. (*have popped off G*)
simpsub_big. simpl. constructor; auto; simpsub_big; simpl.
constructor; auto.
apply tr_arrow_intro; auto.
  }


Theorem onef: forall G e T ebar w1 l1,
    of_m G e T ->
    tr [::] (oof (ppair w1 l1) world) ->
    trans G e ebar -> 
    tr (Gamma_at_ctx G w1 l1) (oof (app (app ebar l1) 
              (arrow (Gamma_at G w1 l1) (trans_type w1 l1 T))).
