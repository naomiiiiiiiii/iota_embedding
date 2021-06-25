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



Ltac simpsubg :=
  match goal with |- (tr ?G (deq ?M ?M ?T)) =>
autounfold with subst1 in M;
autounfold with subst1 in T;
autorewrite with subst1 in M;
autorewrite with subst1 in T
  end.

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
constructor; auto. 
simpsub_big. simpl. apply tr_pi_intro; auto.
apply tr_arrow_intro; auto.
apply Gamma_at_type; auto;
  [rewrite - {2}(subst_pw (sh 2)) |
   rewrite - {2} (subst_nat (sh 1))]; var_solv.
eapply tr_formation_weaken.
match goal with |- tr ?G (deq ?A ?A ?T) =>
               (change A with
(trans_type (var 1) (var 0) (comp_m B))) end; auto.
eapply trans_type_works; auto. (*have popped off G*)
simpsub_big. simpl. constructor; auto; simpsub_big; simpl.
constructor; auto.
apply tr_arrow_intro; auto.
eapply tr_formation_weaken.
    eapply compm1_type; auto. rewrite subst_trans_type; auto.
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
  (*start here can this be shorter with some sort of mapping*)
  Ltac comptype := replace (@ppair False (var 5) (var 4)) with (@subst False (sh 2) (ppair (var 3) (var 2))); auto; eapply tr_formation_weaken; try apply compm4_type; try apply compm3_type;
                   try apply compm2_type;
                   try apply compm1_type; try apply compm0_type; auto;
try apply trans_type_works; auto.
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
eapply tr_arrow_elim. apply (@Gamma_at_type _ G); [eapply split_world1 |
                                                   eapply split_world2]; apply uworld65.
(*start here replace the replaces with match*)
eapply tr_formation_weaken; apply (trans_type_works (var 6) (var 5)); auto. simpl. simpsub_big. simpl.
simpsub. simpl. rewrite subst_trans_type; auto.
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
             (ret_a
                (ppair (ppi1 (var 0))
                   (ppair make_subseq
                      (ppair (picomp3 (var 0)) (picomp4 (var 0)))))))
     )) end.
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
} eapply tr_formation_weaken; apply trans_type_works; auto.
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
apply trans_typed1; auto. var_solv. auto.
simpl. apply Gamma_at_intro; auto.
eapply (move_gamma_works _ _ (var 9) (var 8)).
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
  + simpsub_big. simpl. apply ret_type.
    match goal with |- (tr ?G' (oof ?M ?T)) => change M with
        (subst1 (var 0)
          (ppair (ppi1 (var 0))
             (ppair make_subseq
                (ppair (picomp3 (var 0))
                   (picomp4 (var 0))))))
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
simpsub_big. simpl. rewrite ! subst_trans_type; auto.
      change (ppair (var 4)
                    (ppi1 (var 3))) with
          (@shift False 1 (ppair (var 3) (ppi1 (var 2)))).
change (var 1) at 1 2 with (@shift False 1 (var 0)).
apply (tr_exist_intro _ _ _ _ (var 1)); auto.
    * var_solv.
      simpsubg.
      simpsub_type; auto.
      apply tr_sigma_intro; auto.
      - apply picomp1_works.
        match goal with |- tr (?y::(?x::?G')) (oof ?M ?T) =>
                        change (y::x::G') with ([:: y; x] ++ G');
           (change M with
                (@shift False 2 (ppair (var 1) (ppi1 (var 0))))
           ); change (y::x::G') with ([:: y; x] ++ G'); change T with
(@shift False 2 T)
end.
apply tr_weakening_append; auto. var_solv.
simpsub_big. simpl. (*get rid of the subst1 trans type here if it becomes
                     annoying*)
change (ppair (var 4) (ppi1 (var 3))) with
    (@shift False 1 (ppair (var 3) (ppi1 (var 2))))
apply tr_prod_intro; constructor.
        * apply subseq_type; auto.
          apply picopm_world.
      - change (ppair (var 3) (ppi1 (var 2))) with
            (@shift False 2 (ppair (var 1) (ppi1 (var 0)))).
        rewrite - (subst_world (sh 2)) subst_sh_shift.
      rewrite subst1_trans_type. simpl.

      rewrite ! subst_trans_type; auto.
simpsub_type.


        eapply tr_exist_intro.
  eapply tr_formation_weaken; apply compm3_type; auto.
  apply trans_type_works; auto.
apply world_pair; auto; try var_solv.
eapply IHDe1; try assumption . simpsub_type; auto.




 replace
       (make_bind
          (app
             (app
                (app
                   (app
                      (lam
                         (subst
                            (dot (var 0) (sh 6))
                            (move_Gamma G
                              make_subseq 1
                              (app Et2
                              (picomp1 (var 0))))))
                      (picomp4 (var 0)))
                   (ppi1 (var 0))) make_subseq)
             (picomp3 (var 0)))
          (lam
             (ret_a
                (ppair (ppi1 (var 0))
                   (ppair make_subseq
                      (ppair (picomp3 (var 0))
                         (picomp4 (var 0)))))))) with
       (subst1 (var 0) (make_bind
             (app
                (app
                   (app
                      (app
                         (lam
                            (subst (dot (var 0) (sh 6))
                               
                            (move_Gamma G
                              make_subseq 1
                              (app Et2
                              (picomp1 (var 0))))))

                         (picomp4 (var 0))) 
                      (ppi1 (var 0)))
                make_subseq) (picomp3 (var 0)))
          (lam
             (app ret
                (ppair (ppi1 (var 0))
                   (ppair make_subseq
                          (ppair (picomp3 (var 0)) (picomp4 (var 0)))))))) ).
   simpl.
   replace (subst (sh (size G + 1 + 1).+4) l1)
     with (subst sh1
                 (subst (sh (size G + 1+ 1).+3) l1)
          ).
   subst. rewrite out_of_lam.
   rewrite - subst_lam.
(*trying to replace with karl's substitution*)
   assert (
                         (compose
                            (gen_sub_mvl_list (size G) 5)
                            (dot (var 0)
                               (dot (var 1)
                                  (dot (var 2)
                                     (dot 
                                       (var 3)
                                       (dot
                                       (subst
                                       (sh
                                       (size G + 1 + 1).+3)
                                       l1) 
                                       (sh 5)))))))
     )


   rewrite compose_under.
simpl.
(*trying to figure out what the substitution around
 move Gamma actually is*)
   (*start here*)
   (*IDEA: do the move when there's only one variable to move: before 72*)
   subst.
fold gen_sub_mvl_list.

   (*rule 72*)
   eapply (tr_exist_elim _ (subst (sh 1) nzero)
                         (subst (sh 1) preworld) 
             (subst (under 1 (sh 1)) (sigma nattp
                (prod
                   (prod
                      (subseq (ppair (var 5) (var 4))
                         (ppair (var 1) (var 0)))
                      (store (ppair (var 1) (var 0))))
                   (trans_type (var 1) (var 0) A)))) ).
 -  rewrite - subst_exist. var_solv.
    apply pw_type. simpsub_big. simpl.
   replace (ppair (var 6) (var 5)) with
       (@subst False (sh 2)
              (ppair (var 4) (var 3))
       ). comptype.
   eapply tr_formation_weaken; apply compm4_type.
   clear Hequiv Hequivt.
   eapply uworld43.
   rewrite subst_trans_type. apply trans_type_works.
   auto. simpsub. auto. simpsub. auto.
   simpsub_big. simpl.
   rewrite subst_trans_type.
   unfold subst1. simpsub1.
   (*make bind*)
   rewrite subst_bind. simpsub_big. simpl.
    eapply (bind_type _
                      (exist nzero preworld (
                                          sigma nattp (*l1 = 6 u := 5, l := 4, v= 1, lv := 0*)
                                          (let u := Syntax.var 3 in
                              let l := (picomp1 (Syntax.var 2)) in
                                              let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let U := ppair u l in
                                              let V := ppair v lv in
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq U V) (store V))
                                                     (trans_type v lv B))))
                                 ).
    (*et2*)
    apply (tr_arrow_elim _ (store (ppair (var 1) (picomp1 (var 0))) )).
 - eapply tr_formation_weaken; eapply store_U0.
   apply world_pair. var_solv. eapply picomp1_works.
 - simpl.
   replace (ppair (var 3) (picomp1 (var 2))) with
       (subst (sh 2) (ppair (var 1) (picomp1 (var 0)))). 
   eapply tr_formation_weaken; apply compm2_type.
   apply picomp_world. apply trans_type_works; auto. simpsub; auto.
 - apply (tr_arrow_elim _ (subseq (ppair (var 1) (picomp1 (var 0)))
                                  (ppair (var 1) (picomp1 (var 0)))
         )).
   eapply tr_formation_weaken; apply subseq_U0.
   apply picomp_world.
   apply picomp_world.
simpl.
   replace (ppair (var 3) (picomp1 (var 2))) with
       (subst (sh 2) (ppair (var 1) (picomp1 (var 0)))). 
eapply tr_formation_weaken; apply compm1_type. apply picomp_world.
apply trans_type_works. auto. simpsub; auto.
(*need to have a sub before i can pi elim*)
- 
assert (
       (arrow
          (subseq (ppair (var 1) (picomp1 (var 0)))
             (ppair (var 1) (picomp1 (var 0))))
          (arrow
             (store
                (ppair (var 1) (picomp1 (var 0))))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (let u := var 3 in
                       let l := picomp1 (var 2) in
                       let v := var 1 in
                       let lv := var 0 in
                       let U := ppair u l in
                       let V0 := ppair v lv in
                       prod
                         (prod (subseq U V0)
                            (store V0))
                         (trans_type v lv B))))))) =
subst1 (picomp1 (var 0)) 
       (arrow
          (subseq (ppair (var 2) (picomp1 (var 1)))
             (ppair (var 2) (var 0)))
          (arrow
             (store
                (ppair (var 2) (var 0)))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (let u := var 4 in
                       let l := var 2 in
                       let v := var 1 in
                       let lv := var 0 in
                       let U := ppair u l in
                       let V0 := ppair v lv in
                       prod
                         (prod (subseq U V0)
                            (store V0))
                         (trans_type v lv B)))))))) as Hsub.
simpsub. unfold subst1; simpsub1. simpsub_big.
simpl. unfold subst1. simpsub1.
rewrite subst_trans_type. auto. simpsub. auto.
rewrite Hsub.
eapply (tr_pi_elim _ nattp).
(*need a forall here to get exactly comp 2 before i go into the x lambda*)
    assert(   
       (pi nattp
          (arrow
          (subseq (ppair (var 2) (picomp1 (var 1)))
                (ppair (var 2) (var 0)))
             (arrow (store (ppair (var 2) (var 0)))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (let u := var 4 in
                          let l := var 2 in
                          let v := var 1 in
                          let lv := var 0 in
                          let U := ppair u l in
                          let V0 := ppair v lv in
                          prod
                            (prod 
                               (subseq U V0)
                               (store V0))
                            (trans_type v lv B))))))))
 =
subst1 (var 1) 
       (pi nattp
          (arrow
          (subseq (ppair (var 3) (picomp1 (var 2)))
                (ppair (var 1) (var 0)))
             (arrow (store (ppair (var 1) (var 0)))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (let u := var 3 in
                          let l := var 2 in
                          let v := var 1 in
                          let lv := var 0 in
                          let U := ppair u l in
                          let V0 := ppair v lv in
                          prod
                            (prod 
                               (subseq U V0)
                               (store V0))
                            (trans_type v lv B)))))))))
           as Hsub2.
    simpsub_big. simpl.
    rewrite subst_trans_type.
    unfold subst1. simpsub1. auto. simpsub; auto.
    rewrite Hsub2.
    eapply (tr_all_elim _ nzero preworld).
    clear Hsub Hsub2.
    simpsub.
replace (all nzero preworld
          (pi nattp
             (arrow
                (subseq (ppair (var 3) (picomp1 (var 2)))
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
                               (trans_type (var 1) (var 0) B))))))))) with
    (subst1 (picomp1 (var 0)) (all nzero preworld
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
                               (trans_type (var 1) (var 0) B)))))))))).
replace 
    (subst1 (picomp1 (var 0)) (all nzero preworld
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
                               (trans_type (var 1) (var 0) B))))))))))
  with (trans_type (var 1) (picomp1 (var 0)) (comp_m B)).
2 : {
simpl. auto.
}
2 : { simpsub_big. simpl. unfold subst1. simpsub1.
      rewrite subst_trans_type. auto.
      simpsub; auto.
}
(*going into the et2 function*)
    apply (tr_arrow_elim _ (trans_type (var 1)
                                       (ppi1 (var 0)) A));
  try (eapply tr_formation_weaken; apply trans_type_works; apply picomp_world).
replace (dot (var 0) (sh 7)) with (@under False 1 (sh 6)).
2: {simpsub; auto. }
rewrite - subst_lam.
(*can't get rid of all of them, def still need var 1 and var 0 for the type to even work*)

apply tr_arrow_intro; try (eapply tr_formation_weaken; apply trans_type_works; apply picomp_world).
.
  apply uworld10.
assert 
       (all nzero preworld
          (pi nattp
             (arrow
                (subseq
                   (ppair
                      (subst (sh (6 + size G))
                         w1)
                      (subst (sh (6 + size G))
                         l1))
                   (ppair (var 1) (var 0)))
                (arrow
                   (store
                      (ppair (var 1) (var 0)))
                   (laters
                      (exist nzero preworld
                         (sigma nattp
                            (prod
                              (prod
                              (subseq
                              (ppair 
                              (var 3) 
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
= subst1 (subst (sh (4 + size G)) l1)
       (all nzero preworld
          (pi nattp
             (arrow
                (subseq
                   (ppair (shift 3(subst (sh (4 + size G)) w1))
                          (var 2))
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
                               (trans_type (var 1) (var 0) A))))))))))
      as Hsub3.
rewrite - subst_sh_shift.
simpsub. simpl. unfold subst1. simpsub1. simpsub_big. simpl.
repeat rewrite plusE.
rewrite subst_trans_type. repeat rewrite - addnA.
replace (3 + 2) with 5; auto.
replace (1 + 1) with 2; auto.
repeat rewrite - (addn1 (size G + 5)).
repeat rewrite - (addn4 (size G + 2)).
rewrite addnC. auto. repeat rewrite - addnA.
replace (5 + 1) with 6; auto.
replace (2 + 4) with 6; auto.
(*ask karl: a mess!!*)
rewrite Hsub3.
clear Hsub3.
assert( 
       (subst1 (subst (sh (4 + size G)) l1)
          (all nzero preworld
             (pi nattp
                (arrow
                   (subseq
                      (ppair (shift 3 (subst (sh (4 + size G)) w1))
                         (var 2)) (ppair (var 1) (var 0)))
                   (arrow (store (ppair (var 1) (var 0)))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq (ppair (var 3) (var 2))
                                        (ppair (var 1) (var 0)))
                                     (store (ppair (var 1) (var 0))))
                                  (trans_type (var 1) (var 0) A)))))))))) =
trans_type (subst (sh (4 + size G)) w1) (subst (sh (4 + size G)) l1) (comp_m A) ) as Hsub4.
simpl. auto.
rewrite Hsub4.
clear Hsub4.
rewrite - (addn2 (size G)).
repeat rewrite plusE.
repeat rewrite - (sh_sum (size G) 4).
rewrite - sh_trans_type. rewrite - subst_app.
unfold subst1. rewrite subst_pw. rewrite - hseq4.
repeat rewrite subst_sh_shift. apply tr_weakening_append.
eapply IHDe1; try assumption.

rewrite - subst_ppair. rewrite (subst_sh_shift _ (4 + (size G))).
rewrite - (addn2 (size G)).
unfold subst1. rewrite subst_pw. rewrite - Hsize.
rewrite - hseq4. rewrite catA.
rewrite hseq4. rewrite - (subst_world 4)
apply tr_weakening_append.
















(*start here with the bring shift out lemma*)
eapply tr_all_elim. clear Hsub3.
(*IH features l1 specifically*)
assert(
       (all nzero preworld
          (pi nattp
             (pi nattp
                (arrow
                   (subseq
                      (ppair (subst (sh (8 + size G)) w1)
                         (var 1)) (ppair (var 2) (var 0)))
                   (arrow (store (ppair (var 2) (var 0)))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq
                                        (ppair (var 8) (var 7))
                                        (ppair (var 1) (var 0)))
                                     (store
                                        (ppair (var 1) (var 0))))
                                  (trans_type (var 1) (var 0) A)))))))))) =
       subst (sh 5)
(all nzero preworld
          (pi nattp
             (pi nattp
                (arrow
                   (subseq
                      (ppair (subst (sh (8 + size G)) w1)
                         (var 1)) (ppair (var 2) (var 0)))
                   (arrow (store (ppair (var 2) (var 0)))
                      (laters
                         (exist nzero preworld
                            (sigma nattp
                               (prod
                                  (prod
                                     (subseq
                                        (ppair (var 8) (var 7))
                                        (ppair (var 1) (var 0)))
                                     (store
                                        (ppair (var 1) (var 0))))
                                  (trans_type (var 1) (var 0) A))))))))))

  )



    rewrite sh_sum.
    rewrite - compose_sh.
unfold subst1
repeat rewrite subst_store. simpsub.

eapply tr_pi_elim.

apply world_pair.
  var_solv.
  var_solv. apply trans_type_works.





    rewrite - (subst_world (sh 2)).
    rewrite - Hsize. rewrite - Hseq. repeat rewrite subst_sh_shift.
apply tr_weakening_append. assumption. assumption.
    auto. unfold nzero. simpsub. apply store_U0. auto.
    rewrite subst_nzero. apply A_t.
    auto. apply leq_refl. auto.

        (*do a suffices somehow*)
suffices:
          tr [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp & Gamma_at G w1 l1 ++ D]
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

Theorem onef: forall G e T ebar w1 l1,
    of_m G e T ->
    tr [::] (oof (ppair w1 l1) world) ->
    trans G e ebar -> 
    tr (Gamma_at_ctx G w1 l1) (oof (app (app ebar l1) 
              (arrow (Gamma_at G w1 l1) (trans_type w1 l1 T))).
