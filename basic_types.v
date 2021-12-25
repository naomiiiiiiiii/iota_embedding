(*Trivial facts that would clutter up the other files*)
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined lemmas0 derived_rules.


Definition U0 : (term obj) := univ nzero.

Lemma subst_nat: forall s,
    @ subst obj s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat: core subst1.

Ltac weaken H := eapply tr_formation_weaken; apply H.
Ltac var_solv0 := try (apply tr_hyp_tm; repeat constructor).

Hint Rewrite subst_nat: core subst1.

Ltac var_solv' := unfold oof; match goal with |- tr ?G' (deq (var ?n) ?n' ?T) => try
                                 rewrite - (subst_nat (sh (n.+1))); var_solv0 end.

Lemma equiv_arrow :
  forall (m m' n n' : term obj),
    equiv m m'
    -> equiv n n'
    -> equiv (arrow m n) (arrow m' n').
Proof.
prove_equiv_compat.
Qed.

Lemma nat_U01 G: tr ((hyp_tm booltp)::G) (oof (bite (var 0) voidtp unittp) U0).
change U0 with (subst1 (var 0) U0).
apply tr_booltp_elim. change booltp with (@subst obj (sh 1) booltp). var_solv0. apply tr_voidtp_formation. apply tr_unittp_formation.
Qed.


Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.
Hint Resolve nat_U0. 

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.
Hint Resolve nat_type. 
Lemma unit_type: forall G,
      tr G (deqtype unittp unittp). Admitted.
Hint Resolve unit_type. 

Lemma nsucc_type G n:
  tr G (oof n nattp) ->
  tr G (oof (nsucc n) nattp). Admitted.
Hint Resolve nsucc_type. 

Definition leq_t n m : term obj :=
  app (app leqtp n) m.

Definition lt_t n m : term obj :=
  app (app lttp n) m.

Lemma zero_typed: forall G,
    tr G (oof nzero nattp). Admitted.

Lemma leq_refl: forall G n,
    tr G (deq n n nattp) ->
    tr G (oof triv (leqpagetp n n)). Admitted.

Lemma leq_type: forall G n1 n2,
    tr G (oof n1 nattp) -> tr G (oof n2 nattp) ->
    tr G (oof (leq_t n1 n2) U0).
  Admitted.


Lemma lt_type: forall G n1 n2,
    tr G (oof n1 nattp) -> tr G (oof n2 nattp) ->
    tr G (oof (ltpagetp n1 n2) U0).
  Admitted.


Lemma U0_type: forall G,
    tr G (deqtype U0 U0). Admitted.

Hint Resolve nat_type nat_U0 zero_typed leq_refl leq_type lt_type U0_type.

Definition if_z (n: term obj): (term obj) := ppi1 n.


Lemma if_z_typed n G : tr G (oof n nattp) -> tr G (oof (if_z n) booltp).
Admitted.

(*n - m*)
Definition minusbc: (term obj) := lam
                         (
                           (*f := 0*)
                           lam ( (*f:= 1, n := 0*)
                               lam ((*f := 2, n:= 1, m := 0*)
                                   let f := (var 2) in
                                   let n := (var 1) in
                                   let m := (var 0) in
                                                  bite (if_z n)
                                                  (n)
                                                  (bite (if_z m)
                                                     (n)
                                                    (app (app f (app (ppi2 n) triv)) (app (ppi2 m) triv)))
                                                  ))).
 Definition minus: (term obj) := app theta minusbc.

 Lemma minus_typed {G}: tr G (oof minus (arrow nattp (arrow nattp nattp))).
Admitted.

(*lt_b x y*)
 Definition lt_b := lam ( lam (*x = 1, y = 0*)

                            (if_z (app (app minus (nsucc (var 1)))  (var 0)))
                       ).

Definition ltb_app m n := app (app lt_b m) n.

(*should be fine*)
Lemma ltapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (ltb_app m n) booltp). Admitted.

(*more difficult, need induction*)
Lemma ltb_false G n : tr G (oof n nattp) -> tr G (deq (ltb_app n n) bfalse booltp).
Admitted.

Lemma nsucc_lt: forall G n, tr G (oof n nattp) ->
                       tr G (oof triv (lt_t n (nsucc n))).
Admitted.

Definition eq_b n1 := app (wind (lam (* x = 0*)
                             (lam (*x = 1, y= 0*)
                                ( lam
                                    ( (*x = 2, y = 1, z = 0*)
                                      bite (var 2)
                                           (lam (*x = 3, y = 2, z = 1, n2 = 0*)
                                              (if_z (var 0))
                                           ) (*first one is zero*)
                                           ( (*first one is nonzero*)
                                             lam
                                               ( (*x = 3, y = 2, z = 1, n2 = 0*)
                                                 bite (if_z (var 0))
                                                      bfalse
                                                      (app (app (var 1) triv) (app (ppi2 (var 0)) triv))
                                               )
                                           )
                                    )
                                )
                             )                           
                          )) n1.


Lemma w_elim_hyp G1 G2 a b J :
  tr G1 (deqtype a a) ->
      tr (cons (hyp_tm a) G1) (deqtype b b) ->
      tr (G2 ++ hyp_tm (sigma a (arrow b (subst sh1 (wt a b)))) :: G1) J
      -> tr (G2 ++ hyp_tm (wt a b) :: G1) J.
  intros. eapply tr_subtype_convert_hyp; unfold dsubtype;
  change triv with (@shift obj 1 triv);
  change (subtype
       (subst sh1 ?one)
       (subst sh1 ?sigma)) with
      (subst sh1 (subtype one sigma)) (*ask karl if i write shift here it doesnt work*); try rewrite ! subst_sh_shift;
    try apply tr_weakening_append1. apply tr_wt_subtype_sigma; auto.
  apply tr_wt_sigma_subtype; auto.
  assumption.
Qed.




           Lemma eqb_typed {G} n1:
  tr G (oof n1 nattp) ->
  tr G (oof (eq_b n1) (arrow nattp booltp)).
  intros.
  change (arrow nattp booltp) with (subst1 n1 (arrow nattp booltp)).
  apply (tr_wt_elim _ booltp (bite (var 0) voidtp unittp)).
  - assumption.
  - simpsub. simpl.
    rewrite make_app2.
    change (lam (if_z (var 0))) with
      (subst (under 2 sh1)  (lam (if_z (var 0)))).
    change (lam
             (bite (if_z (var 0)) bfalse
                (app (app (var 1) triv)
                     (app (ppi2 (var 0)) triv)))) with
        (subst (under 2 sh1)
(lam (bite (if_z (var 0)) bfalse
                (app (app (var 1) triv)
                     (app (ppi2 (var 0)) triv))))
        ).
    apply tr_booltp_eta_hyp; simpsub; simpl; simpsub; rewrite ! subst_nat;
      apply tr_arrow_intro; auto; try weaken tr_booltp_formation.
    + apply if_z_typed. var_solv'.
    + apply (w_elim_hyp _ [::]).
      weaken tr_booltp_formation. weaken nat_U01.
      match goal with |- tr ?G (deq ?M ?M ?A) => change M with
       (@subst obj (under 0 (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)))
       (bite (var 1) bfalse
          (app (app (var 2) triv)
               (app (var 0) triv)))) end.
      apply tr_sigma_eta_hyp.
      simpsub. simpl.
          change (app (app (var 2) triv)
                      (app (var 0) triv)) with
              (@subst obj (under 1 sh1)
                     (app (app (var 1) triv)
                          (app (var 0) triv))).
          change bfalse with (@subst obj (under 1 sh1) bfalse).
          rewrite make_app1.
          apply tr_booltp_eta_hyp; simpsub.
      * constructor.
      * eapply tr_compute_hyp.
        {
          constructor. apply equiv_pi. apply reduce_equiv.
          apply reduce_bite_beta2. apply reduce_id.
          apply equiv_refl.
        }
        simpl. eapply (tr_compute_hyp _ [::]).
        {
          constructor. apply equiv_arrow. apply reduce_equiv.
          apply reduce_bite_beta2. apply reduce_id.
          apply equiv_refl.
        }
        simpl.
        apply (tr_arrow_elim _ nattp); auto. weaken tr_booltp_formation.
        change (arrow nattp booltp) with (@subst1 obj triv (arrow nattp booltp)). 
        apply (tr_pi_elim _ (unittp)).
        - change (pi unittp (arrow nattp booltp))
          with (@subst obj (sh 2) (pi unittp (arrow nattp booltp))).
        var_solv0. constructor.
        - apply (tr_arrow_elim _ unittp); auto. 
          change (arrow unittp nattp) with (@subst obj (sh 1) (arrow
                                                                 unittp nattp)).
          var_solv0.
          constructor.
Qed.


Definition nat_ind_fn : (term obj) := lam (lam (lam (lam (*P = 3 BC = 2 IS = 1 x = 0 *)
                                          (app (
                                            wind ( lam (lam (lam ( (*c = 0, b= 1, a = 2, x = 3, IS = 4, BC = 5,
                                                                    P = 6*)
                                                                 bite (var 2) (var 5)
                                                                      (app (app (var 4)
                                                                           (app (var 1) triv))
                                                                           (app (var 0) triv))
                          )))))                
                                               (var 0)
                                          )
                                               ))).

Definition nat_elim G := (tr_wt_elim G booltp (bite (var 0) voidtp unittp)).

Lemma tr_wt_intro :
    forall G a b m m' n n',
      tr G (deq m m' a)
      -> tr G (deq n n' (subst1 m (arrow b (subst sh1 (wt a b)))))
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (deq (ppair m n) (ppair m' n') (wt a b)).
  Admitted.

  Lemma nat_ind G : tr G (oof nat_ind_fn
                              (pi (arrow nattp U0)
                                  (pi (app (var 0) nzero)
                                         (pi (pi nattp
                                                    (
                                                      arrow (app (var 2) (var 0))
                                                            (app (var 2) (nsucc (var 0)))
                                                           )
                                                )
                                                (pi nattp
                                                    (app (var 3) (var 0))
                                                )
                                         )
                                  )
                         )).
    intros.
    assert (forall G2 x y, tr (G2 ++ (hyp_tm (arrow nattp U0) :: G))
                       (deq x y nattp) ->
        (tr (G2 ++ (hyp_tm (arrow nattp U0) :: G))
            (deqtype (app (var (length G2)) x) (app (var (length G2)) y)))) as Hp.
    intros.
      eapply tr_formation_weaken. apply (tr_arrow_elim _ nattp); auto.
      apply U0_type.
change (arrow (nattp) (univ nzero)) with
    (@subst obj (sh (length G2)) (arrow nattp (univ nzero))). change (var (length G2)) with (@subst obj (sh (length G2)) (var 0)). rewrite ! subst_sh_shift. apply tr_weakening_append.
change (arrow (nattp) (univ nzero)) with
    (@subst obj (sh 1) (arrow nattp (univ nzero))). var_solv0.
    simpl.
    apply tr_pi_intro. apply tr_arrow_formation; auto.
    apply tr_pi_intro; auto.
    + apply (Hp [::]); auto.
  (*  + apply tr_arrow_formation; auto. apply tr_pi_formation; auto.
      apply tr_arrow_formation; auto.
      rewrite make_app1. eapply Hp; auto. simpl. var_solv'.
      rewrite make_app1. eapply Hp; simpl; auto. apply nsucc_type. var_solv'.
      apply tr_pi_formation; auto.
      rewrite make_app1. eapply Hp; auto. simpl. var_solv'.*)
    + apply tr_pi_intro; auto.
      - apply tr_pi_formation; auto. apply tr_arrow_formation; auto.
      rewrite make_app2. eapply Hp; auto. simpl. var_solv'.
      rewrite make_app2. eapply Hp; simpl; auto. apply nsucc_type. var_solv'.
      - apply tr_pi_intro; auto. change (app (var 3) (var 0)) with
                                     (@subst1 obj (var 0) (app (var 4) (var 0))).
        eapply nat_elim. fold (@nattp obj). var_solv'.
        change (var 5) with (@subst obj (under 2 sh1) (var 4)).
        change (app (app (var 4) (app (var 1) triv))
                    (app (var 0) triv)) with (@subst obj (under 2 sh1)
(app (app (var 3) (app (var 1) triv))
                    (app (var 0) triv)) 
                                             ).
        rewrite make_app2. apply tr_booltp_eta_hyp. (*true case*)
        { repeat (simpl; simpsub). rewrite make_app1.
          eapply tr_compute_hyp.
        {
          constructor. apply equiv_arrow. apply reduce_equiv.
          apply reduce_bite_beta1. apply reduce_id.
          apply equiv_refl.
        }
        simpl. eapply (tr_compute_hyp _ [::]).
        {
          constructor. apply equiv_pi. apply reduce_equiv.
          apply reduce_bite_beta1. apply reduce_id.
          apply equiv_refl.
        }
        simpl.
        apply (tr_eqtype_convert _#3 (app (var 5) nzero)).
        { 
          rewrite make_app5. apply Hp.
          unfold nzero. apply tr_wt_intro. constructor.
          simpsub. eapply tr_compute.
          apply equiv_arrow. apply reduce_equiv.
          apply reduce_bite_beta1. apply reduce_id.
          apply equiv_refl. apply equiv_refl. apply equiv_refl.
          apply (tr_transitivity _ _ (lam (app (subst sh1 (var 1)) (var 0))) ).
          {
            simpsub. simpl. apply tr_arrow_intro; auto.
            - weaken tr_voidtp_formation.
              apply (tr_voidtp_elim _ (var 0) (var 0)).
              change voidtp with (@subst obj (sh 1) voidtp).
              var_solv0.
          }
          apply tr_symmetry. apply tr_arrow_eta.
          change 
            (arrow voidtp (wt booltp (bite (var 0) voidtp unittp)))
            with (@subst obj (sh 2)
            (arrow voidtp (wt booltp (bite (var 0) voidtp unittp)))
                 ). var_solv0.
          apply tr_booltp_elim_eqtype. change booltp with (@subst obj (sh 1) booltp). var_solv0. weaken tr_voidtp_formation. weaken tr_unittp_formation. }
        change (app (var 5) nzero) with
            (@subst obj (sh 5) (app (var 0) nzero)). var_solv0. }
        (*false case*)
        { repeat (simpl; simpsub). rewrite make_app1.
          eapply tr_compute_hyp.
        {
          constructor. apply equiv_arrow. apply reduce_equiv.
          apply reduce_bite_beta2. apply reduce_id.
          apply equiv_refl.
        }
        simpl. eapply (tr_compute_hyp _ [::]).
        {
          constructor. apply equiv_pi. apply reduce_equiv.
          apply reduce_bite_beta2. apply reduce_id.
          apply equiv_refl.
        }
        simpl.
        apply (tr_eqtype_convert _#3 (app (var 5) (ppair bfalse
                                                         (lam (app (var 2) triv))
              ))).
        rewrite make_app5. apply Hp. apply tr_wt_intro; auto. constructor.
        (*b = \x.b * *)
        {
          simpsub.
          eapply tr_compute. apply equiv_arrow.
           apply reduce_equiv.
           apply reduce_bite_beta2. apply reduce_id. apply equiv_refl. apply equiv_refl.
           apply equiv_refl.
          simpsub. simpl. 
          apply (tr_transitivity _ _
                                           (lam (app (var 2) (var 0)))
                          ).
          {
            apply tr_arrow_intro; auto.
            apply (tr_arrow_elim _ unittp); auto.
            match goal with |- tr ?G (deq ?M ?M ?T) =>
                                                      change T with
       (@subst obj (sh 3)                                   
       (arrow unittp
          (wt booltp
              (bite (var 0) voidtp unittp)))) end. var_solv0.
          apply tr_symmetry. apply tr_unittp_eta.
          change unittp with (@subst obj (sh 1) unittp). var_solv0.
          }
          {
            apply tr_symmetry.
            apply tr_arrow_eta.
            match goal with |- tr ?G (deq ?M ?M ?T) =>
                                                      change T with
       (@subst obj (sh 2)                                   
       (arrow unittp
          (wt booltp
              (bite (var 0) voidtp unittp)))) end. var_solv0.
          }
        }
        weaken nat_U01.
        (* IS (b triv ) (c triv) : P (succ (b triv )) *)
        apply (tr_arrow_elim _ (app (var 5) (app (var 1) triv))).
          * rewrite make_app5. apply Hp.
            apply (tr_arrow_elim _ unittp); auto. 
            change (arrow unittp nattp) with (@subst obj (sh 2)
                                                     (arrow unittp nattp)).
            var_solv0. constructor.
            rewrite make_app5. apply Hp.
            change (ppair bfalse (lam (app (var 2) triv))) with
                (@nsucc obj (app (var 1) triv)).
            apply nsucc_type.
            apply (tr_arrow_elim _ unittp); auto.
            change (arrow unittp nattp) with (@subst obj (sh 2)
                                                     (arrow unittp nattp)).
            var_solv0. constructor.
            match goal with |- tr ?G (deq ?M ?M ?T) => change T with
                (@subst1 obj (app (var 1) triv)
                (arrow (app (var 6) (var 0))
          (app (var 6)
               (ppair bfalse (lam (var 1)))))
                ) end.
            apply (tr_pi_elim _ nattp).
            match goal with |- tr ?G (deq ?M ?M ?T) => change T with
                (@subst obj (sh 4)
       (pi nattp
          (arrow (app (var 2) (var 0))
             (app (var 2)
                  (ppair bfalse (lam (var 1))))))) end.
            var_solv0.
            apply (tr_arrow_elim _ unittp); auto.
            change (arrow unittp nattp) with (@subst obj (sh 2)
                                                     (arrow unittp nattp)).
            var_solv0. constructor.
            change (app (var 5) (app (var 1) triv)) with (@subst1 obj triv
(app (var 6) (app (var 2) (var 0)))
                                                         ).
            apply (tr_pi_elim _ unittp). 
            change (pi unittp (app (var 6) (app (var 2) (var 0))))
              with (@subst obj (sh 1)
(pi unittp (app (var 5) (app (var 1) (var 0))))
                   ). var_solv0.
            constructor. }
            Qed.

  Lemma nat_ind_app G P BC IS: tr G (oof P (arrow nattp U0)) ->
                        tr G (oof BC (app P nzero)) ->
                        tr G (oof IS
                                  (pi nattp
                                      (arrow (app P (var 0))
                                             (app P (nsucc (var 0)))
                                  ))) ->
                              tr G (oof (app (app (app nat_ind_fn P) BC
                                   ) IS)
                                                (pi nattp
                                                    (app (shift 1 P) (var 0))
                                   )).
    intros.
    replace (pi nattp (app (shift 1 P) (var 0))) with
        (subst1 IS
(pi nattp (app (shift 2 P) (var 0)))
        ).
    2:{
      rewrite - ! subst_sh_shift. simpsub. unfold subst1. rewrite subst_nat. auto.
    }
    apply (tr_pi_elim _
           (pi nattp
             (arrow (app (shift 1 P) (var 0))
                      (app (shift 1 P) (nsucc (var 0))))
          )).
    match goal with |- tr ?G (deq ?T ?T ?A) =>
                    replace A with
        (subst1 BC
       (pi
          (pi nattp
             (arrow (app (shift 2 P) (var 0))
                (app (shift 2 P)
                   (nsucc (var 0)))))
          (pi nattp
             (app (shift 3 P) (var 0))))) end.
    2:{ unfold nsucc.
      rewrite - ! subst_sh_shift. simpsub. unfold subst1. rewrite ! subst_nat.
      simpsub. auto.
    }
    apply (tr_pi_elim _ (app P nzero)).
    match goal with |- tr ?G (deq ?T ?T ?A) =>
                    replace A with (subst1 P
       (pi (app (var 0) nzero)
          (pi
             (pi nattp
                (arrow
                   (app (var 2)
                      (var 0))
                   (app (var 2)
                      (nsucc (var 0)))))
             (pi nattp
                 (app (var 3) (var 0)))))) end.
    eapply tr_pi_elim; try apply nat_ind; auto.
    unfold nsucc. simpsub. rewrite ! subst_nattp.


        )

          )

                             )

    Tr G (oof nat_ind_fn
                              (pi (arrow nattp U0)
                                  (pi (app (var 0) nzero)
                                         (pi (pi nattp
                                                    (
                                                      arrow (app (var 2) (var 0))
                                                            (app (var 2) (nsucc (var 0)))
                                                           )
                                                )
                                                (pi nattp
                                                    (app (var 3) (var 0))
                                                )
                                         )
                                  )
                         )).

(*do a lemma for applying nat ind*)


Lemma eqb_P G n m : tr G (oof n nattp) ->
                    tr G (oof m nattp) ->
  tr G (deq (app (app eq_b n) m) btrue booltp) ->
                    tr G (deq n m nattp).
  intros.
Admitted.

          Lemma eqapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (app (eq_b m) n) booltp). Admitted.



