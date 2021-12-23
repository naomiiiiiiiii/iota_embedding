(*Trivial facts that would clutter up the other files*)
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined lemmas0 derived_rules.


Definition U0 : (term obj) := univ nzero.

Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.
Hint Resolve nat_U0. 

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.
Hint Resolve nat_type. 

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

Lemma subst_nat: forall s,
    @ subst obj s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat: core subst1.

Ltac weaken H := eapply tr_formation_weaken; apply H.
Ltac var_solv0 := try (apply tr_hyp_tm; repeat constructor).

Hint Rewrite subst_nat: core subst1.

Ltac var_solv' := unfold oof; match goal with |- tr ?G' (deq (var ?n) ?n' ?T) => try
                                 rewrite - (subst_nat (sh (n.+1))); var_solv0 end.

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



Lemma equiv_arrow :
  forall (m m' n n' : term obj),
    equiv m m'
    -> equiv n n'
    -> equiv (arrow m n) (arrow m' n').
Proof.
prove_equiv_compat.
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
    + apply (w_elim_hyp _ [::]). match goal with |- tr ?G (deq ?M ?M ?A) => change M with
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
        - apply (tr_arrow_elim _ unittp); auto. weaken tr_unittp_formation.
          change (arrow unittp nattp) with (@subst obj (sh 1) (arrow
                                                                 unittp nattp)).
          var_solv0.
          constructor.
Qed.

          Lemma eqapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (app (eq_b m) n) booltp). Admitted.

Lemma eqb_P G n m : tr G (oof n nattp) ->
                    tr G (oof m nattp) ->
  tr G (deq (app (app eq_b n) m) btrue booltp) ->
                    tr G (deq n m nattp).
  intros.
Admitted.


