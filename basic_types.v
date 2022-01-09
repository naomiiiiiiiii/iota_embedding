(*Trivial facts that would clutter up the other files*) 
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined PageType lemmas0 derived_rules.

      Lemma bool_contra G J : tr G (deq bfalse btrue booltp) ->
                          tr G J.
    Admitted.
Definition if_z (n: term obj): (term obj) := ppi1 n.

Definition U0 : (term obj) := univ nzero.

Lemma U0_type: forall G,
    tr G (deqtype U0 U0). Admitted.

Hint Resolve U0_type : core.

Lemma subst_nat: forall s,
    @ subst obj s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat: core subst1.

Definition lt_t n m : term obj :=
  app (app lttp n) m.

Definition leq_b n1 := app (wind (lam (* x = 0*)
                             (lam (*x = 1, y= 0*)
                                ( lam
                                    ( (*x = 2, y = 1, z = 0*)
                                      bite (var 2) (*if n1 = 0*)
                                           (lam (*x = 3, y = 2, z = 1, n2 = 0*)
                                             btrue) 
                                           ( 
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
Definition leqb_app n1 n2 := app (leq_b n1) n2.
Definition ltb_app n1 n2 := app (leq_b (nsucc n1)) n2.


Lemma subst_U0: forall s,
    (@ subst obj s (univ nzero)) = univ nzero.
  auto. Qed.
Hint Rewrite subst_U0: core subst1.

Lemma subst_nzero: forall s,
    @ subst obj s nzero = nzero.
  intros. unfold nzero. auto. Qed.
Hint Rewrite subst_nzero: core subst1.

Lemma equiv_equal :
  forall (m m' n n' t t' : term obj),
    equiv t t' ->
    equiv m m'
    -> equiv n n'
    -> equiv (equal t m n) (equal t' m' n').
Proof.
prove_equiv_compat.
Qed.



Ltac weaken H := eapply tr_formation_weaken; apply H.
Ltac var_solv0 := try (apply tr_hyp_tm; repeat constructor).

Hint Rewrite subst_nat: core subst1.

Ltac var_solv' := unfold oof; match goal with |- tr ?G' (deq (var ?n) ?n' ?T) =>
                                              try rewrite - (subst_nat (sh (n.+1)));
                                              try rewrite - (subst_unittp _ (sh (n.+1)));
                                              try rewrite - (subst_arrow _ (sh (n.+1)));
                                                                               var_solv0 end.

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

Lemma zero_typed: forall G,
    tr G (oof nzero nattp). Admitted.
Hint Resolve zero_typed :core .
Lemma unit_type: forall G,
      tr G (deqtype unittp unittp). Admitted.
Hint Resolve unit_type. 

Lemma nsucc_type G n m:
  tr G (deq n m nattp) ->
  tr G (deq (nsucc n) (nsucc m) nattp). Admitted.
Hint Resolve nsucc_type. 

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

Ltac simpsub1 :=
autounfold with subst1; autorewrite with subst1.

Ltac simpsub_big := repeat (simpsub; simpsub1).


Hint Unfold subst1: subst1.

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
            (arrow voidtp nattp)
            with (@subst obj (sh 2)
            (arrow voidtp nattp)
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
                                      (arrow (app (shift 1 P) (var 0))
                                             (app (shift 1 P) (nsucc (var 0)))
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
      rewrite - ! subst_sh_shift. simpsub. unfold subst1. auto.
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
      rewrite - ! subst_sh_shift. simpsub. unfold subst1. 
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
    unfold nsucc. unfold nzero. simpsub. rewrite - ! subst_sh_shift. simpl.
    auto. assumption. assumption.
  Qed.


Hint Rewrite <- subst_sh_shift: core subst1.

  Lemma nat_ind_lamapp G P BC IS IS_type: tr G (oof (lam P) (arrow nattp U0)) ->
                                  tr G (oof BC (subst1 nzero P)) ->
                                  IS_type = (subst1 (nsucc (var 0)) (subst (under 1 (sh 1)) P)) ->
                        tr G (oof IS
                                  (pi nattp
                                      (arrow P IS_type
                                             
                                  ))) ->
                              tr G (oof (app (app (app nat_ind_fn (lam P)) BC
                                   ) IS)
                                                (pi nattp
                                                    P)).
    intros.
    -
      replace P with (subst1 (var 0) (subst (under 1 (sh 1)) P)) at 2.
      2:{ simpsub_big. auto. rewrite - {2} (subst_id obj P).
          apply subst_eqsub. apply eqsub_symm. apply eqsub_expand_id. }
      eapply tr_compute.
apply equiv_symm. apply equiv_pi. apply equiv_refl.
apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
apply equiv_refl. apply equiv_refl.
rewrite - subst_lam subst_sh_shift.
apply nat_ind_app; try assumption.
    - eapply tr_compute.  apply reduce_equiv; try apply reduce_app_beta;
                            apply reduce_id. apply equiv_refl. apply equiv_refl. assumption.
    - eapply tr_compute. apply equiv_pi. apply equiv_refl.
      apply equiv_arrow; rewrite - subst_sh_shift subst_lam; apply reduce_equiv; apply reduce_app_beta; apply reduce_id. apply equiv_refl. apply equiv_refl.
      replace (subst1 (var 0) (subst (under 1 (sh 1)) P)) with P.
      2:{ simpsub_big. auto. rewrite - {1}  (subst_id obj P).
          apply subst_eqsub. apply eqsub_expand_id. }
      subst. assumption.
Qed.


Definition leq_t n m : term obj :=
  app (app leqtp n) m.

Lemma leq_type: forall G n1 n2,
    tr G (oof n1 nattp) -> tr G (oof n2 nattp) ->
    tr G (oof (leq_t n1 n2) U0).
  Admitted.


Lemma leq_succ_equiv n1_pred n2 : equiv (leq_t (ppair bfalse n1_pred) n2) (bite (if_z n2)
                                                      voidtp
                                                      (leq_t (app n1_pred triv)
                                                             (app (ppi2 n2) triv))).
  Admitted. 
Lemma leq_zero_equiv n2: equiv (leq_t nzero n2) unittp. Admitted.

Lemma leq_succsucc_equiv n1_pred n2_pred : equiv (leq_t (ppair bfalse n1_pred)
                                            (ppair bfalse n2_pred))                                                                               (leq_t (app n1_pred triv)
                                                             (app n2_pred triv)).
  Admitted. 


Lemma leqb_succ_equiv n1_pred n2 : equiv (leqb_app (ppair bfalse n1_pred) n2) (bite (if_z n2)
                                                     bfalse
                                                      (leqb_app (app n1_pred triv)
                                                             (app (ppi2 n2) triv))).
  Admitted. 
Lemma leqb_zero_equiv n2: equiv (leqb_app nzero n2) btrue. Admitted.

Lemma lt_zero_equiv n2: equiv (lt_t nzero n2) (bite (if_z n2)
                                                       voidtp 
                                                       unittp).
Admitted.

Lemma lt_succ_equiv n1_pred n2 : equiv (lt_t (ppair bfalse n1_pred) n2) (bite (if_z n2)
                                                     voidtp
                                                      (leq_t (ppair bfalse n1_pred)
                                                             (app (ppi2 n2) triv))).
  Admitted. 
 

Lemma ltb_zero_equiv n2: equiv (ltb_app nzero n2) (bite (if_z n2)
                                                       bfalse
                                                       btrue).
Admitted.

Lemma ltb_succ_equiv n1_pred n2 : equiv (ltb_app (ppair bfalse n1_pred) n2) (bite (if_z n2)
                                                      bfalse
                                                      (leqb_app (ppair bfalse n1_pred)
                                                             (app (ppi2 n2) triv))).
  Admitted. 
(* unfold wind. unfold leq_t. unfold leqtp. unfold wind.
  eapply equiv_trans.
  {
    apply equiv_app.
    { apply equiv_app.
      { apply steps_equiv. apply theta_fix. }
      {apply equiv_refl. }
    }
    {apply equiv_refl. }
  }
  {
  eapply equiv_trans.
  {
    apply equiv_app.
    { apply equiv_app.
      { apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
      }
      {apply equiv_refl. }
    }
    {apply equiv_refl. }
  }
  {
    simpsub. simpl. simpsub.
    eapply equiv_trans.
  {
    apply equiv_app.
    { apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
      }
      {apply equiv_refl. }
    }
  { simpsub. simpl.
    eapply equiv_trans.
    {
      apply equiv_app.
      {
        apply equiv_app.
        {
          apply equiv_app.
          {
            apply reduce_equiv. apply reduce_app_beta. apply reduce_id.
            unfold nzero. apply reduce_ppi1_beta. apply reduce_id.
          }
          {
            unfold nzero. apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id.
          }
        }
        apply equiv_refl.
      }
      {apply equiv_refl. }
    }
    { simpsub. simpl.
    eapply equiv_trans.
    {
      apply equiv_app.
      {
        apply equiv_app.
        {
          apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
        }
        { apply equiv_refl.
        }
      }
      {apply equiv_refl. }
    }
    { simpsub. simpl.
      eapply equiv_trans.
      { apply equiv_app.
        apply reduce_equiv. apply reduce_app_beta.
        apply reduce_bite_beta1. apply reduce_id.
        apply reduce_id.
        {apply equiv_refl. }
      }
      {
        simpsub.  apply reduce_equiv.
        change unittp with (subst1 n2 unittp).
        apply reduce_app_beta; apply reduce_id.
      }
    }
    }
    
  }
  }
  } 
Qed.*)



Lemma subst_leqtp: forall s,
    @ subst obj s (leqtp) = leqtp.
  intros. unfold leqtp. unfold wind. unfold theta.
  repeat rewrite subst_app.
  repeat rewrite subst_lam. simpsub. simpl.
  repeat rewrite project_dot_succ.
  rewrite project_dot_zero. auto. Qed.
Hint Rewrite subst_leqtp: core subst1.


Lemma if_z_typed n G : tr G (oof n nattp) -> tr G (oof (if_z n) booltp).
Admitted.

Lemma equiv_leqb :
  forall (m m' : term obj),
    equiv m m'
    -> equiv (leq_b m) (leq_b m').
Proof.
prove_equiv_compat. apply equiv_refl.
Qed.

(*n1 <= n2*)
Lemma leqapp_typed {G} n1 n2:
  tr G (oof n1 nattp) ->
  tr G (oof n2 nattp) ->
  tr G (oof (leqb_app n1 n2) booltp).
Admitted.
         
Lemma lt_type: forall G n1 n2,
    tr G (oof n1 nattp) -> tr G (oof n2 nattp) ->
    tr G (oof (ltpagetp n1 n2) U0).
Admitted.

(*should be fine*)
Lemma ltapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (ltb_app m n) booltp). Admitted.

(*more difficult, need induction*)
Lemma ltb_false G n : tr G (oof n nattp) -> tr G (deq (ltb_app n n) bfalse booltp).
Admitted.

Lemma nsucc_lt: forall G n, tr G (oof n nattp) ->
                       tr G (oof triv (lt_t n (nsucc n))).
Admitted.


      Definition leqb_complete_fn :=
    (app (app (app nat_ind_fn (lam
                  (pi nattp
                      ( (*x = 1, y = 0*)
                        arrow 
                          (leq_t (var 1) (var 0))
                          (equal booltp (leqb_app (var 1) (var 0)) btrue)
                  )
               )))
               (lam (*y : nat*)
                  (lam  (*hyp : x < y*)
                  triv 
                  )
               ))
               (lam (*x : nat*) (lam (*IH: P(x) ie pi y *)
                                   (lam  (*y'  : nat*)
                                      (lam (*lt_t n m*)
                                         triv (*s x  = y  : nat*)
                                      )
                  )
               ))).

      Lemma subst_leq_b s n: subst s (leq_b n) = leq_b (subst s n).
  intros. unfold leq_b. simpsub. auto. Qed.
Hint Rewrite subst_leq_b: core subst1.

Lemma subst_leqb_app s n m: subst s (leqb_app n m) = leqb_app (subst s n)(subst s m).
  intros. unfold leqb_app. simpsub_big. auto. Qed.
Hint Rewrite subst_leq_b: core subst1.

Lemma subst_ltb s n m: subst s (ltb_app n m) = ltb_app (subst s n) (subst s m).
  intros. unfold ltb_app. simpsub_big. auto. Qed.


Hint Rewrite subst_ltb: core subst1.
      Lemma leqb_complete G : tr G (oof leqb_complete_fn
                                       (pi nattp (pi nattp (arrow (leq_t (var 1) (var 0))
                                          (equal booltp (leqb_app (var 1) (var 0)) btrue)
                                   )))).
        unfold leqb_complete_fn.
    assert (forall G' x, tr G' (oof x nattp) ->
                    tr G' (oof (pi nattp (arrow 
                                            (leq_t (subst sh1 x) (var 0))
                                            (equal booltp (leqb_app (subst sh1 x) (var 0)) btrue)
                                                                        )
                               )
                               U0))
           as Hp.
    {
      intros. unfold leqb_app. 
      apply tr_pi_formation_univ; auto.
      apply tr_arrow_formation_univ; auto.
      apply leq_type; auto; try var_solv'.
      change nattp with (@subst obj sh1 nattp).
      rewrite ! subst_sh_shift. apply tr_weakening_append1. assumption.
      apply tr_equal_formation_univ; auto.
      simpsub_big. apply tr_booltp_formation.
      apply leqapp_typed; try var_solv'.  change nattp with (@subst obj sh1 nattp).
      rewrite ! subst_sh_shift. apply tr_weakening_append1. assumption.
      constructor.
    }
    eapply nat_ind_lamapp; simpsub_big; try reflexivity.
    { (*type p*)
      apply tr_arrow_intro; auto. simpsub_big.
      change (var 1) with (@subst obj sh1 (var 0)). apply Hp; var_solv'. }
    { (*type BC*)
       apply tr_pi_intro; auto. 
       apply tr_arrow_intro; auto. 
      weaken leq_type; auto; try var_solv'. 
      apply tr_equal_formation; auto.
      weaken tr_booltp_formation. unfold leqb_app. simpsub_big.
      apply leqapp_typed; auto; try var_solv'. constructor.
      unfold leqb_app. simpsub_big. simpl. eapply tr_compute;
                                             try (apply equiv_equal; try apply leqb_zero_equiv); try apply equiv_refl.
      repeat constructor. } 
      { apply tr_pi_intro; auto. 
       apply tr_arrow_intro; auto.
       change (var 1) with (@subst obj sh1 (var 0)). weaken Hp.
       var_solv'.
       simpl. change (nsucc (var 1)) with (@subst obj sh1 (nsucc (var 0))).
       weaken Hp. apply nsucc_type. var_solv'.
       simpsub_big. apply tr_pi_intro; auto.
       apply tr_arrow_intro; auto.
       {
      weaken leq_type; auto; try apply nsucc_type; try var_solv'. 
       }
      { 
      apply tr_equal_formation; auto.
      weaken tr_booltp_formation. unfold leqb_app. simpsub_big.
      apply leqapp_typed; auto; try apply nsucc_type; try var_solv'.  constructor. 
}
      simpsub_big. eapply (tr_compute_hyp _ [::]).
      { constructor. unfold nsucc. apply leq_succ_equiv. 
      } simpl. unfold leqb_app. simpsub_big.
      eapply tr_compute. {apply equiv_equal; try apply leqb_succ_equiv; apply equiv_refl. }
                         apply equiv_refl. apply equiv_refl.
      (*split y into pair*)
      simpl. rewrite make_app1. apply w_elim_hyp. weaken tr_booltp_formation.
      weaken nat_U01.
      change triv with (@subst obj (under 1 (dot (ppi2 (var 0))
                                                 (dot (ppi1 (var 0)) sh1))) triv).
       apply tr_sigma_eta_hyp.
      simpsub_big. simpl. simpsub_big.
      eapply (tr_compute_hyp _ [::]).
      {  constructor. 
        apply equiv_bite. apply reduce_equiv.
        apply reduce_ppi1_beta. apply reduce_id. apply equiv_refl.
        apply equiv_app. apply equiv_refl. apply equiv_app.
        apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id.
        apply equiv_refl. 
      }
      simpl. eapply tr_compute.
      {
        apply equiv_equal. apply equiv_refl. apply equiv_bite. apply reduce_equiv.
        apply reduce_ppi1_beta. apply reduce_id. apply equiv_refl.
       unfold leqb_app.  
        simpsub_big.  apply equiv_app.   apply equiv_leqb.
        
         apply reduce_equiv.   apply reduce_app_beta; apply reduce_id.
         apply equiv_app. 
        apply reduce_equiv.   apply reduce_ppi2_beta.  apply reduce_id.
        apply equiv_refl. apply equiv_refl. 
      } apply equiv_refl. apply equiv_refl. simpsub_big. simpl.
      simpl. rewrite make_app2. 
      match goal with |- tr ?G (deq triv triv ?T) =>
                      suffices: (tr G (oof (bite (var 2) triv triv) T)) end.
      { intros Hannoying. constructor. eapply deq_intro. apply Hannoying. }
      change triv with (@subst obj (under 2 sh1) triv). 
      apply tr_booltp_eta_hyp; simpl; simpsub_big.
      { (*y' = 0*)
        eapply (tr_compute_hyp _ [::]). { constructor. 
        apply reduce_equiv. apply reduce_bite_beta1.
        apply reduce_id. }
                                       apply (tr_voidtp_elim _ (var 0) (var 0)).
        change voidtp with (@subst obj sh1 voidtp). var_solv'. }
      {  (*y' = s y''*)
       simpl.  eapply (tr_compute_hyp _ [::]).
          { constructor. 
            eapply equiv_trans.
            apply reduce_equiv. apply reduce_bite_beta2.
            apply reduce_id. apply equiv_app.
            apply equiv_app. apply equiv_refl. apply reduce_equiv.
            apply reduce_app_beta; apply reduce_id. apply equiv_refl.
          } simpsub_big.
          simpl. rewrite make_app1. eapply tr_compute_hyp.
          { constructor. apply equiv_arrow. apply reduce_equiv.
       apply reduce_bite_beta2.
       apply reduce_id. apply equiv_refl. }
            eapply tr_compute.
          {  eapply equiv_equal. apply equiv_refl.
            apply reduce_equiv. apply reduce_bite_beta2.
            apply reduce_id. apply equiv_refl.
          }  apply equiv_refl.  apply equiv_refl.
            constructor. simpl. 
            apply (deq_intro _#4 (app (app (var 2) (app (var 1) triv))
                                      (var 0))
                             (app (app (var 2) (app (var 1) triv))
                                      (var 0))
                  ).
            apply (tr_arrow_elim _ (app (app leqtp (var 3)) (app (var 1) triv))).
       {
      weaken leq_type; auto; try apply nsucc_type; try var_solv'. 
      apply (tr_arrow_elim _ unittp); auto.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'.  constructor.  }
      {   apply tr_equal_formation; auto.
       weaken tr_booltp_formation.
      apply leqapp_typed; auto; try apply nsucc_type; try var_solv'.
        apply (tr_arrow_elim _ unittp); auto.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'. constructor.
      constructor. }
      match goal with |- tr ?G (deq ?M ?M ?T) => change T with
          (subst1 (app (var 1) triv)
       (arrow
          (app (app leqtp (var 4))
                (var 0))
          (equal booltp (app (leq_b (var 4)) (var 0)) btrue))) end.
      apply (tr_pi_elim _ nattp).
      match goal with |- tr ?G (deq ?M ?M ?T) => change T with
      ( subst (sh 3) 
       (pi nattp
          (arrow (app (app leqtp (var 1)) (var 0))
             (equal booltp
                (app (leq_b (var 1)) (var 0)) btrue))))
 end. var_solv'.
        apply (tr_arrow_elim _ unittp); auto.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'. constructor.
      match goal with |- tr ?G (deq ?M ?M ?T) => change T with
          (@subst obj (sh 1)
       (app (app leqtp (var 2)) (app (var 0) triv)))
 end. var_solv'. } } 
Qed.


Definition leqb_complete_fn_app n m h := (app (app (app leqb_complete_fn n) m) h).


Lemma lt_P p G n m: tr G (oof n nattp) ->
                    tr G (oof m nattp) ->
  tr G (oof p (lt_t n m)) ->
  tr G (deq (ltb_app n m) btrue booltp).
  intros.
  assert (tr G (oof p (leq_t (nsucc n) m))) as Hleqt. shelve.
  remember (subst (sh 1) n) as n'.
  remember (subst (sh 1) m) as m'.
  assert (tr (hyp_tm (leq_t (nsucc n) m) :: G) (deq n' n' nattp)) as Hn. 
    subst; change nattp with (@subst obj (sh 1) nattp);
      rewrite ! subst_sh_shift; apply tr_weakening_append1; assumption.
  assert (tr (hyp_tm (leq_t (nsucc n) m) :: G) (deq m' m' nattp)) as Hm. 
  subst; change nattp with (@subst obj (sh 1) nattp);
      rewrite ! subst_sh_shift; apply tr_weakening_append1; assumption.
  match goal with |- tr G ?J => replace J with (substj (dot p id)
                                                     (deq (ltb_app n' 
                                                                  m') 
                                                          btrue booltp)                                             ) end.
  2:{
    unfold substj. unfold ltb_app. subst. simpsub_big. auto.
  }
  eapply tr_generalize. apply Hleqt.
  unfold ltb_app.
   eapply (deq_intro _ _ _ _ (leqb_complete_fn_app (nsucc n') m'
                                                 (subst sh1 p)
                             )
(leqb_complete_fn_app (nsucc n') m'
                                                 (subst sh1 p)
                            )
          ).
   apply (tr_arrow_elim _ (leq_t (nsucc n') m')
        ).
  weaken leq_type; try apply nsucc_type; auto.
apply tr_equal_formation. weaken tr_booltp_formation.
    apply leqapp_typed; try apply nsucc_type; auto. constructor.
match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with  
          (subst1 m' 
       (arrow (leq_t (nsucc (subst sh1 n')) (var 0))
          (equal booltp
             (app (leq_b (nsucc (subst sh1 n')))
                (var 0)) btrue))) end.
2:{simpsub_big. auto. }
      apply (tr_pi_elim _ nattp).
match goal with |- tr ?G (deq ?M ?M' ?T) => replace T with  
          (subst1 (nsucc n') 
       (pi nattp
          (arrow
             (leq_t
                (var 1)
                (var 0))
             (equal booltp
                (app
                   (leq_b
                      (var 1))
                   (var 0)) btrue)))) end.
2:{simpsub_big. auto. }
apply (tr_pi_elim _ nattp); try apply leqb_complete; try 
                                                       apply nsucc_type; try assumption. assumption.
replace (leq_t (nsucc n') m') with (shift 1 (leq_t (nsucc n) m)).
rewrite ! subst_sh_shift. apply tr_weakening_append1. assumption.
simpsub_big. subst. auto.
Unshelve.
unfold lt_t in H1. 
  eapply (tr_compute _ _ (app
               (app
                  (lam
                     (app (subst sh1 leqtp)
                       (nsucc (var 0)))) n)
               m)).
  apply equiv_symm.
  { apply equiv_app. apply reduce_equiv.
    replace (app leqtp (nsucc n)) with
        (subst1 n (app leqtp (nsucc (var 0)))).
    2:{ simpsub_big. auto. }
    apply reduce_app_beta; try apply reduce_id.
    apply equiv_refl.
  }
  {apply equiv_refl. }
  {apply equiv_refl. } assumption. Qed.

Definition leq_P := (pi nattp (pi nattp
                      ( (*n1 = 2, n2 = 1, n3 = 0*)
                        arrow 
                        (leq_t (var 2) (var 1))
                        (arrow (leq_t (var 1) (var 0))
                               (leq_t (var 2) (var 0))
                        )))).

Definition leq_trans_fn := (app (app (app nat_ind_fn (lam leq_P))
                  (lam (*n2 : nat*)
                     (lam (*n3 : nat*)
                        (lam (*n1 <= n2*)
                  (lam  (*n2 <= n3*)
                  triv) 
               ))))
               (lam (*x : nat*) (lam (*IH: P(x) ie pi y (eqb x y = t -> x = y)*)
                                   (lam  (*n2  : nat*)
                                      (lam (*n3*)
                                         (lam (*n1 <= n2*)
                                            (lam (*n2 <= n3*)
                                               (bite (if_z (var 3)) triv (bite (if_z (var 2)) triv
(*
ih = 4
n2 = 3
n3 = 2
n1 <= n2 = 1
n2 <= n3 = var 0*)

      (app (app (app (app  (var 4) (*IH*)
         (app (ppi2 (var 3)) triv)) (*n2 * *)
              (app (ppi2 (var 2)) triv)) (*n3 **)
              (var 1))
              (var 0))
                                               ))
                                               (*s x  = y  : nat*)
                                      )))))
                           )).

Definition leq_trans_fn_app n1 n2 n3 h12 h23 :=
  app (app (app (app (app leq_trans_fn n1) n2) n3) h12) h23.

(*try and get it to be so that if x : x <= y
 then triv  : x <= y

 induct on x F
 honestly you do the trans reasoning in proofs_working already so just try and see how that goes*)

Lemma leq_trans_help G : tr G (oof leq_trans_fn
                                 (pi nattp leq_P)
                              ).
      assert (forall G' x, tr G' (oof x nattp) ->
                    tr G' (oof 
        (pi nattp
          (pi nattp
             (arrow
                (leq_t (subst (sh 2) x) (var 1))
                (arrow
                   (leq_t 
                      (var 1) 
                      (var 0))
                   (leq_t 
                      (subst (sh 2) x) 
                      (var 0))))))
                               U0)
             ) as Hp.
      {
        intros. repeat apply tr_pi_formation_univ; auto.
        apply tr_arrow_formation_univ.
        {apply leq_type. change nattp with (@subst obj (sh 2) nattp). rewrite ! subst_sh_shift.
         apply tr_weakening_append2. assumption.
         var_solv'.
        }
        {apply tr_arrow_formation_univ; apply leq_type; try var_solv'.
change nattp with (@subst obj (sh 2) nattp). rewrite ! subst_sh_shift.
         apply tr_weakening_append2. assumption.
        }
      }
  eapply nat_ind_lamapp.
    { (*type p*)
      apply tr_arrow_intro; auto. simpsub_big. unfold leq_P.
      change (var 2) with (@subst obj (sh 2) (var 0)). apply Hp; var_solv'. }
    {
(*type BC*)
      unfold leq_P. simpsub_big.
      repeat apply tr_pi_intro; auto. 
      apply tr_arrow_intro; simpsub;
        try apply tr_arrow_intro; auto;
        try weaken leq_type; try var_solv'; auto.
      apply tr_arrow_formation; auto;
        try weaken leq_type; try var_solv'; auto.
      simpsub_big.
      eapply tr_compute.
      {apply leq_zero_equiv. }
      apply equiv_refl. apply equiv_refl. constructor.
    }
    {unfold leq_P. simpsub_big. simpl. reflexivity. }
    { (*type IS*)
      apply tr_pi_intro; auto.
      apply tr_arrow_intro; auto.
      { unfold leq_P. change (var 2) with
                          (@subst obj (sh 2) (var 0)).
        weaken Hp. var_solv'.
      }
      {repeat apply tr_pi_formation; auto.
      apply tr_arrow_formation; auto;
        try weaken leq_type; try var_solv'; auto.
      apply nsucc_type. var_solv'.
      apply tr_arrow_formation; auto;
        try weaken leq_type; try var_solv'; auto.
      apply nsucc_type. var_solv'.
      }
      {
        simpsub_big. repeat apply tr_pi_intro; auto.
        simpl. apply tr_arrow_intro; auto.
        try weaken leq_type; try apply nsucc_type;
          try var_solv'; auto.
      apply tr_arrow_formation; auto;
        try weaken leq_type; try apply nsucc_type;
          try var_solv'; auto.
      simpsub.
      apply tr_arrow_intro; auto; 
        try weaken leq_type; try apply nsucc_type;
          try var_solv'; auto.
      simpsub.
      eapply tr_compute. apply leq_succ_equiv.
     apply equiv_refl.
     apply equiv_refl.
     simpl. rewrite make_app1.
     eapply tr_compute_hyp. constructor. apply leq_succ_equiv.
     (*case on n2*)
     simpl. rewrite make_app3. apply w_elim_hyp. weaken tr_booltp_formation.
     weaken nat_U01. constructor.
      change triv with (@subst obj (under 3 (dot (ppi2 (var 0))
                                                 (dot (ppi1 (var 0)) sh1))) triv).
      apply tr_sigma_eta_hyp. simpsub_big. simpl. simpsub_big. simpl.
      constructor.
      eapply tr_compute. apply equiv_refl.
      { apply equiv_bite.
      {apply reduce_equiv; apply reduce_ppi1_beta; apply reduce_id. }
      {apply equiv_refl. }
      {apply equiv_bite. apply equiv_refl. apply equiv_refl.
       repeat apply equiv_app; try (apply reduce_equiv; apply
                                                          reduce_ppi2_beta; apply reduce_id);
       try apply equiv_refl.
      } }
      { apply equiv_bite.
      {apply reduce_equiv; apply reduce_ppi1_beta; apply reduce_id. }
      {apply equiv_refl. }
      {apply equiv_bite. apply equiv_refl. apply equiv_refl.
       repeat apply equiv_app; try (apply reduce_equiv; apply
                                                          reduce_ppi2_beta; apply reduce_id);
       try apply equiv_refl.
      } } (*make lemma for evaling both terms to the same thing*)
      rewrite make_app1. eapply tr_compute_hyp.
     constructor; try (apply equiv_bite; [apply reduce_equiv;
                                            [apply reduce_ppi1_beta;
                                            apply reduce_id] |
                                             apply equiv_refl | apply equiv_refl]).
     simpl. rewrite make_app4.
     change triv with
         (@subst obj (under 4 sh1) triv) at 3 7.
     match goal with |- tr ?G (deq (bite ?b ?m1 ?m2) ?M2 ?T) =>
                     change m2 with
          (@subst obj (under 4 sh1) (bite (ppi1 (var 2)) triv
             (app
                (app
                   (app
                      (app (var 4)
                         (app (var 3)
                            triv)) (app (ppi2 (var 2)) triv))
                   (var 1)) (var 0)))) end.
     apply tr_booltp_eta_hyp; simpsub_big; simpl; simpsub_big; simpl.
     { (*case: n2 = 0 *)
       rewrite make_app1. eapply tr_compute_hyp. constructor.
       apply reduce_equiv. apply reduce_bite_beta1. apply reduce_id.
       simpl. eapply (tr_voidtp_elim _ (var 1)). change voidtp with
                                                     (@subst obj (sh 2) voidtp).
       var_solv'.
     }
     { (*case: n2 = s n2 '*)
       rewrite make_app1. eapply tr_compute_hyp. constructor.
       eapply equiv_trans.
       { apply equiv_bite. apply equiv_refl. apply equiv_refl.
       apply equiv_app. apply equiv_app. apply equiv_refl.
       apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
       apply equiv_app.
       apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id.
       apply equiv_refl. }
       {apply reduce_equiv. apply reduce_bite_beta2.
        apply reduce_id.
       } simpsub_big. simpl.
       eapply (tr_compute_hyp _ [::]). constructor. apply leq_succ_equiv.
       simpl.
       (*case on n3*)
       simpl. rewrite make_app2. apply w_elim_hyp. weaken tr_booltp_formation.
     weaken nat_U01. constructor.
      change triv with (@subst obj (under 2 (dot (ppi2 (var 0))
                                                 (dot (ppi1 (var 0)) sh1))) triv).
      apply tr_sigma_eta_hyp.  simpsub_big. simpl. simpsub_big. simpl.
      constructor.
      eapply tr_compute.
      { apply equiv_bite.
      {apply reduce_equiv; apply reduce_ppi1_beta; apply reduce_id. }
      {apply equiv_refl. }
      {unfold leqpagetp. 
       apply equiv_app. apply equiv_app. apply equiv_refl.
       apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
       apply equiv_app. apply reduce_equiv; apply reduce_ppi2_beta;
                          apply reduce_id.
       apply equiv_refl.
      } }
      { apply equiv_bite.
      {apply reduce_equiv; apply reduce_ppi1_beta; apply reduce_id. }
      {apply equiv_refl. }
      {unfold leqpagetp. 
       repeat apply equiv_app; try (apply reduce_equiv; apply
                                                          reduce_ppi2_beta; apply reduce_id);
       try apply equiv_refl.
      } }
      { apply equiv_bite.
      {apply reduce_equiv; apply reduce_ppi1_beta; apply reduce_id. }
      {apply equiv_refl. }
      {unfold leqpagetp. 
       repeat apply equiv_app; try (apply reduce_equiv; apply
                                                          reduce_ppi2_beta; apply reduce_id);
       try apply equiv_refl.
      } } 
      simpsub_big. 
     eapply (tr_compute_hyp _ [::]).
     { constructor. apply equiv_bite. apply reduce_equiv.
       apply reduce_ppi1_beta; apply reduce_id.  apply equiv_refl.
       unfold leqpagetp. apply equiv_app. apply equiv_refl.
       apply equiv_app. apply reduce_equiv. apply reduce_ppi2_beta.
       apply reduce_id. apply equiv_refl. }
     simpl. rewrite make_app4. eapply tr_compute_hyp.
     { constructor. apply equiv_arrow. apply reduce_equiv.
       apply reduce_bite_beta2. apply reduce_id. apply equiv_refl. }
     simpl. rewrite make_app3.
         change triv with
             (@subst obj (under 3 sh1) triv) at 4 7.
         change 
          (app
             (app
                (app (app (var 5) (app (var 4) triv))
                   (app (var 2) triv)) (var 1)) 
             (var 0)) with
             (@subst obj (under 3 sh1)
          (app
             (app
                (app (app (var 4) (app (var 3) triv))
                   (app (var 2) triv)) (var 1)) 
             (var 0))).
     apply tr_booltp_eta_hyp; simpsub_big; simpl; simpsub_big; simpl.
     { (*case: n3 = 0 *)
       eapply (tr_compute_hyp _ [::]). constructor.
       apply reduce_equiv. apply reduce_bite_beta1. apply reduce_id.
       simpl. eapply (tr_voidtp_elim _ (var 0)). change voidtp with
                                                     (@subst obj (sh 1) voidtp).
       var_solv'.
     }
     { (*case: n3 = s n3 '*)
        eapply (tr_compute_hyp _ [::]). constructor. 
       {apply reduce_equiv. apply reduce_bite_beta2.
        apply reduce_id. }
       simpl.
       unfold leq_P. 
       eapply tr_compute. 
       {apply reduce_equiv. apply reduce_bite_beta2.
       apply reduce_id. }
       apply equiv_refl. apply equiv_refl.
       rewrite make_app2. eapply tr_compute_hyp.
       constructor. {apply equiv_arrow. apply reduce_equiv.
                     apply reduce_bite_beta2. apply reduce_id.
                    apply equiv_refl. }
       apply (tr_arrow_elim _ 
          (app (app leqtp (app (var 3) triv))
               (app (var 2) triv))).
       3:{ apply (tr_arrow_elim _
          (app (app leqtp (var 5))
               (app (var 3) triv))).
           3: { 
             match goal with |- tr ?G (deq ?M ?M ?T) => change T with
       (@subst1 obj (app (var 2) triv) (arrow
          (app (app leqtp (var 6))
             (app (var 4) triv))
          (arrow
             (app
                (app leqtp
                   (app (var 4) triv))
                (var 0))
             (app
                (app leqtp (var 6))
                (var 0))))) end.
             apply (tr_pi_elim _ nattp).
             match goal with |- tr ?G (deq ?M ?M ?T) => change T with
       (@subst1 obj (app (var 3) triv) 
       (pi nattp
          (arrow
             (app
                (app leqtp (var 7))
                (var 1))
             (arrow
                (app
                   (app leqtp
                      (var 1))
                   (var 0))
                (app
                   (app leqtp
                      (var 7))
                   (var 0)))))) end.
             apply (tr_pi_elim _ nattp). 
             match goal with |- tr ?G (deq ?M ?M ?T) => change T with
       (@subst obj (sh 5)
       (pi nattp (pi nattp
          (arrow
             (app
                (app leqtp (var 2))
                (var 1))
             (arrow
                (app
                   (app leqtp
                      (var 1))
                   (var 0))
                (app
                   (app leqtp
                      (var 2))
                   (var 0))))))) end. var_solv0.
             Ltac app_nat := try apply (tr_arrow_elim _ unittp); try var_solv';
                             auto; try apply tr_unittp_intro.
             app_nat. app_nat. }
           try weaken leq_type; try app_nat.
           apply tr_arrow_formation; try weaken leq_type; try app_nat. 
           { match goal with |- tr ?G (deq ?M ?M ?T) => change T with  (@subst obj (sh 2)
       (app (app leqtp (var 3))
            (app (var 1) triv))) end. var_solv0. } }
           weaken leq_type; try app_nat.
           weaken leq_type; try app_nat.
           { match goal with |- tr ?G (deq ?M ?M ?T) => change T with  (@subst obj (sh 1)
       (app (app leqtp (app (var 2) triv))
         (app (var 1) triv))) end. var_solv0. }
           }
          } 
       } } 
Qed.



Lemma leq_refl: forall G n,
    tr G (deq n n nattp) ->
    tr G (oof triv (leqpagetp n n)). Admitted.






Hint Resolve nat_type nat_U0 zero_typed leq_refl leq_type lt_type U0_type.




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

Lemma eqapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (app (eq_b m) n) booltp). Admitted.

          Lemma subst_eqb s n: subst s (eq_b n) = eq_b (subst s n).
  intros. unfold eq_b. simpsub. auto. Qed.
          Hint Rewrite subst_eqb: core subst1.

Lemma eq_b_succ n1 n2: equiv (app (eq_b (nsucc n1)) n2) (bite (if_z n2)
                                                      bfalse
                                                      (app (eq_b n1) (app (ppi2 n2) triv))).
  intros.
  unfold eq_b. unfold wind.
  eapply equiv_trans.
  {
    apply equiv_app.
    { apply equiv_app.
      { apply steps_equiv. apply theta_fix. }
      {apply equiv_refl. }
    }
    {apply equiv_refl. }
  }
  {
  eapply equiv_trans.
  {
    apply equiv_app.
    { apply equiv_app.
      { apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
      }
      {apply equiv_refl. }
    }
    {apply equiv_refl. }
  }
  {
    simpsub. simpl. simpsub.
    eapply equiv_trans.
  {
    apply equiv_app.
    { apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
      }
      {apply equiv_refl. }
    }
  { simpsub. simpl.
    eapply equiv_trans.
    {
      apply equiv_app.
      {
        apply equiv_app.
        {
          apply equiv_app.
          {
            apply reduce_equiv. apply reduce_app_beta. apply reduce_id.
            unfold nzero. apply reduce_ppi1_beta. apply reduce_id.
          }
          {
            unfold nsucc. apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id.
          }
        }
        apply equiv_refl.
      }
      {apply equiv_refl. }
    }
    { simpsub. simpl.
    eapply equiv_trans.
    {
      apply equiv_app.
      {
        apply equiv_app.
        {
          apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
        }
        { apply equiv_refl.
        }
      }
      {apply equiv_refl. }
    }
    { simpsub. simpl.
      eapply equiv_trans.
      { apply equiv_app.
        apply reduce_equiv. apply reduce_app_beta.
        apply reduce_bite_beta2. apply reduce_id.
        apply reduce_id.
        {apply equiv_refl. }
      }
      {
        simpsub.
        simpl.
        {eapply equiv_trans.
         { apply reduce_equiv.
           apply reduce_app_beta; apply reduce_id. }
           {
             simpsub. simpl.
             apply equiv_bite.
             - apply equiv_refl.
             - apply equiv_refl.
             - apply equiv_app.
               { eapply equiv_trans. 
                 { apply reduce_equiv. apply reduce_app_beta;
                   apply reduce_id. (*?*)
                 }
                 {simpsub. simpl.
                  apply equiv_app.
                  - apply equiv_refl.
                  - unfold nsucc.
                    eapply equiv_trans.
                    apply equiv_app.
                    apply reduce_equiv. apply reduce_ppi2_beta;
                                          apply reduce_id. apply equiv_refl.
                    apply reduce_equiv.
                    replace n1 with (subst1 triv (subst sh1 n1)).
                    apply reduce_app_beta. simpsub. apply reduce_id.
                    apply reduce_id.
                    simpsub. auto.
                 }
               }
               apply equiv_refl.
           }
           } } } } } } }
Qed.


Lemma eq_b0 n2: equiv (app (eq_b nzero) n2) (if_z n2).
  unfold eq_b. unfold wind.
  eapply equiv_trans.
  {
    apply equiv_app.
    { apply equiv_app.
      { apply steps_equiv. apply theta_fix. }
      {apply equiv_refl. }
    }
    {apply equiv_refl. }
  }
  {
  eapply equiv_trans.
  {
    apply equiv_app.
    { apply equiv_app.
      { apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
      }
      {apply equiv_refl. }
    }
    {apply equiv_refl. }
  }
  {
    simpsub. simpl. simpsub.
    eapply equiv_trans.
  {
    apply equiv_app.
    { apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
      }
      {apply equiv_refl. }
    }
  { simpsub. simpl.
    eapply equiv_trans.
    {
      apply equiv_app.
      {
        apply equiv_app.
        {
          apply equiv_app.
          {
            apply reduce_equiv. apply reduce_app_beta. apply reduce_id.
            unfold nzero. apply reduce_ppi1_beta. apply reduce_id.
          }
          {
            unfold nzero. apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id.
          }
        }
        apply equiv_refl.
      }
      {apply equiv_refl. }
    }
    { simpsub. simpl.
    eapply equiv_trans.
    {
      apply equiv_app.
      {
        apply equiv_app.
        {
          apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
        }
        { apply equiv_refl.
        }
      }
      {apply equiv_refl. }
    }
    { simpsub. simpl.
      eapply equiv_trans.
      { apply equiv_app.
        apply reduce_equiv. apply reduce_app_beta.
        apply reduce_bite_beta1. apply reduce_id.
        apply reduce_id.
        {apply equiv_refl. }
      }
      {
        simpsub. unfold if_z. apply reduce_equiv.
        replace (ppi1 n2) with (subst1 n2 (ppi1 (var 0))).
        2: {
          simpsub. auto.
        }
        apply reduce_app_beta; apply reduce_id.
      }
    }
    }
    
  }
  }
  }
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
    apply tr_booltp_eta_hyp; simpsub; simpl; simpsub;
    (*rewrite ! subst_nat; *)
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




      



      Definition eqb_sound_fn :=
    (app (app (app nat_ind_fn (lam
                  (pi nattp
                      ( (*x = 1, y = 0*)
                        arrow 
                        (equal booltp (app (eq_b (var 1)) (var 0)) btrue
                               )
                        (equal nattp (var 1) (var 0))
                  )
               )))
               (lam (*y : nat*)
                  (lam  (*hyp : eqb 0 y  = tt*)
                  triv 
                  )
               ))
               (lam (*x : nat*) (lam (*IH: P(x) ie pi y (eqb x y = t -> x = y)*)
                                   (lam  (*y'  : nat*)
                                      (lam (*eqb s x y' = t*)
                                         triv (*s x  = y  : nat*)
                                      )
                  )
               ))).
     (*          
  tr
    [:: hyp_tm
          (equal booltp
             (if_z (var 0)) btrue),
        hyp_tm nattp
      & G]
    (deq nzero
       (var (1 + 0)%coq_nat) nattp) *)


      Lemma equal_nzero_help G n:
        tr G (oof n nattp) -> tr G (oof (lam triv)
                                       (arrow (equal booltp (if_z n) btrue)
                                              (equal nattp nzero n)
                                       )
                                  ).
        intros. 
        replace 
    (oof (lam triv)
       (arrow
          (equal booltp 
             (if_z n) btrue)
          (equal nattp nzero n)))
 with
            (substj (dot n id) 
    (oof (lam triv)
       (arrow
          (equal booltp 
             (if_z (var 0)) btrue)
          (equal nattp nzero (var 0))))) .
        2:{ simpl. simpsub_big. auto. } 
        eapply (tr_generalize _ nattp). assumption.
        apply tr_arrow_intro; auto. { apply tr_equal_formation; auto.
                                      weaken tr_booltp_formation.
                                      apply if_z_typed. var_solv'. constructor. }
                                    { apply tr_equal_formation; auto. var_solv'. }
                                    simpsub_big.
        rewrite make_app1. eapply w_elim_hyp.
        weaken tr_booltp_formation. weaken nat_U01.
        change triv with (@subst obj (under 1 (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) triv). apply tr_sigma_eta_hyp. simpsub_big.
        simpl. simpsub_big. simpl.
        rewrite make_app2.
      match goal with |- tr ?G (deq triv triv ?T) =>
                      suffices: (tr G (oof (bite (var 2) triv triv) T)) end.
      { intros Hannoying. constructor. eapply deq_intro. apply Hannoying. }
      rewrite make_app2.
        change triv with 
            (@subst obj (under 2 sh1) triv).
        apply tr_booltp_eta_hyp; simpl; simpsub_big; simpl.
        { (*true*)
          rewrite make_app1.
          eapply tr_compute_hyp.
        {
          constructor. apply equiv_arrow. apply reduce_equiv.
          apply reduce_bite_beta1. apply reduce_id.
          apply equiv_refl.
        }
        constructor. apply tr_wt_intro. constructor.
        simpsub_big.
        eapply tr_compute. { apply equiv_arrow. apply reduce_equiv.
          apply reduce_bite_beta1. apply reduce_id.
          apply equiv_refl.
 } apply equiv_refl. apply equiv_refl.
        apply (tr_transitivity _#2 (lam (app (subst sh1 (var 1)) (var 0)))).
        { apply tr_arrow_intro; auto. weaken tr_voidtp_formation.
          eapply (tr_voidtp_elim  _ (var 0) (var 0)).
          change voidtp with (@subst obj (sh 1) voidtp). var_solv0.
        }
        { apply tr_symmetry. apply tr_arrow_eta.
          change (arrow voidtp nattp) with (@subst obj (sh 2) (arrow voidtp nattp)).
          var_solv0.
        }
        weaken nat_U01. }
        {(*false*)
          eapply (tr_compute_hyp _ [::]).
        {
          constructor. apply equiv_equal. apply equiv_refl. apply reduce_equiv.
          apply reduce_ppi1_beta. apply reduce_id.
          apply equiv_refl.
        }
        apply bool_contra. simpl. apply (deq_intro _#4 (var 0) (var 0)).
        change (equal booltp bfalse btrue) with (@subst obj sh1 (equal booltp bfalse btrue)).
        var_solv0. } 
       Qed. 


      Lemma equal_nzero G n:
        tr G (oof n nattp) ->
        tr G (deq (if_z n) btrue booltp) ->
        tr G (deq nzero n nattp).
        intros.
        apply (deq_intro _#4 (app (lam triv) triv) (app (lam triv) triv)).
        apply (tr_arrow_elim _ (equal booltp (if_z n) btrue)).
        apply tr_equal_formation; auto. weaken tr_booltp_formation.
        apply if_z_typed. assumption. constructor.
        apply tr_equal_formation; auto. apply equal_nzero_help. assumption.
        constructor. assumption. Qed.

  Lemma equal_succ G preds: tr G (oof preds (arrow unittp nattp)) ->
                        tr G (deq (nsucc (app preds triv )) (ppair bfalse preds) nattp).
    intros. unfold nsucc. simpsub. apply tr_wt_intro. constructor.
    simpsub_big.
    eapply tr_compute. { apply equiv_arrow. apply reduce_equiv.
                         apply reduce_bite_beta2. apply reduce_id. apply equiv_refl. } apply equiv_refl. apply equiv_refl.
    apply (tr_transitivity _ _ (lam (app (subst sh1 preds) (var 0)))).
    {
            apply tr_arrow_intro; auto.
            apply (tr_arrow_elim _ unittp); auto.
            match goal with |- tr ?G (deq ?M ?M ?T) =>
                                                      change T with
       (@shift obj 1
               (arrow unittp nattp)) end. rewrite subst_sh_shift. apply tr_weakening_append1.
            assumption.
          apply tr_symmetry. apply tr_unittp_eta.
          change unittp with (@subst obj (sh 1) unittp). var_solv0.
    }
    {
      apply tr_symmetry. apply tr_arrow_eta. assumption.
    }
    weaken nat_U01. Qed.

  Lemma eqb_sound G : tr G (oof eqb_sound_fn (pi nattp (pi nattp (arrow (equal booltp (app (eq_b (var 1)) (var 0))
                                                                               btrue
                                                                        )
                                                                        (equal nattp (var 1) (var 0))

                           )))).
    unfold eqb_sound_fn.
    assert (forall G' x, tr G' (oof x nattp) ->
                    tr G' (oof (pi nattp (arrow (equal booltp (app (eq_b (subst sh1 x)) (var 0))
                                                                               btrue
                                                                        )
                                                                        (equal nattp (subst sh1 x) (var 0))


                               ))
                               U0)
           ) as Hp.
    {
      intros. 
      apply tr_pi_formation_univ; auto.
      apply tr_arrow_formation_univ; auto.
      apply tr_equal_formation_univ; auto.
      simpsub_big. apply tr_booltp_formation.
      apply eqapp_typed; try var_solv'.  change nattp with (@subst obj sh1 nattp).
      rewrite ! subst_sh_shift. apply tr_weakening_append1. assumption.
      constructor.
      apply tr_equal_formation_univ; auto; try var_solv'.
      change nattp with (@subst obj sh1 nattp).
      rewrite ! subst_sh_shift. apply tr_weakening_append1. assumption.
    }
    eapply nat_ind_lamapp; simpsub_big; try reflexivity.
    { (*type p*)
      apply tr_arrow_intro; auto. simpsub_big.
      change (var 1) with (@subst obj sh1 (var 0)). apply Hp; var_solv'. }
    { (*type BC*)
       apply tr_pi_intro; auto. 
       apply tr_arrow_intro; auto. 
      apply tr_equal_formation; auto.
      weaken tr_booltp_formation.
      apply eqapp_typed; auto; try var_solv'. constructor.
      apply tr_equal_formation; auto; try var_solv'.
      eapply (tr_compute_hyp _ [::]). constructor. apply equiv_equal. apply equiv_refl.
      apply eq_b0. apply equiv_refl. simpl. simpsub_big.
      constructor. apply equal_nzero.
      var_solv'.
      apply (deq_intro _#4 (var 0) (var 0)).  
      match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
          (subst sh1
       (equal booltp
              (if_z (var 0)) btrue)) end.
      2:{
        simpl. simpsub_big. auto.
      }
      var_solv0.
    }
    { (*type IS*)
       apply tr_pi_intro; auto. 
       apply tr_arrow_intro; auto.
       change (var 1) with (@subst obj sh1 (var 0)). weaken Hp.
       var_solv'.
       simpl. change (nsucc (var 1)) with (@subst obj sh1 (nsucc (var 0))).
       weaken Hp. apply nsucc_type. var_solv'.
       simpsub_big. apply tr_pi_intro; auto.
       apply tr_arrow_intro; auto.
      { apply tr_equal_formation; auto.
      weaken tr_booltp_formation.
      apply eqapp_typed; auto; try apply nsucc_type; try var_solv'. constructor. }
      { apply tr_equal_formation; auto; try apply nsucc_type; try var_solv'. }
      simpsub_big. eapply (tr_compute_hyp _ [::]).
      { constructor. apply equiv_equal. apply equiv_refl. apply eq_b_succ.
        apply equiv_refl. }
      (*split y into pair*)
      simpl. rewrite make_app1. apply w_elim_hyp. weaken tr_booltp_formation.
      weaken nat_U01.
      change triv with (@subst obj (under 1 (dot (ppi2 (var 0))
                                                 (dot (ppi1 (var 0)) sh1))) triv).
      apply tr_sigma_eta_hyp.
      simpsub_big. simpl. simpsub_big.
      eapply (tr_compute_hyp _ [::]).
      { constructor. apply equiv_equal. apply equiv_refl.
        apply equiv_bite. apply reduce_equiv.
        apply reduce_ppi1_beta. apply reduce_id. apply equiv_refl.
        apply equiv_app. apply equiv_refl. apply equiv_app.
        apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id.
        apply equiv_refl. apply equiv_refl.
      }
      simpl. rewrite make_app2.
      match goal with |- tr ?G (deq triv triv ?T) =>
                      suffices: (tr G (oof (bite (var 2) triv triv) T)) end.
      { intros Hannoying. constructor. eapply deq_intro. apply Hannoying. }
      change triv with (@subst obj (under 2 sh1) triv).
      apply tr_booltp_eta_hyp; simpl; simpsub_big.
      { (*y' = 0*)
        eapply (tr_compute_hyp _ [::]). { constructor. apply equiv_equal.
        apply equiv_refl. apply reduce_equiv. apply reduce_bite_beta1.
        apply reduce_id. apply equiv_refl. }
        apply bool_contra. simpl. apply (deq_intro _#4 (var 0) (var 0)).
        change (equal booltp bfalse btrue) with
            (@subst obj (sh 1) (equal booltp bfalse btrue)). var_solv0. }
      { (*y' = s y''*)
       simpl.  eapply (tr_compute_hyp _ [::]).
          { constructor. apply equiv_equal.
        apply equiv_refl. apply reduce_equiv. apply reduce_bite_beta2.
        apply reduce_id. apply equiv_refl. }
          simpl. rewrite make_app1. eapply tr_compute_hyp.
          { constructor. apply equiv_arrow. apply reduce_equiv.
       apply reduce_bite_beta2.
        apply reduce_id. apply equiv_refl. }
          simpl.
          constructor.
          eapply (tr_transitivity _#2 (nsucc (app (var 1) triv))).
          { (*succ x = succ (y' * *)
            apply nsucc_type.
            apply (deq_intro _#4 (app (app (var 2) (app (var 1) triv))
                                      (var 0))
                             (app (app (var 2) (app (var 1) triv))
                                      (var 0))
                  ).
            apply (tr_arrow_elim _
(equal booltp (app (eq_b (var 3)) (app (var 1) triv))
       btrue)).
      { apply tr_equal_formation; auto.
      weaken tr_booltp_formation.
      apply eqapp_typed; auto; try apply nsucc_type; try var_solv'.
      apply (tr_arrow_elim _ unittp); auto.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'. constructor. constructor. }
      {
        apply tr_equal_formation; auto; try var_solv'.
        apply (tr_arrow_elim _ unittp); auto.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'. constructor. 
      }
      match goal with |- tr ?G (deq ?M ?M ?T) => change T with
          (subst1 (app (var 1) triv)
       (arrow
          (equal booltp
             (app (eq_b (var 4))
                (var 0)) btrue)
          (equal nattp (var 4) (var 0)))) end.
      apply (tr_pi_elim _ nattp).
      match goal with |- tr ?G (deq ?M ?M ?T) => change T with
      ( subst (sh 3) (pi nattp
          (arrow
             (equal booltp
                (app (eq_b (var 1)) (var 0)) btrue)
             (equal nattp (var 1) (var 0))))) end. var_solv'.
        apply (tr_arrow_elim _ unittp); auto.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'. constructor.
      match goal with |- tr ?G (deq ?M ?M ?T) => change T with
          (subst (sh 1)
       (equal booltp
          (app (eq_b (var 2)) (app (var 0) triv))
          btrue)) end. var_solv'. }
          {  apply equal_succ.
      change 
          (arrow unittp nattp) with (@subst obj (sh 2)
(arrow unittp nattp)
                                    ). var_solv'.  } } } 
Qed.

Lemma eqb_P G n m : tr G (oof n nattp) ->
                    tr G (oof m nattp) ->
  tr G (deq (app (eq_b n) m) btrue booltp) ->
                    tr G (deq n m nattp).
  intros.
  match goal with |- tr G ?J => replace J with (substj (dot triv id)
                                                    (deq (subst (sh 1) n)
                                                         (subst (sh 1) m)
                                                    nattp)
                                             ) end.
  2:{
    unfold substj. simpsub. auto.
  }
  eapply tr_generalize. apply tr_equal_intro in H1. apply H1.
  remember (subst (sh 1) n) as n'.
  remember (subst (sh 1) m) as m'.
  suffices: (tr (hyp_tm (equal booltp (app (eq_b n) m) btrue) :: G)
                (deq triv (app (app (app eqb_sound_fn n') m') (var 0))
                       (equal nattp n' m')
            )).
  move/ tr_eq_reflexivity => Hdeq.
  constructor. assumption.
  apply tr_symmetry. apply tr_equal_eta.
  assert (tr
    (hyp_tm (equal booltp (app (eq_b n) m) btrue)
     :: G) (deq n' n' nattp)) as Hn. 
    subst; change nattp with (@subst obj (sh 1) nattp);
      rewrite ! subst_sh_shift; apply tr_weakening_append1; assumption.
  assert (tr
    (hyp_tm (equal booltp (app (eq_b n) m) btrue)
     :: G) (deq m' m' nattp)) as Hm. 
  subst; change nattp with (@subst obj (sh 1) nattp);
      rewrite ! subst_sh_shift; apply tr_weakening_append1; assumption.
 (* replace (equal nattp n' m') with
      (subst1 (var 0) (equal nattp (subst (sh 1) n') (subst (sh 1) m'))). *)
  apply (tr_arrow_elim _ (equal booltp (app (eq_b n') m') btrue)
        ).
  - apply tr_equal_formation. weaken tr_booltp_formation.
    apply eqapp_typed; assumption.
    constructor. apply tr_equal_formation; auto.
    - match goal with |- tr ?G (deq ?M ?M ?T) => replace T with  
          (subst1 m' 
       (arrow
          (equal booltp (app (eq_b (subst (sh 1) n')) (var 0)) btrue)
          (equal nattp (subst (sh 1) n') (var 0)))) end.
      2:{
        unfold subst1. simpsub_big.  auto.
      }
      apply (tr_pi_elim _ nattp).
      match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
       (subst1 n' (pi nattp
          (arrow
             (equal booltp
                (app
                   (eq_b (var 1))
                   (var 0)) btrue)
             (equal nattp  (var 1)
                (var 0))))) end.
      apply (tr_pi_elim _ nattp); try assumption. apply eqb_sound.
      simpsub_big. auto.
      assumption.
      match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
      (subst (sh 1) (equal booltp (app (eq_b n) m) btrue)) end. var_solv0.
      subst. simpsub_big. auto.
Qed.

(*write out subseq refl and subseq trans on paper*)

Definition nsucc_leq_fn :=
    (app (app (app nat_ind_fn (lam
                          (leq_t (var 0) (nsucc (var 0))))
               )
               triv )
               (lam (*x : nat*) (lam (*IH: P(x) *)
                                         (var 0) (*s x  <= s nsucc x  : nat*)
                                      )
                  )
               ).

 
Lemma nsucc_leq: forall G n, tr G (oof n nattp) ->
                       tr G (oof (app nsucc_leq_fn n) (leq_t n (nsucc n))).
  intros. unfold nsucc_leq_fn.
  replace (leq_t n (nsucc n)) with (subst1 n (leq_t (var 0) (nsucc (var 0)))).
  2:{ simpsub_big. auto. } apply (tr_pi_elim _ nattp).
    eapply nat_ind_lamapp; simpsub_big; try reflexivity.
    { (*type p*)
      apply tr_arrow_intro; try apply leq_type; try apply nsucc_type; try var_solv'; auto. }
    { eapply tr_compute; try apply leq_zero_equiv; try apply equiv_refl. constructor.
    }
    {
      apply tr_pi_intro; auto. apply tr_arrow_intro; try weaken leq_type.
      var_solv'.
      apply nsucc_type; var_solv'. 
      apply nsucc_type; var_solv'.
      repeat apply nsucc_type; var_solv'.
      simpsub. eapply tr_compute. 
      eapply equiv_trans.
      { try apply leq_succsucc_equiv; try apply equiv_refl. }
      { apply equiv_app. apply equiv_app. apply equiv_refl.
        apply reduce_equiv. apply reduce_app_beta; apply reduce_id. 
        apply reduce_equiv. apply reduce_app_beta; apply reduce_id. 
      }
      apply equiv_refl. apply equiv_refl.
      simpsub. simpl. 
      change 
       (app (app leqtp (var 1))
            (nsucc (var 1))) with (subst sh1
          (leq_t (var 0)
             (nsucc (var 0)))
                                  ). var_solv0.
    } assumption.
Qed.
