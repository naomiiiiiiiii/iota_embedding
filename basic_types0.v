(*Trivial facts that would clutter up the other files*) 
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined PageType lemmas0 derived_rules.
Lemma subst_U0: forall s,
    (@ subst obj s (univ nzero)) = univ nzero.
  auto. Qed.
Hint Rewrite subst_U0: core subst1.

Lemma subst_nzero: forall s,
    @ subst obj s nzero = nzero.
  intros. unfold nzero. auto. Qed.
Hint Rewrite subst_nzero: core subst1.
Ltac simpsub1 :=
autounfold with subst1; autorewrite with subst1.

Ltac simpsub_big := repeat (simpsub; simpsub1).


Hint Unfold subst1: subst1.

Ltac var_solv0 := try (apply tr_hyp_tm; repeat constructor).
 Lemma bool_contra G m n A : tr G (deq bfalse btrue booltp) ->
                          tr G (deq m n A).
   intros Hcontra. apply (tr_voidtp_elim _ triv triv).
   eapply (tr_compute _ _ (bite btrue voidtp unittp)).
   apply equiv_symm. apply reduce_equiv. apply reduce_bite_beta1.
 apply reduce_id. apply equiv_refl. apply equiv_refl.
 eapply tr_eqtype_convert. apply tr_booltp_elim_eqtype;
                             try apply Hcontra;
                             apply (tr_formation_weaken _ nzero). apply tr_voidtp_formation.
 apply tr_unittp_formation.
 eapply tr_compute. apply reduce_equiv. apply reduce_bite_beta2.
 apply reduce_id. apply equiv_refl. apply equiv_refl.
 constructor.
Qed.

 Lemma tr_wt_intro 
    G a b m m' n n':
      tr G (deq m m' a)
      -> tr G (deq n n' (subst1 m (arrow b (subst sh1 (wt a b)))))
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (deq (ppair m n) (ppair m' n') (wt a b)).
 intros Hm Hn Hb.
 apply (tr_subtype_elim _ (sigma a
                                 (arrow b (subst sh1 (wt a b))))).
 apply tr_wt_sigma_subtype.
 {eapply tr_inhabitation_formation. apply Hm. }
 {assumption. }
 { apply tr_sigma_intro; try assumption.
   apply tr_arrow_formation; try assumption.
   rewrite make_app1 ! subst_sh_shift.
   apply tr_weakening_appendt. apply tr_wt_formation.
 eapply tr_inhabitation_formation. apply Hm. assumption.
 } Qed.

 Definition U0 : (term obj) := univ nzero.

Lemma nat_U01 G: tr ((hyp_tm booltp)::G) (oof (bite (var 0) voidtp unittp) U0).
change U0 with (subst1 (var 0) U0).
apply tr_booltp_elim. change booltp with (@subst obj (sh 1) booltp). var_solv0. apply tr_voidtp_formation. apply tr_unittp_formation.
Qed.


Lemma nat_U0: forall G,
    tr G (oof nattp U0).
  intros. unfold nattp.
  apply tr_wt_formation_univ. constructor.
  change (univ (subst sh1 nzero)) with
      (subst1 (var 0) U0).
  apply tr_booltp_elim.
  change booltp with (@subst obj sh1 booltp). var_solv0.
  simpsub_big. apply tr_voidtp_formation.
  simpsub_big. apply tr_unittp_formation. Qed.

Hint Resolve nat_U0. 

Lemma nat_type: forall G,
    tr G (deqtype nattp nattp).
  intros. eapply tr_formation_weaken. apply nat_U0. Qed.
Hint Resolve nat_type. 

Lemma unit_type: forall G,
      tr G (deqtype unittp unittp). 
  intros. eapply tr_formation_weaken. apply tr_unittp_formation. Qed.

Hint Resolve unit_type. 

Lemma bool_type: forall G,
      tr G (deqtype booltp booltp). 
  intros. eapply tr_formation_weaken. apply tr_booltp_formation. Qed.

Hint Resolve bool_type.

Lemma void_type: forall G,
      tr G (deqtype voidtp voidtp). 
  intros. eapply tr_formation_weaken. apply tr_voidtp_formation. Qed.

Hint Resolve void_type.

 Definition if_z (n: term obj): (term obj) := ppi1 n.


Lemma zero_typed: forall G,
    tr G (oof nzero nattp).
  intros.  unfold nattp. unfold nzero.
  apply tr_wt_intro. 
  {constructor. }
  {simpsub_big.  apply tr_arrow_intro; auto.
   apply tr_booltp_elim_eqtype; auto. constructor.
   eapply (tr_compute_hyp _ [::]). constructor.
   {apply reduce_equiv. apply reduce_bite_beta1.
    apply reduce_id. }
   simpl.  apply (tr_voidtp_elim _ (var 0) (var 0)).
   rewrite - (subst_voidtp obj (sh 1)). var_solv0.
  }
   apply tr_booltp_elim_eqtype; auto.  
   rewrite - (subst_booltp obj (sh 1)). var_solv0. Qed.

Hint Resolve zero_typed :core .

Lemma U0_type: forall G,
    tr G (deqtype U0 U0).
  intros. apply tr_univ_formation; auto. Qed.

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


Lemma nsucc_type G n m:
  tr G (deq n m nattp) ->
  tr G (deq (nsucc n) (nsucc m) nattp).
  intros.  unfold nsucc.
  apply tr_wt_intro.
  constructor. simpsub_big.
  apply tr_arrow_intro; try apply tr_booltp_elim_eqtype; auto. constructor.
  rewrite ! subst_sh_shift make_app1. apply tr_weakening_append1. assumption.
  apply tr_booltp_elim_eqtype; auto.
  change  booltp with (@subst obj sh1 booltp). var_solv0. Qed.

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
            - 
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
  intros. unfold leq_t.
  apply (tr_arrow_elim _ nattp); auto.
  unfold leqtp.
  change (arrow nattp U0) with (subst1 n1 (arrow nattp U0)).
  apply (tr_wt_elim _ booltp (bite (var 0) voidtp unittp)).
  - assumption.
  - simpsub. simpl.
    rewrite make_app2.
     change (lam unittp) with
      (@subst obj (under 2 sh1)  (lam unittp)) .
    change 
          (lam
             (bite (ppi1 (var 0)) voidtp
                (app (app (var 1) triv)
                   (app (ppi2 (var 0)) triv))))
 with
        (@subst obj (under 2 sh1)
          (lam
             (bite (ppi1 (var 0)) voidtp
                (app (app (var 1) triv)
                   (app (ppi2 (var 0)) triv))))).
    apply tr_booltp_eta_hyp; simpsub; simpl; simpsub;
    (*rewrite ! subst_nat; *)
      apply tr_arrow_intro; auto; try weaken tr_booltp_formation.
    {simpsub_big. apply tr_unittp_formation. }
    + simpsub_big. apply (w_elim_hyp _ [::]); auto.
      weaken nat_U01.
      match goal with |- tr ?G (deq ?M ?M ?A) => change M with
       (@subst obj (under 0 (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)))
       (bite (var 1) voidtp
          (app (app (var 2) triv)
               (app (var 0) triv)))) end.
      apply tr_sigma_eta_hyp.
      simpsub_big. simpl.
          change (app (app (var 2) triv)
                      (app (var 0) triv)) with
              (@subst obj (under 1 sh1)
                     (app (app (var 1) triv)
                          (app (var 0) triv))).
          change voidtp with (@subst obj (under 1 sh1) voidtp).
          rewrite make_app1.
          apply tr_booltp_eta_hyp; simpsub_big; auto.
      * apply tr_voidtp_formation. 
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
        apply (tr_arrow_elim _ nattp); auto.  
        change (arrow nattp (univ nzero)) with
            (@subst1 obj triv (arrow nattp (univ nzero))).
        apply (tr_pi_elim _ (unittp)).
        - change (pi unittp (arrow nattp (univ nzero)))
          with (@subst obj (sh 2) (pi unittp (arrow nattp (univ nzero)))).
        var_solv0. constructor.
        - apply (tr_arrow_elim _ unittp); auto. 
          change (arrow unittp nattp) with (@subst obj (sh 1) (arrow
                                                                 unittp nattp)).
          var_solv0.
          constructor.
Qed.


Lemma leq_succ_equiv n1_pred n2 : equiv (leq_t (ppair bfalse n1_pred) n2) (bite (if_z n2)
                                                      voidtp
                                                      (leq_t (app n1_pred triv)
                                                             (app (ppi2 n2) triv))).
  intros.
  unfold leq_t. unfold wind.
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
                    apply equiv_app.
                    apply reduce_equiv. apply reduce_ppi2_beta;
                                          apply reduce_id. apply equiv_refl. }
               }
               apply equiv_refl.
           }
           } } } } } } }
Qed.

Lemma leq_zero_equiv n2: equiv (leq_t nzero n2) unittp. 
  unfold leq_t. unfold wind.
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
        change unittp with (subst1 n2 unittp).
        apply reduce_app_beta; apply reduce_id.
      }
    }
    }
    
  }
  }
  }
  Qed.




Lemma leq_succsucc_equiv n1_pred n2_pred : equiv (leq_t (ppair bfalse n1_pred)
                                            (ppair bfalse n2_pred))                                                                               (leq_t (app n1_pred triv)
                                                             (app n2_pred triv)).
  eapply equiv_trans.
  apply leq_succ_equiv.
  eapply equiv_trans.
  {apply equiv_bite.
   apply reduce_equiv. apply reduce_ppi1_beta. apply reduce_id.
   apply equiv_refl.
   apply equiv_app. apply equiv_refl. apply equiv_app.
   apply reduce_equiv. apply reduce_ppi2_beta. apply reduce_id. apply equiv_refl.
  }
  {apply reduce_equiv. apply reduce_bite_beta2. apply reduce_id. }
  Qed.


Lemma leqb_succ_equiv n1_pred n2 : equiv (leqb_app (ppair bfalse n1_pred) n2) (bite (if_z n2)
                                                     bfalse
                                                      (leqb_app (app n1_pred triv)
                                                                (app (ppi2 n2) triv))).

  intros.
  unfold leq_b. unfold wind.
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
                    apply equiv_refl.                  }
               }
               apply equiv_refl.
           }
           } } } } } } }
Qed.



Lemma leqb_zero_equiv n2: equiv (leqb_app nzero n2) btrue. 
  unfold leq_b. unfold wind.
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
        change btrue with (subst1 n2 (btrue)).
        apply reduce_app_beta; apply reduce_id.
      }
    }
    }
    
  }
  }
  }
  Qed.

Lemma subst_leqtp: forall s,
    @ subst obj s (leqtp) = leqtp.
  intros. unfold leqtp. unfold wind. unfold theta.
  repeat rewrite subst_app.
  repeat rewrite subst_lam. simpsub. simpl.
  repeat rewrite project_dot_succ.
  rewrite project_dot_zero. auto. Qed.
Hint Rewrite subst_leqtp: core subst1.
Lemma subst_lttp: forall s,
    @ subst obj s (lttp) = lttp.
  intros. unfold lttp.
  simpsub. rewrite subst_leqtp. unfold nsucc. simpsub. simpl.
  rewrite subst_leqtp. auto. Qed.
Hint Rewrite subst_leqtp: core subst1.


Lemma subst_leq: forall s n1 n2,
    @ subst obj s (leq_t n1 n2) =  leq_t (subst s n1) (subst s n2).
  intros. unfold leq_t.  repeat rewrite subst_app. auto. 
Qed.
Lemma subst_lt: forall s n1 n2,
    subst s (lt_t n1 n2) = lt_t (subst s n1) (@ subst obj s n2).
  intros. repeat rewrite subst_app. rewrite subst_lttp. auto. Qed. 

Hint Rewrite subst_leq subst_lttp subst_lt.
