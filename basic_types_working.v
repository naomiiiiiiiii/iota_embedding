
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined PageType lemmas0 derived_rules basic_types.

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
               

Lemma equal_nzero G n: tr G (deq (if_z n) btrue booltp) ->
                       tr G (deq nzero n nattp). (*
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
            (@subst obj (sh 5) (app (var 0) nzero)). var_solv0. } *) Admitted.

  Lemma equal_succ G preds: tr G (oof preds (arrow (bite bfalse voidtp unittp) nattp)) ->
                        tr G (deq (ppair bfalse preds) (nsucc (app preds triv)) nattp).
    Admitted.

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
      { constructor. 
      }
        }
    }

          
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
