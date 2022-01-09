
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined PageType lemmas0 derived_rules basic_types.

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

Lemma leq_succsucc_equiv n1_pred n2_pred : equiv (leq_t (ppair bfalse n1_pred)
                                            (ppair bfalse n2_pred))                                                                               (leq_t (app n1_pred triv)
                                                             (app n2_pred triv)).
  Admitted. 

 
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
