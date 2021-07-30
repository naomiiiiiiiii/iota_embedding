Require Import Program.Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Lemma silly: forall n m, (n + 1) = m \/ (n + 1) = 2.
 move=> + m. ask arthur why doesn't this work
            + doesnt work either*)

(*crucial lemmas leading up to the final theorem (one) showing
 well-typedness of the translation*)


Lemma tr_booltp_eta_hyp0 :
    forall G m n p q a,
      tr G (deq m n (subst1 btrue a))
      -> tr G (deq p q (subst1 bfalse a))
      -> tr ((hyp_tm booltp)::G) (deq 
              (bite (var 0) 
                 (subst sh1 m)
                 (subst sh1 p))
              (bite (var 0)
                 (subst sh1 n) 
                 (subst sh1 q) )
              a).
  intros. rewrite - (cat0s ((hyp_tm booltp)::G)).
  change (sh1) with (@under False 0 sh1).
  change 0 with (size ([::]: @context False)).
  apply tr_booltp_eta_hyp; simpl; assumption.
Qed. (*start here move this to derived_rules*)

(*Start here ask karl
 path induction? 
Goal forall (e: 5 = 3 + 2), etrans e e = e.
  intros. Set Printing All. replace (3 + 2) with 5. rewrite e.
  change (3 + 2) with 5.*)
Lemma fold_substj M1 M2 T x: (deq (subst1 x M1) (subst1 x M2) (subst1 x T)) =
                               (substj (dot x id) (@deq False M1 M2 T)).
Admitted.

Definition ltb_app m n := app (app lt_b m) n.

Lemma ltapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (ltb_app m n) booltp). Admitted.

  Ltac simpsubs := simpsub; simpl.

Ltac simpsub_big_T := match goal with |- tr ?G (deq ?M ?M' ?T) =>
                                    let T' := fresh "T" in
                                    let Ht := fresh "Ht" in
                                    remember T as T' eqn:Ht;
                                   simpsubin_big Ht; rewrite Ht
                    end.

Ltac comptype := eapply tr_formation_weaken; try apply compm5_type; try apply compm4_type; try apply compm3_type;
                   try apply compm2_type;
                   try apply compm1_type; try apply compm0_type; auto;
try apply trans_type_works; auto.

(*default value after s(len w1) is x*)
Definition cons_b w l x :=lam (let i := (var 0) in
                              bite (app (app lt_b i) (shift 1 l)) (app (shift 1 w) i) (shift 1 x)).

Lemma consb_typed : forall D w l x, tr D (oof w preworld) ->
                                tr D (oof l nattp) ->
                                tr D (oof x (karrow (fut preworld)
                                                    (arrow (fut nattp) U0)
                                     )) ->
                                tr D (oof (cons_b w l x) preworld).
Admitted.

Lemma subst_consb w l x s: @subst False s (cons_b w l x) =
                           cons_b (subst s w) (subst s l) (subst s x).
  unfold cons_b. simpsub_big. auto. Qed.

Hint Rewrite subst_consb: subst1 core.

Hint Rewrite <- subst_sh_shift subst_consb subst_U0 subst_ret subst_ret_a subst_subseq subst_leq subst_leq
     subst_lttp subst_lt subst_nzero subst_nat subst_world subst_pw subst_world
     subst_nth subst_laters subst_picomp1 subst_picomp2 subst_picomp4
     subst_picomp3 subst_make_subseq subst_theta subst_minus subst_ltb subst_univ subst_cty subst_con subst_karrow subst_arrow subst_pi subst_clam subst_capp subst_ctlam subst_ctapp subst_lam subst_app subst_fut subst_cnext subst_cprev subst_next subst_prev subst_rec subst_equal subst_triv subst_eqtype subst_subtype subst_kuniv subst_all subst_exist subst_voidtp subst_unittp subst_cunit subst_booltp subst_btrue subst_bfalse subst_bite subst_prod subst_sigma subst_cpair subst_cpi1 subst_cpi2 subst_ppair subst_ppi1 subst_ppi2 subst_set subst_quotient subst_guard subst_wt subst_ext : inv_subst.

Ltac inv_subst :=
autounfold with subst1; autorewrite with inv_subst.


Lemma nsucc_nat G n: tr G (oof n nattp) ->
                    tr G (oof (nsucc n) nattp).
  Admitted. (*start here move this to basic types*)

Hint Resolve nsucc_nat.

(*start here move to subst_help0*)

(*for any W, W <= x:: W, start here move this out of here*)
Lemma consb_subseq G' w' l' x: tr G' (oof w' preworld) ->
                                    tr G' (oof l' nattp) ->
                                tr G' (oof x (karrow (fut preworld)
                                                    (arrow (fut nattp) U0)
                                     )) ->
                                tr G' (oof make_subseq (subseq (ppair w' l')
                                                              (ppair (cons_b w' l' x) (nsucc l'))
                                      )).
Admitted.

Lemma types_hygienic: forall G A A', tr G (deqtype A A') ->
                                hygiene (ctxpred G) A /\ hygiene (ctxpred G) A'.
  Admitted.





 Theorem two: forall G e T ebar,
    trans G e T ebar ->
    tr [::] (oof ebar
                (all nzero preworld (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                                     (trans_type (var 1) (var 0) T))))
           ).
  (*gamma can be part of D, don't even need to move gamma (var 5) over i think*)
  move => G e T ebar Dtrans. induction Dtrans; intros.
  (*ref case*)
  2: { apply comp_front. (*is a valid intro form for comp type*)
       simpsub_bigs. simpsubs.
       apply ret_type.
       remember (lam
                (lam
                   (subst1 (prev ((var 0)))
                      (subst1 (prev ((var 2)))
                              (fut (trans_type ((var 0)) ((var 1)) A)))))) as x.
         remember (cons_b ((var 3)) ((var 2)) x) as u1. (*u1 = u::A*)
         remember (ppair u1 (nsucc (var 2))) as U1.
        - (*u1 : preworld*)
         match goal with |- tr ?G' ?J => assert (tr G' (oof x (karrow (fut preworld)
                                                                    (arrow (fut nattp) U0)
                                              ))) as Hx end.
         subst x. apply tr_karrow_intro; try assumption; auto.
         simpsub_big_T.
         apply tr_arrow_intro; try assumption; auto.
         apply tr_univ_formation; auto.
         simpsub_big_T. change (univ nzero) with (@subst1 False (prev (var 0)) (univ nzero)).
         apply (tr_fut_elim _ _ _ nattp). var_solv. inv_subst. var_solv. auto.
         change (univ nzero) with (@subst1 False (prev (var 2)) (univ nzero)).
         apply (tr_fut_elim _ _ _ preworld). var_solv. inv_subst. var_solv. auto.
         constructor. apply trans_type_works; auto. apply world_pair; var_solv.
         auto.
         match goal with |- tr ?G' ?J => assert (tr G' (oof u1 preworld)) as Hu1 end.
         subst. apply consb_typed; try assumption; try var_solv; auto.
        - (*U1 : world*)
         match goal with |- tr ?G' ?J => assert (tr G' (oof U1 world)) as HU1 end.
         subst. apply world_pair; try assumption; apply nsucc_nat; var_solv; auto. subst U1.
         (*new reference is at world U1*)
       eapply (tr_exist_intro _ _ _ _ u1); auto. 
      (*<succ l, p1, <l, <*, \_:nat.*>>>: Sigma(l1: Nat).(<u, l> <= <u1, l1> x storeU1 x ref(A)@U1) *)
         simpsub_bigs. simpsub_type; auto.
         (*split up nat from pair*)
         apply tr_sigma_intro. apply nsucc_nat. var_solv.
         (*<p1, <l, <*, \_:nat.*>>>: <u, l> <= <u1, l1> x storeU1 x ref(A)@U1) *)
       simpsub_bigs.
         repeat (apply tr_prod_intro); try (apply tr_prod_formation); try ((apply subseq_type || apply store_type);
                                         try assumption; auto).
         + (*showing ref(A)@U1 is a type*)
           match goal with |- tr ?G' (deqtype ?T ?T) =>
                           replace T with (trans_type u1 (nsucc (var 2)) (reftp_m A)) end.
           trans_type; auto. simpl. simpsub_type; auto.
           subst. apply consb_subseq; try assumption; try var_solv.
      (*showing the new store is a store at U1*)
      subst u1. unfold store. apply tr_all_intro; auto. simpsub_bigs.
      apply tr_pi_intro; auto. apply tr_arrow_intro; auto. apply subseq_type; auto.
      (*ltac for showing (sh 2 U1) to be a world in context grown by 2*)
      Hint Rewrite <- subst_ppair subst_nsucc: inv_subst.
      Ltac u1_pw2 := sh_var 2 5; inv_subst; match goal with |- tr (?a::?b::?G') ?J => change (a::b::G') with ([::a; b] ++ G') end; rewrite - (subst_pw (sh 2)) ! subst_sh_shift; apply tr_weakening_append; try assumption.
      apply world_pair. u1_pw2. apply nsucc_nat; var_solv.
      (*start here move this out*)
      suffices: forall G w v lv, tr G (oof w preworld) -> tr G (oof (ppair v lv) world) -> tr G (deqtype (gettype w v lv) (gettype w v lv)). move => gettype_typed. apply gettype_typed; auto. u1_pw2. 
      2: { unfold gettype. simpsub_bigs. apply tr_pi_intro; auto.
           unfold cons_b.
           (*need to beta reduce the innermost lam*)
           match goal with |- tr ?G' (deq ?M ?M ?T) =>
                                           suffices: (hygiene (ctxpred G') M) /\
                                                     (hygiene (ctxpred G') T) end.
           (*=> [HctxT HeqT] ask arthur why cant i put this here*)
           move =>  [HctxM HctxT ].
           match goal with |- tr ?G' (deq ?M ?M ?T)
                           => suffices: (equiv T  (app (app (bite (ltb_app (var 0) (var 6))
                                                                     (app (var 7) (var 0))
                                                                     (shift 4 x)
                                                           ) (next (var 3))) (next (var 2))))
           end.
           move => HeqT.
           (*show that the type does reduce to what I claim it reduces to*)
           2: { do 2 (apply equiv_app; try apply equiv_refl). apply reduce_equiv. simpsub_bigs.
                replace (bite
       (ltb_app (var 0) (var 6))
       (app (var 7) (var 0))
       (subst (sh 4) x)) with (subst1 (var 0) (bite
       (ltb_app (var 0) (var 7))
       (app (var 8) (var 0))
       (subst (sh 5) x))). apply reduce_app_beta; try apply reduce_id. subst x.
       simpsub_bigs. auto. 
           }
           eapply (tr_compute _ _ _ _ _ _ _ HctxT HctxM HctxM HeqT); try (apply equiv_refl).
           clear HctxM HctxT HeqT.
(*match goal with |- tr ?G' (@deq False ?M ?M ?T) => change M with M end.
  literally what
 *)
(*case on whether index is < l = size u*)
match goal with |- tr ?G' (@deq False ?M ?M ?T) => replace M with 
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
(*start here make this its own lemma about lt_b*)
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
             match goal with |- tr ?G' (deq ?M ?M ?T) => suffices: (hygiene (ctxpred G') M) /\
                                                    (hygiene (ctxpred G') T) end.
             move => [HctxM HctxT].
             eapply (tr_compute _ _ _ _ _ _ _ HctxT HctxM HctxM HeqT);
               try (apply equiv_refl).


         match goal with |- (tr ?G' (deq ?M ?M ?T)) => assert  





assert (forall G A B T, tr G (deq A B T)).
  intros. match goal with |- tr ?G' (deq ?M ?M ?T') => change M with M end.
           change (@var var 0) with (@var var 0).
           match goal with |- tr ?G' (@deq False ?X ?X ?Y) => change (@var var 0) with
               (var 0) end.
                           subst1 .
Check (@nattp False). Check (@deq False).


(bite (ltb_app (var 0) (var 6))
          (app
             (app (app (var 4) (var 2))
                make_subseq) (var 0))
          (next
             (move_app A make_subseq
                (app
                   (app (subst (sh 11) Et)
                      (var 9)) 
                   (var 8)))))
 end.

    (subst1 (ltb_app (var 0) (var 6))
       (bite (var 0) 
          (app
             (app (app (var 5) (var 3))
                make_subseq) (var 1))
          (next
             (move_app A make_subseq
                (app
                   (app (subst (sh 12) Et)
                      (var 10)) 
                   (var 9)))))) end.


                                                                     (*plan out how to use hygiene*)
      }


         comptype;
apply compm5_type.
                                         try (var_solv; auto).

         (*ID 1299 is showing the ref type is valid*)
           Search nsucc.
           var_solv.
         . rewrite (subst_trans_type (var 1) (var 0)); auto. repeat rewrite subst1
         Ltac simpsub_invert1 :=
autounfold with subst1; autorewrite - with subst1.
         var_solv.
         simpsub; auto. apply tr_fut_formation_univ.
         simpsub_bigs.
    - (*the type being quantified *)


  }
(*pop them all off*)
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
(@under (var 1) (dot (var 6) id)). rewrite subst1_under_Gamma_at. auto.
}
eapply (tr_all_elim _ nzero preworld). 
match goal with |- tr ?G (deq ?M ?M ?T) =>
               (replace T with
                    (shift 7 T)) end.
2: {  simpsub_type; auto. 
change (dot (var 0)
            (dot (var 1) (sh 9))) with (@under (var 2) (sh 7)).
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
change (var 1) with (@shift (var 1) (var 0)).
apply trans_type_works2; auto.
var_solv.
simpsub_type; auto.
var_solv. replace (Gamma_at G (var 6) (var 5)) with
              (shift 5 (Gamma_at G (var 1) (var 0))). rewrite - subst_sh_shift.
try (apply tr_hyp_tm; repeat constructor).
rewrite - subst_sh_shift. change (sh 5) with (@under (var 0) (sh 5)).
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
(@under (var 1) (dot (var 1) id)). rewrite subst1_under_Gamma_at. simpsub_type; auto.
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
change (var 1) with (@shift (var 1) (var 0)).
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
2: { change (sh 8) with (@under (var 0) (sh 8)).
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
      change (dot (var 0) (dot (var 2) sh1))  with (@under (var 1) (dot (var 1) id)). rewrite ! subst1_under_trans_type; auto. simpsub. simpl.
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


Theorem onef: forall G e T ebar w1 l1,
    of_m G e T ->
    tr [::] (oof (ppair w1 l1) world) ->
    trans G e ebar -> 
    tr (Gamma_at_ctx G w1 l1) (oof (app (app ebar l1) 
              (arrow (Gamma_at G w1 l1) (trans_type w1 l1 T))).
