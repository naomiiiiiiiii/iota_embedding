Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
(*crucial lemmas leading up to the final theorem (one) showing
 well-typedness of the translation*)

(*no free variables in translation of types*)
Lemma subst_trans_type :forall w l A s,
    (subst s (ppair w l)) = (ppair w l) ->
    (subst s (trans_type w l A)) = (trans_type w l A).
  move => w l A s H. move: w l s H. induction A; intros;simpl; auto; simpsub_big; simpl; try rewrite - subst_ppair;
 try rewrite subst_compose; try rewrite H. 
  - (*arrow*)
    suffices:  ((subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A1)) = (trans_type (var 1) (var 0) A1)) /\ ((subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A2)) = (trans_type (var 1) (var 0) A2)). move => [Heq1 Heq2].
    rewrite Heq1 Heq2. auto.
    split; [eapply IHA1 | eapply IHA2]; simpsub; auto.
  - (*comp*)
 rewrite subst_ppair in H. inversion H. rewrite H1.
rewrite !subst_ppair !subst_compose !H2.
simpsub_big. simpl. suffices: (
            (subst
                            (dot (var 0)
                               (dot (var 1)
                                  (dot (var 2)
                                     (dot (var 3)
                                        (dot 
                                           (subst (sh 4) l)
                                           (compose s (sh 4)))))))
                            (trans_type (var 1) (var 0) A)
            ) = subst
                            (dot (var 0)
                               (dot 
                                 (var 1)
                                 (dot 
                                 (var 2)
                                 (dot 
                                 (var 3)
                                 (dot
                                 (subst (sh 4) l)
                                 (sh 4))))))
                            (trans_type 
                               (var 1) 
                               (var 0) A)

          ).
move => Heq.
rewrite Heq. unfold subst1. auto. repeat rewrite IHA; simpsub; auto.
  - (*ref*)
    rewrite !subst_compose - !subst_ppair H.
    suffices: (subst
                      (dot (var 0)
                         (dot (var 1)
                            (dot (var 2) (compose s (sh 3)))))
                      (trans_type (var 1) (var 0) A)) =
              (trans_type (var 1) (var 0) A).
    move => Heq. rewrite Heq. auto. simpsub_big.
eapply IHA. simpsub. auto.
Qed.


(*start here automate these ugly cases*)
Lemma sh_trans_type : forall w l A s,
    (subst (sh s) (trans_type w l A)) = (trans_type
                                           (subst (sh s) w)
                                           (subst (sh s) l) A).
  induction A; intros; simpl; auto; simpsub_big; repeat rewrite plusE;
repeat rewrite - addnA;
    simpl; change (1 + 1) with 2;
      replace (1 + 0) with 1; auto; repeat rewrite subst_trans_type; auto.
Qed.

Lemma sh_under_trans_type : forall w l A s n ,
    (subst (under n (sh s)) (trans_type w l A)) = (trans_type
                                            (subst (under n (sh s)) w)
                                         (subst (under n (sh s)) l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.


 Lemma sh_under_Gamma_at: forall G w l s n, 
    (subst (under n (sh s)) (Gamma_at G w l)) = (Gamma_at G (subst (under n (sh s)) w)
                                                (subst (under n (sh s)) l)).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite sh_under_trans_type IHG. auto. Qed.

 (*start here write ltac for these two*)
 Lemma subst1_trans_type : forall w l A s,
    (subst1 s (trans_type w l A)) = (trans_type
                                            (subst1 s w)
                                         (subst1 s l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.

 Lemma subst1_under_trans_type : forall w l A s n ,
    (subst (under n (dot s id)) (trans_type w l A)) = (trans_type
                                            (subst (under n (dot s id)) w)
                                         (subst (under n (dot s id)) l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.

 Lemma subst1_Gamma_at: forall G w l s, 
    (subst (dot s id) (Gamma_at G w l)) = (Gamma_at G (subst1 s w)
                                                                (subst1 s l)).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite subst1_trans_type IHG. auto. Qed.

Lemma subst1_under_Gamma_at: forall G w l s n, 
     (subst (under n (dot s id)) (Gamma_at G w l)) =
     (Gamma_at G (subst (under n (dot s id) ) w)
               (subst (under n (dot s id) ) l)).
  intros. induction G. simpl; auto.
  simpl. simpsub. rewrite subst1_under_trans_type IHG. auto.
Qed.

(*subterms of the computation type*)
Lemma compm4_type: forall U A G,
    (tr G (oof U world)) ->
    (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
   tr [:: hyp_tm preworld & G] (oof (sigma nattp ( let v := Syntax.var 1 in
                  let lv := Syntax.var 0 in
                  let V := ppair v lv in
                  prod (prod (subseq (subst (sh 2) U) V) (store V))
                                                   A))
                                                    
             U0). intros.
  eapply tr_sigma_formation_univ.
  unfold nzero. simpsub. apply nat_U0.
  simpl.
    eapply tr_prod_formation_univ.
    eapply tr_prod_formation_univ. unfold nzero. simpl.
    apply subseq_U0.
    rewrite - (subst_world (sh 2)).
assert (size [:: hyp_tm nattp; hyp_tm preworld] = 2) as Hsize. by auto. 
    rewrite - Hsize. rewrite - hseq2. repeat rewrite subst_sh_shift.
eapply tr_weakening_append; try apply X; try reflexivity. apply uworld10. 
    auto. unfold nzero. simpsub. apply store_U0. auto.
    rewrite subst_nzero. apply X0. Qed. 

Lemma compm3_type: forall U A G,
    (tr G (oof U world)) -> (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
                    tr G  (oof (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let V := ppair v lv in
                                              prod (prod (subseq (subst (sh 2) U) V) (store V))
                                                   A
                                                    ))
                               ) U0).
  intros. apply tr_exist_formation_univ.
  apply pw_kind. eapply compm4_type; try assumption; auto. auto.
 apply leq_refl. auto. Qed.


Lemma compm2_type: forall U A G,
    (tr G (oof U world)) -> (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
                    tr G  (oof (laters (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let V := ppair v lv in
                                              prod (prod (subseq (subst (sh 2) U) V) (store V))
                                                   A
                                                    ))
                               )) U0).
  intros. apply laters_type. apply compm3_type; try assumption. Qed.



  Lemma compm1_type : forall U A G,
    (tr G (oof U world)) -> (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
    tr G (oof (arrow (store U)
                     (*split the theorem up so that this
                      laters part stands alone*)
                         (laters (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let V := ppair v lv in
                                              prod (prod (subseq (subst (sh 2) U) V) (store V))
                                                   A
                                                    ))
                                    )
         )) U0). (*A should be substed by 2 here start here fix this in trans also*)
  move => U A G U_t A_t.
  eapply tr_arrow_formation_univ.
  apply store_U0. assumption. apply compm2_type; assumption.
  Qed.


  Lemma compm0_type : forall A G w1 l1,
      (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof (ppair w1 l1) world)) ->
      (tr [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
    tr [:: hyp_tm preworld & G] (oof
       (pi nattp
          (arrow
             (subseq
                (ppair w1 l1)
                (ppair (var 1) (var 0)))
             (arrow (store (ppair (var 1) (var 0)))
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
                            A))))))) U0
          ).
         intros. 
        apply tr_pi_formation_univ. auto.
        apply tr_arrow_formation_univ.
        apply subseq_U0. assumption.
        apply uworld10.
        apply compm1_type; auto. Qed. 

  (*ppicomps*)
  Lemma picomp1_works: forall G x y z a A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                A)),
       x, y, z, a,
       hyp_tm nattp, hyp_tm preworld
      & G]
    (oof (picomp1 (var 0)) nattp).
    intros. 
   unfold picomp1. apply (tr_sigma_elim1 _ _
       (subst (under 1 (sh 1))
             (prod
                (prod
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                A)) ).
   rewrite - (subst_nat (sh 1)). rewrite - subst_sigma.
   var_solv. Qed.

  Lemma picomp2_works: forall G x y z a A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                A)),
       x, y, z, a,
       hyp_tm nattp, hyp_tm preworld
      & G]
    (oof (picomp2 (var 0))
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
    ).
  Admitted.

  Lemma picomp_world: forall G y z a A,
      tr 
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                A)),
       hyp_tm preworld, y, z, a,
       hyp_tm nattp, hyp_tm preworld
                     & G] (oof (ppair (var 1) (picomp1 (var 0))) world).
   intros. apply world_pair. rewrite - (subst_pw (sh 2)). var_solv. eapply picomp1_works. Qed. 

  Lemma trans_type_works : forall w l A G,
      (tr G (oof (ppair w l) world)) ->
      tr G (oof (trans_type w l A) U0).
    move => w l A G Du.
  move : w l G Du.
    induction A; intros; simpl; try apply nat_U0.
    + (*arrow*)
        apply tr_all_formation_univ.
      apply pw_kind.
      apply tr_pi_formation_univ.
      rewrite subst_nzero. apply nat_U0.
      apply tr_arrow_formation_univ.
      repeat rewrite subst_nzero.
      apply subseq_U0.
    - (*showing w, l world*)
      rewrite - (subst_world (sh 2)).
      rewrite subst_sh_shift. rewrite - hseq2.
      eapply tr_weakening_appends; try apply Du; try reflexivity; auto. 
      apply uworld10.
        apply tr_arrow_formation_univ; try auto.
        repeat rewrite subst_nzero.
        eapply IHA1; try assumption; try auto. 
        eapply IHA2; try assumption; try auto.
        auto. apply leq_refl. auto.
        (*comp type*)
      + simpsub_big. simpl. unfold subst1. simpsub1.
       (* unfold U0. rewrite - (subst_U0 (dot l id)).
        eapply tr_pi_elim.
        eapply tr_pi_intro. apply nat_type.*)
        apply tr_all_formation_univ. auto.
        apply compm0_type; try assumption.
        rewrite - subst_ppair.
        eapply (tr_weakening_appends _
                                     [:: hyp_tm nattp; hyp_tm preworld])
        ; try apply Du; try assumption.
        replace (size [:: hyp_tm nattp; hyp_tm preworld]) with 2; auto.
        rewrite - subst_sh_shift. auto.
        replace (size [:: hyp_tm nattp; hyp_tm preworld]) with 2; auto.
        rewrite - subst_sh_shift. auto. simpsub1. auto. auto.
        rewrite subst_trans_type.
        eapply IHA; auto.  auto. auto.
        apply leq_refl. auto. 
    - (*ref type*)
      eapply tr_sigma_formation_univ; auto.
      eapply tr_prod_formation_univ. apply lt_type.
      rewrite - (subst_nat sh1). var_solv.
      rewrite subst_ppi2. apply split_world_elim2.
      rewrite - (subst_world sh1).
      rewrite - cat1s. repeat rewrite subst_sh_shift.
      eapply tr_weakening_append; try apply Du; try reflexivity; auto. 
      apply tr_all_formation_univ. apply pw_kind.
      apply tr_pi_formation_univ; auto.
      repeat rewrite subst_nzero. apply nat_U0.
      apply tr_eqtype_formation_univ.
      eapply (tr_arrow_elim _ (fut nattp) ). constructor; auto.
      apply tr_univ_formation.  auto.
      apply (tr_karrow_elim _ (fut preworld)).
      eapply kind_type. apply tr_fut_kind_formation. apply pw_kind. auto.
      apply tr_arrow_formation. constructor; auto.
      apply tr_univ_formation. auto. 
      eapply nth_works.
      rewrite - hseq3. rewrite - (subst_world (sh 3) ). rewrite subst_sh_shift.
      eapply tr_weakening_append; try apply Du; try reflexivity; auto. 
      rewrite - (subst_nat (sh 3) ).
      var_solv. apply tr_fut_intro.
      rewrite - (subst_pw (sh 2)). var_solv.
      apply tr_fut_intro.
      rewrite - (subst_nat (sh 1)). var_solv.
      apply tr_fut_formation_univ; auto. apply IHA; auto. apply uworld10.
      auto. apply leq_refl. auto. apply tr_unittp_formation.
Qed.

Lemma size_cons: forall(T: Type) (a: T) (L: seq T),
    size (a:: L) = 1 + (size L). Admitted.
 
(*Lemma size_Gamma_at: forall G w l,
    size (Gamma_at G w l) = size G. Admitted.*)

Theorem typed_hygiene: forall G M M' A,
    (tr G (deq M M' A)) -> (hygiene (ctxpred G) M).
  intros. dependent induction X; auto; try repeat constructor.
  - rewrite ctxpred_length. eapply Sequence.index_length. apply i0.
  - suffices:  (fun j : nat =>
     (j < 0)%coq_nat \/
     (j >= 0)%coq_nat /\ ctxpred G (j - 0)%coq_nat) = (ctxpred G).
    intros Heq. rewrite Heq. eapply IHX1; try reflexivity.
    (*apply extensionality.*)
    Admitted.


(*Opaque laters.
Opaque preworld.
Opaque U0.
Opaque subseq.
Opaque leqtp.
Opaque nzero.
Opaque nattp.
Opaque world.
Opaque nth.*)

(*Theorem one_five: forall G D e T ebar w1 l1, 
    of_m G e T ->
    trans e ebar -> 
         tr (Gamma_at G ___? (oof ebar (all nzero preworld (pi nattp (trans_type
                                                      (var 1) (var 0)
                                                    T )))).*)

Lemma wworld4: forall G x y z a w1 l1,
    tr G (oof (ppair w1 l1) world) ->
tr
    [:: x, y, z, a & G]
    (oof
       (ppair (subst (sh 4) w1)
          (subst (sh 4 ) l1)) world).
  intros. rewrite - (subst_world (sh 4)).
  repeat rewrite (subst_sh_shift _ ).
rewrite - hseq4. eapply tr_weakening_appends; try apply X; try reflexivity; auto. Qed.

Lemma wworld5: forall G x y z a b w1 l1,
    tr G (oof (ppair w1 l1) world) ->
tr
    [:: x, y, z, a, b & G]
    (oof
       (ppair (subst (sh 5) w1)
          (subst (sh 5) l1)) world).
  intros. rewrite - (subst_world (sh 5)).
  repeat rewrite (subst_sh_shift _ ).
  eapply (tr_weakening_appends _
                               [:: x; y; z; a; b]); try apply X; try reflexivity; auto.
Qed.

Lemma wworld6: forall G x y z a b c w1 l1,
    tr G (oof (ppair w1 l1) world) ->
tr
    [:: x, y, z, a, b, c & G]
    (oof
       (ppair (subst (sh 6) w1)
          (subst (sh 6) l1)) world).
  intros. rewrite - (subst_world (sh 6)).
  repeat rewrite (subst_sh_shift _ ).
  eapply (tr_weakening_appends _
                               [:: x; y; z; a; b; c]); try apply X; try reflexivity; auto.
Qed.

Lemma wworld_app: forall G D w1 l1,
    tr D (oof (ppair w1 l1) world) ->
    tr (G ++ D) (oof
                   (subst (sh (size G)) (ppair w1 l1)) world
                ).
  intros. eapply tr_weakening_appends; try apply X; try reflexivity; auto.
  rewrite - subst_sh_shift. auto.
  rewrite - subst_sh_shift. auto. Qed.


(*keep trying to massage the substitution you get into something reasonable
 wrok on paper!!*)
Lemma out_of_lam: forall s l,
(dot (var 0)
(compose s
(dot (var 1)
(dot (var 2) (dot (var 3) (dot (var 4) (dot (subst sh1 l)
                                            (sh 6)))))))) =
(@under False 1  
(compose s
(dot (var 0)
(dot (var 1) (dot (var 2) (dot (var 3) (dot l
                                            (sh 5)))))))).
  intros. simpsub. simpl. auto.
Qed.

Lemma lt1: forall n, n < 1 -> n = 0. Admitted.

Lemma mvl_works0: forall (g: nat), project (gen_sub_mvl (g.+1)) 0 = (var 1).
  intros. induction g.
  simpl. simpsub. auto.
   replace (gen_sub_mvl g.+2) with
       (compose (under (g.+1) (dot (var 1) (dot (var 0) (sh 2)))) (gen_sub_mvl (g.+1))).
   rewrite project_compose. rewrite project_under_lt.
   rewrite subst_var. auto. lia. simpl. auto. Qed.

Lemma mvl_worksg (g: nat): project (gen_sub_mvl g) g = (var 0).
  intros. induction g.
  simpl. simpsub. auto.
simpl.
rewrite project_compose. rewrite project_under_geq. rewrite minusE.
replace (g.+1 - g) with 1. simpsub. rewrite plusE. replace (g+ 0) with g.
apply IHg. rewrite addn0. auto.
rewrite subSnn. auto. apply/ leP. 
apply leqnSn.  Qed.


Lemma subSaddS (n : nat): n > 0 -> (n -1).+1 = n.
  rewrite subn1. intros. rewrite prednK; auto. Qed.

Lemma mvl_works_nz (g: nat) : forall (i: nat), (i < (S g) ->
                                       project (gen_sub_mvl (S g)) i = (var (S i)))
                                      /\ ((i > (S g)) ->
                                         project (gen_sub_mvl (S g)) i = (var i)).
  induction g; simpl; intros; split; intros. 
  simpsub. apply lt1 in H.  subst. simpsub. auto. rewrite project_dot_geq.
  rewrite project_dot_geq. simpsub. simpl.
  rewrite - subnDA. change (1 + 1) with 2.
  rewrite - (addn2 (i - 2)).
  Search ((_ - _) +_). rewrite - addnABC. change (2- 2) with 0.
  rewrite addn0. auto. assumption. auto.
 Search (0 < _ - _).
 rewrite subn_gt0.  assumption. eapply (ltn_trans _ H).
 Unshelve.
 simpsub. move: (IHg i) => [IH1 IH2].
replace (dot
       (subst (gen_sub_mvl g)
          (project
             (under g (dot (var 1) (dot (var 0) (sh 2))))
             0))
       (compose
          (under g (dot (var 1) (dot (var 0) (sh 2))))
          (compose sh1
             (compose
                (under g
                   (dot (var 1) (dot (var 0) (sh 2))))
                (gen_sub_mvl g))))) with
    (gen_sub_mvl (g.+2)).
2: {
  simpl. simpsub. simpl. auto.

}
replace (gen_sub_mvl g.+2) with
    (compose (under g.+1 (dot (var 1) (dot (var 0) (sh 2)))) (gen_sub_mvl g.+1)). Opaque gen_sub_mvl. rewrite project_compose.
destruct (i < (g.+1)) eqn: Hbool. rewrite project_under_lt.
rewrite subst_var IH1; try constructor. apply/ltP: Hbool.
assert (g.+1 = i) as Heq.
apply anti_leq. apply/ andP. split. 
rewrite ltnNge in Hbool. move/ negbT / negPn : Hbool.  apply.
apply H. subst.
rewrite project_under_eq. simpsub.
move: (IHg (g.+2)) => [IHn IHy].
rewrite plusE. replace (g.+1 + 1) with (g.+2).
rewrite IHy. auto. auto.
Search (_.+1 + _ = _ + (_.+1)). ring.
Transparent gen_sub_mvl. simpl. auto.
replace
 (dot
       (subst
          (compose (under g (dot (var 1) (dot (var 0) (sh 2))))
             (gen_sub_mvl g)) (varx False 0))
       (compose
          (compose (under g (dot (var 1) (dot (var 0) (sh 2))))
             (sh 1))
          (compose (under g (dot (var 1) (dot (var 0) (sh 2))))
                   (gen_sub_mvl g)))) with
    (gen_sub_mvl (g.+2)).
replace (gen_sub_mvl g.+2) with
    (compose (under g.+1 (dot (var 1) (dot (var 0) (sh 2)))) (gen_sub_mvl g.+1)). Opaque gen_sub_mvl. rewrite project_compose.
rewrite project_under_geq. rewrite minusE.
replace ((project (dot (var 1) (dot (var 0) (sh 2)))) (i - g.+1))
  with (@var False (i - g.+1)).
2: {
rewrite project_dot_geq.
rewrite project_dot_geq. simpsub. rewrite plusE.
replace (2 + (i - g.+1 -1 -1)) with (2 - 2 + (i - g.+1)).
(*showing
  var (i - g.+1) = var (2 - 2 + (i - g.+1))
 *)
auto. rewrite 2! subnAC.
Search (_ + (_ - _) = (_ + _) - _).
rewrite (addnBA 2).
replace (i - 1 - 1) with (i - 2).
Search ((_ + (_ - _)) =  ( _ - _ + _)).
rewrite (@addnABC 2).  replace (2-2) with 0; auto. auto.
eapply (ltn_trans _ H). rewrite subn2. rewrite 2! subn1. auto.
rewrite 2! subn1 2! ltn_predRL. assumption.
Search ((_ - _ - _) =  ( _ - (_ + _))).
replace (i - g.+1 - 1) with (i - (g.+1 + 1)). 
rewrite subn_gt0. rewrite addn1. assumption.
rewrite addn1. rewrite subn1. rewrite subnS. auto.
rewrite subn_gt0. eapply (ltn_trans _ H). Unshelve.
rewrite ltnS. auto. auto. }
simpsub. rewrite plusE.
replace (g.+1 + (i - g.+1)) with i.
move : (IHg i) => [IH1 IH2]. rewrite IH2. auto.
eapply (ltn_trans _ H). rewrite subnKC; auto.
apply/ leP. auto. simpl. auto. simpl. auto. auto.
Unshelve. auto.
Qed.

(*Lemma et2_eqsub: forall g l1,
           eqsub (compose (gen_sub_mvl_list g 5)
                            (dot (var 0)
                               (dot (var 1)
                                  (dot (var 2)
                                     (dot (var 3)
                                        (dot (subst (sh (g + 5)) l1)
                                             (sh 5)))))))
   (compose (under g (dot (var 0) (dot (var 1) (dot (var 2) (dot (var 3)
                                                    (sh 5))))))
           (compose (gen_sub_mvl_list g 6) (under 5 (dot (subst (sh g) l1) id)))).
  intros.
  apply eqsub_project. intros.
  induction g. simpl. simpsub. simpl.
  simpsub.
  suffices: (var i) = (@project False (dot (var 0) sh1) i). intros Hi.
  rewrite - Hi subst_var. auto.
  rewrite - subst_var.
  replace (var i) with (@subst False id (var i)).
  move: (eqsub_expand_id False 0). apply. simpsub. auto.
  remember g.+1 as gs. simpl. simpsub. simpl. subst.
  destruct (i < g.+1) eqn: Hi; remember Hi as Hi1; clear HeqHi1.
  - apply mvl_works_nz in Hi. repeat (repeat rewrite Hi; simpl; simpsub).
       change (dot (var 0)
          (compose
             (under g
                (dot (var 0)
                   (dot (var 1)
                      (dot (var 2) (dot (var 3) (sh 5))))))
             sh1)) with (@under False g.+1 (dot (var 0) (dot (var 1) (dot (var 2) (dot (var 3)
                                                    (sh 5)))))).
rewrite project_under_lt. repeat (simpsub; repeat rewrite Hi; simpl). auto.
apply/leP. rewrite Hi1. constructor.
  - apply negbT in Hi. rewrite - leqNgt in Hi. rewrite leq_eqVlt in Hi.
    move/ orP : Hi => [H1 | H2].
    + move/ eqP: H1 => H1. subst. repeat rewrite project_under_eq. simpsub.
      rewrite plusE. replace (g.+1 + 0) with (g.+1). repeat rewrite mvl_worksg. simpsub. auto. ring.
      repeat rewrite project_under_geq. simpsub.
      apply mvl_works_nz in H2. repeat rewrite H2. simpsub.
    simpl. simpsub. repeat rewrite Hi. simpsub. simpl.
  - rewrite (mvl_works_nz g i Hi).


induction i.
  - subst. repeat (repeat rewrite mvl_works0; simpsub). auto.
    repeat rewrite mvl_works0. simpsub.
  simpsub. simpl. simpsub. simpl.

  rewrite mvl_works0.
induction g. simpl. simpsub. auto.



simpsub. simpl. simpsub.


simpl. simpsub.*)

Opaque gen_sub_mvl_list.

(* looks like nothing can be done with this
 try and figure if something can be doen with this
Lemma checking: forall t, @subst False (dot (var 0)
(dot (var 1) (dot (var 2) (dot (var 3) (dot nattp
                                            (sh 6)))))) t = t.
  intros. simpsub_big.*)

(*Lemma testing:
  @subst False (dot (var 0) (dot (var 1) (dot (var 2) (dot (var 3) 
                                                           (dot nattp (sh 5)
                                                                     )
           )))) (var 5) = (var 5).
  simpsub.*)

Theorem two: forall G e T ebar,
    of_m G e T ->
    trans G e ebar -> 
    tr [::] (oof ebar
                (all nzero preworld (pi nattp (arrow (Gamma_at G (var 1) (var 0))
                                                     (trans_type (var 1) (var 0) T))))
           ).
  (*gamma can be part of D, don't even need to move gamma (var 5) over i think*)
  move => G e T ebar De Dtrans.
  move : ebar Dtrans. induction De; intros.
  10 : {
(*pop them all off*)
constructor; auto. 
inversion Dtrans. rename H5 into Hebar.
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
  Ltac comptype := replace (@ppair False (var 5) (var 4)) with (@subst False (sh 2) (ppair (var 3) (var 2))); auto; eapply tr_formation_weaken;
                   try apply compm2_type;
                   try apply compm1_type; try apply compm0_type; auto;
try apply trans_type_works; auto.
  comptype. 
  (*engage Et1 *)
  eapply tr_arrow_elim.
  (*start here fix this*)
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
simpsub_big. simpl. rewrite subst_trans_type; auto.
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
    simpsub_big. simpl. rewrite subst_trans_type; auto. }
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
2: { simpsub_big. simpl. rewrite subst_trans_type; auto. rewrite subst1_Gamma_at; auto. }
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
2: { simpsub_big. simpl. rewrite subst_trans_type; auto.
     change (dot (var 0) (dot (var 7) sh1)) with
(@under False 1 (dot (var 6) id)). rewrite subst1_under_Gamma_at. auto.
}
eapply (tr_all_elim _ nzero preworld). 
match goal with |- tr ?G (deq ?M ?M ?T) =>
               (replace T with
                    (shift 7 T)) end.
2: { simpsub_big. simpl. rewrite subst_trans_type; auto. 
change (dot (var 0)
            (dot (var 1) (sh 9))) with (@under False 2 (sh 7)).
rewrite sh_under_Gamma_at. simpsub. auto. }
match goal with |- tr ?G' ?J => rewrite - (cats0 G'); change (sh 7)
with (@sh False (size G')); rewrite ! subst_sh_shift
end. apply tr_weakening_append.
match goal with |- tr ?G (deq ?M ?M (all _ _ (pi _ (arrow _ ?T)))
                        ) =>
                replace T with
    (trans_type (var 1) (var 0) (comp_m A)) end.
eapply IHDe1.
change (sh 7) with (sh (si))


eapply trans_type_works; auto. (*have popped off G*)
simpsub_big. simpl. constructor; auto; simpsub_big; simpl.
constructor; auto.

comptype. apply compm0_type.

    auto. unfold subst1. simpsub1. rewrite - addnA.
    rewrite subst_trans_type. rewrite addnC. auto. simpsub. auto.
    rewrite Hsub2.
    eapply (tr_all_elim _ nzero preworld).
    (*strange goal comes from here
     get this out of comp type
     get w to have the shift in front from the start*)
    clear Hsub Hsub2.
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
rewrite - (subst_pw (sh 4)). var_solv.
(*replace 6 with (2 + 4). rewrite - addnA.*)
(*repeat rewrite - (sh_sum (4 + size G) 2). *)
eapply tr_formation_weaken; apply compm0_type.
do 2! rewrite - (sh_sum _ 6).
apply wworld6. erewrite <- size_Gamma_at. apply wworld_app. assumption.
apply trans_type_works. apply uworld10. 
rewrite - (subst_nat (sh 3)). var_solv.
rewrite - (addn2 (size G)).
replace ( subseq
          (ppair (subst (sh (4 + size G)) w1)
             (subst (sh (4 + size G)) l1))
          (ppair (var 3) (var 2)))
  with (subst (sh 2)
          (subseq
             (ppair (subst (sh (size G + 2)) w1)
                (subst (sh (size G + 2)) l1)) (ppair (var 1) (var 0))
       )). var_solv. simpsub_big. auto. rewrite plusE.
replace (size G + 2 + 2) with (4 + size G); auto.
rewrite addnC. rewrite - addnA. auto.
replace (store (ppair (var 3) (var 2)))
with (subst (sh 1) (store (ppair (var 2) (var 1)))). var_solv.
simpsub_big. auto. simpsub.
(*e2bar*)
 rewrite subst_bind.
 simpsub_big. simpl. simpsub.
 apply tr_arrow_intro.
 - 
   replace (ppair (var 5) (var 4)) with
       (@subst False (sh 2)
              (ppair (var 3) (var 2))
       ).
   eapply tr_formation_weaken; eapply compm3_type; auto.
   apply trans_type_works; auto.
   simpsub. auto.
 -
   replace (ppair (var 5) (var 4)) with
       (@subst False (sh 2)
              (ppair (var 3) (var 2))
       ).
   eapply tr_formation_weaken; eapply compm2_type; auto.
   apply trans_type_works; auto.
   simpsub. auto.
 - simpsub_big. simpl.
   rewrite ! plusE.
   remember 
    [:: hyp_tm
          (exist nzero preworld
             (sigma nattp
                (prod
                   (prod (subseq (ppair (var 5) (var 4)) (ppair (var 1) (var 0)))
                      (store (ppair (var 1) (var 0)))) (trans_type (var 1) (var 0) A)))),
        hyp_tm (store (ppair (var 2) (var 1))),
        hyp_tm
          (subseq (ppair (subst (sh (size G).+2) w1) (subst (sh (size G + 2)) l1)) (ppair (var 1) (var 0))),
        hyp_tm nattp, hyp_tm (subst1 (subst (sh (size G)) l1) preworld)
                      & Gamma_at G w1 l1 ++ D] as G'.
   remember 
       (laters
          (exist nzero preworld
             (sigma nattp
                (prod (prod (subseq (ppair (var 6) (var 5)) (ppair (var 1) (var 0))) (store (ppair (var 1) (var 0))))
                   (subst (dot (var 0) (dot (var 1) (sh 3))) (trans_type (var 1) (var 0) B)))))) as a'.
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
             (ret_t
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
       ).
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
   apply world_pair. rewrite - (subst_pw (sh 2)). var_solv. eapply picomp1_works.
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
  rewrite - (subst_pw (sh 4)). var_solv.
  rewrite - (subst_nat (sh 3)). var_solv. apply trans_type_works.





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
