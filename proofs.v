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

Ltac simpsub_type := simpl; simpsub_big; simpl; rewrite subst_trans_type; simpl.


Lemma subst_Gamma_at :forall w l s G,
    (subst s (ppair w l)) = (ppair w l) ->
    (subst s (Gamma_at G w l)) = (Gamma_at G w l).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite IHG subst_trans_type; auto. Qed.

Lemma subst_move_gamma :forall g m s G,
    (subst s (move_gamma G m g)) = move_gamma G (subst s m) (subst s g).
  intros. move: g m s. induction G; intros; auto. simpl. simpsub.
  rewrite (IHG (ppi2 g) m s); auto. unfold move_app. simpsub. rewrite subst_move.
  auto. Qed.

Hint Rewrite subst_move_gamma: subst1.

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
  Lemma picomp1_works: forall G T,
  tr
    [:: hyp_tm
          (sigma nattp T)
      & G]
    (oof (picomp1 (var 0)) nattp).
    intros. 
   unfold picomp1. apply (tr_sigma_elim1 _ _
       (subst (under 1 (sh 1)) T) ).
   rewrite - (subst_nat (sh 1)). rewrite - subst_sigma.
   var_solv. Qed.

  Lemma picomp2_works: forall G W u A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (shift 1 W)
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                A)),
hyp_tm preworld
      & G]
    (oof (picomp2 (var 0))
                   (subseq (shift 1 W) 
                      (ppair (shift 1 u) (picomp1 (var 0))))
    ).
  Admitted.

  Lemma picomp3_works: forall G T1 T2,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   T1
                   (store (ppair (var 1) (var 0))))
                T2)), hyp_tm preworld
      & G]
    (oof (picomp3 (var 0)) (store (ppair (var 1) (picomp1 (var 0))))).
  Admitted.

  Lemma picomp4_works: forall G T1 T2 A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod T1 T2)
                (trans_type (var 1) (var 0) A))), hyp_tm preworld
      & G]
    (oof (picomp4 (var 0)) (trans_type (var 1) (picomp1 (var 0)) A)).
  Admitted.

  Lemma picomp_world: forall G T,
      tr 
    [:: hyp_tm
          (sigma nattp T), hyp_tm preworld & G] (oof (ppair (var 1) (picomp1 (var 0))) world).
    intros. apply world_pair. var_solv. eapply picomp1_works.
  Qed.


  (*  Lemma picomp_world1: forall G y z a A,
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
Admitted. 

    Lemma picomp_world2: forall G y z a A,
      tr 
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq
                      (ppair (var 4) (ppi1 (var 3)))
                      (ppair (var 1)
                         (var 0)))
                   (store
                      (ppair (var 1)
                         (var 0))))
                A)), hyp_tm preworld, y, z,
       hyp_tm preworld
                     & G] (oof (ppair (var 1) (picomp1 (var 0))) world).
    Admitted.

  Lemma picomp1_works1: forall G x y z a A,
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
Admitted.*)


     Lemma picomp2_works1: forall G y z a A,
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
      & G]
    (oof (picomp2 (var 0))
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (picomp1 (var 0))))
    ).
  Admitted.

 Lemma picomp2_works2: forall G x A T,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq 
                         (ppair (var 4)
                            (ppi1 (var 3)))
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                A)),
     hyp_tm preworld, x,
        hyp_tm
          (sigma nattp T), hyp_tm preworld & G]
    (oof (picomp2 (var 0))
                   (subseq (ppair (var 4)
                            (ppi1 (var 3)))
                      (ppair (var 1) (picomp1 (var 0))))
    ).
  Admitted.

    (*  Lemma picomp3_works1: forall G y z a A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
                   (store (ppair (var 1) (var 0))))
                (trans_type (var 1) (var 0) A))),
       hyp_tm preworld, y, z, a,
       hyp_tm nattp, hyp_tm preworld
      & G]
    (oof (picomp3 (var 0)) (store (ppair (var 1) (picomp1 (var 0))))).
      Admitted.

 Lemma picomp4_works1: forall G y z a A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   T1
                   (store (ppair (var 1) (var 0))))
                (trans_type (var 1) (var 0) A))),
       hyp_tm preworld, y, z, a,
       hyp_tm nattp, hyp_tm preworld
      & G]
    (oof (picomp4 (var 0)) (trans_type (var 1) (picomp1 (var 0)) A)).
 Admitted.*)


    Hint Resolve picomp1_works picomp2_works1 picomp2_works2 picomp3_works picomp4_works
      picomp_world.

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
      var_solv.
      apply tr_fut_intro.
      var_solv.
      apply tr_fut_formation_univ; auto. apply IHA; auto. apply uworld10.
      auto. apply leq_refl. auto. apply tr_unittp_formation.
Qed.

Lemma trans_type_works2: forall w A G D,
      (tr D (oof w preworld)) ->
  tr D (deqtype (pi nattp
          (arrow (Gamma_at G (shift 1 w)  (var 0))
                 (trans_type (shift 1 w) (var 0) A)))
          (pi nattp
          (arrow (Gamma_at G (shift 1 w) (var 0))
             (trans_type (shift 1 w) (var 0) A)))).
Admitted.


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

(*Lemma mvl_works_nz (g: nat) : forall (i: nat), (i < (S g) ->
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

*)
