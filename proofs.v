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




(*proofs about type translation *)

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

Lemma sh_under_trans_type : forall w l A s n ,
    (subst (under n (sh s)) (trans_type w l A)) = (trans_type
                                            (subst (under n (sh s)) w)
                                         (subst (under n (sh s)) l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.

(*subterms of the computation type's translation*)
Lemma compm5_type: 
  forall T u lu w lw G,
    tr G (oof (ppair w lw) world) ->
    tr G (oof (ppair u lu) world) ->
    (tr G (oof T U0)) ->
    tr G (oof  (prod (prod (subseq (ppair w lw) (ppair u lu)) (store u lu)) T) U0).
intros. repeat (eapply tr_prod_formation_univ).
apply subseq_U0; auto.
apply store_U0; auto. apply X1.
Qed.

(*start here fix this one to use compm5*)
Lemma compm4_type: forall U A G,
    (tr G (oof U world)) ->
    (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
   tr [:: hyp_tm preworld & G] (oof (sigma nattp ( let v := Syntax.var 1 in
                  let lv := Syntax.var 0 in
                  let V := ppair v lv in
                  prod (prod (subseq (subst (sh 2) U) V) (store v lv))
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
    rewrite - Hsize. rewrite make_app2. repeat rewrite subst_sh_shift.
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
                                              prod (prod (subseq (subst (sh 2) U) V) (store v lv))
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
                                              prod (prod (subseq (subst (sh 2) U) V) (store v lv))
                                                   A
                                                    ))
                               )) U0).
  intros. apply laters_type. apply compm3_type; try assumption. Qed.



  Lemma compm1_type : forall u lu A G,
    (tr G (oof (ppair u lu) world)) -> (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
    tr G (oof (arrow (store u lu)
                     (*split the theorem up so that this
                      laters part stands alone*)
                         (laters (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let V := ppair v lv in
                                              let U := ppair u lu in
                                              prod (prod (subseq (subst (sh 2) U) V) (store v lv))
                                                   A
                                                    ))
                                    )
         )) U0). (*A should be substed by 2 here start here fix this in trans also*)
  move => u lu A G U_t A_t.
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
             (arrow (store (var 1) (var 0))
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
                                   (var 1) 
                                   (var 0)))
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
                   (store (var 1) (var 0)))
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
                   (store (var 1) (var 0)))
                T2)), hyp_tm preworld
      & G]
    (oof (picomp3 (var 0)) (store (var 1) (picomp1 (var 0)))).
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


     Lemma picomp2_works1: forall G y z a A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (ppair (var 6) (var 5))
                      (ppair (var 1) (var 0)))
                   (store (var 1) (var 0)))
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
                   (store (var 1) (var 0)))
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

    Hint Resolve picomp1_works picomp2_works1 picomp2_works2 picomp3_works picomp4_works
      picomp_world.

  Lemma trans_type_works : forall w l A G,
      (tr G (oof (ppair w l) world)) ->
      tr G (oof (trans_type w l A) U0).
    move => w l A G Du.
  move : w l G Du.
    induction A; intros; simpl; try apply tr_unittp_formation; try apply nat_U0.
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
      rewrite subst_sh_shift. rewrite make_app2.
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
      rewrite make_app3. rewrite - (subst_world (sh 3) ). rewrite subst_sh_shift.
      eapply tr_weakening_append; try apply Du; try reflexivity; auto. 
      rewrite - (subst_nat (sh 3) ).
      var_solv. apply tr_fut_intro.
      var_solv.
      apply tr_fut_intro.
      var_solv.
      apply tr_fut_formation_univ; auto. apply IHA; auto. apply uworld10.
      auto. apply leq_refl. auto. 
Qed.

 (*the actual type of translated terms*)
Lemma trans_type_works2: forall w A G D,
      (tr D (oof w preworld)) ->
  tr D (deqtype (pi nattp
          (arrow (Gamma_at G (shift 1 w)  (var 0))
                 (trans_type (shift 1 w) (var 0) A)))
          (pi nattp
          (arrow (Gamma_at G (shift 1 w) (var 0))
             (trans_type (shift 1 w) (var 0) A)))).
Admitted.

  Ltac comptype := eapply tr_formation_weaken; try apply compm5_type; try apply compm4_type; try apply compm3_type;
                   try apply compm2_type;
                   try apply compm1_type; try apply compm0_type; auto;
try apply trans_type_works; auto.

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

(**************proofs about translation of contexts*****************)
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


(*an expression in one world can be moved to any accessible world
 should move this to embedded lemmas probably*)
 Lemma move_works: forall G w1 l1 w2 l2 T,
     tr G (oof (ppair w1 l1) world) ->
     tr G (oof (ppair w2 l2) world) ->
     tr G (oof (move T) (arrow (subseq (ppair w1 l1) (ppair w2 l2))
                               (arrow
                                  (trans_type w1 l1 T)
                                  (trans_type w2 l2 T)
                               )
                        )
          ).
   Admitted.


 Lemma Gamma_at_type {D G w l}:
   tr D (oof (ppair w l) world) ->
 tr D
    (deqtype (Gamma_at G w l)
             (Gamma_at G w l)).
   induction G; move => Hw ; simpl.
   - weaken tr_unittp_formation.
   - constructor. weaken trans_type_works; auto. apply IHG; auto.
 Qed.

Lemma Gamma_at_intro {D G A w l x P}: 
 tr D (oof (ppair w l) world) ->
 tr D (oof P (Gamma_at G w l)) ->
tr D (oof x (trans_type w l A)) ->
tr D (oof (ppair x P) (Gamma_at (A::G) w l)).
  move => Hw Hpair H1. simpl. apply tr_prod_intro; auto.
  (*show that the product type is wellformed *)
    weaken trans_type_works; auto. apply Gamma_at_type; auto. 
Qed.



 Lemma sh_under_Gamma_at: forall G w l s n, 
    (subst (under n (sh s)) (Gamma_at G w l)) = (Gamma_at G (subst (under n (sh s)) w)
                                                (subst (under n (sh s)) l)).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite sh_under_trans_type IHG. auto. Qed.


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



Lemma sub_refl: forall ( U: term False) (G: context),
                         tr G (oof U world)
                         ->tr G (oof make_subseq 
                                    (subseq U U)).
Admitted.

(*don't do this because figuring out the substitutions for the term will be weird
 and hard*)


Ltac trans_type := weaken trans_type_works; auto.
 Lemma move_gamma_works: forall D G w1 l1 w2 l2 m gamma,
    tr D (oof (ppair w1 l1) world) ->
    tr D (oof (ppair w2 l2) world) ->
     tr D (oof m (subseq (ppair w1 l1) (ppair w2 l2))) ->
     tr D (oof gamma (Gamma_at G w1 l1)) ->
     tr D (oof (move_gamma G m gamma) (Gamma_at G w2 l2)).
  move => D G. move: D. induction G; simpl; move => D w1 l1 w2 l2 m gamma
                                                  Hw1 Hw2 Hsub Hg; auto.
  (*IS*)
   apply tr_prod_intro.
  - (*show product type is well formed*)
    weaken trans_type_works; auto.
    apply Gamma_at_type; auto.
  - (*pi1*)
    unfold move_app.
    (apply (tr_arrow_elim _ (trans_type w1 l1 a))); try trans_type.
    apply (tr_arrow_elim _ (subseq (ppair w1 l1)
                                   (ppair w2 l2)
                           )
          ).
    apply subseq_type; auto.
    apply tr_arrow_formation; try trans_type.
    apply move_works; auto. auto.
    eapply tr_prod_elim1. apply Hg.
  - (*pi2*)
    eapply IHG. apply Hw1. apply Hw2. auto.
    eapply tr_prod_elim2. apply Hg.
    Qed.

 Lemma comp_front G D tau M: tr
                            ((hyp_tm (store (var 2) (var 1)))::
                             (hyp_tm (subseq (ppair (var 4) (var 3))
                                             (ppair (var 1) (var 0))
                                     ))::
                            (hyp_tm nattp)::
                            (hyp_tm preworld)::
                            (hyp_tm (Gamma_at G (var 1) (var 0)))::
                            (hyp_tm nattp)::
                            (hyp_tm preworld)::D)
                            (oof
                               (subst (under 3 (sh 1)) (subst (under 5 (sh 1)) M))
                               (laters (exist nzero preworld ((* l1 = 3, u := 2, l:= 1, v = 0*)
                                          sigma nattp (*l1 = 4 u := 3, l := 2, v= 1, lv := 0*)
                                          (let u := Syntax.var 5 in
                                              let l := Syntax.var 4 in
                                              let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let U := ppair u l in
                                              let V := ppair v lv in
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq U V) (store v lv))
                                                     (trans_type v lv tau))))
                                    )
                                 )
                             ->
                            tr D (oof (lam (lam (lam (lam (lam M)))))
                                      (all nzero preworld (pi nattp
                                                               (arrow (Gamma_at G (var 1)  (var 0))
                                                                      (trans_type (var 1) (var 0)
                                                                                  (comp_m tau))
                                                               )
                                                          )
                                      )
                                 ).
intros Ht.
simpl. constructor; auto. unfold move_app. unfold nsucc.
simpsub_bigs. simpl. apply tr_pi_intro; auto.
apply tr_arrow_intro; auto.
    - (*show arrow type is well formed*)
      apply Gamma_at_type; auto. simpsub_type; auto.
     match goal with |- tr ?G' (deqtype ?T ?T) => replace T with (trans_type (var 1) (var 0) (comp_m tau)); auto end. trans_type; auto. simpsub_type; auto.
    - (*show the translated term has type comp ref A*)
      simpsub_bigs. simpsub_type; auto.
      constructor; auto. simpsub_bigs.
      constructor; auto.
      apply tr_arrow_intro; auto.
      weaken compm1_type; auto.
      apply trans_type_works; auto.
      (*start here should bring out this part as its exactly
       same as front of bind case*)
      simpsub_big. simpl. apply tr_arrow_intro; auto.
    replace (@ppair False (var 4) (var 3)) with (@subst False (sh 2) (ppair (var 2) (var 1))); auto.
    weaken compm2_type; auto.
 rewrite subst_trans_type; auto.
 apply trans_type_works; auto.
 move: Ht. simpsub_type; auto.
Qed.
