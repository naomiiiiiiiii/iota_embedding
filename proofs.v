Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences.
From istari Require Import Rules Defined DefsEquiv.
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
    rewrite !subst_compose.
    simpsubin H. inversion H. rewrite ! H1 ! H2.
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
move =>> H1 H2. repeat (eapply tr_prod_formation_univ).
apply subseq_U0; auto.
apply store_U0; auto. 
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
                                                    
             U0). move =>> H1 H2.
  eapply tr_sigma_formation_univ.
  unfold nzero. simpsub. apply nat_U0.
  simpl.
    eapply tr_prod_formation_univ.
    eapply tr_prod_formation_univ. unfold nzero. simpl.
    apply subseq_U0.
    rewrite - (subst_world (sh 2)).
assert (size [:: hyp_tm nattp; hyp_tm preworld] = 2) as Hsize. by auto. 
    rewrite - Hsize. rewrite make_app2. repeat rewrite subst_sh_shift.
    eapply tr_weakening_append; try apply H1; try reflexivity.
    apply uworld10.
    auto. unfold nzero. simpsub. apply store_U0. auto.
    rewrite subst_nzero. apply H2. Qed. 

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
  move =>> H1 H2. apply tr_exist_formation_univ.
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
    apply (split_world2 (subst sh1 w)).
      rewrite - (subst_world sh1).
      rewrite - cat1s - subst_ppair. repeat rewrite subst_sh_shift.
      eapply tr_weakening_append; try apply Du; try reflexivity; auto. 
      apply tr_all_formation_univ. apply pw_kind.
      apply tr_pi_formation_univ; auto.
      apply tr_eqtype_formation_univ.
      eapply (tr_arrow_elim _ (fut nattp) ). constructor; auto.
      apply tr_univ_formation.  auto.
      apply (tr_karrow_elim _ (fut preworld)).
      eapply kind_type. apply tr_fut_kind_formation. apply pw_kind. auto.
      apply tr_arrow_formation. constructor; auto.
      apply tr_univ_formation. auto. apply (tr_arrow_elim _ nattp); auto.
      eapply tr_eqtype_convert; try apply unfold_pw.
    apply (split_world1 _ (shift 3 l)).
    rewrite - (subst_world (sh 3) ) - ! subst_sh_shift - subst_ppair
    ! subst_sh_shift make_app3. 
      eapply tr_weakening_append; try apply Du; try reflexivity; auto. 
      rewrite - (subst_nat (sh 3) ).
      var_solv. apply tr_fut_intro.
      var_solv.
      apply tr_fut_intro.
      var_solv.
      apply tr_fut_formation_univ; auto. apply IHA; auto. apply uworld10.
      auto. apply leq_refl. auto. 
Qed.

 (*the actual type of translated terms (without the forall)*)
Lemma trans_type_works1: forall w A G D,
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



Lemma sub_refl: forall ( U: term obj) (G: context),
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
      sh_var 2 4. rewrite - ! subst_sh_shift - ! subst_ppair.
      weaken compm2_type; auto.
 rewrite subst_trans_type; auto.
 apply trans_type_works; auto.
 move: Ht. simpsub_type; auto.
Qed.

Lemma trans_type_equiv: forall A w w' l l', equiv w w' -> equiv l l' ->
                                       equiv (trans_type w l A)
                                             (trans_type w' l' A).
  Admitted.


 Lemma subseq_trans M M' U1 U2 U3 G:
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof make_subseq 
                                    (subseq U1 U3)).
 Admitted.

Lemma store_type1 G w l: (tr G (oof (ppair w l) world)) -> tr G (oof_t (pi nattp (*v = 1, l v= 0*) 
                                                ( let W := (shift 1 (ppair w l)) in
                                                  let V := (ppair (var 1) (var 0)) in
                                                  (arrow (subseq W V) (gettype (shift 1 w) (var 1) (var 0)))))
                                                                       ).
Admitted.

             Lemma fold_substj M1 M2 T x: (deq (subst1 x M1) (subst1 x M2) (subst1 x T)) =
                               (substj (dot x id) (@ deq obj M1 M2 T)).
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

Lemma subst_consb w l x s: @ subst obj s (cons_b w l x) =
                           cons_b (subst s w) (subst s l) (subst s x).
  unfold cons_b. simpsub_big. auto. Qed.

Lemma sh_Gamma_at: forall G w l s,
    (subst (sh s) (Gamma_at G w l)) = (Gamma_at G (subst (sh s) w)
                                                (subst (sh s) l)). intros.
  change (sh s) with (@ under obj 0 (sh s)). apply sh_under_Gamma_at.
Qed.

Hint Rewrite subst_consb sh_Gamma_at: subst1 core.

Hint Rewrite <- sh_Gamma_at subst_sh_shift subst_consb subst_U0 subst_ret subst_ret_a subst_subseq subst_leq subst_leq
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


Lemma ltb_false G n : tr G (oof n nattp) -> tr G (deq (ltb_app n n) bfalse booltp).
Admitted.

Lemma nsucc_lt: forall G n, tr G (oof n nattp) ->
                       tr G (oof triv (lt_t n (nsucc n))).
Admitted.

Lemma tr_eq_reflexivity:
  forall G m n a,
    tr G (deq m n a) ->
    tr G (deq m m a).
  intros  G m n a H0. pose proof (tr_symmetry _#4 H0) as H1.
  apply (tr_transitivity _#5 H0 H1).
Qed.

Lemma reduce_consb {w l x i v lv} : equiv (app (app (app (cons_b w l x) i) v) lv)
                                        (app (app (bite (ltb_app i l) (app w i) x) v) lv).
  unfold cons_b.
           do 2 (apply equiv_app; try apply equiv_refl).
              apply reduce_equiv. 
                replace (bite
       (ltb_app i l)
       (app w i)
       x) with (subst1 i (bite
       (ltb_app (var 0) (shift 1 l))
       (app (shift 1 w) (var 0))
       (shift 1 x))).
                2:{ unfold ltb_app. simpsub_bigs. auto. }
                apply reduce_app_beta; try apply reduce_id.
Qed.

Lemma eq_iffalse {G m n p A}: tr G (deq m bfalse booltp) ->
                              tr G (oof p A) ->
                              tr G (oof n A) ->
                              tr G (deq (bite m n p) p A).
  intros.
  apply tr_equal_elim.
  suffices: tr G (oof (lam triv) (pi (equal booltp m bfalse)
                                     (shift 1 (equal A (bite m n p) p))
                 )).
  intros Heq.
  eapply tr_compute. apply equiv_refl.
  change triv with (@subst1 obj triv triv).
  apply equiv_symm. apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
  change triv with (@subst1 obj triv triv).
  apply equiv_symm. apply reduce_equiv. apply reduce_app_beta; apply reduce_id.
  replace (equal A (bite m n p) p) with (subst1 triv
                                                (shift 1 (equal A (bite m n p) p))).
  2:{
    simpsub_big. auto.
  }
  eapply tr_pi_elim. apply Heq. apply tr_equal_intro. assumption.
  match goal with |- tr ?G ?J => replace J with
    (substj (dot m id) (deq (lam triv) (lam triv)
       (pi (equal booltp (var 0) bfalse)
           (shift 1 (equal (shift 1 A) (bite (var 0)
                                             (shift 1 n)
                                             (shift 1 p))
                           (shift 1 p)))))) end.
  2: {
    simpsub_bigs. auto.
  }
  eapply tr_generalize. eapply tr_eq_reflexivity. apply H.
  apply tr_pi_intro.
  - apply tr_equal_formation. weaken tr_booltp_formation.
    rewrite - (@subst_booltp obj (sh 1)). var_solv0. constructor.
  - simpsub_bigs.
    match goal with |- tr (?x :: ?y :: ?G) (deq triv triv ?T) =>
                    change (?x :: ?y :: ?G) with ([:: x] ++ (y :: G));
    change triv with (@subst obj (under 1 sh1) triv);
    eapply (tr_substitution G [::x] booltp bfalse) end.
  - apply tr_equal_formation. simpl. unfold deqtype.
    change triv with (@shift obj 2 triv).
    inv_subst. rewrite ! subst_sh_shift.
    apply tr_weakening_append2. eapply tr_inhabitation_formation. apply H0.
    replace (@subst obj (sh 2) A) with (subst1 (var 1) (shift 3 A)).
    2: {
      simpsub_bigs. auto.
    }
    constructor. simpl. rewrite - (@subst_booltp obj (sh 2)). var_solv0.
    simpsub_bigs. rewrite ! subst_sh_shift. apply tr_weakening_append2. assumption.
    simpsub_bigs. rewrite ! subst_sh_shift. apply tr_weakening_append2. assumption.
    simpsub_bigs. rewrite ! subst_sh_shift. apply tr_weakening_append2. assumption.
  - simpl. eapply (deq_intro _#4 (var 0) (var 0)).
    change (subst (sh 2) booltp) with (@subst obj sh1 (subst sh1 booltp)).
    change (subst (sh 2) bfalse) with (@subst obj sh1 (subst sh1 bfalse)).
    sh_var 1 1. inv_subst. var_solv.
  - simpsub_bigs. simpsub. eapply tr_compute; try (eapply equiv_equalterm; try (apply reduce_equiv;
                                                                           apply reduce_bite_beta2);
                                              try (apply equiv_refl)); try apply equiv_refl.
    apply reduce_id. apply tr_equal_intro. rewrite ! subst_sh_shift.
    apply tr_weakening_append1. assumption.
Qed.



Lemma reduce_consb_end {G w l x v lv} :
  tr G (oof w preworld) ->
  tr G (oof l nattp) ->
  tr G (oof v (fut preworld)) ->
  tr G (oof lv (fut nattp)) ->
   tr G (oof (lam (lam x)) (karrow (fut preworld) (arrow (fut nattp) U0))) ->
  tr G (deq (app (app (app (cons_b w l (lam (lam x))) l) v) lv) (subst1 lv (subst (under 1 (dot v id)) x)) U0).
  intros.
  unfold cons_b.
  - eapply tr_compute; try apply reduce_consb; try eapply equiv_refl.
  - eapply tr_transitivity. 
    eapply (tr_arrow_elim _ (fut nattp)); try apply H2; auto.
    eapply (tr_karrow_elim _ (fut preworld)); try apply H1; auto.
    apply eq_iffalse; try apply ltb_false; auto.
    (*w l : |> pw -> |> N -> U0 *)
      eapply tr_arrow_elim; try apply H0; auto.
    eapply tr_eqtype_convert; try apply unfold_pw; auto.
  - eapply tr_compute; last 2 [ apply (equiv_symm _ (app (app (lam (lam x)) v) lv)) ]; try (apply equiv_refl).
     eapply equiv_trans.
     apply equiv_app; [ apply reduce_equiv;
                        apply reduce_app_beta; try apply reduce_id | ..]; apply equiv_refl.
     replace (subst1 v (lam x)) with (lam (subst (under 1 (dot v id)) x)).
     2: { simpsub_bigs. auto. }
     apply reduce_equiv.
    apply reduce_app_beta; try apply reduce_id; try apply equiv_refl.
  - eapply (tr_arrow_elim _ (fut nattp)); auto.
    (eapply (tr_karrow_elim _ (fut preworld))); auto.
Qed.

    (*Lemma reduce_consb1_help {G m n p a b c A}: tr G (deq m bfalse booltp) ->
                                      tr G (oof p A) ->
                                      tr G (deqtype (app (app p a) b) c) ->
                                      tr G (deqtype (app (app (bite m n p) a) b) c).
  intros.
  eapply tr_eqtype_transitivity; [.. | apply H1].

apply (tr_eqtype_transitivity #4_
need too much stuff about p being a function
which produces a type, just do consb straight 
 *)

(*need to change ltb_false to have n < n = false,
 not equiv*)
