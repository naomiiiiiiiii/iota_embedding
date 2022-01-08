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


(*subterms of the computation type's translation*)
Lemma compm5_type: 
  forall T u lu w lw G,
    tr G (oof w preworld) ->
    tr G (oof lw nattp) ->
    tr G (oof u preworld) ->
    tr G (oof lu nattp) ->
    (tr G (oof T U0)) ->
    tr G (oof  (prod (prod (subseq w lw u lu) (store u lu)) T) U0). 
  intros. apply tr_prod_formation_univ.
  apply tr_prod_formation_univ.
apply subseq_U0; auto.
apply store_U0; auto.  assumption.
Qed.

(*start here fix this one to use compm5*)
Lemma compm4_type: forall u lu A G,
    tr G (oof u preworld) ->
    tr G (oof lu nattp) ->
    (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
   tr [:: hyp_tm preworld & G] (oof (sigma nattp ( let v := Syntax.var 1 in
                  let lv := Syntax.var 0 in
                  prod (prod (subseq (subst (sh 2) u)
                                     (subst (sh 2) lu) v lv) (store v lv))
                                                   A))
                                                    
             U0). move =>> H1 H2 H3.
  eapply tr_sigma_formation_univ.
  unfold nzero. simpsub. apply nat_U0.
  simpl.
    eapply tr_prod_formation_univ.
    eapply tr_prod_formation_univ. unfold nzero. simpl.
    apply subseq_U0; try var_solv;
      try rewrite - (subst_pw (sh 2)); try rewrite - (subst_nat (sh 2));
 rewrite ! subst_sh_shift;
 apply tr_weakening_append2; try assumption.
  apply store_U0; try var_solv. auto.
Qed.

Lemma compm3_type: forall u lu A G,
    tr G (oof u preworld) ->
    tr G (oof lu nattp) ->
 (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
                    tr G  (oof (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                  prod (prod (subseq (subst (sh 2) u)
                                     (subst (sh 2) lu) v lv) (store v lv))
                                                   A
                                                    ))
                               ) U0).
  move =>> H1 H2 H3. apply tr_exist_formation_univ.
  apply pw_kind. eapply compm4_type; try assumption; auto. auto.
 apply leq_refl. auto. Qed.


Lemma compm2_type: forall u lu A G,
    tr G (oof u preworld) ->
    tr G (oof lu nattp) ->
  (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
                    tr G  (oof (laters (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                  prod (prod (subseq (subst (sh 2) u)
                                     (subst (sh 2) lu) v lv) (store v lv))
                                                   A
                                                    ))
                               )) U0).
  intros. apply laters_type. apply compm3_type; try assumption. Qed.



  Lemma compm1_type : forall u lu A G,
    tr G (oof u preworld) ->
    tr G (oof lu nattp) ->
    (tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
    tr G (oof (arrow (store u lu)
                     (*split the theorem up so that this
                      laters part stands alone*)
                         (laters (exist nzero preworld (
                                          sigma nattp 
                                          ( let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let V := ppair v lv in
                  prod (prod (subseq (subst (sh 2) u)
                                     (subst (sh 2) lu) v lv) (store v lv))
                                                   A
                                                    ))
                                    )
         )) U0). (*A should be substed by 2 here start here fix this in trans also*)
  move => u lu A G u_t l_t A_t.
  eapply tr_arrow_formation_univ.
  apply store_U0; try assumption. apply compm2_type; assumption.
  Qed.


  Lemma compm0_type : forall A G w1 l1,
      tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof w1 preworld) ->
tr [:: hyp_tm nattp, hyp_tm preworld & G] (oof l1 nattp) ->
      (tr [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp, hyp_tm preworld & G] (oof A U0)) ->
    tr [:: hyp_tm preworld & G] (oof
       (pi nattp
          (arrow
             (subseq
                w1 l1
    (var 1) (var 0))
             (arrow (store (var 1) (var 0))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq
                                   (var 3) 
                                   (var 2)
                                   (var 1) 
                                   (var 0))
                               (store
                                   (var 1) 
                                   (var 0)))
                            A))))))) U0
          ).
         intros. 
        apply tr_pi_formation_univ. auto.
        apply tr_arrow_formation_univ.
        apply subseq_U0; try assumption; try var_solv.
        apply compm1_type; auto; try var_solv. Qed. 


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
    intros. unfold picomp3. 
    apply (tr_prod_elim2 _  (subst1 (ppi1 (var 0))
                                     (subst (under 1 sh1) T1))).
    apply (tr_prod_elim1 _  _ (subst1 (ppi1 (var 0))
                                     (subst (under 1 sh1) T2))).
    match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
                               (subst1 (ppi1 (var 0))
                                       (prod (
                 prod (subst (under 1 sh1) T1) 
(store (var 2) (var 0))) (subst (under 1 sh1) T2) 
                               )) end.
    2:{ simpsub_bigs. auto. }
    apply (tr_sigma_elim2 _ nattp). 
    match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
                               (subst sh1 
                                      (sigma nattp
                                      (prod (
                 prod T1
(store (var 1) (var 0))) T2
                               ))) end.
    var_solv.
    simpsub_bigs. auto.
Qed.

  Lemma picomp4_works: forall G T1 T2 A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod T1 T2)
                (trans_type (var 1) (var 0) A))), hyp_tm preworld
      & G]
    (oof (picomp4 (var 0)) (trans_type (var 1) (picomp1 (var 0)) A)).
    intros. unfold picomp4.  
    apply (tr_prod_elim2 _  (subst1 (ppi1 (var 0))
                                     (subst (under 1 sh1) (prod T1 T2)))).
    match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
                               (subst1 (ppi1 (var 0))
                                       (prod (
                 prod (subst (under 1 sh1) T1) 
                      (subst (under 1 sh1) T2))
          (trans_type (var 2)
              (var 0) A))) end.
    2:{ simpsub_bigs. rewrite fold_subst1 subst1_trans_type. auto. }
    apply (tr_sigma_elim2 _ nattp). 
    match goal with |- tr ?G (deq ?M ?M ?T) => replace T with
                               (subst sh1 
                                      (sigma nattp
                                      (prod 
                                           (prod T1 T2)
                                             (trans_type
                                                (var 1) (var 0) A))
                               )) end.
    var_solv.
    simpsub_bigs. change (dot (var 0) (sh 2)) with
                      (@under obj 1 (sh 1)).
    rewrite sh_under_trans_type. auto.
    Qed.


  Lemma picomp_world: forall G T,
      tr 
    [:: hyp_tm
          (sigma nattp T), hyp_tm preworld & G] (oof (ppair (var 1) (picomp1 (var 0))) world).
    intros. apply world_pair. var_solv. eapply picomp1_works.
  Qed.

  Lemma picomp2_works: forall G w l A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (shift 1 w) (shift 1 l)
                    (var 1) (var 0))
                   (store (var 1) (var 0)))
                A)),
hyp_tm preworld
      & G]
    (oof (picomp2 (var 0))
         (subseq (shift 1 w) (shift 1 l)
                (var 1) (picomp1 (var 0)))
    ).
  Admitted.

  (*
     Lemma picomp2_works1: forall G y z a A,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq (var 6) (var 5)
                    (var 1) (var 0))
                   (store (var 1) (var 0)))
                A)),
       hyp_tm preworld, y, z, a,
       hyp_tm nattp, hyp_tm preworld
      & G]
    (oof (picomp2 (var 0))
                   (subseq  (var 6) (var 5)
        (var 1) (picomp1 (var 0)))
    ).
  Admitted. *)

     (*
 Lemma picomp2_works2: forall G x A T,
  tr
    [:: hyp_tm
          (sigma nattp
             (prod
                (prod
                   (subseq 
                        (var 4)
                            (ppi1 (var 3))
                  (var 1) (var 0))
                   (store (var 1) (var 0)))
                A)),
     hyp_tm preworld, x,
        hyp_tm
          (sigma nattp T), hyp_tm preworld & G]
    (oof (picomp2 (var 0))
                   (subseq  (var 4)
                            (ppi1 (var 3))
       (var 1) (picomp1 (var 0)))
    ).
  Admitted. *)

    Hint Resolve picomp1_works picomp2_works picomp3_works picomp4_works
      picomp_world.

Lemma ref2_type: (forall G w1 v i A,
  tr G (oof w1 preworld) -> 
  tr G (oof i nattp) ->
  tr G (oof v preworld) ->
      tr G (oof (pi nattp 
               ( let lv := (var 0) in
                 eqtype (app (app (app (shift 1 w1) (shift 1 i))
                                  (next (shift 1 v)))
                                  (next lv))
                        (fut (trans_type (shift 1 v) (var 0) A)))) U0)). Admitted.

  Lemma trans_type_works : forall w l A G,
tr G (oof w preworld) ->
                                    tr G (oof l nattp) ->
      tr G (oof (trans_type w l A) U0).
    move => w l A G Du Dl.
  move : w l G Du Dl. 
    induction A; intros; simpl; try apply tr_unittp_formation; try apply nat_U0.
    + (*arrow*) 
        apply tr_all_formation_univ.
      apply pw_kind.
      apply tr_pi_formation_univ.
      rewrite subst_nzero. apply nat_U0.
      apply tr_arrow_formation_univ.
      repeat rewrite subst_nzero.
      apply subseq_U0; (*showing w, l world*) try var_solv;
      rewrite - (subst_pw (sh 2));
      rewrite - (subst_nat (sh 2));
      rewrite ! subst_sh_shift; 
        apply tr_weakening_append2; try assumption.
        apply tr_arrow_formation_univ; try auto.
        repeat rewrite subst_nzero.
        eapply IHA1; try assumption; try auto; try var_solv. 
        eapply IHA2; try assumption; try auto; try var_solv.
        auto. apply leq_refl. auto.
        (*comp type*)
      + simpsub_big. simpl. unfold subst1. simpsub1.
       (* unfold U0. rewrite - (subst_U0 (dot l id)).
        eapply tr_pi_elim.
        eapply tr_pi_intro. apply nat_type.*)
        apply tr_all_formation_univ. auto.
        apply compm0_type; try var_solv;
      try (rewrite - (subst_pw (sh 2));
      rewrite - (subst_nat (sh 2));
      rewrite ! subst_sh_shift; 
        apply tr_weakening_append2; try assumption).
        rewrite subst_trans_type.
        eapply IHA; auto; try var_solv. simpsub. auto. simpsub; auto. auto.
        apply leq_refl. auto. 
    - (*ref type*)
      eapply tr_sigma_formation_univ; auto.
      eapply tr_prod_formation_univ. apply lt_type.
      rewrite - (subst_nat sh1). var_solv.
      rewrite - (subst_nat sh1) ! subst_sh_shift.
      apply tr_weakening_append1. assumption.
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
    rewrite - (subst_pw (sh 3) )  ! subst_sh_shift.
    apply tr_weakening_append3; assumption. var_solv.
    constructor. var_solv.
    constructor. var_solv.
    apply tr_fut_formation_univ; auto. apply IHA; auto; try var_solv.
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


Fixpoint Gamma_at_ctx (G: source.context) (w l: Syntax.term obj):=
  match G with
    [::] => [::]
  | A::rem => hyp_tm (trans_type (shift (size G - 1) w) (shift (size G - 1) l) A) ::
                               (Gamma_at_ctx rem w l)
                    end.

 Lemma Gamma_at_type {D G w l}:
tr D (oof w preworld) ->
                                    tr D (oof l nattp) ->
 tr D
    (deqtype (Gamma_at G w l)
             (Gamma_at G w l)).
   induction G; move => Hw Hl ; simpl.
   - weaken tr_unittp_formation.
   - constructor. weaken trans_type_works; auto. apply IHG; auto.
 Qed.

Lemma Gamma_at_intro {D G A w l x P}: 
tr D (oof w preworld) ->
                                    tr D (oof l nattp) ->
 tr D (oof P (Gamma_at G w l)) ->
tr D (oof x (trans_type w l A)) ->
tr D (oof (ppair x P) (Gamma_at (A::G) w l)).
  move => Hw Hl Hpair H1. simpl. apply tr_prod_intro; auto.
  (*show that the product type is wellformed *)
Qed.





(*

Lemma map_iota {T} : forall n l (f: nat -> T), map f (iota n l) =
                         map (fun i => f (i - 1)) (iota (n+1) l).
  Admitted.

Lemma subst_itprod : forall n s, foldr (fun acc => fun term => @ppair obj acc term)
                                                 triv
                                                 (mkseq (fun i => shift s (var i)) n) =
shift s (foldr (fun acc => fun term => @ppair obj acc term)
                                                 triv
                                                 (mkseq (fun i => (var i)) n)).
Admitted.


Lemma gamma_at_rec {a G}: (gamma_at (a:: G)) =
                          ppair (var 0) (shift 1 (gamma_at G)).
  unfold gamma_at. simpl. rewrite - subst_itprod.
  unfold mkseq. rewrite (map_iota 0).
  suffices: {in (iota 1 (size G)),  (fun i => shift 1 (var (i - 1))) =1 (fun i => @var obj i)}.
  intros Hfn.
  apply eq_in_map in Hfn.
  rewrite Hfn.
  auto.
  intros i Hi. rewrite mem_iota in Hi.
  induction i.
  discriminate Hi.
  simpsub_bigs. rewrite subn1. simpl. auto.
Qed.*)


Lemma size_Gamma_at_ctx {G w l} : (size G) = (size (Gamma_at_ctx G w l)).
    induction G.
    simpl. auto.
    simpl. rewrite IHG. auto. Qed. 


Lemma gamma_at_typed {G w l} :
tr [::] (oof w preworld) ->
tr [::] (oof l nattp) ->
  tr (Gamma_at_ctx G w l) (deq (gamma_at G) (gamma_at G)
       (Gamma_at G (shift (size G) w)
                 (shift (size G) l))).
  intros. induction G.
  - simpl. 
    constructor.
  - Opaque Gamma_at_ctx. simpl. 
    apply Gamma_at_intro.
  - 
    rewrite - ! subst_sh_shift - (subst_pw (sh (size G).+1)) ! subst_sh_shift
    - (cats0 (Gamma_at_ctx (a:: G) w l)).
    replace (size G).+1 with (size (Gamma_at_ctx (a:: G) w l)).
    apply tr_weakening_append. auto.
    rewrite - size_Gamma_at_ctx. auto.
  - 
    rewrite - ! subst_sh_shift - (subst_nat (sh (size G).+1)) ! subst_sh_shift
    - (cats0 (Gamma_at_ctx (a:: G) w l)).
    replace (size G).+1 with (size (Gamma_at_ctx (a:: G) w l)).
    apply tr_weakening_append. auto.
    rewrite - size_Gamma_at_ctx. auto.
  - simpl.
    rewrite - ! subst_sh_shift - sh_Gamma_at - (addn1 (size G)) addnC - sh_sum ! subst_sh_shift.
    Transparent Gamma_at_ctx. simpl.
    apply tr_weakening_append1.
    rewrite - subst_sh_shift sh_Gamma_at ! subst_sh_shift.
    assumption.
  - simpl. rewrite subn1. simpl. rewrite - addn1 addnC - ! subst_sh_shift - ! sh_sum
                                 - ! sh_trans_type. var_solv0.
Qed.





Ltac trans_type := weaken trans_type_works; auto.
 Lemma move_gamma_works: forall D G w1 l1 w2 l2 m gamma,
tr D (oof w1 preworld) ->
                                    tr D (oof l1 nattp) ->
                                    tr D (oof w2 preworld) ->
                                    tr D (oof l2 nattp) ->
     tr D (oof m (subseq w1 l1 w2 l2)) ->
     tr D (oof gamma (Gamma_at G w1 l1)) ->
     tr D (oof (move_gamma G m gamma) (Gamma_at G w2 l2)).
  move => D G. move: D. induction G; simpl; move => D w1 l1 w2 l2 m gamma
                                                  Hw1 Hl1 Hw2  Hl2 Hsub Hg; auto.
  (*IS*)
   apply tr_prod_intro.
  - (*pi1*)
    unfold move_app.
    (apply (tr_arrow_elim _ (trans_type w1 l1 a))); try trans_type.
    apply (tr_arrow_elim _ (subseq w1 l1
                                   w2 l2
                           )
          ).
    apply subseq_type; auto.
    apply tr_arrow_formation; try trans_type.
    apply move_works; auto. auto.
    eapply tr_prod_elim1. apply Hg.
  - (*pi2*)
    eapply IHG. apply Hw1. apply Hl1. apply Hw2. apply Hl2. auto.
    eapply tr_prod_elim2. apply Hg.
    Qed.

 Lemma comp_front G D tau M: tr
                            ((hyp_tm (store (var 2) (var 1)))::
                             (hyp_tm (subseq (var 4) (var 3)
                                   (var 1) (var 0)
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
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq u l v lv) (store v lv))
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
      apply Gamma_at_type; auto; try var_solv. simpsub_type; auto.
     match goal with |- tr ?G' (deqtype ?T ?T) => replace T with (trans_type (var 1) (var 0) (comp_m tau)); auto end. trans_type; auto; try var_solv. simpsub_type; auto.
    - (*show the translated term has type comp ref A*)
      simpsub_bigs. simpsub_type; auto.
      constructor; auto. simpsub_bigs.
      constructor; auto.
      apply tr_arrow_intro; auto.
      apply subseq_type; auto; try var_solv.
      weaken compm1_type; try var_solv.
      apply trans_type_works; try var_solv.
      (*start here should bring out this part as its exactly
       same as front of bind case*)
      simpsub_big. simpl. apply tr_arrow_intro; auto.
      apply store_type; var_solv.
      sh_var 2 4. rewrite - ! subst_sh_shift.
      weaken compm2_type; try var_solv.
 rewrite subst_trans_type; auto.
 apply trans_type_works; var_solv.
 move: Ht. simpsub_type; auto.
Qed.

Lemma trans_type_equiv: forall A w w' l l', equiv w w' -> equiv l l' ->
                                       equiv (trans_type w l A)
                                             (trans_type w' l' A).
  Admitted.




             Lemma fold_substj M1 M2 T x: (deq (subst1 x M1) (subst1 x M2) (subst1 x T)) =
                               (substj (dot x id) (@ deq obj M1 M2 T)).
Admitted.


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

Lemma consb_typed : forall D w l x, tr D (oof w preworld) ->
                                tr D (oof l nattp) ->
                                tr D (oof x (karrow (fut preworld)
                                                    (arrow (fut nattp) U0)
                                     )) ->
                                tr D (oof (cons_b w l x) preworld).
Admitted.






Lemma nsucc_nat G n: tr G (oof n nattp) ->
                    tr G (oof (nsucc n) nattp).
  Admitted. (*start here move this to basic types*)

Hint Resolve nsucc_nat.

(*start here move to subst_help0*)

(*for any W, W <= x:: W
 going to need lt reflection *)

Lemma nsucc_leq: forall G n, tr G (oof n nattp) ->
                       tr G (oof triv (leq_t n (nsucc n))).
Admitted.



Lemma pw_app_typed2 G u l: tr G (oof u preworld) ->
                                    tr G (oof l nattp) ->
                                    tr G (oof (app u l)
       (karrow (fut preworld)
               (arrow (fut nattp) (univ nzero)))).
  Admitted.

  Lemma consb_subseq G' w' l' x: tr G' (oof w' preworld) ->
                                    tr G' (oof l' nattp) ->
                                tr G' (oof x (karrow (fut preworld)
                                                    (arrow (fut nattp) U0)
                                     )) ->
                                tr G' (oof make_subseq (subseq w' l'
                                                         (cons_b w' l' x) (nsucc l')
                                      )).
  intros. unfold make_subseq.
  apply tr_prod_intro.
  { apply nsucc_leq; auto. }
  { apply tr_all_intro; auto.
  constructor. apply pw_kind. auto.
  simpsub_bigs.
  apply tr_pi_intro. constructor. auto.
  apply tr_pi_intro; auto.
  apply tr_arrow_intro; try apply tr_eqtype_formation; try (weaken lt_type; try var_solv;
    try (rewrite - (subst_nat (sh 3)) ! subst_sh_shift; apply tr_weakening_append3;
         assumption)).
  apply pw_app_typed; try var_solv.
 rewrite - (subst_pw (sh 3)) ! subst_sh_shift; apply tr_weakening_append3;
   assumption.
 apply pw_app_typed; try apply consb_typed;
   try var_solv; try rewrite - (subst_pw (sh 3));
   try rewrite - (subst_nat (sh 3));
   try (rewrite ! subst_sh_shift; apply tr_weakening_append3;
        assumption). change U0 with (subst (sh 3) U0). inv_subst. rewrite ! subst_sh_shift. apply tr_weakening_append3. assumption.
 {
   unfold cons_b. unfold app3. simpsub_bigs.
   eapply tr_compute. eapply equiv_eqtype.
   {apply equiv_refl. }
   { apply equiv_app; try apply equiv_app;
       try( apply reduce_equiv; apply reduce_app_beta;
            apply reduce_id); try apply equiv_refl. } apply equiv_refl. apply equiv_refl.
   simpsub_bigs.
   eapply (tr_eqtype_convert _#3
       (eqtype
          (app
             (app (app (subst (sh 4) w') (var 1))
                (var 3)) (var 2))
          (app
             (app
                   (app (subst (sh 4) w') (var 1))
                (var 3)) (var 2))))
   .
   apply tr_eqtype_formation.
   {apply pw_app_typed; try var_solv; try rewrite - (subst_pw (sh 4));
   try (rewrite ! subst_sh_shift; apply tr_weakening_append4;
        assumption). }
   { apply tr_eqtype_symmetry. apply (tr_eqtype_transitivity _ _
           ( app (app (bite
               btrue 
                (app (subst (sh 4) w') (var 1))
                (subst (sh 4) x)) (var 3)) (var 2))  
                                     ).
     {
       apply (tr_formation_weaken _ nzero).
       apply (tr_arrow_elim _ (fut nattp)); try var_solv; auto.
       apply (tr_karrow_elim _ (fut preworld)); try var_solv; auto.
       change 
       (karrow (fut preworld)
               (arrow (fut nattp) (univ nzero))) with
           (subst1 (ltb_app (var 1) (subst (sh 4) l'))
(karrow (fut preworld)
               (arrow (fut nattp) (univ nzero))) 
           ).
       apply tr_booltp_elim. 
       {
         apply (lt_P (var 0)); try var_solv. rewrite - (subst_nat (sh 4));
   try (rewrite ! subst_sh_shift; apply tr_weakening_append4;
        assumption). rewrite - (sh_sum 3 1). sh_var 1 1. inv_subst.
         var_solv.
       }
       {simpsub_bigs.  apply pw_app_typed2; try var_solv.
        rewrite - (subst_pw (sh 4));
   try (rewrite ! subst_sh_shift; apply tr_weakening_append4;
        assumption). }
       {simpsub_bigs.
       change 
       (karrow (fut preworld)
               (arrow (fut nattp) (univ nzero))) with
           (subst (sh 4)
(karrow (fut preworld)
               (arrow (fut nattp) (univ nzero))) 
           ). rewrite ! subst_sh_shift. apply tr_weakening_append4. assumption.
       } }
     { eapply tr_compute. eapply equiv_eqtype.
       repeat apply equiv_app; try (apply reduce_equiv; apply reduce_bite_beta1; apply reduce_id);
         apply equiv_refl. apply equiv_refl. apply equiv_refl. apply equiv_refl. apply pw_app_typed; try var_solv.
       try rewrite - (subst_pw (sh 4));
   try (rewrite ! subst_sh_shift; apply tr_weakening_append4;
        assumption). } }
   {
apply pw_app_typed; try var_solv.
       try rewrite - (subst_pw (sh 4));
   try (rewrite ! subst_sh_shift; apply tr_weakening_append4;
        assumption).
  } } }

  Qed.


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
