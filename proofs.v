Require Import Program.Equality.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import source subst_src rules_src help trans basic_types.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
Check context.

Ltac var_solv :=
  try (apply tr_hyp_tm; repeat constructor).



Lemma tr_arrow_elim: forall G a b m n p q, 
    tr G (deqtype a a) ->
    tr G (deqtype b b) ->
      tr G (deq m n (arrow a b))
      -> tr G (deq p q a) 
      -> tr G (deq (app m p) (app n q) b).
intros. 
suffices: (subst1 p (subst sh1 b)) = b. move => Heq.
rewrite - Heq.
eapply (tr_pi_elim _ a); try assumption.
eapply tr_eqtype_convert; try apply tr_arrow_pi_equal; assumption.
simpsub. auto. Qed.

Lemma tr_arrow_intro: forall G a b m n,
    tr G (deqtype a a) ->
      tr G (deqtype b b)
      -> tr (cons (hyp_tm a) G) (deq m n (subst sh1 b))
      -> tr G (deq (lam m) (lam n) (arrow a b) ).
intros. eapply tr_eqtype_convert.
apply tr_eqtype_symmetry. apply tr_arrow_pi_equal; try assumption.
eapply tr_pi_intro; try assumption. Qed.

Lemma tr_karrow_elim: forall G a b m n p q,
    tr G (deqtype a a) ->
    tr G (deqtype b b) ->
      tr G (deq m n (karrow a b))
      -> tr G (deq p q a) 
      -> tr G (deq (app m p) (app n q) b).
  intros. apply (tr_arrow_elim _ a); try assumption.
  eapply tr_eqtype_convert. apply tr_eqtype_symmetry.
  apply tr_arrow_karrow_equal; assumption.
  assumption. Qed.

Lemma kind_type: forall {G K i},
    tr G (deq K K (kuniv i)) -> tr G (deqtype K K).
  intros. eapply tr_formation_weaken.
  eapply tr_kuniv_weaken. apply X. Qed.

Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.
Hint Resolve nat_U0. 

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.
Hint Resolve nat_type. 




Lemma pw_kind: forall {G},
    tr G (deq preworld preworld (kuniv nzero)).
  intros. apply tr_rec_kind_formation.
  apply tr_arrow_kind_formation.
  auto. apply tr_karrow_kind_formation.
  apply tr_fut_kind_formation.
  simpl. rewrite - subst_kuniv.
  apply tr_hyp_tm. repeat constructor.
  auto.
  apply tr_arrow_kind_formation. apply tr_fut_formation_univ.
  rewrite subst_nzero. apply nat_U0. auto.
  apply tr_univ_kind_formation; auto. apply zero_typed. Qed.
Hint Resolve pw_kind. 

Lemma pw_type: forall {G},
    tr G (deqtype preworld preworld ).
  intros. apply (kind_type pw_kind). Qed.

Hint Resolve pw_type.

Lemma pw_type2: forall {G}, tr G (deqtype (arrow (fut nattp) (univ nzero))
                                   (arrow (fut nattp) (univ nzero))).
  intros. apply tr_arrow_formation.
  apply tr_fut_formation. auto.
  apply tr_univ_formation. auto. Qed.

Lemma pw_type1: forall {G}, tr G (deqtype
       (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
       (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
  ).
  intros. apply tr_karrow_formation.
  apply tr_fut_formation. auto. apply pw_type2. Qed.



Lemma unfold_pw: forall G,
    tr G (deqtype preworld (arrow nattp
          (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))). Admitted.

Lemma split_world_elim2: forall W G,
    tr G (oof W world) -> tr G (oof (ppi2 W) nattp).
Admitted.

Lemma split_world_elim1: forall W G,
    tr G (oof W world) -> tr G (oof (ppi1 W) preworld).
Admitted.

Lemma world_type: forall G,
      tr G (deqtype world world). Admitted.
Hint Resolve world_type. 

    Lemma split_world1: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof w1 preworld). (*ask karl can't put a
                                                          conjunction here*)
    Admitted.

    Lemma split_world2: forall w1 l1 G,
tr G (oof (ppair w1 l1) world) -> tr G (oof l1 nattp). (*ask karl can't put a
                                                          conjunction here*)
    Admitted.

    Lemma nth_works: forall G w n,
        tr G (oof w world) -> tr G (oof n nattp) -> tr G (oof (nth w n)
                           (karrow (fut preworld) (arrow (fut nattp) U0))).
      intros. unfold nth. apply (tr_arrow_elim _ nattp); auto.
      do 2? constructor. auto.
      constructor. auto.
      apply tr_univ_formation. auto.
      eapply tr_eqtype_convert. apply unfold_pw.
      apply split_world_elim1. assumption.
      Qed.


Lemma subseq_U0: forall G w1 w2,
    tr G (oof w1 world) -> tr G (oof w2 world) ->
    tr G (oof (subseq w1 w2) (univ nzero)).
  intros.
  assert (forall V,
tr [:: hyp_tm
          (leq_t (var 0)
             (subst (sh 3) (ppi2 (var 0)))),
        hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld), hyp_tm world,
        hyp_tm world
        & G] (oof V world) ->

  tr
    [:: hyp_tm
          (leq_t (var 0)
             (subst (sh 3) (ppi2 (var 0)))),
        hyp_tm nattp, hyp_tm (fut nattp),
        hyp_tm (fut preworld), hyp_tm world,
        hyp_tm world
      & G]
    (oof
       (app3 (ppi1 V) 
          (var 1) (var 3) (var 2)) 
     (univ nzero))
         ) as Hworldapp.
  intros V Hvw.

  rewrite - (subst_nzero (dot (var 2) id)). (*start of the application proof,
                                              make this general for any
                                              (var 0) which gamma says is world*)
  rewrite - subst_univ.
  eapply (tr_pi_elim _ (fut nattp) ).
   simpsub. simpl.
  assert (forall s, pi (fut nattp) (univ nzero)
                     =  @subst False s (pi (fut nattp) (univ nzero))
         ) as sub1.
  auto.
  assert (forall s, @subst False s (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
                     = (karrow (fut preworld) (arrow (fut nattp) (univ nzero)))
         ) as sub2.
  auto.
  assert (forall s, arrow (fut nattp) (univ nzero)
                     =  @subst False s (arrow (fut nattp) (univ nzero))
         ) as sub3.
  auto.
  eapply tr_eqtype_convert.
  rewrite - (subst_U0 (sh 1)).
  eapply tr_arrow_pi_equal.
  eapply tr_fut_formation. eapply nat_type.
  eapply tr_univ_formation.
  apply zero_typed.
  rewrite (sub3 (dot (var 3) id)).
  eapply (tr_pi_elim _ (fut preworld)).
  eapply tr_eqtype_convert.
  rewrite (sub3 sh1).
  eapply tr_arrow_pi_equal.
  eapply tr_fut_formation. eapply pw_type.
  eapply pw_type2.
  assert (forall s, (arrow (fut preworld)
          (arrow (fut nattp) (univ nzero)))
               =  @subst False s (arrow (fut preworld)
          (arrow (fut nattp) (univ nzero)))
)
    as sub4.
  auto.
  eapply tr_eqtype_convert.
  eapply tr_eqtype_symmetry.
  eapply tr_arrow_karrow_equal.
  eapply tr_fut_formation. eapply pw_type.
  eapply pw_type2.
  rewrite - (sub2 (dot (var 1) id)).
  eapply (tr_pi_elim _ nattp).
  eapply tr_eqtype_convert.
  rewrite - (sub2 (sh1)).
  eapply tr_arrow_pi_equal.
  apply nat_type.
  eapply pw_type1.
  eapply tr_eqtype_convert.
  apply unfold_pw.
  eapply (tr_sigma_elim1 _ _ nattp).
  (*assert (forall s, (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
               =  @subst False s (arrow nattp
             (karrow (fut preworld) (arrow (fut nattp) (univ nzero))))
)
    as sub5.
  intros. auto.*)
  apply Hvw.
  (*assert (sigma preworld nattp = world) by auto. rewrite H.
  rewrite - {3}(subst_world (sh 5)).
  apply tr_hyp_tm. repeat constructor.*)
  rewrite - {3}(subst_nat (sh 2)).
  apply tr_hyp_tm. repeat constructor.
  rewrite - {2}(subst_pw (sh 4)).
  rewrite - subst_fut.
  apply tr_hyp_tm. repeat constructor.
  rewrite - {2}(subst_nat (sh 3)).
  rewrite - subst_fut.
  apply tr_hyp_tm. repeat constructor.
  simpsub. simpl.


unfold subseq.
  rewrite - (subst_nzero (dot w2 id)).
  rewrite - subst_univ.
  eapply (tr_pi_elim _ world).
  rewrite - (subst_nzero (under 1 (dot w1 id)) ).
  rewrite - subst_univ.
  rewrite - (subst_world (dot w1 id)).
  rewrite - subst_pi.
  eapply (tr_pi_elim _ world).
  apply tr_pi_intro. apply world_type.
  apply tr_pi_intro. apply world_type.
  eapply tr_prod_formation_univ.
  eapply leq_type.
  eapply split_world_elim2.
  rewrite - (subst_world (sh 1)).
  eapply tr_hyp_tm. constructor.
  eapply split_world_elim2.
  rewrite - (subst_world (sh 2)).
  eapply tr_hyp_tm. repeat constructor.
  eapply tr_all_formation_univ.
  eapply tr_fut_kind_formation.
  apply pw_kind.
  apply zero_typed.
  eapply tr_pi_formation_univ.
  eapply tr_fut_formation_univ.
  apply nat_U0.
  repeat rewrite subst_nzero. apply zero_typed.
  repeat rewrite subst_nzero.
  eapply tr_pi_formation_univ. apply nat_U0.
  repeat rewrite subst_nzero. eapply tr_pi_formation_univ.
  apply leq_type.
  rewrite - (subst_nat (sh 1)).
  eapply tr_hyp_tm. repeat constructor.
  rewrite subst_ppi2. simpsub. simpl.
  eapply split_world_elim2.
  rewrite - (subst_world (sh 4)).
  eapply tr_hyp_tm. repeat constructor.
  repeat rewrite subst_nzero.
  eapply tr_eqtype_formation_univ.
apply Hworldapp. 
  rewrite - {3}(subst_world (sh 5)).
  apply tr_hyp_tm. repeat constructor.
simpsub. simpl. apply Hworldapp. 
  rewrite - {3}(subst_world (sh 6)).
  apply tr_hyp_tm. repeat constructor.
  auto.
  repeat rewrite subst_nzero. apply leq_refl. auto.
assumption. assumption.
Qed.



Ltac simpsub1 :=
  unfold leq_t; unfold leqtp; unfold nattp; unfold preworld; unfold app3; unfold nzero; simpsub; simpl.

Lemma tr_weakening_append: forall (G1: context) G2 J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (G2 ++ G1) (
                       (deq (shift (size G2) J1)
                            (shift (size G2) J2)
                            (shift (size G2) t))).
 intros. induction G2.
 -  simpl. repeat rewrite - subst_sh_shift. simpsub. assumption.
 -
  suffices: (tr (substctx sh1 [::] ++ cons a (G2 ++ G1))
                (substj (under (length [::]) sh1)
                        (substj (sh (size G2)) (deq J1 J2 t)))).
  move => Hdone.
  simpl in Hdone.
  rewrite (size_ncons 1).
  rewrite - plusE. 
  repeat rewrite subst_sh_shift.
  repeat rewrite - shift_sum.
  repeat rewrite subst_sh_shift in Hdone.
  rewrite cat_cons.
 apply (Hdone False). 
 intros.
 eapply tr_weakening.
 simpl. repeat rewrite subst_sh_shift. assumption.
Qed.

Lemma store_type: forall W G,
    (tr G (oof W world)) -> tr G (oof (store W) U0).
Admitted.
Hint Resolve store_type.

Lemma laters_type: forall A G i,
    (tr G (oof A (univ i))) -> tr G (oof (laters A) (univ i)).
  Admitted.
Hint Resolve laters_type.

Lemma bind_type: forall G A B M0 M1,
    tr G (oof M0 (laters A)) ->
    tr G (oof M1 (arrow A (laters B))) ->
    tr G (oof (make_bind M0 M1) (laters B)). Admitted.

Lemma sh_sum :
  forall m n t,
    @subst False (sh n) (subst (sh m) t) = @subst False (sh (n+m)) t.
  intros. repeat rewrite subst_sh_shift.
  rewrite shift_sum. auto. Qed.

Lemma world_pair: forall w l G, tr G (oof w preworld) ->
                           tr G (oof l nattp) ->
    tr G (oof (ppair w l) world).
intros.
   (* eapply tr_eqtype_convert.
    eapply tr_eqtype_symmetry.
      eapply tr_prod_sigma_equal.*)
    (*eapply tr_formation_weaken; eapply tr_kuniv_weaken.
    eapply pw_kind. eapply nat_type.*)
    eapply tr_sigma_intro; try assumption.     apply nat_type. Qed.

Lemma hseq2: forall (T: Type) (x y: T)
                  (L: seq T), [:: x; y] ++ L=
                 [:: x, y & L].
intros. auto. Qed.

  Lemma hseq3: forall (T: Type) (x y z: T)
                  (L: seq T), [:: x; y; z] ++ L=
                 [:: x, y, z & L].
intros. auto. Qed.

Lemma hseq5: forall (T: Type) (x y z a b: T)
                  (L: seq T), [:: x; y; z; a; b] ++ L=
                 [:: x, y, z, a, b & L].
intros. auto. Qed.

  Lemma uworld10: forall G,
      (tr [:: hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 1) (var 0)) world)). intros.
     apply world_pair. 
        rewrite - (subst_pw (sh 2)).
      apply tr_hyp_tm; repeat constructor.
        rewrite - (subst_nat (sh 1)).
        apply tr_hyp_tm; repeat constructor. Admitted.

  Hint Resolve uworld10.

Lemma uworld32: forall G x y,
      (tr [:: x, y, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 3) (var 2)) world)). intros.
   apply world_pair.
  rewrite - (subst_pw (sh 4)). var_solv.
  rewrite - (subst_nat (sh 3)). var_solv. Qed. 

Hint Resolve uworld32.

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
  intros. apply laters_type.
  apply tr_exist_formation_univ.
  apply pw_kind. eapply tr_sigma_formation_univ.
  unfold nzero. simpsub. apply nat_U0.
  simpl.
    eapply tr_prod_formation_univ.
    eapply tr_prod_formation_univ. unfold nzero. simpl.
    apply subseq_U0.
    rewrite - (subst_world (sh 2)).
assert (size [:: hyp_tm nattp; hyp_tm preworld] = 2) as Hsize. by auto. 
    rewrite - Hsize. rewrite - hseq2. repeat rewrite subst_sh_shift.
apply tr_weakening_append. assumption. apply uworld10. 
    auto. unfold nzero. simpsub. apply store_type. auto.
    rewrite subst_nzero. apply X0. 
    auto. apply leq_refl. auto. Qed.



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
  apply store_type. assumption. apply compm2_type; assumption.
  Qed.

Lemma subst_trans_type : forall w l A s,
    (subst s (ppair w l)) = (ppair w l) ->
    (subst s (trans_type w l A)) = (trans_type w l A).
  move => w l A s H. move: w l s H. induction A; intros;simpl; auto; simpsub; simpl; repeat rewrite subst_lt; repeat rewrite subst_nth; repeat rewrite subst_nat; repeat rewrite subst_pw;
  repeat rewrite subst_subseq; repeat rewrite subst_nzero; repeat rewrite subst_store; repeat rewrite - subst_sh_shift; simpsub; try rewrite - subst_ppair;
 try rewrite subst_compose; try rewrite H. 
  - (*arrow*)
    suffices:  (subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A1)) = (trans_type (var 1) (var 0) A1). move => Heq1.
  suffices:  (subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A2)) = (trans_type (var 1) (var 0) A2). move => Heq2.
  rewrite Heq1 Heq2. auto. 
eapply IHA2. simpsub. auto. 
eapply IHA1. simpsub. auto.
  - (*comp*)
 rewrite subst_ppair in H. inversion H. rewrite H1.
repeat rewrite subst_ppair.
rewrite subst_laters. simpsub.  simpl.
repeat rewrite subst_nat; repeat rewrite subst_pw;
  repeat rewrite subst_subseq; repeat rewrite subst_nzero; repeat rewrite subst_store; repeat rewrite - subst_sh_shift. simpsub. simpl.
repeat rewrite subst_compose.
repeat rewrite H2. rewrite subst_laters.
simpsub. simpl. rewrite subst_subseq.
rewrite subst_nzero. rewrite subst_nat. rewrite subst_pw. 
rewrite subst_store. simpsub.
suffices: (
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
move => Heq. rewrite Heq. unfold subst1. auto. repeat rewrite IHA; simpsub; auto.
  - (*ref*)
    rewrite - subst_ppair. rewrite subst_compose. rewrite H.
    suffices: (subst
                      (dot (var 0)
                         (dot (var 1)
                            (dot (var 2) (compose s (sh 3)))))
                      (trans_type (var 1) (var 0) A)) =
              (trans_type (var 1) (var 0) A).
    move => Heq. rewrite Heq. auto.
eapply IHA. simpsub. auto.
Qed.

                        

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
      apply tr_weakening_append. assumption.
      apply uworld10.
        apply tr_arrow_formation_univ; try auto.
        repeat rewrite subst_nzero.
        eapply IHA1; try assumption; try auto. 
        eapply IHA2; try assumption; try auto.
        auto. apply leq_refl. auto.
        (*comp type*)
      + simpsub. simpl.
        rewrite subst_subseq. simpsub.  rewrite subst_laters. simpsub. simpl.
        rewrite subst_trans_type. repeat rewrite subst_nzero subst_nat subst_store. repeat rewrite subst_store. simpsub. repeat rewrite subst_subseq. simpsub. auto.
        rewrite - subst_sh_shift. simpsub.
       (* unfold U0. rewrite - (subst_U0 (dot l id)).
        eapply tr_pi_elim.
        eapply tr_pi_intro. apply nat_type.*)
        apply tr_all_formation_univ. auto.
        apply tr_pi_formation_univ.
        rewrite subst_nzero. apply nat_U0.
        apply tr_arrow_formation_univ.
        apply subseq_U0.
        apply world_pair.
        rewrite - (subst_pw (sh 2)).
        rewrite - hseq2.
        repeat rewrite subst_sh_shift.
        apply tr_weakening_append.
        eapply split_world1. apply Du.
        rewrite - (subst_nat (sh 2)).
        rewrite - hseq2.
        repeat rewrite subst_sh_shift.
        apply tr_weakening_append. eapply split_world2. apply Du.
        apply uworld10.
        apply compm1_type.
        apply uworld10.
        eapply IHA. apply uworld10. auto.
        apply leq_refl. auto. simpsub. auto.
        eapply split_world2. apply Du.
    - (*ref type*)
      eapply tr_sigma_formation_univ; auto.
      eapply tr_prod_formation_univ. apply lt_type.
      rewrite - (subst_nat sh1). var_solv.
      rewrite subst_ppi2. apply split_world_elim2.
      rewrite - (subst_world sh1).
      rewrite - cat1s. repeat rewrite subst_sh_shift.
      apply tr_weakening_append. assumption.
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
      apply tr_weakening_append; assumption.
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
 
Lemma size_gamma_at: forall G w l,
    size (gamma_at G w l) = size G. Admitted.

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


Theorem test: forall s, (@subst False s nattp) = nattp.
  intros. simpsub1. Admitted.


Theorem one: forall G D e T ebar w1 l1,
    of_m G e T -> tr D (oof (ppair w1 l1) world) ->
    trans e ebar -> 
         tr ((gamma_at G w1 l1) ++ D) (oof (app ebar (shift (size G) l1))
                                                   (trans_type
                                                      (shift (size G)
                                                             w1) (shift (size G)
                                                             l1)
                                                    T )).
  move => G D e T ebar w1 l1 De Dw Dtrans.
  move : D w1 l1 ebar Dw Dtrans. induction De; intros.
  10 : {
(*Useful facts that will help us later*)
   remember (size ([:: hyp_tm nattp,
        hyp_tm preworld,
        hyp_tm nattp
        & gamma_at G w1 l1])) as sizel.
    assert (sizel = (3 + size G)) as Hsizel. subst.
    repeat rewrite size_cons. repeat rewrite addnA.
    rewrite size_gamma_at. auto.
   (*assert (tr
    [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp
      & gamma_at G w1 l1 ++ D]
    (oof (ppair (var 1) (var 0)) world) ) as Hu.
   apply world_pair.
        rewrite - (subst_pw (sh 2)).
      apply tr_hyp_tm; repeat constructor.
        rewrite - (subst_nat (sh 1)).
        apply tr_hyp_tm; repeat constructor.*)
assert (tr
    [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp
      & gamma_at G w1 l1 ++ D]
    (oof (ppair (shift 3 (shift (size G) w1)) (var 2)) world)) as Hwv2.
   rewrite shift_sum.
    apply world_pair. 
    (*rewrite subst_sh_shift. subst.
    repeat rewrite - Hseq.*)
    rewrite - {2}(subst_pw (sh (3 + size G))).
    rewrite subst_sh_shift. repeat rewrite plusE.
    repeat rewrite - Hsizel.
    repeat rewrite - cat_cons. subst.
    apply tr_weakening_append; auto.
eapply split_world1. apply Dw.
      rewrite - (subst_nat (sh 3)).
      apply tr_hyp_tm; repeat constructor.
    (*actual proof*)
    simpl.
    suffices:
  tr (gamma_at G w1 l1 ++ D)
(deqtype
      (
       subst1 (shift (size G) l1) 
             (all nzero preworld
                (pi nattp
                   (arrow
                      (subseq
                         (ppair (shift 3 (shift (size G) w1))
                            (var 2)) (ppair (var 1) (var 0)))
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
                                     (trans_type (var 1) (var 0) B)))))))))
              )
    (app
          (lam
             (all nzero preworld
                (pi nattp
                   (arrow
                      (subseq
                         (ppair (shift 3 (shift (size G) w1))
                            (var 2)) (ppair (var 1) (var 0)))
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
                                     (trans_type (var 1) (var 0) B))))))))))
          (shift (size G) l1))
    ). move => Heq.
eapply tr_eqtype_convert. apply Heq.
    inversion Dtrans; subst. simpl.
      eapply (tr_pi_elim _ nattp).
    (*remember (size ([:: hyp_tm nattp,
        hyp_tm preworld,
        hyp_tm nattp
        & gamma_at G w1 l1])) as sizel.*)
-eapply tr_pi_intro. eapply nat_type.
    apply tr_all_intro.
    apply pw_kind.
    rewrite subst_lam.
    simpsub. simpl.
    apply tr_pi_intro.  apply nat_type.
    apply tr_arrow_intro.
    eapply tr_formation_weaken.
    apply subseq_U0. (*to show subseqs
                        are the same type,
 need to show that the variables are both of type world*)
  + apply Hwv2. 
  + apply uworld10.
  +
    eapply tr_formation_weaken.
    eapply compm1_type. apply uworld10.
    apply trans_type_works. apply uworld10.
  (*back to main proof*)
- 
  rewrite subst_arrow.
  apply tr_arrow_intro.
  + repeat rewrite subst_store.
    eapply tr_formation_weaken. simpsub. simpl.
    apply store_type. simpsub. simpl.
    apply tr_sigma_intro. rewrite - (subst_pw (sh 3)).
    var_solv.
    unfold subst1.
    rewrite subst_nat.
    rewrite - (subst_nat (sh 2)). var_solv. auto.
    rewrite subst_laters.
    eapply (tr_formation_weaken _ nzero).
    apply laters_type.
    rewrite subst_exist.
  apply tr_exist_formation_univ; try rewrite subst_nzero.
  apply pw_kind. rewrite subst_sigma.
  eapply tr_sigma_formation_univ.
  repeat rewrite subst_nat.
  apply nat_U0.
  repeat rewrite subst_prod. 
    repeat eapply tr_prod_formation_univ; try rewrite subst_nzero.
    rewrite subst_subseq.
    apply subseq_U0;simpsub; simpl.
    apply world_pair.
    rewrite - (subst_pw (sh 5)). var_solv.
    rewrite - (subst_nat (sh 4)). var_solv.
    auto.
    repeat rewrite subst_store. repeat rewrite subst_nat.
    repeat rewrite subst_pw.
    simpsub. simpl.
    auto. apply store_type. apply uworld10.
    simpsub. simpl.
    repeat rewrite subst_nat. repeat rewrite subst_pw.
    rewrite subst_trans_type.
    apply trans_type_works.
    apply uworld10. simpsub. auto.
    auto. apply leq_refl. auto.
    rewrite subst_bind. repeat rewrite subst_laters. simpsub. simpl.
    repeat rewrite - subst_sh_shift. 
    repeat rewrite subst_store. simpsub. simpl.
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
                                                                             simpsub.
(*at make_bind*)
    eapply (tr_arrow_elim _  (store (ppair (var 3)
                                                   (var 2)
           ))).
- 
 eapply tr_formation_weaken. apply store_type.
  apply world_pair. rewrite - (subst_pw (sh 4)). var_solv.
  rewrite - (subst_nat (sh 3)). var_solv. eapply tr_formation_weaken.
  assert (@ppair False (var 5) (var 4) = subst (sh 2) (ppair (var 3) (var 2))) as Hppair. simpsub. auto. rewrite Hppair.
  apply compm2_type. apply uworld32. apply trans_type_works.
  apply uworld10.
apply (tr_arrow_elim _
          (subseq
             (ppair
                (subst (sh (5 + size G)) w1)
                (var 4)) (ppair (var 3) (var 2)))).
eapply tr_formation_weaken. apply subseq_U0.
apply world_pair.
assert (size [:: hyp_tm (store (ppair (var 2) (var 1))),
        hyp_tm
          (subseq
             (ppair
                (subst (sh (size G + 3)%coq_nat) w1)
                (var 2)) (ppair (var 1) (var 0))),
        hyp_tm nattp, hyp_tm preworld, 
       hyp_tm nattp
      & gamma_at G w1 l1] = (5 + size G)
       ) as Hsize. repeat rewrite size_cons. rewrite size_gamma_at.
auto. rewrite - {2}(subst_pw  (sh (5 + size G))).
repeat rewrite (subst_sh_shift _ (5 + size G)). rewrite - hseq5.
rewrite - Hsize.
rewrite catA.
apply tr_weakening_append; try assumption.
eapply split_world1. apply Dw.
rewrite - (subst_nat (sh 5)). var_solv. apply uworld32.
eapply tr_formation_weaken; apply compm1_type.
auto. apply trans_type_works. auto.
assert (
       (arrow
          (subseq (ppair (subst (sh (5 + size G)) w1) (var 4))
             (ppair (var 3) (var 2)))
          (arrow (store (ppair (var 3) (var 2)))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (prod
                         (prod
                            (subseq (ppair (var 5) (var 4))
                               (ppair (var 1) (var 0)))
                            (store (ppair (var 1) (var 0))))
                         (trans_type (var 1) (var 0) A))))))) =
subst1 (var 2) 
       (arrow
          (subseq (ppair (subst (sh (6 + size G)) w1) (var 5))
             (ppair (var 4) (var 0)))
          (arrow (store (ppair (var 4) (var 0)))
             (laters
                (exist nzero preworld
                   (sigma nattp
                      (prod
                         (prod
                            (subseq (ppair (var 6) (var 5))
                               (ppair (var 1) (var 0)))
                            (store (ppair (var 1) (var 0))))
                         (trans_type (var 1) (var 0) A)))))))) as Hsub.
simpsub. repeat unfold subst1. 
rewrite - (sh_sum _ 6). repeat rewrite subst_subseq. rewrite subst_store.
rewrite subst_laters.
simpsub. simpl. rewrite subst_subseq. rewrite subst_store. simpsub. simpl.
rewrite subst_trans_type. rewrite addnC. auto. simpsub. auto.
rewrite Hsub.
eapply (tr_pi_elim _ nattp).


(*do forall first, then the subst1 as below
 only dif is you dont need to do the pi_elim
 after the subst1*)
    assert(   (pi nattp
          (arrow
             (subseq
                (ppair (subst (sh (6 + size G)) w1) (var 5))
                (ppair (var 4) (var 0)))
             (arrow (store (ppair (var 4) (var 0)))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq (ppair (var 6) (var 5))
                                  (ppair (var 1) (var 0)))
                               (store (ppair (var 1) (var 0))))
                            (trans_type (var 1) (var 0) A)))))))) =
subst1 (var 3) (pi nattp
          (arrow
             (subseq
                (ppair (subst (sh (7 + size G)) w1) (var 6))
                (ppair (var 1) (var 0)))
             (arrow (store (ppair (var 5) (var 0)))
                (laters
                   (exist nzero preworld
                      (sigma nattp
                         (prod
                            (prod
                               (subseq (ppair (var 3) (var 6))
                                  (ppair (var 1) (var 0)))
                               (store (ppair (var 1) (var 0))))
                            (trans_type (var 1) (var 0) A))))))))
          ) as Hsub2.
simpsub. repeat unfold subst1. 
rewrite - (sh_sum _ 7). repeat rewrite subst_subseq. rewrite subst_store.
rewrite subst_laters.
simpsub. simpl. rewrite subst_subseq. rewrite subst_store. simpsub. simpl.
rewrite subst_trans_type. rewrite addnC. auto. simpsub. auto.
    rewrite Hsub2.
    eapply (tr_all_elim _ preworld).
    clear Hsub Hsub2.
assert ( 
       (pi nattp
          (pi nattp
             (arrow
                (subseq
                   (ppair (subst (sh (7 + size G)) w1) (var 1))
                   (ppair (var 5) (var 0)))
                (arrow (store (ppair (var 5) (var 0)))
                   (laters
                      (exist nzero preworld
                         (sigma nattp
                            (prod
                               (prod
                                  (subseq
                                     (ppair (var 7) (var 6))
                                     (ppair (var 1) (var 0)))
                                  (store
                                     (ppair (var 1) (var 0))))
                               (trans_type (var 1) (var 0) A)))))))))
= subst1 (var 3)
       (pi nattp
          (pi nattp
             (arrow
                (subseq
                   (ppair (subst (sh (8 + size G)) w1) (var 1))
                   (ppair (var 2) (var 0)))
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
                               (trans_type (var 1) (var 0) A)))))))))
  ) as Hsub3.
simpsub. unfold subst1. 
rewrite - (sh_sum _ 8). repeat rewrite subst_subseq. rewrite subst_store.
rewrite subst_laters.
simpsub. simpl. rewrite subst_subseq. rewrite subst_store. simpsub. simpl.
rewrite subst_trans_type. rewrite addnC. auto. simpsub. auto.
rewrite Hsub3.
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
    auto. unfold nzero. simpsub. apply store_type. auto.
    rewrite subst_nzero. apply A_t.
    auto. apply leq_refl. auto.

        (*do a suffices somehow*)
suffices:
          tr [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp & gamma_at G w1 l1 ++ D]
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
