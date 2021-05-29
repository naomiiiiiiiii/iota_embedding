Require Import Program.Equality Ring.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src help trans basic_types.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
Check context.
Ltac var_solv :=
  try (apply tr_hyp_tm; repeat constructor).

Ltac simpsub_backup := repeat (try rewrite subst_laters; try rewrite subst_subseq; try rewrite subst_store;
        try rewrite subst_pw;
        try rewrite subst_nzero; try rewrite subst_nat; try rewrite subst_pw; simpsub; simpl).

Ltac simpsub_big := repeat (simpsub; simpsub1).


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


Lemma tr_weakening_appends: forall G1 G2 G3 J1 J2 t J1' J2' t',
    tr G1 (deq J1 J2 t) ->
    J1' = (shift (size G2) J1) ->
    J2' = (shift (size G2) J2) ->
    t' = (shift (size G2) t) ->
    G3 = G2 ++ G1 ->
      tr G3 (deq J1' J2' t').
 intros. move: G3 t t' J1' J2' J1 J2 H H0 H1 H2 X. induction G2; intros.
 -  simpl. subst. repeat rewrite - subst_sh_shift. simpsub. assumption.
 -
  suffices: (tr (substctx sh1 [::] ++ cons a (G2 ++ G1))
                (substj (under (length [::]) sh1)
                        (substj (sh (size G2)) (deq J1 J2 t)))).
  move => Hdone.
  simpl in Hdone. subst.
  rewrite (size_ncons 1).
  rewrite - plusE. 
  repeat rewrite subst_sh_shift.
  repeat rewrite - shift_sum.
  repeat rewrite subst_sh_shift in Hdone.
  rewrite cat_cons.
 apply (Hdone False). 
 intros.
 eapply tr_weakening.
 simpl. repeat rewrite subst_sh_shift. eapply IHG2; try reflexivity. assumption.
Qed.

 Lemma tr_weakening_append: forall (G1: context) G2 J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (G2 ++ G1) (
                       (deq (shift (size G2) J1)
                            (shift (size G2) J2)
                            (shift (size G2) t))).
   intros. eapply tr_weakening_appends; try apply X; try reflexivity.
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

Lemma shh_sum :
  forall m n t,
    @substh False (sh n) (substh (sh m) t) = @substh False (sh (n+m)) t.
Admitted.

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

Lemma hseq4: forall (T: Type) (x y z a: T)
                  (L: seq T), [:: x; y; z; a] ++ L=
                 [:: x, y, z, a & L].
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

  Lemma uworld43: forall G x y z,
      (tr [:: x, y, z, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 4) (var 3)) world)). intros.
   apply world_pair.
  rewrite - (subst_pw (sh 5)). var_solv.
  rewrite - (subst_nat (sh 4)). var_solv. Qed. 

Hint Resolve uworld32.

Lemma uworld21: forall G x,
      (tr [:: x, hyp_tm nattp, hyp_tm preworld & G]
    (oof (ppair (var 2) (var 1)) world)). intros.
   apply world_pair.
  rewrite - (subst_pw (sh 3)). var_solv.
  rewrite - (subst_nat (sh 2)). var_solv. Qed. 

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
repeat rewrite subst_compose.
repeat rewrite H2. 
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



Lemma sh_trans_type : forall w l A s,
    (subst (sh s) (trans_type w l A)) = (trans_type
                                           (subst (sh s) w)
                                           (subst (sh s) l) A).
  induction A; intros; simpl; auto; simpsub_big; repeat rewrite plusE;
repeat rewrite - addnA;
    simpl; replace (1 + 1) with 2;
      replace (1 + 0) with 1; auto.
  - (*arrow*)
     repeat rewrite - subst_sh_shift.
     simpsub. rewrite plusE.
    repeat rewrite subst_trans_type; auto.
  - (*comp*)
    repeat rewrite subst_trans_type; simpsub; auto.
    unfold subst1. simpsub1.
    repeat rewrite - subst_sh_shift. simpsub. auto.
  - (*ref*)
    repeat rewrite subst_trans_type; simpsub; auto.
    unfold subst1. simpsub1.
    repeat rewrite - subst_sh_shift. simpsub. auto.
    rewrite subst_lt. simpsub. auto.
Qed.

(*pick up here*)
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
    auto. unfold nzero. simpsub. apply store_type. auto.
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
  apply store_type. assumption. apply compm2_type; assumption.
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
        rewrite - subst_sh_shift. simpsub.
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

(*Theorem one_five: forall G D e T ebar w1 l1, 
    of_m G e T ->
    trans e ebar -> 
         tr (gamma_at G ___? (oof ebar (all nzero preworld (pi nattp (trans_type
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

(*Definition gen_sub G s := foldr (fun _  => fun s => )*)


Lemma test1: forall (t: term False), subst (dot (var 1) (dot (var 0) (sh 2)))
                                  (subst (under 1 (dot (var 1) (dot (var 0) (sh 2)))) t) =
                            subst (gen_sub_mvl 2) t.
intros. simpl. simpsub. simpl. auto. Qed.


(*Lemma test2:
  @subst False (dot (var 0) (sh 2)) (ppair (var 0)
                                    (var 1)
                             ) = subst sh1 (ppair (var 0)
                                    (var 1)
                                           ).
  simpsub. simpl.*)

Lemma substctx_eqsub :
  forall (s: @sub False) s' t,
    eqsub s s'
    -> substctx s t = substctx s' t. Admitted.

(*Lemma test1: forall (t: term False), subst (dot (var 1) (dot (var 0) (sh 2)))
                       (subst (under 1 (dot (var 1) (dot (var 0) (sh 2)))) t) =
                            t.
  intros. simpsub. ring.*)

(*start here*)
(*IDEA: do the move when there's only one variable to move: before 72*)



Lemma substctx_app: forall G1 G2 s,
    @substctx False s (G1 ++ G2) = (substctx (under (size G2) s) G1) ++ (substctx s G2).
  intros. induction G1; simpsub. repeat rewrite cat0s. auto.
  simpl. simpsub. repeat rewrite plusE.
  replace ((length G1) + (size G2)) with (size (G1 ++ G2)).
  rewrite - IHG1. auto.
  rewrite size_cat. auto. Qed.

Lemma substctx_rcons: forall G1 g s,
    @substctx False s (rcons G1 g) = rcons (substctx (under 1 s) G1) (substh s g).
  intros. repeat rewrite - cats1. rewrite substctx_app. simpl. auto. Qed.


(*induction G; simpsub. auto.
  simpl. move: IHG. simpsub. move => IHG. simpl. auto.
  rewrite IHG.
  suffices: (@eqsub False (dot (var 0) (sh 2)) sh1).
  move/(eqsub_under _ (length G)) => Heqsub.
  rewrite (substh_eqsub _ _ _ _ Heqsub). auto.
  intros b c. induction b; simpsub.
  .
  rewrite - (sh_sum 1 1).*)


Lemma size_substctx :
  forall s G, size (@substctx False s G) = size G.
Proof.
  intros. move: (length_substctx False s G). apply.
Qed.

Lemma move_var_r: forall E v G D m m' a,
    tr ((substctx (gen_sub_mvr (size G)) E) ++ (substctx (sh1) G) ++ v::D) (deq m m'
                                         (subst (under (size E) (gen_sub_mvr (size G))) a)
                                                               ) ->
    tr (E ++ ((substh (sh (size G)) v):: (G ++ D))) (deq (subst (under (size E) (gen_sub_mvl (size G))) m)
                               (subst (under (size E) (gen_sub_mvl (size G))) m')
                               a).
  move => E v G. move: E v. induction G using last_ind; intros. move: X.
  simpl. unfold gen_sub_mvl. simpl. unfold sh1. simpsub. auto.
  (*suffices: @ eqsub False id (dot (var 0) sh1). move => Heq. remember Heq as Heq1.
  clear HeqHeq1. move/eqsub_under : Heq1 => Heq1.
  rewrite - !(subst_eqsub _ _ _ _ (Heq1 (size E))) - !(substctx_eqsub _ _ _ Heq). simpsub. auto. *)
  - rewrite size_rcons. simpl. rewrite !compose_under !subst_compose.
    rewrite - 1!(addn1 (size G)). rewrite - shh_sum.
    rewrite cat_rcons.
    eapply IHG.
    rewrite catA. rewrite under_sum. rewrite !plusE.
    replace (size E + size G) with
        (size (substctx (gen_sub_mvr (size G)) E ++ substctx sh1 G)).
    apply tr_exchange.
    rewrite substctx_app.
    repeat rewrite size_substctx. rewrite - substctx_compose.
    replace (substctx
        (compose (gen_sub_mvr (size G))
           (under (size G)
                  (dot (var 1) (dot (var 0) (sh 2))))) E) with
        (substctx (gen_sub_mvr (size (rcons G x))) E).
    rewrite substctx_mvr.
    suffices: (((substctx (gen_sub_mvr (size (rcons G x))) E) ++
      substctx (under 1 sh1) G) ++
                                [:: substh sh1 x, v & D])%list=
((substctx (gen_sub_mvr (size (rcons G x))) E) ++
                                                   (rcons (substctx (under 1 sh1) G) (substh sh1 x)) ++ [:: v & D]).
    move => Heq. rewrite Heq. rewrite - (cats1 _ (substh sh1 x)).
    replace (substctx (under 1 sh1) G ++ [:: substh sh1 x]) with
        (substctx sh1 (rcons G x)).
    replace 
       (subst
          (under
             (length
                (substctx
                   (gen_sub_mvr
                      (size G)) E ++
                 substctx sh1 G))
             (dot (var 1)
                (dot (var 0) (sh 2))))
          (subst
             (under (size E)
                (gen_sub_mvr
                   (size G))) a))
 with
           (subst
              (under (size E)
                     (gen_sub_mvr (size (rcons G x)))) a). apply X.
    rewrite size_rcons. simpl. rewrite List.app_length.
    repeat rewrite length_substctx.
    rewrite compose_under. rewrite under_sum.
    rewrite - subst_compose. auto.
    rewrite - cats1. rewrite substctx_app. simpl. auto.
    rewrite - (cats1 _ (substh sh1 x)).
    rewrite - catA. rewrite (cat1s _ (v::D)). auto.
    rewrite catA. auto.
    rewrite size_rcons. auto.
    rewrite size_cat. repeat rewrite size_substctx. auto.
Qed.

Fixpoint gen_sub_mvl_list g v :=
  match v with
    0 => id
          | S v' => compose (gen_sub_mvl_list g v') (under v' (gen_sub_mvl g)) end.

Fixpoint gen_sub_mvr_list g v :=
  match v with
    0 => id
          | S v' => compose (under v' (gen_sub_mvr g )) (gen_sub_mvr_list g v') end.

Fixpoint gen_sub_mvr_ctx g v :=
  match v with
    0 => id
          | S v' => compose (gen_sub_mvr g ) (gen_sub_mvr_ctx g v') end.

(*prove this
 try and implement it practically with trans
Lemma move_var_r: forall E v G D m m' a,
    tr ((substctx (gen_sub_mvr (size G)) E) ++ (substctx (sh1) G) ++ v::D) (deq m m'
                                         (subst (under (size E) (gen_sub_mvr (size G))) a)
                                                               )
    -> tr (E ++ ((substh (sh (size G)) v):: (G ++ D))) (deq (subst (under (size E) (gen_sub_mvl (size G))) m)
                               (subst (under (size E) (gen_sub_mvl (size G))) m')
                               a).*)
(*looks a lot like substctx_mvr*)
Lemma eqsub_project : forall s s',
  (forall i,
      project s i = project s' i) ->
    @eqsub False s s'
.
  Admitted. 


(*Lemma aa: forall g,
    project (gen_sub_mvr g) 0 = (var 0).
  intros. induction g; simpl; simpsub. auto.
  rewrite IHg. simpsub.
  suffices:  g = 0.
  intros. subst. simpsub.
works for g > 1
*)

Lemma mvr_works_n0_lt: forall (g i: nat), (i < g ->
                                 project (gen_sub_mvr g) (S i) = (var i)).
  intros.
  move: (mvr_works_nz g i) => [one two]. apply one. assumption. Qed.

Lemma mvr_works_n0_gt: forall (g i: nat), ((i >= g) -> project (gen_sub_mvr g) (S i) = (var (S i))).
  intros.
  move: (mvr_works_nz g i) => [one two]. apply two. assumption. Qed.



  Lemma mvr_shift_help: forall g,
    eqsub (compose (compose (under 1 (sh g))
                           (gen_sub_mvr g)) (sh1))
(compose (under 1 (sh (g + 1)))
                           (gen_sub_mvr (g + 1))). 
  intros. induction g.
  simpl. simpsub. simpl. apply eqsub_refl.
  apply eqsub_project.
  intros. simpsub. rewrite plusE.
induction i. simpl. simpsub.
  simpl.
  Opaque compose.
  simpl. rewrite - addnE. simpl.
  simpl in IHg. rewrite addnC in IHg. simpl in IHg.
  repeat rewrite mvr_works0. simpsub.
  repeat rewrite project_under_eq. simpsub.
  rewrite plusE.
replace (1 + (g + 1)) with (g + 1 + 1). auto.
ring.
simpsub. rewrite plusE. Opaque addn.
replace (g.+1 + 1 + i) with ((g+1 +i).+1).
replace (g.+1 + 1 + 1 + i) with ((g+1 + 1 +i).+1).
repeat rewrite mvr_works_n0_gt. simpsub. apply succ_inj.
(g.+1) (g.+1 + 1 + i)).
simpl.

  rewrite - ! (addn1 g). 
  rewrite (addnC g 1). simpl.
  rewrite - IHg.
  Transparent compose. simpsub. simpl.
  rewrite - addnE. 
  simpsub. rewrite plusE. rewrite - addnE.
  rewrite addnC. simpl. simpsub.

Lemma mvr_shift : forall g,
    eqsub (compose (under 1 (sh g))
                   (gen_sub_mvr g)) (sh g).
  induction g.
  simpsub. simpl. simpsub. apply (eqsub_symm _ _ _
                                             (@eqsub_expand_id False)).

  rewrite - {1 3}(addn1 g). simpsub.
  simpl. rewrite plusE.
  replace (g + 1 + 1) with (g + 2). simpsub.
  rewrite - trunc_sum. simpsub.
  replace (g + 1) with (1 + g).
  rewrite - sh_sum. simpsub.

  intros n t. simpsub. rewrite plusE.


  simpl.

  intros. induction g. simpsub.
  Transparent gen_sub_mvr.
  rewrite - {1 3}(addn1 g).
  simpl. simpsub.
  apply (eqsub_symm _ _ _ (@eqsub_expand_sh False 1)).


Lemma move_list_r: forall E V G D m m' a,
    tr ((substctx (gen_sub_mvr_ctx (size G) (size V)) E) ++
        (substctx (sh (size V)) G) ++ V ++ D) (deq m m'
                                         (subst (gen_sub_mvr_list (size G) (size V)) a)
                                                               )
    -> tr (E ++ (substctx (sh (size G)) V)++ G ++ D)
         (deq
            (subst (under (size E) (gen_sub_mvl_list (size G) (size V))) m)
            (subst (under (size E)  (gen_sub_mvl_list (size G) (size V))) m')
                               a).
  intros. move: m m' a G D E X. induction V using last_ind; intros; move: X; simpl; simpsub.
 apply.
  repeat rewrite size_rcons. simpl.
  move => X. rewrite substctx_rcons.
replace 
    (E ++
     rcons (substctx (under 1 (sh (size G))) V)
       (substh (sh (size G)) x) ++ 
       G ++ D) with
    ((E ++ (substctx (under 1 (sh (size G))) V)) ++
       (substh (sh (size G)) x::
               (G ++ D))).
rewrite !compose_under !under_sum !subst_compose !plusE. 
replace (size E + size V) with
    (size (E ++
substctx (under 1 (sh (size G))) V
    )). apply move_var_r.
rewrite substctx_app.


  rewrite - cats1.
replace 

  rewrite catA.
  rewrite 
  simpl in X. simpsub in X.

  unfold gen_sub_mvl_list. simpl.

Arguments compose _ s1 s2: simpl nomatch.

Lemma testing1: (dot (var 0) (dot (var 1) (sh 6)) ) =
                under 1 (dot (var 0) (sh 5)).

Lemma testing :
   (dot (var 0)
                               (compose (sh 4)
                                  (compose
                                     (gen_sub_mvl (4 + (*here*) 2))
                                     (dot 
                                        (var 1)
                                        (dot 
                                         (var 2)
                                         (dot 
                                         (var 3)
                                         (dot 
                                         (var 4)
                                         (dot
                                         (subst
                                         (sh
                                         ((1+ 2(*here*))%coq_nat +
                                         1)%coq_nat.+4) (nattp))
                                         (sh 6))))))))) = id.
 Transparent gen_sub_mvl. simpl.
simpsub. simpl. simpsub. simpl.

Theorem one: forall G D e T ebar w1 l1,
    of_m G e T -> tr D (oof (ppair w1 l1) world) ->
    trans G e ebar -> 
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
assert (size
         [:: hyp_tm (store (ppair (var 2) (var 1))),
      hyp_tm
        (subseq
           (ppair (subst (sh (size G + 2)) w1)
              (subst (sh (size G + 2)) l1))
           (ppair (var 1) (var 0))),
     hyp_tm nattp, hyp_tm preworld & gamma_at G w1 l1]
= (4 + size G)
       ) as Hsize. intros. repeat rewrite size_cons. rewrite size_gamma_at. auto.
     remember (size ([:: hyp_tm nattp,
        hyp_tm preworld
        & gamma_at G w1 l1])) as sizel.
    assert (sizel = (2 + size G )) as Hsizel. subst.
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
(*assert (tr
    [:: hyp_tm nattp, hyp_tm preworld, hyp_tm nattp
      & gamma_at G w1 l1 ++ D]
    (oof (ppair (subst (sh (3 + (size G))) w1) (var 2)) world)) as Hwv2.
    apply world_pair. 
    (*rewrite subst_sh_shift. subst.
    repeat rewrite - Hseq.*)
    rewrite - {2}(subst_pw (sh (3 + size G))).
    repeat rewrite subst_sh_shift. repeat rewrite plusE.
    repeat rewrite - Hsizel.
    repeat rewrite - cat_cons. subst.
    apply tr_weakening_append; auto.
eapply split_world1. apply Dw.
      rewrite - (subst_nat (sh 3)).
      apply tr_hyp_tm; repeat constructor.*)
    (*actual proof*)
    suffices: hygiene (ctxpred (gamma_at G w1 l1 ++ D)) (trans_type (shift (size G) w1)
                                                          (shift (size G) l1) (comp_m B)) /\
              hygiene (ctxpred (gamma_at G w1 l1 ++ D)) (app ebar (shift (size G) l1)).
    move => [Hh1 Hh2].
    suffices: equiv 
       (trans_type (shift (size G) w1) 
          (shift (size G) l1) (comp_m B))
       (trans_type (shift (size G) w1) 
                   (shift (size G) l1) (comp_m B)). move => Hequivt. simpl in Hequivt.
    (*start here NEED A CONTEXT IN THE TRANS RELATION STAT
     to fix G problem below
     translation IS dependent on context for SURE cuz sometimes
     you have move gamma*)
    inversion Dtrans; subst.
    Opaque gen_sub_mvl gen_sub_mvr.
    simpl.
    suffices: (equiv 
       (app
          (lam
             (lam
                (lam
                   (lam
                      (make_bind
                         (app
                            (app
                               (app
                                  (app 
                                     (shift 4 Et1) 
                                     (var 3)) 
                                  (var 2)) 
                               (var 1)) 
                            (var 0))
                         (lam
                            (make_bind
                                  (app
                                  (app
                                     (app
                                        (app
                                           (subst
                                           (gen_sub_mvl
                                           (4 + size G))
                                           (subst 
                                           (sh 4)
                                           (lam
                                           (move_gamma G
                                           make_subseq 1
                                           (app Et2 (var (size G)))))))
                                           (picomp4 (var 0)))
                                        (picomp1 (var 0)))
                                     make_subseq) 
                                  (picomp3 (var 0)))
                               (lam
                                  (ret_t
                                     (ppair (picomp1 (var 0))
                                        (ppair make_subseq
                                           (ppair (picomp3 (var 0)) (picomp4 (var 0))))))))))))))
          (shift (size G) l1))
          (subst1 (subst (sh (size G)) l1)
             (lam
                (lam
                   (lam
                      (make_bind
                         (app
                            (app
                               (app (app (subst (sh 4) Et1) (var 3))
                                  (var 2)) (var 1)) 
                            (var 0))
                         (lam
                            (make_bind
                                  (app
                                  (app
                                     (app
                                        (app
                                           (subst
                                           (gen_sub_mvl
                                           (4 + size G))
                                           (subst 
                                           (sh 4)
                                           (lam
                                           (move_gamma G
                                           make_subseq 1
                                           (app Et2 (var (size G)))))))
                                           (picomp4 (var 0)))
                                        (picomp1 (var 0)))
                                     make_subseq) 
                                  (picomp3 (var 0)))
                               (lam
                                  (ret_t
                                     (ppair (picomp1 (var 0))
                                        (ppair make_subseq (ppair (picomp3 (var 0)) (picomp4 (var 0))))))))))))))).
    move => Hequiv.
apply (tr_compute _ _ _ _ _ _ _ Hh1 Hh2 Hh2 Hequivt Hequiv Hequiv); try assumption.
(*get the substitutions nice before i split
 things up*)
simpsub. simpl.
repeat rewrite - subst_sh_shift. simpsub_big.
rewrite subst_trans_type. simpl.
    repeat rewrite plusE. rewrite - trunc_sum. simpsub. simpl.
    rewrite trunc_sh.
(*put the arith assert in here if you need it*) 
     apply tr_all_intro.
    apply pw_kind.
    simpsub_big. simpl.
    apply tr_pi_intro.  apply nat_type. 
    apply tr_arrow_intro.
    eapply tr_formation_weaken. 
    apply subseq_U0. (*to show subseqs
                        are the same type,
 need to show that the variables are both of type world*)
   + repeat rewrite plusE.
     rewrite - hseq2. rewrite catA.
     rewrite - addn2.
      rewrite - subst_ppair.
      rewrite - (subst_world (sh (2 + size G))).
  repeat rewrite subst_sh_shift.
      repeat rewrite addnC - Hsizel.
      eapply tr_weakening_append; try apply Du; try reflexivity; auto. 
  + apply uworld10.
  +
    eapply tr_formation_weaken.
    eapply compm1_type. apply uworld10.
    apply trans_type_works. apply uworld10. 
  (*back to main proof*)
-  simpsub_big. simpl.
  apply tr_arrow_intro.
  + 
    eapply tr_formation_weaken. 
    apply store_type.  apply uworld21.
    assert (@ppair False (var 4) (var 3) = subst (sh 2) (ppair (var 2) (var 1))) as Hppair. simpsub. auto. rewrite Hppair. eapply tr_formation_weaken.
  apply compm2_type. apply uworld21. rewrite subst_trans_type. apply trans_type_works. auto.
simpsub. auto.
    rewrite subst_bind. simpsub_big. simpl. rewrite subst_trans_type.
    repeat rewrite plusE. rewrite - trunc_sum. simpsub. simpl.
    rewrite trunc_sh.
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
  rewrite - (subst_nat (sh 3)). var_solv.
  eapply tr_formation_weaken.
  assert (@ppair False (var 5) (var 4) = subst (sh 2) (ppair (var 3) (var 2))) as Hppair. simpsub. auto. rewrite Hppair.
  apply compm2_type. apply uworld32. apply trans_type_works.
  apply uworld10.
  (*Et1 nonsense
   *)
apply (tr_arrow_elim _
          (subseq
             (ppair
                (subst (sh (4 + size G)) w1)
                (subst (sh (4 + size G)) l1))
 (ppair (var 3) (var 2)))).
eapply tr_formation_weaken. apply subseq_U0.
rewrite - hseq4.
do 2! rewrite - (sh_sum _ 4).
apply wworld4. erewrite <- size_gamma_at. apply wworld_app; assumption.
apply uworld32.
eapply tr_formation_weaken; apply compm1_type. apply uworld32.
apply trans_type_works. auto.
assert (
       (arrow
          (subseq (ppair (subst (sh (4 + size G)) w1)
                         (subst (sh (4 + size G)) l1))
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
          (subseq (ppair (subst (sh (5 + size G)) w1)
                         (subst (sh (5 + size G)) l1))
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
                         (trans_type (var 1) (var 0) A)))))))) as Hsub.
simpsub. unfold subst1; simpsub1. simpsub_big.
(*ask karl arrow subseq*) simpl. unfold subst1. simpsub1.
rewrite subst_trans_type.
rewrite addnC. auto. simpsub. rewrite - (addn4 (size G)).
auto. simpsub. auto.
rewrite Hsub.
eapply (tr_pi_elim _ nattp).
    assert(   (pi nattp
          (arrow
             (subseq
                (ppair (subst (sh (5 + size G)) w1)
                       (subst (sh (5 + size G)) l1))
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
                            (trans_type (var 1) (var 0) A)))))))) =
subst1 (var 3) (pi nattp
          (arrow
             (subseq
                (ppair (subst (sh (6 + size G)) w1)
                       (subst (sh (6 + size G)) l1))
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
                            (trans_type (var 1) (var 0) A))))))))
       )
           as Hsub2.
    simpsub_big. simpl. rewrite - (addn4 (size G)) - (addn1 (size G + 4)).
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
apply wworld6. erewrite <- size_gamma_at. apply wworld_app. assumption.
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
   replace 
       (make_bind
          (app
             (app
                (app
                   (app
                      (lam
                         (subst
                            (dot (var 0) (sh 6))
                            (move_gamma G
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
                               
                            (move_gamma G
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
 - eapply tr_formation_weaken; eapply store_type.
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
