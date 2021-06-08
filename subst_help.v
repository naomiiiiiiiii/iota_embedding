From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src help subst_help0.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.


Lemma eqsub_project : forall s s',
  (forall i,
      subst s (var i) = subst s' (var i)) ->
    @eqsub False s s'
.
  Admitted. 

Lemma size_substctx :
  forall s G, size (@substctx False s G) = size G.
Proof.
  intros. move: (length_substctx False s G). apply.
Qed.

Hint Rewrite size_substctx.

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

Lemma substctx_eqsub {s s': @sub False} {G: context}
: eqsub s s'
    -> substctx s G = substctx s' G. Admitted.

Ltac simpsub_big := repeat (simpsub; simpsub1).
Lemma project_dot_geq :
  forall t s i, i > 0 ->
           project (dot t s) i = @project False s (i - 1).
  Admitted.

Lemma sh_sum :
  forall m n t,
    @subst False (sh n) (subst (sh m) t) = @subst False (sh (n+m)) t.
  intros. repeat rewrite subst_sh_shift.
  rewrite shift_sum. auto. Qed.

Lemma shh_sum :
  forall m n t,
    @substh False (sh n) (substh (sh m) t) = @substh False (sh (n+m)) t.
Admitted.

(*substitutions for moving variables around in context*)
(*move old to new*)
Fixpoint gen_sub_mvl G := match G with
                        0 => id
                          | n'.+1 =>
@compose False (under n' (dot (var 1) (dot (var 0) (sh 2)))) (gen_sub_mvl n')
                                    end.

(*move new to old*)
Fixpoint gen_sub_mvr E := match E with
                        0 => id
    | n'.+1 => @compose False (gen_sub_mvr n')
(under n' (dot (var 1) (dot (var 0) (sh 2))))
                          end.

Fixpoint gen_sub_mvl_list g v :=
  match v with
    0 => id
          | S v' => compose (gen_sub_mvl_list g v') (under v' (gen_sub_mvl g)) end.

Fixpoint gen_sub_mvr_list g v :=
  match v with
    0 => id
          | S v' => compose (under v' (gen_sub_mvr g )) (gen_sub_mvr_list g v') end.

Lemma mvr_works0: forall (g: nat), project (gen_sub_mvr g) 0 = (var g).
  intros. induction g; simpl.
  simpsub. auto.
  simpsub. rewrite IHg. simpsub.
  destruct (0 == g) eqn: Hbool. move/ eqP : Hbool => Hbool; subst. 
  simpsub.  auto.
rewrite project_under_eq. simpsub. rewrite plusE. rewrite addn1. auto.
Qed.


Lemma mvr_works_nz: forall (g i: nat), (i < g ->
                                 project (gen_sub_mvr g) (S i) = (var i))
/\ ((i >= g) -> project (gen_sub_mvr g) (S i) = (var (S i))).
  move => g. induction g; simpl; intros; split; intros. discriminate H. 
  simpsub. auto.
  simpsub. move: (IHg i) => [IH1 IH2].
  destruct (i < g) eqn: Hbool.
  - rewrite IH1. rewrite subst_var. rewrite project_under_lt. auto.
    apply/ltP. rewrite Hbool; try constructor. constructor.
    suffices: i = g. intros. subst.
    rewrite IH2. rewrite subst_var. rewrite project_under_geq.
    rewrite minusE. replace (g.+1 - g) with 1.
    simpsub. rewrite plusE. rewrite addn0. auto.
    rewrite subSnn. auto. auto. auto.
apply anti_leq. apply/ andP. split.
rewrite - ltnS. assumption. rewrite leqNgt.
apply / negbT : Hbool.
  - simpsub. move: (IHg i) => [IH1 IH2]. rewrite IH2. simpsub. rewrite project_under_geq.
    rewrite - subst_var. rewrite minusE.
    replace
(subst (dot (var 1) (dot (var 0) (sh 2)))
       (varx False (i.+1 - g))) with (@var False (i.+1 - g)). simpsub. 
    rewrite plusE. simpl. rewrite subnKC. auto.
    apply ltnW in H.
    eapply (leq_trans H). auto. simpsub.
    rewrite project_dot_geq.
    replace (i.+1 - g - 1) with (i- g).
    rewrite project_dot_geq. simpsub.
    simpl. rewrite - 1! (addn2). simpl.
    replace (i.+1 - g) with (i - g - 1 + 2). auto.
    rewrite subn1. rewrite addn2. simpl. rewrite prednK.
    rewrite - addn1. rewrite addnBAC. rewrite addn1. auto.
    rewrite leq_eqVlt. apply/orP. right. assumption. rewrite subn_gt0.
    assumption. rewrite subn_gt0.
    assumption.
    replace (i.+1 - g - 1) with (i.+1 - (g.+1)).
    rewrite subSS. auto.
    rewrite subn1. rewrite subSKn. rewrite subSS. auto.
    rewrite subn_gt0. eapply (ltn_trans H). auto.
    apply/ leP. apply leqW. rewrite leq_eqVlt. apply/ orP. right. assumption.
rewrite leq_eqVlt. apply/ orP. right. assumption.
Qed.


Lemma substctx_mvr: forall G,
    (substctx (dot (var 1) (dot (var 0) (sh 2))) (substctx sh1 G)) =
    (@substctx False (under 1 sh1) G).
  intros. simpsub. auto. Qed.

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
repeat rewrite mvr_works_n0_gt. simpsub. rewrite plusE.
replace (1 + (g +1 + i).+1) with (g + 1 + 1 + i).+1. auto.
ring. repeat rewrite addn1. apply ltn_addr.
apply ltnSn. apply ltn_addr. rewrite addn1. apply ltnSn.
ring. ring.
Qed.


Lemma mvr_shift : forall g,
    eqsub (compose (under 1 (sh g))
                   (gen_sub_mvr g)) (sh g).
  induction g.
  simpsub. simpl. simpsub. apply (eqsub_symm _ _ _
                                             (@eqsub_expand_id False)).
Admitted.

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

(*tests*)
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

Lemma move_list_r: forall E V G D m m' a,
    tr ((substctx (gen_sub_mvr_list (size G) (size V)) E) ++
        (substctx (sh (size V)) G) ++ V ++ D) (deq m m'
                                                   (subst (under (size E)
                                                      (gen_sub_mvr_list (size G) (size V))) a)
                                                               ) (*need an under for a i think*)
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
rewrite - substctx_compose. rewrite (substctx_eqsub (mvr_shift (size G)) ).
replace (size G) with (size (substctx sh1 G)).
remember (substctx
        (under (size (substctx (under 1 (sh (size (substctx sh1 G)))) V))
           (gen_sub_mvr (size (substctx sh1 G)))) E) as E'. 
replace (size E) with (size E').
rewrite - catA.
apply IHV.
repeat rewrite size_substctx. subst.
simpsub. rewrite plusE.
repeat rewrite size_substctx.
replace 
       
       (subst
          (compose
             (under
                (size
                   (E ++
                    substctx (dot (var 0) (sh (size G + 1))) V))
                (gen_sub_mvr (size G)))
             (under (size E)
                (gen_sub_mvr_list (size G) (size V)))) a)
 with
           (subst
              (under (size E)
                 (compose
                    (under 
                       (size V)
                       (gen_sub_mvr
                        (size G)))
                    (gen_sub_mvr_list
                       (size G)
                       (size V)))) a).
replace 
    (substctx
       (compose (under (size V) (gen_sub_mvr (size G)))
          (gen_sub_mvr_list (size G) (size V))) E ++
       substctx (sh (1 + size V)) G ++ V ++ x :: D) with
        (substctx
           (compose (under (size V) (gen_sub_mvr (size G)))
              (gen_sub_mvr_list (size G) (size V))) E ++
         substctx (sh (size V).+1) G ++ rcons V x ++ D).
apply X.
rewrite - cats1. rewrite - (catA V [::x]). rewrite cat1s. auto.
rewrite size_cat. rewrite - under_sum. rewrite - compose_under.
rewrite size_substctx. auto. subst. 
rewrite size_substctx. auto.
rewrite size_substctx. auto.
rewrite size_cat size_substctx. auto.
rewrite - catA. rewrite cat_rcons. auto. Qed.
