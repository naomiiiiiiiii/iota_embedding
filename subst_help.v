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

