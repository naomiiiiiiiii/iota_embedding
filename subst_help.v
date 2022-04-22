
From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src basic_types help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Lemma subst_world: forall s,
    subst s world = world.
intros. unfold world. unfold preworld. unfold nattp. auto. Qed.  
Hint Rewrite subst_world: core subst1.

Lemma subst_nat: forall s,
    @ subst obj s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat: core subst1.

Lemma subst_pw: forall s,
    subst s preworld = preworld.
intros. unfold preworld. unfold nattp. auto. Qed.
Hint Rewrite subst_pw : core subst1.

Lemma subst_U0: forall s,
    (@ subst obj s (univ nzero)) = univ nzero.
  auto. Qed.
Lemma subst_subseq: forall w1 w2 l1 l2 s,
       (subst s
              (subseq w1 l1 w2 l2)) = subseq (subst s w1)
                                             (subst s l1)
                                             (subst s w2)
                                             (subst s l2).
   intros. unfold subseq.
   unfold app3.
   simpsub_bigs.
   auto.
 Qed.

Lemma subst_laters: forall s A, (subst s (laters A)) = (laters (subst s A)).
  intros. unfold laters. unfold plus. rewrite subst_rec. rewrite subst_sigma.
  rewrite subst_booltp. rewrite subst_bite. simpsub. simpl.
  repeat rewrite <- subst_sh_shift. simpsub. auto. Qed.

Lemma subst_store: forall w l s, subst s (store w l) = store (subst s w) (subst s l).
  intros. unfold store. unfold gettype. simpsub_big. auto. Qed.

Hint Rewrite subst_store: core subst1.


 Lemma subst_move: forall A l1 l2 s, (subst s (move A l1 l2)) = move A (subst s l1) (subst s l2).
   intros. induction A; unfold make_subseq_trans;
unfold leq_trans_fn_app; unfold leq_trans_fn; simpsub_big; simpl; auto.
   { unfold make_subseq_trans;
unfold leq_trans_fn_app; unfold leq_trans_fn; simpsub_big; simpl; auto.
}
   { unfold make_subseq_trans;
unfold leq_trans_fn_app; unfold leq_trans_fn; simpsub_big; simpl; auto.
}
   { unfold make_subseq_trans;
       unfold lt_trans_fn_app; unfold leq_trans_fn_app;
         unfold leq_trans_fn; simpsub_big; simpl; auto.
}
 Qed.

Hint Rewrite subst_move: core subst1.

Lemma subst_moveapp s A l1 l2 m1 m2 : (subst s (move_app A l1 l2 m1 m2)) =
                              move_app A (subst s l1) (subst s l2) (subst s m1) (subst s m2).
   unfold move_app. simpsub_big. auto. Qed.

Lemma subst_consb w l x s: @ subst obj s (cons_b w l x) =
                           cons_b (subst s w) (subst s l) (subst s x).
  unfold cons_b. simpsub_big. auto.
Qed.

Hint Rewrite subst_consb : subst1 core.

Lemma subst_make_subseq_trans: forall s a b c d e, (subst s (make_subseq_trans a b c d e)) = (make_subseq_trans
                                                                                 (subst s a)
                                                                                 (subst s b)
                                                                                 (subst s c)
                                                                                 (subst s d)
                                                                                 (subst s e)
                                                                                        ).
  intros. unfold make_subseq_trans. unfold leq_trans_fn_app. unfold leq_trans_fn. simpsub. auto. Qed.

Hint Rewrite subst_make_subseq_trans: core subst1.
Hint Rewrite <- subst_make_subseq_trans : inv_subst.

Lemma subst_lttp: forall s,
    @ subst obj s (lttp) = lttp.
  intros. unfold lttp.
  simpsub. rewrite subst_leqtp. unfold nsucc. simpsub. simpl.
  rewrite subst_leqtp. auto. Qed.
Hint Rewrite subst_leqtp: core subst1.

Lemma subst_leq: forall s n1 n2,
    @ subst obj s (leq_t n1 n2) =  leq_t (subst s n1) (subst s n2).
  intros. unfold leq_t.  repeat rewrite subst_app. auto. 
Qed.

Lemma subst_lt: forall s n1 n2,
    subst s (lt_t n1 n2) = lt_t (subst s n1) (@ subst obj s n2).
  intros. repeat rewrite subst_app. rewrite subst_lttp. auto. Qed. 

Lemma subst_nth: forall s m1 m2, (subst s (nth m1 m2)) = (nth (subst s m1) (subst s m2)). intros. unfold nth. simpsub. auto. Qed.

Lemma subst_make_subseq: forall s, (subst s make_subseq) = make_subseq.
  intros. unfold make_subseq. simpsub. auto. Qed.

Hint Rewrite subst_subseq subst_leq subst_lttp subst_lt
     subst_pw subst_world subst_nth subst_laters subst_make_subseq subst_ltb
subst_moveapp
.
