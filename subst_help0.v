From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src basic_types help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*Trivial lemmas to simplify substitutions*)
Lemma fold_subst1:  forall m1 m2, (@subst False (dot m1 id) m2) = subst1 m1 m2.
intros. auto. Qed.

Lemma subst_pw: forall s,
    subst s preworld = preworld.
intros. unfold preworld. unfold nattp. auto. Qed.
Hint Rewrite subst_pw.

Lemma subst_U0: forall s,
    (@subst False s (univ nzero)) = univ nzero.
  auto. Qed.

(*Opaque store.*)

Lemma subst_store: forall W s, subst s (store W) = store (subst s W).
  intros. unfold store. auto. Qed.

Lemma subst_ltb: forall s m n, subst s (ltb m n) = ltb (subst s m) (subst s n).
  intros. auto. Qed.

Lemma subst_world: forall s,
    subst s world = world.
intros. unfold world. unfold preworld. unfold nattp. auto. Qed.  
Hint Rewrite subst_world.

Lemma subst_nat: forall s,
    @subst False s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat.

Lemma subst_nzero: forall s,
    @subst False s nzero = nzero.
  intros. unfold nzero. auto. Qed.
Hint Rewrite subst_nzero.

Lemma subst_leqtp: forall s,
    @subst False s (leqtp) = leqtp.
  intros. unfold leqtp. unfold wind. unfold theta.
  repeat rewrite subst_app.
  repeat rewrite subst_lam. simpsub. simpl.
  repeat rewrite project_dot_succ.
  rewrite project_dot_zero. auto. Qed.
Hint Rewrite subst_leqtp.

Lemma subst_bind: forall s m1 m2,
    @subst False s (make_bind m1 m2) = make_bind (@subst False s m1) (@subst False s m2).
  intros. auto. Qed.


Lemma subst_lttp: forall s,
    @subst False s (lttp) = lttp.
  intros. unfold lttp.
  simpsub. rewrite subst_leqtp. unfold nsucc. simpsub. simpl.
  rewrite subst_leqtp. auto. Qed.
Hint Rewrite subst_leqtp.

Lemma subst_leq: forall s n1 n2,
    @subst False s (leq_t n1 n2) =  leq_t (subst s n1) (subst s n2).
  intros. unfold leq_t.  repeat rewrite subst_app. auto. 
Qed.

Lemma subst_lt: forall s n1 n2,
    subst s (lt_t n1 n2) = lt_t (subst s n1) (@subst False s n2).
  intros. repeat rewrite subst_app. rewrite subst_lttp. auto. Qed. 

Lemma subst_subseq: forall W1 W2 s,
       (subst s
              (subseq W1 W2)) = subseq (subst s W1)
                                       (subst s W2).
  intros. unfold subseq. repeat rewrite subst_app. auto.
Qed.


Lemma subst_ret: forall s, subst s ret = ret.
  intros. unfold ret. unfold inl. simpsub. auto. Qed.

Lemma subst_ret_a: forall s m, subst s (ret_a m) = ret_a (subst s m).
  intros. unfold ret_a. unfold ret. unfold inl. simpsub. auto. Qed.

Lemma subst_laters: forall s A, (subst s (laters A)) = (laters (subst s A)).
  intros. unfold laters. unfold plus. rewrite subst_rec. rewrite subst_sigma.
  rewrite subst_booltp. rewrite subst_bite. simpsub. simpl.
  repeat rewrite <- subst_sh_shift. simpsub. auto. Qed.

Lemma subst_nth: forall s m1 m2, (subst s (nth m1 m2)) = (nth (subst s m1) (subst s m2)). intros. unfold nth. simpsub. auto. Qed.

Lemma subst_make_subseq: forall s, (subst s make_subseq) = make_subseq.
  intros. unfold make_subseq. simpsub. auto. Qed.

Lemma subst_picomp1: forall s m, (subst s (picomp1 m)) = picomp1 (subst s m).
  intros. unfold picomp1. simpsub. auto. Qed.

Lemma subst_picomp2: forall s m, (subst s (picomp2 m)) = picomp2 (subst s m).
  intros. unfold picomp2. simpsub. auto. Qed.

Lemma subst_picomp3: forall s m, (subst s (picomp3 m)) = picomp3 (subst s m).
  intros. unfold picomp3. simpsub. auto. Qed.

Lemma subst_picomp4: forall s m, (subst s (picomp4 m)) = picomp4 (subst s m).
  intros. unfold picomp4. simpsub. auto. Qed.

Hint Rewrite subst_U0 subst_ret subst_ret_a subst_subseq subst_leq subst_leqtp
     subst_lttp subst_lt subst_nzero subst_nat subst_world subst_pw
  subst_world subst_nth subst_store subst_laters subst_picomp1 subst_picomp2 subst_picomp4 subst_picomp3 subst_make_subseq: subst1.

Hint Rewrite <- subst_sh_shift: subst1.

Hint Unfold subst1: subst1.

Ltac simpsub1 :=
autounfold with subst1;
  autorewrite with subst1.
