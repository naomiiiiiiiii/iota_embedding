From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src basic_types help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Ltac simpsub1 :=
autounfold with subst1; autorewrite with subst1.

Ltac simpsubin1 H :=
autounfold with subst1 in H; autorewrite with subst1 in H.

Ltac simpsub_big := repeat (simpsub; simpsub1).

Ltac simpsubin_big H := repeat (simpsubin H; simpsubin1 H).

Ltac sh_var_help sh_amt cap var_num := match (eval compute in (leq var_num cap)) with
                          true => let var_shed := eval compute in (var_num - sh_amt) in
                                   (change (@ var obj var_num) with (shift sh_amt (@ var obj var_shed)));
                                                               sh_var_help sh_amt cap var_num.+1
                        | false => auto
                          (*change (@ var obj 9) with
                              (shift sh_amt (@ var obj 6))*)

                                       end.
(*sh_var amt cap rewrites (Var i) as (shift sh_amt (var (i - sh_amt)))
 for any i <= cap*)
Ltac sh_var sh_amt cap := sh_var_help sh_amt cap sh_amt.

Ltac simpsub_bigs := simpsub_big; simpl.
Ltac simpsubin_bigs H := simpsubin_big H; simpl.
Ltac simpsubss H := simpsubin H; simpl.

Ltac weaken H := eapply tr_formation_weaken; apply H.

Ltac var_nf_help cap var_num := match (eval compute in (leq var_num cap)) with
                          true => (change (@ var obj var_num) with (subst (sh var_num) (@ var obj 0)));
                                                              var_nf_help cap var_num.+1
                        | false => auto
                          (*change (@ var obj 9) with
                              (shift sh_amt (@ var obj 6))*)

                                       end.
(*change var n to sh n var 0 for n <= cap *)
Ltac var_nf cap := var_nf_help cap 1.


(*Trivial lemmas to simplify substitutions*)
Lemma fold_subst1:  forall m1 m2, (@ subst obj (dot m1 id) m2) = subst1 m1 m2.
intros. auto. Qed.

Lemma subst_pw: forall s,
    subst s preworld = preworld.
intros. unfold preworld. unfold nattp. auto. Qed.
Hint Rewrite subst_pw : core subst1.

Lemma subst_U0: forall s,
    (@ subst obj s (univ nzero)) = univ nzero.
  auto. Qed.



Lemma subst_theta s : @ subst obj s theta = theta. 
  unfold theta. simpsub. auto. Qed.
Hint Rewrite subst_theta: core subst1.

Lemma subst_minus s: subst s minus = minus.
  auto. Qed.
Hint Rewrite subst_minus: core subst1.

Lemma subst_ltb s : subst s lt_b = lt_b.
  intros. unfold lt_b. simpsub. auto. Qed.
Hint Rewrite subst_ltb: core subst1.

Lemma subst_world: forall s,
    subst s world = world.
intros. unfold world. unfold preworld. unfold nattp. auto. Qed.  
Hint Rewrite subst_world: core subst1.

Lemma subst_nat: forall s,
    @ subst obj s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat: core subst1.

Lemma subst_nzero: forall s,
    @ subst obj s nzero = nzero.
  intros. unfold nzero. auto. Qed.
Hint Rewrite subst_nzero: core subst1.

Lemma subst_leqtp: forall s,
    @ subst obj s (leqtp) = leqtp.
  intros. unfold leqtp. unfold wind. unfold theta.
  repeat rewrite subst_app.
  repeat rewrite subst_lam. simpsub. simpl.
  repeat rewrite project_dot_succ.
  rewrite project_dot_zero. auto. Qed.
Hint Rewrite subst_leqtp: core subst1.

Lemma subst_bind: forall s m1 m2,
    @ subst obj s (make_bind m1 m2) = make_bind (@ subst obj s m1) (@ subst obj s m2).
  intros. auto. Qed.


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

Hint Rewrite subst_U0 subst_ret subst_ret_a subst_subseq subst_leq subst_leq
     subst_lttp subst_lt subst_nzero subst_nat subst_world subst_pw subst_world
     subst_nth subst_laters subst_picomp1 subst_picomp2 subst_picomp4
     subst_picomp3 subst_make_subseq subst_theta subst_minus subst_ltb: core subst1.

Hint Rewrite <- subst_sh_shift: core subst1.

Hint Unfold subst1: subst1.


Lemma subst_store: forall w l s, subst s (store w l) = store (subst s w) (subst s l).
  intros. unfold store. unfold gettype. simpsub_big. auto. Qed.

Hint Rewrite subst_store: core subst1.


Lemma subst_nsucc s n : (subst s (nsucc n)) = @ nsucc obj (subst s n).
  unfold nsucc. simpsub. auto. Qed.

Lemma subst_moveapp s A m1 m2 : (subst s (move_app A m1 m2)) =
                              move_app A (subst s m1) (subst s m2).
   unfold move_app. simpsub_big. auto. Qed.

Hint Rewrite subst_nsucc subst_moveapp: core subst1.

Lemma subst_eqb s : subst s eq_b = eq_b.
  intros. unfold eq_b. simpsub. auto. Qed.
Hint Rewrite subst_eqb: core subst1.

Lemma subst_inr: forall s t, subst s (inr t)  = inr (subst s t).
  intros. unfold inr. simpsub. auto. Qed.

Lemma subst_inl: forall s t, subst s (inl t)  = inl (subst s t).
  intros. unfold inl. simpsub. auto. Qed.

Lemma subst_plus: forall s A B, subst s (plus A B) =
                           plus (subst s A) (subst s B).
  intros. unfold plus. simpsub_bigs. auto.
  Qed.
  Hint Rewrite subst_inl subst_inr subst_plus: core subst1.
