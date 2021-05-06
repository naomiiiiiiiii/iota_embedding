Require Import Arith.
Require Import Omega.
Require Import Tactics.
Require Import tactics.
Require Export source.


(* Generic development: parameterized over Syntax:SYNTAX, where: *)


Module Type SYNTAX.

(* Renamed because an inductive type cannot instantiate a parameter. *)
Parameter termx : Set.
Parameter varx : nat -> termx.


Parameter traverse : forall S:Set, (S -> S) -> (S -> nat -> termx) -> S -> termx -> termx.

Axiom traverse_var :
  forall S enter resolve s i,
    traverse S enter resolve s (varx i) = resolve s i.

Axiom traverse_parametric :
  forall (S:Set) (S':Set) (R : S -> S' -> Prop) enter enter' resolve resolve' s s' t,
    (forall s s', R s s' -> R (enter s) (enter' s'))
    -> (forall s s' i, R s s' -> resolve s i = resolve' s' i)
    -> R s s'
    -> traverse S enter resolve s t = traverse S' enter' resolve' s' t.

Axiom traverse_id :
  forall (S:Set) (R : S -> Prop) enter resolve s t,
    (forall s, R s -> R (enter s))
    -> (forall s i, R s -> resolve s i = varx i)
    -> R s
    -> traverse S enter resolve s t = t.

Axiom traverse_compose :
  forall (S:Set) (S':Set) enter enter' resolve resolve' s s' t,
    traverse S enter resolve s (traverse S' enter' resolve' s' t)
    = traverse (S * S')
      (fun p => let (s, s') := p in (enter s, enter' s'))
      (fun p i => let (s, s') := p in traverse S enter resolve s (resolve' s' i))
      (s, s') t.

End SYNTAX.


(* Verify that Syntax satisfies SYNTAX. *)
Module TermCheck <: SYNTAX := source.

Goal source.termx = source.term.
Proof. auto. Qed.

Goal source.varx = source.var.
Proof. auto. Qed.


(* Hold Syntax.traverse mostly abstract in proofs.
   (This keeps Syntax.traverse from being unfolded under most
   circumstances, but unfortunately still allows it to be
   unfolded for conversion checks.)
*)
Opaque source.traverse.


Inductive sub : Set :=
| dot : term -> sub -> sub
| sh : nat -> sub.


Fixpoint trunc (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       (match s with
        | sh m => sh (m + n)
        | dot _ s' => trunc n' s'
        end)
   end).


Definition project (s : sub) (n : nat) : term :=
  (match trunc n s with
   | dot t _ => t
   | sh i => var i
   end).


Definition shift_var (n : nat) (i : nat) : term :=
  if lt_dec i n then
    var i
  else
    var (S i).


Definition shift_term (n : nat) (t : term) :=
  traverse nat S shift_var n t.


Fixpoint shift_sub (s : sub) {struct s} : sub :=
  (match s with
   | dot t s' =>
       dot (shift_term 0 t) (shift_sub s')
   | sh m =>
       sh (S m)
   end).


Definition subst : sub -> term -> term :=
  traverse sub (fun s' => dot (var 0) (shift_sub s')) project.


Definition id : sub := sh 0.
Definition sh1 : sub := sh 1.
Definition sh5 : sub := sh 5.
Definition subst1 (t : term) : term -> term := subst (dot t id).
Definition shift1 : term -> term := subst sh1.


(* Composition is written in digrammatic order. *)
Fixpoint compose (s1 : sub) (s2 : sub) {struct s1} : sub :=
  (match s1 with
   | dot t s1' => dot (subst s2 t) (compose s1' s2)
   | sh n => trunc n s2
   end).


Fixpoint under (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       dot (var 0) (shift_sub (under n' s))
   end).


Lemma subst_eq_traverse :
  forall s t,
    subst s t = traverse sub (under 1) project s t.
Proof.
auto.
Qed.


Lemma subst_var : forall s i,
  subst s (var i) = project s i.
Proof.
intros s i.
unfold subst.
apply traverse_var.
Qed.


(* Trunc *)

Definition trunc1 (s : sub) :=
  (match s with
   | dot _ s' => s'
   | sh n => sh (S n)
   end).


Lemma trunc_sh :
  forall m n,
    trunc m (sh n) = sh (m+n).
Proof.
intros m n.
destruct m; auto; [].
simpl.
f_equal; omega.
Qed.


Lemma trunc_succ_outer :
  forall n s,
    trunc (S n) s = trunc1 (trunc n s).
Proof.
intro n.
induct n.

(* 0 *)
intro s.
destruct s; auto; [].
simpl.
replace (n+1) with (S n); [reflexivity | omega].

(* S *)
intros n IH s.
destruct s; [|].
  (* dot *)
  replace (trunc (S (S n)) (dot t s)) with (trunc (S n) s) by reflexivity.
  replace (trunc (S n) (dot t s)) with (trunc n s) by reflexivity.
  apply IH; done.

  (* sh *)
  simpl.
  f_equal; omega.
Qed.


Lemma trunc_sum :
  forall m n s,
    trunc m (trunc n s) = trunc (m+n) s.
Proof.
intros m n s.
induct m.

(* Z *)
reflexivity.

(* S *)
intros m IH.
replace (S m + n) with (S (m + n)); [ | auto].
rewrite -> !trunc_succ_outer; [].
f_equal; auto; done.
Qed.


Lemma trunc_succ_inner :
  forall n s,
    trunc (S n) s = trunc n (trunc1 s).
Proof.
intros n s.
replace (S n) with (n+1); [| omega].
rewrite <- (trunc_sum n 1); [].
f_equal; [].
unfold trunc1.
destruct s; auto; [].
simpl.
f_equal; omega.
Qed.


Lemma trunc1_under :
  forall n s,
    n >= 1
    -> trunc1 (under n s) = shift_sub (under (n-1) s).
Proof.
intros n s H.
destruct n; [omega |].
simpl.
replace (n-0) with n by omega.
reflexivity.
Qed.


Lemma project_zero :
  forall t s,
    project (dot t s) 0 = t.
Proof.
auto.
Qed.


Lemma project_dot :
  forall t s i,
    project (dot t s) (S i) = project s i.
Proof.
intros t s i.
unfold project.
simpl.
reflexivity.
Qed.


Lemma project_sh :
  forall n i,
    project (sh n) i = var (n+i).
Proof.
intros n i.
unfold project.
rewrite -> trunc_sh; [].
f_equal; omega.
Qed.


(* Shift-var *)

Lemma shift_var_lt :
  forall n i,
    i < n -> shift_var n i = var i.
Proof.
intros n i H.
unfold shift_var.
destruct (lt_dec i n); auto; omega.
Qed.


Lemma shift_var_ge :
  forall n i,
    i >= n -> shift_var n i = var (S i).
Proof.
intros n i H.
unfold shift_var.
destruct (lt_dec i n); auto; omega.
Qed.


(* Shift-term *)

Fixpoint nshift_term (n : nat) (t : term) {struct n} : term :=
  (match n with
   | 0 => t
   | S n' => shift_term 0 (nshift_term n' t)
   end).


Lemma shift_term_var :
  forall n i,
    shift_term n (var i) = shift_var n i.
Proof.
intros n i.
apply traverse_var.
Qed.


Lemma nshift_term_var :
  forall n i,
    nshift_term n (var i) = var (n+i).
Proof.
intros n i.
induct n.

(* 0 *)
reflexivity.

(* S *)
intros n IH.
simpl.
rewrite -> IH; [].
rewrite -> shift_term_var; [].
unfold shift_var.
destruct (lt_dec (n+1) 0); [omega |].
reflexivity.
Qed.


Lemma nshift_term_sum :
  forall m n s,
    nshift_term m (nshift_term n s) = nshift_term (m+n) s.
Proof.
intros m n s.
induct m.

(* 0 *)
reflexivity.

(* S *)
intros m IH.
simpl.
rewrite -> IH.
reflexivity.
Qed.


Lemma nshift_term_succ_inner :
  forall n s,
    nshift_term (S n) s = nshift_term n (shift_term 0 s).
Proof.
intros n s.
replace (S n) with (n+1) by omega.
rewrite <- nshift_term_sum.
reflexivity.
Qed.


Lemma shift_term_commute :
  forall n t,
    shift_term (S n) (shift_term 0 t) = shift_term 0 (shift_term n t).
Proof.
intros n t.
unfold shift_term.
rewrite -> !traverse_compose; [].
apply (traverse_parametric (nat * nat) (nat * nat)
       (fun p p' => let (m, i) := p in
        let (i', m') := p' in
                         i = i' /\ m = i+1+n /\ m' = i+n)); auto; [|].

(* enter *)
intros (m, i) (i', m').
omega.

(* resolve *)
clear t.
intros (m, i) (i', m') j (H1 & H2 & H3).
subst i' m m'.
change (shift_term (i+1+n) (shift_var i j) = shift_term i (shift_var (i+n) j)).
unfold shift_var.
destruct (lt_dec j i); [|].
  (* j < i *)
  destruct (lt_dec j (i+n)); [| omega].
  rewrite -> !shift_term_var.
  rewrite -> !shift_var_lt by omega.
  reflexivity.

  (* j >= i *)
  destruct (lt_dec j (i+n)); [|].
    (* i <= j < i+n *)
    rewrite -> !shift_term_var; [].
    rewrite -> shift_var_lt by omega.
    rewrite -> shift_var_ge by omega.
    reflexivity.

    (* j >= i+n *)
    rewrite -> !shift_term_var.
    rewrite -> !shift_var_ge by omega.
    reflexivity.
Qed.


Lemma nshift_term_commute :
  forall m n t,
    m >= n
    -> shift_term m (nshift_term n t) = nshift_term n (shift_term (m-n) t).
Proof.
intros m n.
revert m.
induct n.

(* Z *)
intros m t H.
replace (m-0) with m by omega.
reflexivity.

(* S *)
intros n IH m t H.
simpl.
replace m with (S (m-1)) by omega.
rewrite -> shift_term_commute.
f_equal; [].
rewrite -> (IH (m-1)) by omega.
auto; done.
Qed.


Lemma nshift_term_commute_eq :
  forall n t,
    shift_term n (nshift_term n t) = nshift_term (S n) t.
Proof.
intros n t.
rewrite -> nshift_term_succ_inner.
replace 0 with (n-n) by omega.
apply nshift_term_commute; [].
omega.
Qed.


(* Shift-sub *)

Fixpoint nshift_sub (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' => shift_sub (nshift_sub n' s)
   end).


Lemma nshift_sub_dot :
  forall n t s,
    nshift_sub n (dot t s) = dot (nshift_term n t) (nshift_sub n s).
Proof.
intros n t s.
induct n.

(* Z *)
auto; done.

(* S *)
intros n IH.
simpl.
rewrite -> IH.
reflexivity.
Qed.


Lemma nshift_sub_sh :
  forall m n,
    nshift_sub m (sh n) = sh (m+n).
Proof.
intros m n.
induct m.

(* Z *)
auto; done.

(* S *)
intros m IH.
simpl.
rewrite -> IH.
reflexivity.
Qed.


Lemma trunc_shift_sub :
  forall n s,
    trunc n (shift_sub s) = shift_sub (trunc n s).
Proof.
intros n.
induct n.

(* 0 *)
auto; done.

(* S *)
intros n IH s.
destruct s; auto; [].
simpl.
apply IH; done.
Qed.


Lemma trunc_nshift_sub :
  forall n m s,
    trunc n (nshift_sub m s) = nshift_sub m (trunc n s).
Proof.
intros n m s.
induct m.

(* Z *)
auto; done.

(* S *)
intros m IH.
simpl.
rewrite -> trunc_shift_sub; [].
f_equal; auto; done.
Qed.


Lemma nshift_sub_sum :
  forall m n s,
    nshift_sub m (nshift_sub n s) = nshift_sub (m+n) s.
Proof.
intros m n s.
induct m.

(* 0 *)
reflexivity.

(* S *)
intros m IH.
simpl.
rewrite -> IH.
reflexivity.
Qed.


Lemma nshift_sub_succ_inner :
  forall n s,
    nshift_sub (S n) s = nshift_sub n (shift_sub s).
Proof.
intros n s.
replace (S n) with (n+1) by omega.
rewrite <- nshift_sub_sum; [].
reflexivity.
Qed.


Lemma shift_sub_trunc :
  forall s n,
    shift_sub (trunc n s) = trunc n (shift_sub s).
Proof.
intro s.
induct s.

(* dot *)
intros t s IH n.
destruct n as [| n']; auto; [].
apply IH; done.

(* sh *)
intros i n.
rewrite -> !trunc_sh.
simpl.
rewrite -> trunc_sh.
auto.
Qed.


(* Under *)

Lemma trunc_under :
  forall m n s,
    m <= n
    -> trunc m (under n s) = nshift_sub m (under (n-m) s).
Proof.
intros m.
induct m.

(* 0 *)
intros n s H.
simpl.
replace (n-0) with n by omega.
reflexivity.

(* S *)
intros m IH n s H.
rewrite -> trunc_succ_inner; [].
rewrite -> trunc1_under by omega.
rewrite -> trunc_shift_sub; [].
rewrite -> IH; [| omega].
simpl.
replace (n-1-m) with (n - S m) by omega.
reflexivity.
Qed.


Lemma project_under_lt :
  forall n s i,
    i < n
    -> project (under n s) i = var i.
Proof.
intros n s i H.
unfold project.
rewrite -> trunc_under; [| omega].
remember (n-i) as x.
destruct x; [omega |].
simpl.
rewrite -> nshift_sub_dot; [].
rewrite -> nshift_term_var; [].
replace (i+0) with i by omega.
reflexivity.
Qed.


Lemma trunc_under_more :
  forall m n s,
    m >= n
    -> trunc m (under n s) = trunc (m-n) (nshift_sub n s).
Proof.
intros m n s H.
replace m with ((m-n)+n) by omega.
rewrite <- trunc_sum; [].
f_equal; [|].
  omega.

  rewrite -> trunc_under; auto; [].
  replace (n-n) with 0 by omega.
  reflexivity.
Qed.


Lemma project_under_ge_nshift :
  forall n s i,
    i >= n
    -> project (under n s) i = nshift_term n (project s (i-n)).
Proof.
intros n s i H.
unfold project.
rewrite -> trunc_under_more; [| omega].
rewrite -> trunc_nshift_sub; [].
destruct (trunc (i-n) s); [|].
  rewrite -> nshift_sub_dot; [].
  reflexivity.

  rewrite -> nshift_sub_sh; [].
  rewrite -> nshift_term_var; [].
  reflexivity.
Qed.


Lemma subst_shift_sub :
  forall s t,
    subst (shift_sub s) t = shift_term 0 (subst s t).
Proof.
intros s t.
unfold subst.
unfold shift_term.
rewrite -> traverse_compose.
apply (traverse_parametric sub (nat * sub)
       (fun s1 p => let (n, s2) := p in s1 = under n (shift_sub s) /\ s2 = under n s)); auto; [|].

(* enter *)
clear t.
intros s1 (n, s2) (->, ->).
auto; done.

(* resolve *)
clear t.
intros s1 (n, s2) i (->, ->).
destruct (lt_dec i n); [|].
  (* i < n *)
  rewrite -> !project_under_lt by omega.
  rewrite -> traverse_var; [].
  unfold shift_var.
  destruct (lt_dec i n); auto; [].
  omega.

  (* i >= n *)
  unfold project.
  rewrite -> !trunc_under_more by omega.
  rewrite -> !trunc_nshift_sub.
  rewrite -> trunc_shift_sub.
  rewrite <- nshift_sub_succ_inner.
  destruct (trunc (i-n) s); [|].
    rewrite -> nshift_sub_dot.
    rewrite -> nshift_sub_dot.
    fold (shift_term n (nshift_term n t)).
    symmetry; apply nshift_term_commute_eq; done.

  rewrite -> !nshift_sub_sh.
  simpl.
  rewrite -> traverse_var.
  unfold shift_var.
  destruct (lt_dec (n+n1) n); auto; [].
  omega.
Qed.


Lemma subst_dot_shift_term :
  forall t s t',
    subst (dot t s) (shift_term 0 t') = subst s t'.
Proof.
intros t s t'.
unfold subst; unfold shift_term.
rewrite -> traverse_compose.
apply (traverse_parametric (sub * nat) sub
         (fun p s2 => let (s1, i) := p in s1 = under i (dot t s) /\ s2 = under i s)); auto; [|].

(* enter *)
clear t'.
intros (s1, i) s2 (-> & ->).
auto; done.

(* resolve *)
clear t'.
intros (s1, i) s2 j (-> & ->).
fold (subst (under i (dot t s)) (shift_var i j)).
unfold shift_var.
destruct (lt_dec j i); [|].
  (* j < i *)
  rewrite -> subst_var.
  rewrite -> !project_under_lt by assumption.
  reflexivity.

  (* j >= i *)
  rewrite -> subst_var.
  rewrite -> !project_under_ge_nshift by omega.
  f_equal.
  replace (S j - i) with (S (j-i)) by omega.
  rewrite -> project_dot.
  reflexivity.
Qed.


Lemma shift_term_eq_subst_under_sh :
  forall t n,
    shift_term n t = subst (under n (sh 1)) t.
Proof.
intros t n.
unfold shift_term.
unfold subst.
apply (traverse_parametric nat sub (fun n s => s = under n (sh 1))); auto; [|].

(* enter *)
clear t n.
intros n s ->.
reflexivity.

(* resolve *)
clear t n.
intros n s i ->.
unfold shift_var.
destruct (lt_dec i n); [|].
  (* i < n *)
  symmetry; apply project_under_lt; auto; done.

  (* i >= n *)
  rewrite -> project_under_ge_nshift by omega.
  rewrite -> project_sh.
  rewrite -> nshift_term_var.
  f_equal; omega.
Qed.


Lemma shift_term_eq_sh :
  forall t,
    shift_term 0 t = subst (sh 1) t.
Proof.
intro t.
apply shift_term_eq_subst_under_sh.
Qed.


Lemma shift_sub_eq_compose_sh :
  forall s,
    shift_sub s = compose s (sh 1).
Proof.
intro s.
induct s.

(* dot *)
intros t s IH.
simpl.
f_equal; [|].
  apply shift_term_eq_sh; done.

  apply IH; done.

(* sh *)
intro n.
simpl.
rewrite -> trunc_sh; [].
f_equal; omega.
Qed.


(* Composition *)

Lemma compose_shift_sub_left :
  forall s1 s2,
    compose s1 (shift_sub s2) = shift_sub (compose s1 s2).
Proof.
intros s1 s2.
induct s1.

(* dot *)
intros t s1 IH.
simpl.
f_equal; auto; [].
apply subst_shift_sub; done.

(* sh *)
intros i.
symmetry.
apply shift_sub_trunc; done.
Qed.


Lemma compose_shift_sub_right :
  forall s1 s2 t,
    compose (shift_sub s1) (dot t s2) = compose s1 s2.
Proof.
intros s1 s2 t.
induct s1.

(* dot *)
intros t' s1' IH.
simpl.
f_equal; [|].
  apply subst_dot_shift_term; done.

  apply IH; done.

(* sh *)
auto; done.
Qed.


Lemma compose_sh :
  forall n s,
    compose (sh n) s = trunc n s.
Proof.
auto.
Qed.


Lemma trunc_compose :
  forall i s1 s2,
    trunc i (compose s1 s2) = compose (trunc i s1) s2.
Proof.
intros i.
induct i.

(* 0 *)
reflexivity.

(* S *)
intros n IH s1 s2.
destruct s1 as [t s1' | i]; [|].
  (* dot *)
  apply IH; done.

  (* sh *)
  rewrite -> trunc_sh, !compose_sh.
  apply trunc_sum; done.
Qed.


Lemma project_compose :
  forall i s1 s2,
    project (compose s1 s2) i = subst s2 (project s1 i).
Proof.
intros i s1 s2.
unfold project.
rewrite -> trunc_compose.
generalize (trunc i s1); intro s.
destruct s; auto; done.
Qed.


(* The main lemma *)
Lemma subst_compose :
  forall t s1 s2,
    subst (compose s2 s1) t = subst s1 (subst s2 t).
Proof.
intros t s1 s2.
unfold subst.
rewrite -> traverse_compose; [].
apply (traverse_parametric sub (sub * sub) (fun s p => let (s1, s2) := p in s = compose s2 s1)); auto; [|].

(* enter *)
clear t s1 s2.
intros s (s1, s2) ->.
simpl.
f_equal.
rewrite <- compose_shift_sub_left.
rewrite -> compose_shift_sub_right.
reflexivity.

(* resolve *)
clear t s1 s2.
intros s (s1 & s2) i ->.
apply project_compose; done.
Qed.


Lemma compose_assoc :
  forall s1 s2 s3,
    compose (compose s1 s2) s3 = compose s1 (compose s2 s3).
Proof.
intros s1 s2 s3.
induct s1.

(* dot *)
intros t s1 IH.
simpl.
f_equal; auto using subst_compose; done.

(* sh *)
intros n.
rewrite -> !compose_sh; [].
symmetry.
apply trunc_compose; done.
Qed.


(* Various equivalencies *)

Lemma compose_dot :
  forall t s1 s2,
    compose (dot t s1) s2 = dot (subst s2 t) (compose s1 s2).
Proof.
auto.
Qed.


Lemma compose_sh_0 :
  forall s,
    compose (sh 0) s = s.
Proof.
auto.
Qed.


Lemma compose_sh_succ_dot :
  forall t s n,
    compose (sh (S n)) (dot t s) = compose (sh n) s.
Proof.
auto.
Qed.


Lemma compose_sh_sh :
  forall m n,
    compose (sh m) (sh n) = sh (m+n).
Proof.
intros m n.
simpl.
rewrite -> trunc_sh; [].
f_equal; done.
Qed.


Lemma compose_id_left :
  forall s,
    compose id s = s.
Proof.
apply compose_sh_0.
Qed.


Lemma subst_under_id :
  forall n t,
    subst (under n id) t = t.
Proof.
intros m t.
unfold subst.
apply (traverse_id sub (fun s => exists n, s = under n id)); eauto; [|].

(* enter *)
clear t.
intros s (n, ->).
exists (S n).
reflexivity.

(* resolve *)
clear t.
intros s i (n, ->).
destruct (lt_dec i n); [|].
  (* i < n *)
  apply project_under_lt; assumption.

  (* i >= n *)
  rewrite -> project_under_ge_nshift by omega.
  unfold id.
  rewrite -> project_sh; [].
  rewrite -> nshift_term_var; [].
  f_equal; omega.
Qed.


Lemma subst_id :
  forall t,
    subst id t = t.
Proof.
intro t.
change (subst (under 0 id) t = t).
apply subst_under_id.
Qed.


Lemma compose_id_right :
  forall s,
    compose s id = s.
Proof.
intro s.
induct s.

(* dot *)
intros t s IH.
simpl.
f_equal; [|].
  apply subst_id; done.

  apply IH; done.

(* sh *)
intro n.
simpl.
unfold id.
rewrite -> trunc_sh.
f_equal; omega.
Qed.


Lemma trunc_eq_compose_sh :
  forall n s,
    trunc n s = compose (sh n) s.
Proof.
intros n s.
destruct n; auto.
Qed.


Lemma subst1_shift1 :
  forall t t', subst1 t (shift1 t') = t'.
Proof.
intros t t'.
unfold subst1.
unfold shift1.
rewrite <- subst_compose; [].
unfold sh1.
rewrite -> compose_sh_succ_dot; [].
rewrite -> compose_sh_0; [].
apply subst_id; done.
Qed.


Lemma under_zero :
  forall s, under 0 s = s.
Proof.
auto.
Qed.


Lemma under_succ :
  forall n s,
    under (S n) s = dot (var 0) (compose (under n s) (sh 1)).
Proof.
intros n s.
unfold under.
rewrite -> shift_sub_eq_compose_sh.
reflexivity.
Qed.


Lemma under_plus :
  forall i j s,
    under (i + j) s = under i (under j s).
Proof.
intros i j s.
revert s.
induct i.

(* 0 *)
intro s.
simpl.
reflexivity.

(* S *)
intros i IH s.
replace (S i + j) with (S (i + j)) by omega.
rewrite -> !under_succ; [].
rewrite -> IH; auto; done.
Qed.


Lemma dist_compose_under :
  forall n s1 s2,
    compose (under n s1) (under n s2) = under n (compose s1 s2).
Proof.
intros n s1 s2.
induct n.

(* 0 *)
rewrite -> !under_zero; [].
reflexivity.

(* S *)
intros n IH.
rewrite -> !under_succ; [].
rewrite -> compose_dot; [].
f_equal; [].
rewrite -> compose_assoc.
rewrite -> compose_sh_succ_dot.
rewrite -> compose_sh_0.
rewrite <- compose_assoc.
rewrite -> IH.
reflexivity.
Qed.


Lemma subst_dot0_sh :
  forall t,
    subst (dot (var 0) (sh 1)) t = t.
Proof.
intro t.
rewrite -> (subst_under_id 1 t) at 1.
reflexivity.
Qed.


Hint Unfold id sh1 shift1 subst1 : subst.
Hint Rewrite project_zero project_dot project_sh : subst.
Hint Rewrite subst_id subst1_shift1 : subst.
Hint Rewrite compose_dot compose_sh_0 compose_sh_succ_dot compose_sh_sh compose_id_left compose_id_right : subst.
Hint Rewrite compose_assoc : subst.
Hint Rewrite <- subst_compose : subst.
Hint Rewrite under_zero under_succ dist_compose_under : subst.
Hint Rewrite subst_under_id subst_dot0_sh : subst.
Hint Rewrite shift_sub_eq_compose_sh : subst.


(* Now that we're done, we'll allow traverse to be transparent. *)
Transparent traverse.


Ltac fold_subst1
  :=
  repeat
  (match goal with
   | |- context [subst (dot ?t id)] => fold (subst1 t)
   end).


Tactic Notation "fold_subst1" "in" hyp(H)
  :=
  repeat
  (match type of H with
   | context [subst (dot ?t id)] => fold (subst1 t) in H
   end).


Ltac reduce_subst
  :=
  progress (unfold subst; cbv beta iota delta [traverse]; repeat (fold traverse); repeat (fold subst)).


Tactic Notation "reduce_subst" "in" hyp(H)
  :=
  progress (unfold subst in H; cbv beta iota delta [traverse] in H |-; repeat (fold traverse in H); repeat (fold subst in H)).


Ltac reduce_sub
  :=
  try (repeat (autounfold with subst
               || autorewrite with subst 
               || reduce_subst)).


Tactic Notation "reduce_sub" "in" hyp(H)
  :=
  try (repeat (autounfold with subst in H
               || autorewrite with subst in H
               || reduce_subst in H)).


(*move in karl's tactics*)

Ltac cleanup_sub
  :=
  repeat (fold id); repeat (fold sh1); repeat (fold shift1); repeat fold_subst1; repeat calculate.


Tactic Notation "cleanup_sub" "in" hyp(H)
  :=
  repeat (fold id in H); repeat (fold sh1 in H); repeat (fold shift1 in H); repeat (fold_subst1 in H); repeat (calculate in H).


Ltac simp_sub
  :=
  reduce_sub; cleanup_sub.


Tactic Notation "simp_sub" "in" hyp(H)
  :=
  reduce_sub in H; cleanup_sub in H.


Tactic Notation "replsub" constr(t) "with" constr(t') :=
  replace t with t' by (simp_sub; reflexivity).


Tactic Notation "replsub" constr(t) "with" constr(t') "in" hyp(H) :=
  replace t with t' in H by (simp_sub; reflexivity).


Lemma nshift_term_eq_sh :
  forall n t,
    nshift_term n t = subst (sh n) t.
Proof.
intros n t.
induction n as [| n IH].

(* 0 *)
simp_sub.
reflexivity.

(* S *)
simpl.
rewrite -> IH.
rewrite -> shift_term_eq_sh.
simp_sub.
reflexivity.
Qed.


Lemma compose_sh_under_leq :
  forall i n s,
    i <= n
    -> compose (sh i) (under n s) = compose (under (n - i) s) (sh i).
Proof.
intros i n s Hleq.
revert n Hleq.
induct i.

(* 0 *)
intros n _.
simp_sub.
repl (n - 0) with n by omega.
reflexivity.

(* S *)
intros i IH n Hleq.
destruct n as [| n']; [omega |].
rewrite -> under_succ; [].
rewrite -> compose_sh_succ_dot; [].
rewrite <- compose_assoc; [].
rewrite -> IH; [| omega].
simp_sub.
repl (1 + n' - (1 + i)) with (n' - i) by omega.
reflexivity.
Qed.


Lemma compose_sh_under_geq :
  forall i n s,
    i >= n
    -> compose (sh i) (under n s) = compose (sh (i - n)) (compose s (sh n)).
Proof.
intros i n s Hgeq.
replace (sh i) with (sh ((i - n) + n)) by (f_equal; omega).
rewrite <- compose_sh_sh; [].
rewrite -> compose_assoc; [].
rewrite -> compose_sh_under_leq; [| auto; done].
replace (n - n) with 0 by omega.
rewrite -> under_zero; [].
reflexivity.
Qed.


Lemma compose_sh_under :
  forall i n s,
    compose (sh i) (under (i + n) s) = compose (under n s) (sh i).
Proof.
intros i n s.
exploit (compose_sh_under_leq i (i + n) s) as H; [omega |].
repl (i + n - i) with n in H by omega.
assumption.
Qed.


Lemma compose_sh1_under :
  forall n s,
    compose sh1 (under (S n) s) = compose (under n s) sh1.
Proof.
intros n s.
exact (compose_sh_under 1 n s).
Qed.


Lemma project_under_ge :
  forall n s i,
    i >= n
    -> project (under n s) i = subst (sh n) (project s (i-n)).
Proof.
intros n s i H.
rewrite <- nshift_term_eq_sh.
apply project_under_ge_nshift; auto; done.
Qed.


Lemma split_dot :
  forall t s,
    dot t s = compose (dot (var 0) (compose s sh1)) (dot t id).
Proof.
intros t s.
simp_sub.
reflexivity.
Qed.


Lemma split_dot_compose :
  forall m s n,
    subst (dot m s) n = subst1 m (subst (dot (var 0) (compose s sh1)) n).
Proof.
intros m s n.
rewrite -> split_dot.
rewrite -> subst_compose.
reflexivity.
Qed.


Lemma split_dot_dot_compose :
  forall m1 m2 s n,
    subst (dot m1 (dot m2 s)) n = subst (dot m1 (dot m2 id)) (subst (dot (var 0) (dot (var 1) (compose s (sh 2)))) n).
Proof.
intros m1 m2 s n.
simp_sub.
reflexivity.
Qed.


Lemma dot0_compose_split :
  forall s s',
    dot (var 0) (compose s s') = compose (dot (var 0) (compose s sh1)) (dot (var 0) s').
Proof.
intros s s'.
simp_sub.
reflexivity.
Qed.


Lemma dot01_compose_split :
  forall s s',
    dot (var 0) (dot (var 1) (compose s s')) = compose (dot (var 0) (dot (var 1) (compose s (sh 2)))) (dot (var 0) (dot (var 1) s')).
Proof.
intros s s'.
simp_sub.
reflexivity.
Qed.


Lemma subst_dot01_sh :
  forall t,
    subst (dot (var 0) (dot (var 1) (sh 2))) t = t.
Proof.
intro t.
rewrite -> (subst_under_id 2 t) at 1.
reflexivity.
Qed.


Lemma subst_dot1_sh :
  forall t,
    subst (dot (var 1) (sh 2)) t = shift1 t.
Proof.
intro t.
replsub (shift1 t) with (subst sh1 (subst (dot (var 0) (sh 1)) t)).
rewrite <- subst_compose; [].
simp_sub.
reflexivity.
Qed.


Lemma under_succ2 :
  forall n s,
    under (S (S n)) s = dot (var 0) (dot (var 1) (compose (under n s) (sh 2))).
Proof.
intros n s.
rewrite -> under_succ.
f_equal; [].
rewrite -> under_succ.
simp_sub.
reflexivity.
Qed.


Lemma shift_eq_invert :
  forall n t t',
    subst (sh n) t = subst (sh n) t'
    -> t = t'.
Proof.
intros n t t' Heq.
revert t t' Heq.
induct n.

(* 0 *)
intros t t' Heq.
simp_sub in Heq.
assumption.

(* S *)
intros n IH t t' Heq.
f_apply (fun u => subst1 (var 0) u) in Heq as Heq'.
simp_sub in Heq'.
eapply IH; eauto; done.
Qed.


Lemma subst_under_var :
  forall s i j,
    i < j
    -> subst (under j s) (var i) = var i.
Proof.
intros s i j Hlt.
simp_sub.
rewrite -> project_under_lt; auto.
Qed.


Definition eqsub (s s' : sub) :=
  forall i m, subst (under i s) m = subst (under i s') m.


Lemma subst_eqsub :
  forall s s' m,
    eqsub s s'
    -> subst s m = subst s' m.
Proof.
intros s s' m H.
apply (H 0).
Qed.


Lemma eqsub_expand_sh :
  forall n,
    eqsub (sh n) (dot (var n) (sh (S n))).
Proof.
intros n i t.
rewrite <- (subst_under_id (S i) t) at 1; [].
assert (S i = i + 1) as Heq by omega.
rewrite -> Heq at 1; clear Heq; [].
rewrite -> under_plus; [].
rewrite <- subst_compose; [].
rewrite -> dist_compose_under; [].
simp_sub.
reflexivity.
Qed.    


Lemma eqsub_refl :
  forall s, eqsub s s.
Proof.
intros s i m; auto.
Qed.


Lemma eqsub_trans :
  forall s1 s2 s3,
    eqsub s1 s2
    -> eqsub s2 s3
    -> eqsub s1 s3.
Proof.
intros s1 s2 s3 H12 H23 i m.
transitivity (subst (under i s2) m); auto.
Qed.


Lemma eqsub_dot :
  forall m s s',
    eqsub s s'
    -> eqsub (dot m s) (dot m s').
Proof.
intros m s s' Heqsub.
intros i n.
rewrite -> (split_dot m s); rewrite -> (split_dot m s'); [].
rewrite <- !dist_compose_under; [].
rewrite -> !subst_compose; [].
f_equal; [].
so (Heqsub (i + 1) n) as H.
rewrite -> !under_plus in H.
rewrite -> !under_succ in H.
exact H.
Qed.


Lemma eqsub_compose :
  forall s1 s1' s2 s2',
    eqsub s1 s1'
    -> eqsub s2 s2'
    -> eqsub (compose s1 s2) (compose s1' s2').
Proof.
intros s1 s1' s2 s2' H1 H2.
intros i m.
rewrite <- !dist_compose_under.
rewrite -> !subst_compose.
rewrite -> (H1 i m).
rewrite -> (H2 i).
reflexivity.
Qed.


Lemma eqsub_under :
  forall s s' i,
    eqsub s s'
    -> eqsub (under i s) (under i s').
Proof.
intros s s' i Hs.
induct i.

(* 0 *)
{
rewrite -> under_zero; auto.
}

(* S *)
{
intros i IH.
rewrite -> !under_succ.
apply eqsub_dot.
apply eqsub_compose; auto using eqsub_refl.
}
Qed.


Lemma eqsub_under_id :
  forall i, eqsub (under i id) id.
Proof.
intro i.
intros j m.
rewrite <- under_plus.
rewrite -> !subst_under_id.
reflexivity.
Qed.
