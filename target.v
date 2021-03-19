Require Import Coq.Arith.Arith.

Require Import Axioms.

From istari Require Import Sigma Tactics Equality Ordinal Page.

Import List.ListNotations.

Section object.


Variable object : Type.


Inductive operator : list nat -> Type :=
| oper_nat: operator nil
| oper_z: operator nil
|oper_succ: operator [0]

| oper_arrow       : operator [0; 0]
| oper_lam         : operator [1]
| oper_app         : operator [0; 0]

| oper_comp: operator [0]
| oper_ret_m: operator [0]
| oper_bind_m : operator [0; 1] (*bind x = e1 in e2*)

| oper_reftp: operator [0]
| oper_ref: operator [0]
| oper_deref: operator [0]
| oper_assign: operator [0; 0] (*R := v*)

| oper_triv        : operator nil
| oper_unittp      : operator nil
.


Inductive term : Type :=
| var : nat -> term
| oper : forall a, operator a -> row a -> term

with row : list nat -> Type :=
| rw_nil : row nil
| rw_cons : forall i a, term -> row a -> row (i :: a)
.

Scheme term_mut_ind := Induction for term Sort Prop
with   row_mut_ind := Induction for row Sort Prop.
Combined Scheme syntax_ind from term_mut_ind, row_mut_ind.

Scheme term_mut_rect := Induction for term Sort Type
with   row_mut_rect := Induction for row Sort Type.


Lemma row_nil_invert : forall (r : row nil), r = rw_nil.
Proof.
intros r.
apply eq_dep_impl_eq_snd.
set (a := nil) in r |- * at 1.
assert (a = nil) as Heq by reflexivity.
clearbody a.
revert Heq.
cases r; auto.
intros; discriminate.
Qed.


Lemma row_cons_invert :
  forall i a (r : row (cons i a)),
    exists m (s : row a),
      r = rw_cons i a m s.
Proof.
intros i a r.
cut (exists m s, eq_dep _ row (cons i a) r (cons i a) (rw_cons i a m s)).
  {
  intros (m & s & Heq).
  exists m, s.
  exact (eq_dep_impl_eq_snd _#5 Heq).
  }
set (b := cons i a) in r |- * at 1.
assert (b = cons i a) as Heq by reflexivity.
clearbody b.
revert Heq.
cases r; try (intros; discriminate).
intros i' a' m r Heq.
injection Heq.
intros -> ->.
exists m, r.
apply eq_dep_refl.
Qed.


Lemma row_invert_auto :
  forall a (r : row a),
    list_rect (fun a => (row a -> Prop) -> Prop)
      (fun P => P rw_nil)
      (fun i a IH P =>
         exists m,
           IH (fun r => P (rw_cons i a m r)))
      a
      (eq r).
Proof.
intros a.
induct a.

(* nil *)
{
intro r.
cbn.
apply row_nil_invert.
}

(* cons *)
{
intros i a IH rr.
cbn.
so (row_cons_invert _ _ rr) as (m & r & ->).
exists m.
force_exact (IH r).
f_equal.
fextensionality 1.
intro r'.
pextensionality.
  {
  intros <-; auto.
  }

  {
  intros Heq.
  injection Heq.
  intro H.
  injectionT H.
  auto.
  }
}
Qed.


Inductive hyp : Type :=
(*| hyp_tpl : hyp x: _type_*)
| hyp_tm  : term -> hyp
.


Definition context := list hyp.


Inductive judgement : Type :=
| deq : (* tm *) term -> term -> (* cn *) term -> judgement
.


Fixpoint traverse (resolve : nat -> nat -> term) (i : nat) (m : term) {struct m} : term
  :=
  (match m with
   | var j => resolve i j
   | oper a t r => oper a t (traverse_row resolve i a r)
   end)

with traverse_row (resolve : nat -> nat -> term) (i : nat) (a : list nat) (r : row a) {struct r} : row a
  :=
  (match r
   in row a
   return row a
   with
   | rw_nil => rw_nil
   | rw_cons j a m r => rw_cons j a (traverse resolve (j+i) m) (traverse_row resolve i a r)
   end)
.


Lemma traverse_var :
  forall resolve i j,
    traverse resolve i (var j) = resolve i j.
Proof.
auto.
Qed.


Lemma traverse_oper :
  forall resolve i a t r,
    traverse resolve i (oper a t r)
    =
    oper a t (traverse_row resolve i a r).
Proof.
intros; reflexivity.
Qed.


Lemma traverse_row_cons :
  forall resolve i j a m r,
    traverse_row resolve i (cons j a) (rw_cons j a m r)
    =
    rw_cons j a
      (traverse resolve (j+i) m)
      (traverse_row resolve i a r).
Proof.
intros; reflexivity.
Qed.


Lemma traverse_row_nil :
  forall resolve i,
    traverse_row resolve i nil rw_nil = rw_nil.
Proof.
intros; reflexivity.
Qed.


Lemma traverse_parametric :
  forall (P : nat -> nat -> Prop) resolve resolve',
    (forall i i', P i i' -> P (S i) (S i'))
    -> (forall i i' j, P i i' -> resolve i j = resolve' i' j)
    -> forall i i' t, P i i' -> traverse resolve i t = traverse resolve' i' t.
Proof.
intros P resolve resolve' Pcomp.
revert resolve resolve'.
assert (forall j i i', P i i' -> P (j + i) (j + i')) as Hcomp'.
  intro j.
  induct j.
  (* 0 *)
  intros i i' H.
  exact H.

  (* S *)
  intros j IH i i' HP.
  simpl.
  auto; done.
intros resolve resolve' Hres i i' t.
revert t i i'.
apply
  (term_mut_ind
     (fun m => forall i i', P i i' -> traverse resolve i m = traverse resolve' i' m)
     (fun a r => forall i i', P i i' -> traverse_row resolve i a r = traverse_row resolve' i' a r));
try (intros; simpl; eauto; f_equal; eauto; done).
Qed.


Lemma traverse_id :
  forall resolve,
    (forall i j, resolve i j = var j)
    -> forall i t, traverse resolve i t = t.
Proof.
intros resolve Hres i m.
revert m i.
apply
  (term_mut_ind
     (fun m => forall i, traverse resolve i m = m)
     (fun a r => forall i, traverse_row resolve i a r = r));
intros; simpl; f_equal; eauto.
Qed.


Lemma traverse_compose :
  forall resolve resolve' i t,
    traverse resolve i (traverse resolve' i t)
    = traverse
      (fun i' j => traverse resolve i' (resolve' i' j))
      i t.
Proof.
intros resolve resolve' i m.
revert m i.
apply
  (term_mut_ind
     (fun m =>
        forall i, 
          traverse resolve i (traverse resolve' i m)
          = traverse (fun i' j => traverse resolve i' (resolve' i' j)) i m)
     (fun a r =>
        forall i, 
          traverse_row resolve i a (traverse_row resolve' i a r)
          = traverse_row (fun i' j => traverse resolve i' (resolve' i' j)) i a r));
intros; simpl; f_equal; eauto.
Qed.



Inductive Forallr (P : term -> Type) : forall a, row a -> Type :=
| Forallr_nil
    : Forallr P nil rw_nil

| Forallr_cons {i a m r}
    : P m
      -> Forallr P a r
      -> Forallr P (cons i a) (rw_cons i a m r)
.


Lemma term_row_rect :
  forall (P : term -> Type),
    (forall i, P (var i))
    -> (forall a t r, Forallr P a r -> P (oper a t r))
    -> forall m, P m.
Proof.
intros P H1 H2 m.
apply (term_mut_rect P (Forallr P)); eauto using Forallr.
Qed.


Lemma oper_injection :
  forall a t t' r r',
    oper a t r = oper a t' r'
    -> t = t' /\ r = r'.
Proof.
intros a t t' r r' Heq.
injection Heq.
intros Heqr Heqt.
destruct (eq_dep_impl_eq _#6 (EqdepFacts.eq_sigT_eq_dep _#6 Heqt)) as (h & Heqt').
substrefl h.
cbn in Heqt'.
destruct (eq_dep_impl_eq _#6 (EqdepFacts.eq_sigT_eq_dep _#6 Heqr)) as (h & Heqr').
substrefl h.
cbn in Heqr'.
auto.
Qed.


Lemma rw_cons_injection :
  forall j a m m' r r',
    rw_cons j a m r = rw_cons j a m' r'
    -> m = m' /\ r = r'.
Proof.
intros j a m m' r r' Heq.
injection Heq.
intros Heq' Heqm.
destruct (eq_dep_impl_eq _#6 (EqdepFacts.eq_sigT_eq_dep _#6 Heq')) as (h & Heq'').
substrefl h.
cbn in Heq''.
auto.
Qed.

End object.

(*Arguments var {object}.
Arguments oper {object}.
Arguments rw_nil {object}.
Arguments rw_cons {object}.

Arguments hyp {object}.
Arguments context {object}.
Arguments judgement {object}.*)

Definition nattp_m : @term := oper _ oper_nat rw_nil.
Definition z_m : @term := oper _ oper_z rw_nil.
Definition succ_m M: @term := oper _ oper_succ (rw_cons _ _ M rw_nil).

Definition arrow m1 m2 : @term := oper _ oper_arrow (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition lam m             : @term := oper _ oper_lam (rw_cons _ _ m rw_nil).
Definition app m1 m2         : @term := oper _ oper_app (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).

Definition comp T : @term := oper _ oper_comp (rw_cons _ _ T rw_nil).
Definition ret_m M : @term := oper _ oper_ret_m (rw_cons _ _ M rw_nil).
Definition bind_m M : @term := oper _ oper_ret_m (rw_cons _ _ M rw_nil).

Definition reftp T : @term := oper _ oper_comp (rw_cons _ _ T rw_nil).
Definition ref_m M : @term := oper _ oper_ref (rw_cons _ _ M rw_nil).
Definition deref_m M : @term := oper _ oper_deref (rw_cons _ _ M rw_nil).
Definition assign_m m1 m2 : @term := oper _ oper_assign (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).

Definition unittp_m       : @term := oper _ oper_unittp rw_nil.
Definition triv_m       : @term := oper _ oper_triv rw_nil.


