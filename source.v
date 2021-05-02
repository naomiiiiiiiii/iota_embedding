Require Import Coq.Arith.Arith.

Require Import Axioms.

From istari Require Import Sigma Tactics Equality Ordinal Page.

Import List.ListNotations.

Inductive term: Set :=
| var : nat -> term
| nattp_m : term
| z_m : term
| succ_m : term -> term
| arrow_m : term -> term -> term
| lam_m : term -> term
| app_m : term -> term -> term
| comp_m : term -> term
| ret_m : term -> term
| bind_m : term -> term -> term
| reftp_m: term -> term
| ref_m : term -> term
| deref_m: term -> term
| assign_m: term -> term
| triv_m: term
| unittp_m: term.

Definition context := list term.


Fixpoint traverse (S:Set) (enter : S -> S) (resolve : S -> nat -> term) (s : S) (t : term) {struct t} : term :=
  match t with
   | var i => resolve s i
   | nattp_m => nattp_m
   | z_m => z_m
   | succ_m t1 => succ_m (traverse S enter resolve s t1)
   | arrow_m t1 t2 => arrow_m (traverse S enter resolve s t1) (traverse S enter resolve s t2)
   | lam_m t1 => lam_m (traverse S enter resolve (enter s) t1)
   | app_m t1 t2 => app_m (traverse S enter resolve s t1) (traverse S enter resolve s t2)
   | comp_m t1 => comp_m (traverse S enter resolve s t1)
   | ret_m t1 => ret_m (traverse S enter resolve s t1)
   | bind_m t1 t2 => bind_m (traverse S enter resolve s t1) (traverse S enter resolve (enter s) t2)
   | reftp_m t1 => reftp_m (traverse S enter resolve s t1)
   | ref_m t1 => ref_m (traverse S enter resolve s t1)
   | deref_m t1 => deref_m (traverse S enter resolve s t1)
   | assign_m t1 => assign_m (traverse S enter resolve s t1)
   | triv_m => triv_m
   | unittp_m => unittp_m end.

Ltac prove_traverse_parametric ind :=
intros S S' R enter enter' resolve resolve' s s' t Henter Hresolve Hs;
generalize dependent s';
generalize dependent s;
induction t using ind; intros s s' Hs;
[apply Hresolve; apply Hs | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try
  ((match goal with
    | IH : (forall (s : S) (s' : S'), _ -> _ = ?f _ ?t)
      |- _ = ?g _ ?t
      => apply IH
    end);
   repeat (apply Henter);
   apply Hs).


Ltac prove_traverse_id ind :=
intros S R enter resolve s t Henter Hresolve Hs;
generalize dependent s;
induction t using ind; intros s Hs;
[apply Hresolve; apply Hs | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try ((match goal with
      | IH : (forall (s : S), _ -> _ = ?t)
        |- _ = ?t
        => apply IH
      end);
     repeat (apply Henter);
     apply Hs).


Ltac prove_traverse_compose ind :=
intros S S' enter enter' resolve resolve' s s' t;
generalize dependent s';
generalize dependent s;
induction t using ind; intros s s';
[simpl; reflexivity | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try (match goal with
      | IH : (forall (s : S) (s' : S'), _ = ?f ?t)
        |- _ = ?g ?t
        => apply IH
      end).



Lemma traverse_var :
  forall S enter resolve s i,
    traverse S enter resolve s (var i) = resolve s i.
Proof.
auto.
Qed.


Lemma traverse_parametric :
  forall (S:Set) (S':Set) (R : S -> S' -> Prop) enter enter' resolve resolve' s s' t,
    (forall s s', R s s' -> R (enter s) (enter' s'))
    -> (forall s s' i, R s s' -> resolve s i = resolve' s' i)
    -> R s s'
    -> traverse S enter resolve s t = traverse S' enter' resolve' s' t.
Proof. 
prove_traverse_parametric term_ind.
Qed.


Lemma traverse_id :
  forall (S:Set) (R : S -> Prop) enter resolve s t,
    (forall s, R s -> R (enter s))
    -> (forall s i, R s -> resolve s i = var i)
    -> R s
    -> traverse S enter resolve s t = t.
Proof.
prove_traverse_id term_ind.
Qed.


Lemma traverse_compose :
  forall (S:Set) (S':Set) enter enter' resolve resolve' s s' t,
    traverse S enter resolve s (traverse S' enter' resolve' s' t)
    = traverse (S * S')
      (fun p => let (s, s') := p in (enter s, enter' s'))
      (fun p i => let (s, s') := p in traverse S enter resolve s (resolve' s' i))
      (s, s') t.
Proof.
prove_traverse_compose term_ind.
Qed.


Definition termx := term.
Definition varx := var.
