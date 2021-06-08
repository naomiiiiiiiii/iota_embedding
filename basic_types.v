(*Trivial facts that would clutter up the other files*)
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Definition oof M A: (@Syntax.judgement False) := deq M M A.

Definition oof_t M: (@Syntax.judgement False) := deqtype M M.

Definition U0 : (term False) := univ nzero.

Definition leq_t n m : term False :=
  app (app leqtp n) m.

Definition lt_t n m : term False :=
  app (app lttp n) m.

Lemma zero_typed: forall G,
    tr G (oof nzero nattp). Admitted.

Lemma leq_refl: forall G n,
    tr G (deq n n nattp) ->
    tr G (oof triv (leqpagetp n n)). Admitted.

Lemma leq_type: forall G n1 n2,
    tr G (oof n1 nattp) -> tr G (oof n2 nattp) ->
    tr G (oof (leq_t n1 n2) U0).
  Admitted.


Lemma lt_type: forall G n1 n2,
    tr G (oof n1 nattp) -> tr G (oof n2 nattp) ->
    tr G (oof (ltpagetp n1 n2) U0).
  Admitted.

Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.

Hint Resolve nat_type nat_U0 zero_typed leq_refl leq_type lt_type.


