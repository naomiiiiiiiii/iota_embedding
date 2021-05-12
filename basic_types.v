Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Definition oof M A: (@Syntax.judgement False) := deq M M A.

Definition oof_t M: (@Syntax.judgement False) := deqtype M M.

Lemma zero_typed: forall G,
    tr G (oof nzero nattp). Admitted.

Lemma leq_refl: forall G n,
    tr G (deq n n nattp) ->
    tr G (oof triv (leqpagetp n n)). Admitted.

Hint Resolve zero_typed.
Hint Resolve leq_refl.
