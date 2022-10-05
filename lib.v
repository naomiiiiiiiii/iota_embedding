Require Import Program Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.

Lemma geq0c n: (n >= 0)%coq_nat.
  apply not_lt. intros contra. move/ltP : contra. auto.
  Qed.
 

Hint Rewrite <- minus_n_O : core natrewrite natlib.

Hint Resolve geq0c: core natlib.

Hint Rewrite addn1 add1n: core natlib natrewrite.

Ltac nat_lib := auto with natlib.

Ltac nat_rewrite := autorewrite with natrewrite.


(*ltP is name of reflection from legacy < to ssr < *)
