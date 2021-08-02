Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
(*very basic things*)

Lemma make_app1 T (L: seq T) x: (x::L) = [::x] ++ L.
  auto. Qed.

Lemma make_app2 T (L: seq T) x y: (x::y::L) = [::x; y] ++ L.
  auto. Qed.

Lemma make_app3 T (L: seq T) x y z: (x::y::z::L) = [::x; y; z] ++ L.
  auto. Qed.

Lemma make_app4 T (L: seq T) x y z a: (x::y::z::a::L) = [::x; y; z; a] ++ L.
  auto. Qed.

Lemma make_app5 T (L: seq T) x y z a b: (x::y::z::a::b::L) = [::x; y; z; a; b] ++ L.
  auto. Qed.

Lemma make_app6 T (L: seq T) x y z a b c: (x::y::z::a::b::c::L) = [::x; y; z; a; b; c] ++ L.
  auto. Qed.

Lemma geq0c n: (n >= 0)%coq_nat.
  apply not_lt. intros contra. move/ltP : contra. auto.
  Qed.


Hint Rewrite minus_n_O : core natlib.

Hint Resolve geq0c: core natlib.

Ltac nat_lib := auto with natlib; autorewrite with natlib.
