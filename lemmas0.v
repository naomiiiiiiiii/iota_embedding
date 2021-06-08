Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
(*trivial small lemmas*)
Lemma hseq2: forall (T: Type) (x y: T)
                  (L: seq T), [:: x; y] ++ L=
                 [:: x, y & L].
intros. auto. Qed.

  Lemma hseq3: forall (T: Type) (x y z: T)
                  (L: seq T), [:: x; y; z] ++ L=
                 [:: x, y, z & L].
intros. auto. Qed.

Lemma hseq4: forall (T: Type) (x y z a: T)
                  (L: seq T), [:: x; y; z; a] ++ L=
                 [:: x, y, z, a & L].
intros. auto. Qed.
