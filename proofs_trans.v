Require Import Program Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types0 basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences.
From istari Require Import Rules Defined DefsEquiv.

Theorem total G E A: of_m G E A ->
                exists ebar, trans G E A ebar.
  intros He. induction He.
  {exists (lam (lam (gamma_nth (var 0) i))). constructor. assumption.
  }
  { exists (lam (lam nzero)). constructor. 
  }
  {
    destruct IHHe as [mbar Hm].
    exists (lam (lam (app (app (subst (sh 2) mbar) (var 1)) (var 0)))).
    constructor. assumption.
  }
  {
    (*make separate judgement to tell if a term is a type*)
  }
