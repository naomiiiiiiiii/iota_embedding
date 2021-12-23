(*Trivial facts that would clutter up the other files*)
Require Import ssreflect.
From mathcomp Require Import ssreflect seq ssrnat.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Definition oof M A: (@Syntax.judgement obj) := deq M M A.

Definition oof_t M: (@Syntax.judgement obj) := deqtype M M.

Definition U0 : (term obj) := univ nzero.

Definition leq_t n m : term obj :=
  app (app leqtp n) m.

Definition lt_t n m : term obj :=
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

Lemma U0_type: forall G,
    tr G (deqtype U0 U0). Admitted.

Hint Resolve nat_type nat_U0 zero_typed leq_refl leq_type lt_type U0_type.

Definition if_z (n: term obj): (term obj) := ppi1 n.

(*n - m*)
Definition minusbc: (term obj) := lam
                         (
                           (*f := 0*)
                           lam ( (*f:= 1, n := 0*)
                               lam ((*f := 2, n:= 1, m := 0*)
                                   let f := (var 2) in
                                   let n := (var 1) in
                                   let m := (var 0) in
                                                  bite (if_z n)
                                                  (n)
                                                  (bite (if_z m)
                                                     (n)
                                                    (app (app f (app (ppi2 n) triv)) (app (ppi2 m) triv)))
                                                  ))).
 Definition minus: (term obj) := app theta minusbc.

 Lemma minus_typed {G}: tr G (oof minus (arrow nattp (arrow nattp nattp))).
Admitted.

(*lt_b x y*)
 Definition lt_b := lam ( lam (*x = 1, y = 0*)

                            (if_z (app (app minus (nsucc (var 1)))  (var 0)))
                       ).

Definition ltb_app m n := app (app lt_b m) n.

(*should be fine*)
Lemma ltapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (ltb_app m n) booltp). Admitted.

(*more difficult, need induction*)
Lemma ltb_false G n : tr G (oof n nattp) -> tr G (deq (ltb_app n n) bfalse booltp).
Admitted.

Lemma nsucc_lt: forall G n, tr G (oof n nattp) ->
                       tr G (oof triv (lt_t n (nsucc n))).
Admitted.


Definition eq_bbc: (term obj) := lam
                         (
                           (*f := 0*)
                           lam ( (*f:= 1, n := 0*)
                               lam ((*f := 2, n:= 1, m := 0*)
                                   let f := (var 2) in
                                   let n := (var 1) in
                                   let m := (var 0) in
                                                  bite (if_z n)
                                                  (if_z m)
                                                  (bite (if_z m)
                                                     (bfalse)
                                                    (app (app f (app (ppi2 n) triv)) (app (ppi2 m) triv)))
                                                  ))).
 Definition eq_b: (term obj) := app theta eq_bbc.

Lemma eqb_typed {G}: tr G (oof eq_b (arrow nattp (arrow nattp booltp))).
Admitted.

Lemma eqapp_typed G m n: tr G (oof m nattp) -> tr G (oof n nattp) ->
  tr G (oof (app (app eq_b m) n) booltp). Admitted.

Lemma eqb_P G n m : tr G (oof n nattp) ->
                    tr G (oof m nattp) ->
  tr G (deq (app (app eq_b n) m) btrue booltp) ->
                    tr G (deq n m nattp).
  intros.
Admitted.


Definition eq_wind = wind (lam (* x = 0*)
                             (lam (*x = 1, y= 0*)
                                ( lam
                                    ( (*x = 2, y = 1, z = 0*)
                                      bite x
                                           (lam (*x = 3, y = 2, z = 1, n2 = 0*)
                                              (if_z (var 0))
                                           ) (*first one is zero*)
                                           ( (*first one is nonzero*)
                                             lam
                                               ( (*x = 3, y = 2, z = 1, n2 = 0*)
                                                 bite (if_z (var 0))
                                                      false
                                                      (z * (ppi2 (var 0)) *)
                                               )
                                           )
                                    )
                                )
                             )                           
                          )
