From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules.

Definition theta : (term False) :=
  lam(
      lam (
 app (var 1) (app (app (var 2) (var 2)) (var 1))
        )
    ).

Definition combt A: (term False) := rec (
                                    pi (fut (var 1)) (subst (sh 1) A)).
(*probably have to shift A cuz its going under a binder*)

Definition Yc A: (term False) = lam ((*f := 1*)
                   app
               (lam (fut (comb A)) (
                                    next ( (comb A)) x
                ([x']
                app f (next (app x' x)))
                ))
                (next
               (lam (later (comb A)) ([x]
                                    letnext (later (comb A)) x
                ([x']
                   app f (next (app x' x)))
                 )))
).

