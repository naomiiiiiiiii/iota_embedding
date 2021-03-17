From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules.

Definition theta : (term False) :=
  lam(
      lam (
 app (var 1) (app (app (var 2) (var 2)) (var 1))
        )
    ).
