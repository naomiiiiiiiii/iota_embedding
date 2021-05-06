From Coq.Lists Require Import List.
From istari Require Import source subst_src rules_src help trans.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
Check context.

Theorem one: forall G D e T ebar w1 l1,
    of_m G e T -> tr D (oof (ppair w1 l1) world) ->
    trans e ebar -> 
         tr ((gamma_at G (ppair w1 l1)) ++ D) (app ebar (sh (length G) l1))
            (trans_type T (ppair w1 l1)).
