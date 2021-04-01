From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.
From istari Require Import source subst_src rules_src help.

Inductive trans_type: (source.term False) -> (Syntax.term False) -> Type :=
  tt_ref: forall A As, trans_type A As -> trans_type (reftp_m A) (make_ref As).

Inductive trans
