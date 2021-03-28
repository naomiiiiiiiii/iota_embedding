(*rules*)
Require Import Tactics Sequence source subst_src (*SimpSub*) Promote Hygiene ContextHygiene Equivalence.

Require Import Defined.

Inductive tr : @context False -> @judgement False -> Type :=

(* Hypotheses *)

| tr_hyp_tm :
    forall G i a,
      index i G (hyp_tm a)
      -> tr G (deq (var i) (var i) (subst_src.subst (subst_src.sh (S i)) a)).
  
| tr_hyp_tp :
    forall G i,
      index i G hyp_tp
      -> tr G (deqtype (var i) (var i)).
(*subst wants the syntax term
 not the target term*)
