(*rules*)
Require Import Tactics Sequence source subst_src (*SimpSub*).

Require Import Defined.

Definition oof_m M A: (@judgement False) := deq M M A.

Inductive tr : @context False -> @judgement False -> Type :=

(* Hypotheses *)

| tr_hyp_tm :
    forall G i a,
      index i G (hyp_tm a)
      -> tr G (oof_m (var i) (subst_src.subst (subst_src.sh (S i)) a))
| tr_z: forall G, tr G (oof_m z_m nattp_m)
| tr_succ: forall G M,
    tr G (oof_m M nattp_m) ->
    tr G (oof_m (succ_m M) nattp_m)
| tr_natform: forall G, tr G (typ nattp_m)
| tr_triv: forall G, tr G (oof_m triv_m unittp_m)
| tr_null: forall G, tr G (typ unittp_m)
| tr_arrow_m_formation :
    forall G a b,
      tr G (typ a)
      -> tr G (typ b)
      -> tr G (typ (arrow_m a b))
| tr_arrow_m_intro :
    forall G a b m,
      tr G (typ a)
      -> tr (cons (hyp_tm a) G) (oof_m m b)
      -> tr G (oof_m (lam_m m) (arrow_m a b))
| tr_arrow_m_elim :
    forall G a b m p,
      tr G (oof_m m (arrow_m a b))
      -> tr G (oof_m p a)
      -> tr G (oof_m (app_m m p) b)
| tr_comp: forall G A, tr G (typ A) -> tr G (typ (comp_m A))
| tr_ret: forall G E A, tr G (oof_m E A) -> tr G (oof_m (ret_m E) (comp_m A))
| tr_bind: forall G A B V E,
    tr G (oof_m V (comp_m A)) -> 
    tr (cons (hyp_tm A) G) (oof_m E B) ->
    tr G (oof_m (bind_m V E) B)
|tr_reftp: forall G A, tr G (typ A) -> tr G (typ (reftp_m A))
| tr_ref: forall G E A, tr G (oof_m E A) -> tr G (oof_m (ref_m E) (comp_m (reftp_m A)))
| tr_asgn: forall G R V T, tr G (oof_m V T) ->
                      tr G (oof_m R (comp_m (reftp_m T))) ->
                      tr G (oof_m (asgn_m R V) (comp_m unittp_m)).
