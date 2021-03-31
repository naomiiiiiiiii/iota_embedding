(*rules*)
Require Import Tactics Sequence source subst_src (*SimpSub*).

Require Import Defined.

Definition off M A: (@judgement False) := deq M M A.

Inductive tr : @context False -> @judgement False -> Type :=

(* Hypotheses *)

| tr_hyp_tm :
    forall G i a,
      index i G (hyp_tm a)
      -> tr G (off (var i) (subst_src.subst (subst_src.sh (S i)) a))
| tr_z: forall G, tr G (off z_m nattp_m)
| tr_succ: forall G M,
    tr G (off M nattp_m) ->
    tr G (off (succ_m M) nattp_m)
| tr_natform: forall G, tr G (typ nattp_m)
| tr_triv: forall G, tr G (off triv_m unittp_m)
| tr_null: forall G, tr G (typ unittp_m)
| tr_arrow_m_formation :
    forall G a b,
      tr G (typ a)
      -> tr G (typ b)
      -> tr G (typ (arrow_m a b))
| tr_arrow_m_intro :
    forall G a b m,
      tr G (typ a)
      -> tr (cons (hyp_tm a) G) (off m b)
      -> tr G (off (lam_m m) (arrow_m a b))
| tr_arrow_m_elim :
    forall G a b m p,
      tr G (off m (arrow_m a b))
      -> tr G (off p a)
      -> tr G (off (app_m m p) b)
| tr_comp: forall G A, tr G (typ A) -> tr G (typ (comp_m A))
| tr_ret: forall G E A, tr G (off E A) -> tr G (off (ret_m E) (comp_m A))
| tr_bind: forall G A B V E,
    tr G (off V (comp_m A)) -> 
    tr (cons (hyp_tm A) G) (off E B) ->
    tr G (off (bind_m V E) B)
|tr_reftp: forall G A, tr G (typ A) -> tr G (typ (reftp_m A))
| tr_ref: forall G E A, tr G (off E A) -> tr G (off (ref_m E) (comp_m (reftp_m A)))
| tr_asgn: forall G R V T, tr G (off V T) ->
                      tr G (off R (comp_m (reftp_m T))) ->
                      tr G (off (asgn_m R V) (comp_m unittp_m)).
(*subst wants the syntax term
 not the target term*)
