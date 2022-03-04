(*rules*)
Require Import Tactics Sequence source subst_src (*SimpSub*).

Require Import Defined.


Inductive typ: term -> Prop :=
  nattyp : typ nattp_m
| arrowtyp : forall A1 A2, typ A1 -> typ A2 -> typ (arrow_m A1 A2)
| reftyp: forall A, typ A -> typ (reftp_m A)
| comptyp: forall A, typ A -> typ (comp_m A)
| compunit : typ unittp_m.


Inductive of_m : context -> term -> term -> Type :=

(* Hypotheses *)

| of_m_hyp_tm :
    forall G i a,
      typ a ->
      index i G a ->
      of_m G  (var i) a
| of_m_z: forall G, of_m G z_m nattp_m
| of_m_succ: forall G M,
    of_m G M nattp_m ->
    of_m G  (succ_m M) nattp_m
| of_m_arrow_m_inof_mo :
    forall G a b m,
      typ a
      -> of_m (cons a G) m b
      -> of_m G (lam_m m) (arrow_m a b)
| of_m_arrow_m_elim :
    forall G a b m p,
      of_m G m (arrow_m a b)
      -> of_m G p a
      -> of_m G (app_m m p) b
| of_m_ret: forall G E A, of_m G E A -> of_m G (ret_m E) (comp_m A)
| of_m_bind: forall G A B V E,
    typ A ->
    of_m G V (comp_m A) -> 
    of_m (cons A G) E (comp_m B) ->
    of_m G (bind_m V E) (comp_m B)
| of_m_ref: forall G E A, of_m G E A -> of_m G (ref_m E) (comp_m (reftp_m A))
| of_m_asgn: forall G R V T, of_m G V T ->
                      of_m G R (reftp_m T) ->
                      of_m G (asgn_m R V) (comp_m unittp_m)
| of_m_deref : forall G R T,
    of_m G R (reftp_m T) ->
    of_m G (deref_m R) (comp_m T) 
| of_m_triv: forall G, of_m G triv_m unittp_m.
