(*rules*) 
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
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

(*reduction*)
Inductive val: term -> Prop :=
(*| val_var {i} : val (var i) *) (*can assume terms are closed*)
| val_z : val z_m
| val_succ {n} : val n -> val (succ_m n)
| val_lam {M} : val (lam_m M)
| val_ap {M1 M2} : val M1 -> val M2 -> (forall M3, M1 <> lam_m M3) -> val (app_m M1 M2)
| val_ret {M} : val M -> val (ret_m M)
| val_bind {M1 M2} : val M1 ->
                     (forall M3 M4, M1 <> ret_m M3 /\ M1 <> ref_m M3 /\ M1 <> deref_m M3 /\
                               M1 <> asgn_m M3 M4) -> val (bind_m M1 M2) (*what if M1 is asgn but bind
                                     can't make any steps because M1 is stuck
                                     either ill typed or open, neutral term, dw*)
| val_ref {M} : val M -> val (ref_m M)
| val_deref {M} : val M -> val (deref_m M)
| val_asgn_m {M1 M2} : val M1 -> val M2 -> val (asgn_m M1 M2)
| val_triv : val triv_m
| val_loc {i} : val (loc_m i).


Definition asgn M i v := set_nth triv_m M i v.
Definition get M i := nth triv_m M i.

                          

Definition store := seq term.             
(*
 karl's reduce is nondeterministic*)
Inductive reduce : (prod store term) -> (prod store term) -> Prop :=
| reduce_ref {e M e' M'}: reduce (M, e) (M', e') ->
  reduce (M, ref_m e) (M', ref_m e')
| reduce_deref {e M e' M'}: reduce (M, e) (M', e') ->
  reduce (M, deref_m e) (M', deref_m e')
| reduce_asgn1 {e1 e2 M e1' M'}: reduce (M, e1) (M', e1') ->
  reduce (M, asgn_m e1 e2) (M', asgn_m e1' e2)
| reduce_asgn2 {v1 e2 M e2' M'}:
    val v1 -> 
    reduce (M, e2) (M', e2') ->
    reduce (M, asgn_m v1 e2) (M', asgn_m v1 e2')
| reduce_bind {e1 e2 M e1' M'}: reduce (M, e1) (M', e1') ->
                                reduce (M, bind_m e1 e2) (M', bind_m e1' e2)
| reduce_ret {e M e' M'}: reduce (M, e) (M', e') ->
                          reduce (M, ret_m e) (M', ret_m e')
| reduce_bindref {v e2 M} : val v ->
                            reduce (M, bind_m (ref_m v) e2)
                                   (rcons M v, subst1 e2 (loc_m (size M)))
| reduce_bindasgn {l v e2 M} : val (asgn_m (loc_m l) v) ->
                               reduce (M, bind_m (asgn_m (loc_m l) v) e2)
                                      (asgn M l v, subst1 triv_m e2)
| reduce_bindderef {l e2 M} : val (deref_m (loc_m l)) ->
                              reduce (M, bind_m (deref_m (loc_m l)) e2)
                                     (M, subst1 (get M l) e2)
| reduce_nat {n n' M M'} : reduce (M, n) (M', n') ->
                           reduce (M, succ_m n) (M', succ_m n')
| reduce_app1 {f arg arg' M M'} : reduce (M, arg) (M', arg') ->
                                  reduce (M, (app_m f arg)) (M', (app_m f arg'))
| reduce_app2 {f f' v M M'} : val v ->
                              reduce (M, f) (M', f') ->
                              reduce (M, (app_m f v)) (M', (app_m f' v))

| reduce_app_beta {v f M M'} :
    val v ->
    val f -> reduce (M, (app_m (lam_m f) v)) (M', (subst1 v f)).

Inductive reduce_star : (prod store term) -> (prod store term) -> Prop :=
| reduce_refl {M e} : reduce_star (M, e) (M, e)
| reduce_step {M e M' e' M'' e''} : reduce_star (M, e) (M', e') ->
                                    reduce (M', e') (M'', e'') ->
                                    reduce_star (M, e) (M'', e'').


(*
Inductive reduce : (prod store term) -> (prod store term) -> Prop :=
| reduce_var {i M} : reduce (M, (var i)) (M, (var i))
| reduce_ref {e M e' M'}: reduce (M, e) (M', e') ->
  reduce (M, ref_m e) (M', ref_m e')
| reduce_deref {e M e' M'}: reduce (M, e) (M', e') ->
  reduce (M, deref_m e) (M', deref_m e')
| reduce_asgn1 {e1 e2 M e1' M'}: reduce (M, e1) (M', e1') ->
  reduce (M, asgn_m e1 e2) (M', asgn_m e1' e2)
| reduce_asgn2 {v1 e2 M e2' M'}:
    reduce (M, v1) (M, v1) -> (*v1 is value...kind of ruins normalization property of language?
                              can't use thsi for v is a value cuz could do
                              (asign v, e2) -> asgn(v, e2) by reduce_asgn1 even if e2
                              is not a value*)
    reduce (M, e2) (M', e2') ->
    reduce (M, asgn_m v1 e2) (M', asgn_m v1 e2')
| reduce_bind {e1 e2 M e1' M'}: reduce (M, e1) (M', e1') ->
                                reduce (M, bind_m e1 e2) (M', bind_m e1' e2)
| reduce_ret {e M e' M'}: reduce (M, e) (M', e') ->
                          reduce (M, ret_m e) (M', ret_m e')
| reduce_bindref {v e2 M} : reduce (M, v) (M, v) ->
                            reduce (M, bind_m (ref_m v) e2)
                                   (rcons M v, subst1 e2 (loc_m (size M)))
                                   | reduce_bindas {l v e2 M} : reduce (M, asgn)
| reduce_app_beta {n n' m M M'} :
    reduce (M, n) (M', n')
    -> reduce (M, (app_m (lam_m m) n)) (M', (subst1 n' m)).
*)
