Require Import Program.Equality Ring Lia Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import source subst_src rules_src help subst_help basic_types.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*more useful inference rules*)

Lemma tr_arrow_elim: forall G a b m n p q,
    tr G (deqtype a a) ->
    tr G (deqtype b b) ->
      tr G (deq m n (arrow a b))
      -> tr G (deq p q a) 
      -> tr G (deq (app m p) (app n q) b).
intros. 
suffices: (subst1 p (subst sh1 b)) = b. move => Heq.
rewrite - Heq.
eapply (tr_pi_elim _ a); try assumption.
eapply tr_eqtype_convert; try apply tr_arrow_pi_equal; assumption.
simpsub. auto. Qed.

Lemma tr_arrow_intro: forall G a b m n,
    tr G (deqtype a a) ->
      tr G (deqtype b b)
      -> tr (cons (hyp_tm a) G) (deq m n (subst sh1 b))
      -> tr G (deq (lam m) (lam n) (arrow a b) ).
intros. eapply tr_eqtype_convert.
apply tr_eqtype_symmetry. apply tr_arrow_pi_equal; try assumption.
eapply tr_pi_intro; try assumption. Qed.

Lemma tr_karrow_elim: forall G a b m n p q,
    tr G (deqtype a a) ->
    tr G (deqtype b b) ->
      tr G (deq m n (karrow a b))
      -> tr G (deq p q a) 
      -> tr G (deq (app m p) (app n q) b).
  intros. apply (tr_arrow_elim _ a); try assumption.
  eapply tr_eqtype_convert. apply tr_eqtype_symmetry.
  apply tr_arrow_karrow_equal; assumption.
  assumption. Qed.

Lemma kind_type: forall {G K i},
    tr G (deq K K (kuniv i)) -> tr G (deqtype K K).
  move => G K i H. eapply tr_formation_weaken.
  eapply tr_kuniv_weaken. apply H. Qed.

Lemma tr_prod_intro G A B M M' N N' :
    tr G (deq M M' A) -> tr G (deq N N' B) ->
    tr G (deq (ppair M N) (ppair M' N') (prod A B)).
  intros H0 H1.
  pose proof (tr_inhabitation_formation _#4 H0) as Ha.
  pose proof (tr_inhabitation_formation _#4 H1) as Hb.
  eapply tr_eqtype_convert.
  apply tr_eqtype_symmetry. apply tr_prod_sigma_equal; try assumption.
  eapply tr_sigma_intro; try assumption. simpsub. assumption.
  match goal with |- tr ?G' ?J => change J with (substj (under 0 sh1)
                                                    (deqtype B B));
                                  change G' with (nil ++ G') end.
  change nil with (@substctx Rules.obj sh1 nil).
  apply tr_weakening. assumption.
  Qed.

Lemma tr_booltp_eta_hyp0 :
    forall G m n p q a,
      tr G (deq m n (subst1 btrue a))
      -> tr G (deq p q (subst1 bfalse a))
      -> tr ((hyp_tm booltp)::G) (deq 
              (bite (var 0) 
                 (subst sh1 m)
                 (subst sh1 p))
              (bite (var 0)
                 (subst sh1 n) 
                 (subst sh1 q) )
              a).
  intros. rewrite - (cat0s ((hyp_tm booltp)::G)).
  change (sh1) with (@ under obj 0 sh1).
  change 0 with (size ([::]: @context False)).
  apply tr_booltp_eta_hyp; simpl; assumption.
Qed. 

Lemma nat_U0: forall G,
    tr G (oof nattp U0). Admitted.
Hint Resolve nat_U0. 

Lemma nat_type: forall G,
      tr G (deqtype nattp nattp). Admitted.
Hint Resolve nat_type. 

Lemma tr_weakening_appends: forall G1 G2 G3 J1 J2 t J1' J2' t',
    tr G1 (deq J1 J2 t) ->
    J1' = (shift (size G2) J1) ->
    J2' = (shift (size G2) J2) ->
    t' = (shift (size G2) t) ->
    G3 = G2 ++ G1 ->
      tr G3 (deq J1' J2' t').
 move => G1 G2.  induction G2; intros.
 -  simpl. subst. repeat rewrite - subst_sh_shift. simpsub. assumption.
 -
  suffices: (tr (substctx sh1 [::] ++ cons a (G2 ++ G1))
                (substj (under (length [::]) sh1)
                        (substj (sh (size G2)) (deq J1 J2 t)))).
  move => Hdone.
  simpl in Hdone. subst.
  rewrite (size_ncons 1).
  rewrite - plusE. 
  repeat rewrite subst_sh_shift.
  repeat rewrite - shift_sum.
  repeat rewrite subst_sh_shift in Hdone.
  rewrite cat_cons.
 apply (Hdone False). 
 intros.
 eapply tr_weakening.
 simpl. repeat rewrite subst_sh_shift. eapply IHG2; try reflexivity. assumption.
Qed.

 Lemma tr_weakening_append: forall (G1: context) G2 J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (G2 ++ G1) (
                       (deq (shift (size G2) J1)
                            (shift (size G2) J2)
                            (shift (size G2) t))).
   move =>> H. eapply tr_weakening_appends; try apply H; try reflexivity.
   Qed.

 Lemma tr_weakening_appendt: forall (G1: context) G2 J1 J2,
      tr G1 (deqtype J1 J2) ->
      tr (G2 ++ G1) (deqtype (shift (size G2) J1)
                            (shift (size G2) J2)).
Admitted.

 Lemma tr_weakening_append1: forall G1 x J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (x::G1) (
                       (deq (shift 1 J1)
                            (shift 1 J2)
                            (shift 1 t))).
Admitted.

 Lemma tr_weakening_append2: forall G1 x y J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (x::y::G1) (
                       (deq (shift 2 J1)
                            (shift 2 J2)
                            (shift 2 t))).
Admitted.

 Lemma tr_weakening_append3: forall G1 x y z J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (x::y::z::G1) (
                       (deq (shift 3 J1)
                            (shift 3 J2)
                            (shift 3 t))).
Admitted.

Lemma tr_weakening_append4: forall G1 x y z a J1 J2 t,
      tr G1 (deq J1 J2 t) ->
      tr (x::y::z::a::G1) (
                       (deq (shift 4 J1)
                            (shift 4 J2)
                            (shift 4 t))).
Admitted.
