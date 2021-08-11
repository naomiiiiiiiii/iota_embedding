Require Import Program.Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences Rules Defined.

Definition hctx G := @hygiene False (@ctxpred False G).

Transparent hctx.

Require Import lib.

Lemma under_op (G : @context False) : hincl (fun i => (i < length G)%coq_nat)
                         (fun j : nat => 
     (j < 0)%coq_nat \/
     (j >= 0)%coq_nat /\
     ((j - 0)%coq_nat < (length G))%coq_nat ).
  move => i Hi.  right. split; auto.
  (*Hint Rewrite <- minus_n_O : test.
autorewrite with test. works
but autorewrite with natlib loops?*)
  nat_rewrite. assumption.
Qed.

Lemma under_binder (G : @context False) x : hincl (fun i => (i < length (x :: G))%coq_nat)
                         (fun j : nat => 
     (j < 1)%coq_nat \/
     (j >= 1)%coq_nat /\
     ((j - 1)%coq_nat < (length G))%coq_nat ).
  move => i Hi. destruct (i < 1) eqn: Hbool.
  left. apply/ltP: Hbool.
  right. assert (0 < i). move/negbT: Hbool. rewrite - leqNgt. apply.
  split. apply/leP. assumption.
  apply/ltP. rewrite minusE.
  Search (?n.-1 < ?m = (?n <= ?m)). rewrite ltn_subLR.
  move/ltP: Hi. auto. assumption.
Qed.
Lemma hygiene_pi G m1 m2: (hctx G) m1 ->
                               (hctx ((hyp_tm m1) :: G)) m2 ->
                               (hctx G) (pi m1 m2).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H1. repeat constructor.
  apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_karrow G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (karrow m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_arrow G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (arrow m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.



Lemma hygiene_lam G m: 
                               (hctx ((hyp_tp) :: G)) m ->
                               (hctx G) (lam m).
  unfold hctx. rewrite ! ctxpred_length. move => H1. repeat constructor.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_app G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (app m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_fut G m1: (hctx G) m1 ->
                               (hctx G) (fut m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_next G m1: (hctx G) m1 ->
                               (hctx G) (next m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_prev G m1: (hctx G) m1 ->
                               (hctx G) (prev m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_rec G m: (hctx (hyp_tp :: G)) m -> (hctx G (rec m)).
  unfold hctx. rewrite ! ctxpred_length. move => H1. repeat constructor.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1. Qed.

Lemma hygiene_triv G: (hctx G triv). repeat constructor. Qed.

Lemma hygiene_eqtype G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (eqtype m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_all G i k m: (hctx G) i -> (hctx G) k ->
                               (hctx ((hyp_tm k) :: G)) m ->
                               (hctx G) (all i k m).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H00 H1.
  repeat constructor; try (apply (hygiene_weaken _ _ _ _ (under_op _)); assumption).
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_exist G i k m: (hctx G) i -> (hctx G) k ->
                               (hctx ((hyp_tm k) :: G)) m ->
                               (hctx G) (exist i k m).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H00 H1.
  repeat constructor; try (apply (hygiene_weaken _ _ _ _ (under_op _)); assumption).
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_voidtp G: (hctx G voidtp). repeat constructor. Qed.

Lemma hygiene_unittp G: (hctx G unittp). repeat constructor. Qed.
Lemma hygiene_booltp G: (hctx G booltp). repeat constructor. Qed.
Lemma hygiene_btrue G: (hctx G btrue). repeat constructor. Qed.
Lemma hygiene_bfalse G: (hctx G bfalse). repeat constructor. Qed.

Lemma hygiene_bite G m1 m2 m3: (hctx G) m1 -> (hctx G) m2 ->
                               (hctx G) m3 ->
                               (hctx G) (bite m1 m2 m3).
  unfold hctx. rewrite ! ctxpred_length. 
  repeat constructor; try (apply (hygiene_weaken _ _ _ _ (under_op _)); assumption). Qed.

Lemma hygiene_prod G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (prod m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_sigma G m1 m2: (hctx G) m1 ->
                               (hctx ((hyp_tm m1) :: G)) m2 ->
                               (hctx G) (sigma m1 m2).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H1. repeat constructor.
  apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.

Lemma hygiene_ppair G m1 m2: (hctx G) m1 ->
                               (hctx G) m2 ->
                               (hctx G) (ppair m1 m2).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_ppi1 G m1: (hctx G) m1 ->
                               (hctx G) (ppi1 m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.
Lemma hygiene_ppi2 G m1: (hctx G) m1 ->
                               (hctx G) (ppi2 m1).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Lemma hygiene_wt G m1 m2: (hctx G) m1 ->
                               (hctx ((hyp_tm m1) :: G)) m2 ->
                               (hctx G) (wt m1 m2).
  unfold hctx. rewrite ! ctxpred_length. move => H0 H1. repeat constructor.
  apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
  eapply (hygiene_weaken _ _ _ _ (under_binder _ _)). apply H1.  
Qed.


Lemma hygiene0 G x: (hctx (x::G) (var 0)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene_hint G x y: (hctx (x::y::G) (var 1)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene2 G x y z: (hctx (z::x::y::G) (var 2)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene3 G x y z a: (hctx (a::z::x::y::G) (var 3)).
  unfold hctx. rewrite ! ctxpred_length. constructor.
  simpl. apply/ltP. auto. Qed.

Lemma hygiene_univ G m: (hctx G) m ->
                               (hctx G) (univ m).
    unfold hctx. rewrite ctxpred_length.  repeat constructor; apply (hygiene_weaken _ _ _ _ (under_op _)); assumption.
Qed.

Hint Resolve hygiene_pi hygiene_karrow hygiene_arrow hygiene_lam hygiene_app
     hygiene_fut hygiene_prev hygiene_next hygiene_rec hygiene_triv hygiene_eqtype
     hygiene_all hygiene_exist hygiene_voidtp hygiene_unittp hygiene_booltp
     hygiene_bfalse hygiene_btrue hygiene_bite hygiene_prod hygiene_sigma hygiene_ppair
     hygiene_ppi1 hygiene_ppi2 hygiene_wt hygiene0 hygiene_hint hygiene2 hygiene3 hygiene_univ: hygiene_hint.

Ltac hyg_solv := eauto 50 with hygiene_hint.

Lemma hygiene_makesubseq G: (hctx G) make_subseq.
unfold make_subseq. hyg_solv. Qed.

Hint Resolve hygiene_makesubseq: hygiene_hint.

Lemma hygiene_moveapp G A m v: (hctx G) m ->
                               (hctx G) v ->
                               (hctx G) (move_app A m v).
  unfold move_app. move => Hm Hv.
  induction A; simpl; hyg_solv.
Qed.

Lemma hygiene_nat G: (hctx G) nattp.
  intros. unfold nattp. hyg_solv. Qed.

Lemma hygiene_nzero: forall G, (hctx G) nzero.
   unfold nzero. hyg_solv. Qed.
Hint Resolve hygiene_nat hygiene_nzero: hygiene_hint.

Lemma hygiene_U0: forall G, (hctx G) (univ nzero).
  intros. unfold U0. hyg_solv.
Qed.

Hint Resolve hygiene_U0: hygiene_hint.

Lemma hygiene_pw G: (hctx G) preworld. unfold preworld. hyg_solv.
Qed.

Hint Resolve hygiene_pw : hygiene_hint.

Lemma hygiene_theta G : (hctx G) theta.
  unfold theta. hyg_solv. Qed.
Hint Resolve hygiene_theta: hygiene_hint.

Lemma hygiene_minus G : (hctx G) minus.
  unfold minus. unfold minusbc. hyg_solv. Qed.
Hint Resolve hygiene_minus: hygiene_hint.

Lemma hygiene_nsucc G n: (hctx G) n -> (hctx G) (nsucc n).
  intros. unfold nsucc. hyg_solv. Qed.

Lemma hygiene_ltb G : (hctx G) lt_b.
  intros. unfold lt_b. unfold if_z. hyg_solv. Qed.
Hint Resolve hygiene_ltb: hygiene_hint.

Lemma hygiene_world: forall G, (hctx G) world.
intros. unfold world. unfold preworld. unfold nattp. auto. Qed.  
Hint Resolve hygiene_world: hygiene_hint.


Hint Resolve hygiene_nat: hygiene_hint.


Lemma hygiene_leqtp: forall G, (hctx G) leqtp
  intros. unfold leqtp. unfold wind. unfold theta.
  repeat rewrite hygiene_app.
  repeat rewrite hygiene_lam. hyg_solv. simpl.
  repeat rewrite project_dot_succ.
  rewrite project_dot_zero. auto. Qed.
Hint Resolve hygiene_leqtp: hygiene_hint.

Lemma hygiene_bind: forall G, (hctx G) make_bind (@hygiene False s m1) (@hygiene False s m2)
  intros. auto. Qed.


Lemma hygiene_lttp: forall G, (hctx G) lttp
  intros. unfold lttp.
  hyg_solv. rewrite hygiene_leqtp. unfold nsucc. hyg_solv. simpl.
  rewrite hygiene_leqtp. auto. Qed.
Hint Resolve hygiene_leqtp: hygiene_hint.

Lemma hygiene_leq: forall s n1 n2,
    @hygiene False s (leq_t n1 n2) =  leq_t (hygiene s n1) (hygiene s n2).
  intros. unfold leq_t.  repeat rewrite hygiene_app. auto. 
Qed.

Lemma hygiene_lt: forall s n1 n2,
    hygiene s (lt_t n1 n2) = lt_t (hygiene s n1) (@hygiene False s n2).
  intros. repeat rewrite hygiene_app. rewrite hygiene_lttp. auto. Qed. 

Lemma hygiene_subseq: forall W1 W2 s,
       (hygiene s
              (subseq W1 W2)) = subseq (hygiene s W1)
                                       (hygiene s W2).
  intros. unfold subseq. repeat rewrite hygiene_app. auto.
Qed.



Lemma hygiene_ret: forall G, (hctx G) ret
  intros. unfold ret. unfold inl. hyg_solv. Qed.

Lemma hygiene_ret_a: forall s m, hygiene s (ret_a m) = ret_a (hygiene s m).
  intros. unfold ret_a. unfold ret. unfold inl. hyg_solv. Qed.

Lemma hygiene_laters: forall s A, (hygiene s (laters A)) = (laters (hygiene s A)).
  intros. unfold laters. unfold plus. rewrite hygiene_rec. rewrite hygiene_sigma.
  rewrite hygiene_booltp. rewrite hygiene_bite. hyg_solv. simpl.
  repeat rewrite <- hygiene_sh_shift. hyg_solv. Qed.

Lemma hygiene_nth: forall s m1 m2, (hygiene s (nth m1 m2)) = (nth (hygiene s m1) (hygiene s m2)). intros. unfold nth. hyg_solv. Qed.

Lemma hygiene_make_subseq: forall s, (hygiene s make_subseq) = make_subseq.
  intros. unfold make_subseq. hyg_solv. Qed.

Lemma hygiene_picomp1: forall s m, (hygiene s (picomp1 m)) = picomp1 (hygiene s m).
  intros. unfold picomp1. hyg_solv. Qed.

Lemma hygiene_picomp2: forall s m, (hygiene s (picomp2 m)) = picomp2 (hygiene s m).
  intros. unfold picomp2. hyg_solv. Qed.

Lemma hygiene_picomp3: forall s m, (hygiene s (picomp3 m)) = picomp3 (hygiene s m).
  intros. unfold picomp3. hyg_solv. Qed.

Lemma hygiene_picomp4: forall s m, (hygiene s (picomp4 m)) = picomp4 (hygiene s m).
  intros. unfold picomp4. hyg_solv. Qed.

Hint Resolve hygiene_U0 hygiene_ret hygiene_ret_a hygiene_subseq hygiene_leq hygiene_leq
     hygiene_lttp hygiene_lt hygiene_nzero hygiene_nat hygiene_world hygiene_pw hygiene_world
     hygiene_nth hygiene_laters hygiene_picomp1 hygiene_picomp2 hygiene_picomp4
     hygiene_picomp3 hygiene_make_subseq hygiene_theta hygiene_minus hygiene_ltb: hygiene_hint.

Hint Resolve <- hygiene_sh_shift: hygiene_hint.

Hint Unfold hygiene_hint: hygiene_hint.


Lemma hygiene_store: forall w l s, hygiene s (store w l) = store (hygiene s w) (hygiene s l).
  intros. unfold store. unfold gettype. hyg_solv_big. auto. Qed.

Hint Resolve hygiene_store: hygiene_hint.



Lemma hygiene_moveapp s A m1 m2 : (hygiene s (move_app A m1 m2)) =
                              move_app A (hygiene s m1) (hygiene s m2).
   unfold move_app. hyg_solv_big. auto. Qed.

Hint Resolve hygiene_nsucc hygiene_moveapp: hygiene_hint.
