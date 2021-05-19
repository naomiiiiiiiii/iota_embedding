
From Coq Require Import Lists.List.
From istari Require Import Tactics Sequence source subst_src rules_src basic_types
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.


(*he has arrow, you could be using arrow instead of pi if it makes it easier*)

Definition plus L R : (term False) := sigma booltp (bite (var 0) (subst (sh 1) L)
                                           (subst (sh 1) R) ).
Definition inl L: term False := ppair btrue L.
Definition inr R: term False := ppair bfalse R.

Definition opt w: term False := sigma booltp (bite (var 0) w unittp).

(*recursion*)

Definition combt A: (term False) := rec (
                                    pi (fut (var 0)) (subst (sh 1) A)).
(*probably have to shift A cuz its going under a binder*)

Definition Yc: (term False) := lam ((*f := 0*)
                   app
                     (lam ( (*f := 1, x := 0*)
                          let f := (var 1) in
                          let x := (var 0) in
                app f (next (app (prev x) x))
                        )
                     )
                (next
                   (lam (*f := 1, x := 0*)
                      (
                          let f := (var 1) in
                          let x := (var 0) in
                   app f (next (app (prev x) x))
                      )
                ))
).

Definition laters A : term False := rec (plus (shift 1 A)  (fut (var 0))).
  (*notice similarity w type of nat*)

Definition ret: term False := lam (inl (var 0)).

Definition ret_t x := app ret x.

Definition bind : term False := app Yc
   (lam   ( (*f := 0*)
      lam ( (*f:= 1, x := 0*)
          lam ( (*f:= 2, x := 1, g := 0*)
              let f := (var 2) in
              let x := (var 1) in
              let g := (var 0) in
              let y := ppi2 x in
         bite (ppi1 x) (app g y)
              (let y' := prev y in
               let f' := prev f in
               inr (next (app (app f' y') g))) )
        ))).

Definition make_bind E1 E2 := app (app bind E1) E2.
(*worlds*)


Definition preworld: (term False) := rec 
                                   (arrow nattp (karrow (fut (var 0)) (arrow (fut nattp) U0))).

Definition world: (term False) := sigma preworld nattp.

Definition len w: (term False) := ppi2 w.

Definition if_z (n: term False): (term False) := ppi1 n.

Definition minusbc: (term False) := lam
                         (
                           (*f := 0*)
                           lam ( (*f:= 1, n := 0*)
                               lam ((*f := 2, n:= 1, m := 0*)
                                   let f := (var 2) in
                                   let n := (var 1) in
                                   let m := (var 0) in
                                                  bite (if_z n)
                                                  (m)
                                                  (bite (if_z m)
                                                     (n)
                                                    (app (app f (app (ppi2 n) triv)) (app (ppi2 m) triv)))
                                                  ))).
 Definition minus: (term False) := app theta minusbc.

 Definition plusbc: (term False) := lam
                         (
                           (*f := 0*)
                           lam ( (*f:= 1, n := 0*)
                               lam ((*f := 2, n:= 1, m := 0*)
                                   let f := (var 2) in
                                   let n := (var 1) in
                                   let m := (var 0) in
                                                  bite (if_z m)
                                                     (n)
                                                    (app (app f n) (app (ppi2 m) triv))
                                                  ))).
 Definition plus_n: (term False) := app theta plusbc.

Definition lt_b m n := if_z (app (app minus m) (nsucc n)).

(*uses default value of w2*)

(*Definition cons w1 x :=
  pend w1 (ppair (lam (let n := var 0 in bite (if_z n) x default_f)) one).*)

Definition cons_w w1 x :=
  ppair (lam ( (*n := 0*)
             let n := var 0 in
             bite (lt_b n (len w1))
                  (app (ppi1 w1) n)
                  x
        ))
        (nsucc (len w1)).
(*default value after s(len w1) is x*
ie uses default value of w2*)

(*start here*)


Definition app3 w i u l : term False :=
 app (app (app w i) u) l.

 Definition subseq: (term False) -> (term False) -> (term False) :=
   fun W1 => fun W2 =>
       app  (app   (lam (lam
                   (let W1 := var 0 in
                   let W2 := var 1 in
            let w1 := ppi1  W1 in
            let w2 := ppi1 W2 in
            let l1 := ppi2 W1 in
            let l2 := ppi2 W2 in
            prod (leq_t l1 l2)
                 (all nzero (fut preworld)
                 (*u = 0*)
                 (pi (fut nattp) (*u = 1, l = 0*)
                     (pi (nattp) (*u = 2, l = 1, i = 0*)(
                           pi (leq_t (var 0) (subst (sh 3) l1))
                              ( (*u = 3, l = 2, i = 1, m = 0*)
                          eqtype (app3 (subst (sh 4) w1)                                         (var 1) (var 3) (var 2))
                          (app3 (subst (sh 4) w2) (var 1) (var 3) (var 2))
                              )
                                                   )
                                           )

                 ))))) W1) W2.

 Definition nth w n: term False := app (ppi1 w) n.


Lemma subst_pw: forall s,
    subst s preworld = preworld.
intros. unfold preworld. unfold nattp. auto. Qed.
Hint Rewrite subst_pw.


Lemma subst_world: forall s,
    subst s world = world.
intros. unfold world. unfold preworld. unfold nattp. auto. Qed.  
Hint Rewrite subst_world.

Lemma subst_nat: forall s,
    @subst False s nattp = nattp.
  intros. unfold nattp. auto. Qed.

Hint Rewrite subst_nat.

Lemma subst_nzero: forall s,
    @subst False s nzero = nzero.
  intros. unfold nzero. auto. Qed.
Hint Rewrite subst_nzero.

Lemma subst_leqtp: forall s,
    @subst False s (leqtp) = leqtp.
  intros. unfold leqtp. unfold wind. unfold theta.
  repeat rewrite subst_app.
  repeat rewrite subst_lam. simpsub. simpl.
  repeat rewrite project_dot_succ.
  rewrite project_dot_zero. auto. Qed.
Hint Rewrite subst_leqtp.

Lemma subst_bind: forall s m1 m2,
    @subst False s (make_bind m1 m2) = make_bind (@subst False s m1) (@subst False s m2).
  intros. auto. Qed.


Lemma subst_lttp: forall s,
    @subst False s (lttp) = lttp.
  intros. unfold lttp.
  simpsub. rewrite subst_leqtp. unfold nsucc. simpsub. simpl.
  rewrite subst_leqtp. auto. Qed.
Hint Rewrite subst_leqtp.

Lemma subst_leq: forall s n1 n2,
    @subst False s (leq_t n1 n2) =  leq_t (subst s n1) (subst s n2).
  intros. unfold leq_t.  repeat rewrite subst_app. rewrite subst_leqtp. auto. 
Qed.

Lemma subst_lt: forall s n1 n2,
    subst s (app (app lttp n1) n2) = (app (app lttp (subst s n1)) (@subst False s n2)).
  intros. repeat rewrite subst_app. rewrite subst_lttp. auto. Qed. 

Lemma subst_subseq: forall W1 W2 s,
       (subst s
              (subseq W1 W2)) = subseq (subst s W1)
                                       (subst s W2).
  intros. unfold subseq. repeat rewrite subst_app. auto.
Qed.



 Definition getstore w v: (term False) := pi nattp ((*i = 0*)
                                           let i := var 0 in
                                           (app (app (shift 1 w) i) (next (shift 1 v)))
                                         ).

 Definition store: (term False) -> (term False) := fun W => app (lam (
                                            let w := ppi1 (var 0) in
                                            let n := ppi2 (var 0) in
                                            all nzero preworld ( (*u := var 0*)
                                                  pi 
                                                    (subseq (var 1) (ppair (var 0) (shift 1 n) ))
                                                    (*u :=  var 1, m := var 0*)
                                                     (getstore (shift 2 w) (var 1))))) W.
Lemma subst_U0: forall s,
    (@subst False s (univ nzero)) = univ nzero.
  auto. Qed.


Lemma subst_store: forall W s, (subst s (store W)) = store (subst s W).
  intros. unfold store. auto. Qed.
Opaque store.

Lemma subst_laters: forall s A, (subst s (laters A)) = (laters (subst s A)).
  intros. unfold laters. unfold plus. rewrite subst_rec. rewrite subst_sigma.
  rewrite subst_booltp. rewrite subst_bite. simpsub. simpl.
  repeat rewrite <- subst_sh_shift. simpsub. auto. Qed.

Lemma subst_nth: forall s m1 m2, (subst s (nth m1 m2)) = (nth (subst s m1) (subst s m2)). intros. unfold nth. simpsub. auto. Qed.

Opaque laters.
Opaque preworld.
Opaque U0.
Opaque subseq.
Opaque leqtp.
Opaque nzero.
Opaque nattp.
Opaque world.
Opaque nth.

Hint Rewrite subst_U0 : ssub1.
Hint Rewrite subst_subseq: ssub1.
Hint Rewrite subst_leq: ssub1.
Hint Rewrite subst_leqtp: ssub1.
Hint Rewrite subst_lttp: ssub1.
Hint Rewrite subst_lt: ssub1.
Hint Rewrite subst_nzero: ssub1.
Hint Rewrite subst_nat: ssub1.
Hint Rewrite subst_world: ssub1.
Hint Rewrite subst_pw: ssub1.
Hint Rewrite subst_world: ssub1.
Hint Rewrite subst_nth: ssub1.

Ltac simpsub1 :=
  autorewrite with ssub1.



 Definition make_subseq: term False := ppair triv (lam (lam (lam triv)) ).

 (*M o M'*)

 Lemma compose_sub_works : forall (M M' U1 U2 U3: term False) (G: context),
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof make_subseq 
                                    (subseq U1 U3)).
Admitted.

 (*getstore w v = *(w/v)*)

 (*nats*)
(*mysterious error Definition if_z (n: term False) := ppi1 n. *)



(*start here get rid of vacuous cases w program module*)
 Definition move (A: source.term): term False :=
   match A with
     nattp_m => lam (lam (var 1))
   | arrow_m _ _ =>
lam ( (*m0 := 0*)
lam ( lam (
       lam ( (*m0:= 3, f := 2, l := 1, m:= 0*)
           lam (*m0:= 4, f := 3, l := 2 m:= 1 x := 0*)
             ( (*let m := var 3 in*)
               let f := var 3 in
               let l := var 2 in
             let x := var 0 in
                           app (app (app f l) make_subseq) x (*compose_sub m m0*)
  )))))
     | comp_m _ => lam (lam (* m0= 1, c:= 0,*) ( lam (
                           lam (*m0 = 3, c:= 2, l = 1, m := 0*)
                             (lam (*m0 = 4, c:= 3, l = 2, m := 1, s := 0*)
                                ( 
                                  let c:= var 3 in
                                  let l:= var 2 in
                                let s := var 0 in
                                app (app (app c l) make_subseq) s
                                (*compose_sub m m0*)
                             )
                         ))))
     | reftp_m _ => lam (lam (*R := 0*)
                          (let i := ppi1 (var 0) in
                           ppair i (ppair triv (lam triv))
                          ))
     | unittp_m  => lam (lam (var 1))
     | _ => triv (*not a type operator, error case*)
end.
 Definition move_app A m x :=
   app (app (move A) m) x.

 Fixpoint move_gamma (G: source.context) (m: term False) (e: Syntax.term False) :=
   match G with
     nil => e
   | b::bs => move_gamma bs m (subst ( dot (move_app b m (var 0)) 
                                                 id) e)

     (*assuming variables are stored in context with 0 first
      DONT need the counter cuz all the other variables get moved down a slot with the
      cons subtitution*)
   end.

Opaque app.
Lemma aaa: (move_gamma (cons nattp_m (cons unittp_m nil)) triv (var 0) ) = unittp.
  simpl.




