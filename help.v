(*Shallow embedding of simple constructs from the monadic language into the store-passing logic*)
From Coq Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import Tactics Sequence source subst_src rules_src.
From istari Require Import basic_types Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.



(*small abbreviations that will help us later*)
Definition app3 w i u l : term False :=
 app (app (app w i) u) l.

(*quickly access the nth element of the big tuple in the comp type*)
Definition picomp1 (M: term False) := ppi1 M.
Definition picomp2 (M: term False) := ppi1 (ppi1 (ppi2 M) ). 
Definition picomp3 (M: term False) := ppi2 (ppi1 (ppi2 M)). 
Definition picomp4 (M: term False) := ppi2 (ppi2 M).
(********************************************)



(*useful types*)

Definition plus L R : (term False) := sigma booltp (bite (var 0) (subst (sh 1) L)
                                           (subst (sh 1) R) ).
Definition inl L: term False := ppair btrue L.
Definition inr R: term False := ppair bfalse R.

Definition opt w: term False := sigma booltp (bite (var 0) w unittp).

Definition laters A : term False := rec (plus (shift 1 A) (fut (var 0))).
(*notice similarity w type of nat in logic*)
(********************************************)


(*useful terms*)

(*Unguarded recursion*)
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

(*Computation monad*)
Definition ret: term False := lam (inl (var 0)).

Definition ret_a x := app ret x.

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

(*arithmetic*)

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

(*worlds*)

Definition preworld: (term False) := rec 
                                   (arrow nattp (karrow (fut (var 0)) (arrow (fut nattp) U0))).

Definition world: (term False) := sigma preworld nattp.

Definition len w: (term False) := ppi2 w.

Definition nth w n: term False := app (ppi1 w) n.

(*default value after s(len w1) is x*)
Definition cons_w x w1 :=
  ppair (lam ( (*n := 0*)
             let n := var 0 in
             bite (lt_b n (len w1))
                  (app (ppi1 w1) n)
                  x
        ))
        (nsucc (len w1)).

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
                          eqtype (app3 (subst (sh 4) w1) (var 1) (var 3) (var 2))
                          (app3 (subst (sh 4) w2) (var 1) (var 3) (var 2))
                              )
                                                   )
                                           )

                 ))))) W1) W2.

 Definition make_subseq: term False := ppair triv (lam (lam (lam triv)) ).

 (*transitivity of subseq*)

 Lemma compose_sub_works : forall (M M' U1 U2 U3: term False) (G: context),
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof make_subseq 
                                    (subseq U1 U3)).
 Admitted.

 (*need to do refl*)

(*mysterious error Definition if_z (n: term False) := ppi1 n. *)



(********************************************)

 (*memory store*)

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


(********************************************)

(*moving terms in a world to a future world*)

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

 Lemma subst_move: forall A s, (subst s (move A)) = move A.
   intros. induction A; simpsub; simpl; auto. Qed.

 (*moving all variables specified by G to a future world*)
 (*n keeps track of index at which G starts*)
 (* for (var i): B in G, (sub_4_moveG G m n) substitutes
(move_B m (var (i + n))) in for (var (i + n)) while leaving all other variables untouched 
 Fixpoint sub_4_moveG (G: source.context) (m: term False) (n: nat) :=
 under n (match G with
   nil => id
          | b :: bs => dot (move_app b m (var 0)) (sub_4_moveG bs m (n + 1))
       end
).*)



(*Lemma aaa: (move_gamma (cons nattp_m (cons unittp_m nil)) triv 1) (var 1) = unittp.
  simpl. simpsub. unfold move_app. simpsub. rewrite subst_move. unfold move. simpl.
  simpsub. simpl.
  (*want one that replaces var 0 but leaves the other vars the same*)
  Admitted.


(*problems with this:
 always substs in for var 0
 *)
  Lemma test: (@subst False (dot nattp sh1) (ppair (var 0) (var 1) )) = unittp.
    unfold sh1. simpsub. simpl. (*seems to work*)
    Admitted.

  Lemma test1: (@subst False (dot nattp sh1) (ppair (var 0) (var 14) )) = unittp.
    unfold sh1. simpsub. simpl.
    (*found*)
    Admitted.
*)
(* p sure this is wrong
Lemma mg_bind_help: forall G m e s,
    subst (dot (var 0) s) (move_gamma G m 1 e) =
    subst s (move_gamma G m 1 e).
  intros. unfold move_gamma. induction G.
simpl. simpsub. simpl.*)

(*Lemma test1: forall (t: term False), subst (dot (var 1) (dot (var 0) (sh 2)))
                       (subst (under 1 (dot (var 1) (dot (var 0) (sh 2)))) t) =
                            t.
  intros. simpsub. ring.*)


Opaque laters preworld U0 subseq leqtp nzero nattp world nth.
