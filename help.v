
From Coq Require Import Lists.List.
From istari Require Import Tactics Sequence source subst_src rules_src
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Definition oof M A: (@Syntax.judgement False) := deq M M A.

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

Definition laters A : term False := rec (plus A (fut (var 0))).
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
(*worlds*)

Definition U0 : (term False) := univ nzero.

Definition preworld: (term False) := rec 
                                   (arrow nattp (karrow (fut (var 0)) U0)).

Definition world: (term False) := prod preworld nattp.

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

Definition leq_t n m : term False :=
  app (app leqtp n) m.

Definition app3 w i u l : term False :=
 app (app (app w i) u) l.

 Definition subseq: (term False) -> (term False) -> (term False) :=
   fun W1 => fun W2 =>
            let w1 := ppi1 W1 in
            let w2 := ppi1 W2 in
            let n1 := ppi2 W1 in
            let n2 := ppi2 W2 in
            prod (leq_t n1 n2)
                 (pi nattp 
                     (*i = var 0*)
                     ( pi nattp (*i = 1, l = 0*)
                       (all (*i = 2, l = 1, h = 0*)
                     nzero (leq_t (var 2) (subst (sh 3) n1))
                     (all nzero (fut preworld) (*i = 3, l = 2, h = 1, u= 0*)
                          (eqtype (app3 (subst (sh 3) w1)
                                        (var 3) (var 0) (var 2))
                          (app3 (subst (sh 3) w2) (var 3) (var 0) (var 2)))
                     ))
                 )).

Ltac simpsub1 :=
  unfold leq_t; unfold leqtp; unfold nattp; unfold preworld; unfold app3; unfold nzero; simpsub; simpl.

 Lemma subseq_subst: forall s W1 W2, 
       (subst s 
              (subseq W1 W2)) = (subseq (subst s W1) (subst s W2)).
   intros. unfold subseq. simpsub1. unfold wind. simpl. simpsub1.
   repeat rewrite <- compose_dot.
   simpl.
   (*weird dots stacked on top of compose
    but s is in the middle
    solution to all of this is make subseq a function :/*)
   reflexivity.



 Definition test :=   (subst (dot (var 0) (dot (var 1) (sh 3)))
                             (subseq (var 0) (ppair (var 1) (var 0)))).

 Definition make_subseq: term False := ppair triv (lam (lam (lam triv)) ).

 (*M o M'*)

 Lemma compose_sub_works : forall (M M' U1 U2 U3: term False) (G: context),
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof make_subseq 
                                    (subseq U1 U3)).
Admitted.

 (*getstore w v = *(w/v)*)
 Definition getstore w v: (term False) := pi nattp ((*i = 0*)
                                           let i := var 0 in
                                           (app (app w i) (next v))
                                         ).

 Definition store: (term False) -> (term False) := fun wn =>
                                            let w := ppi1 wn in
                                            let n := ppi2 wn in
                                            all nzero preworld ( (*u := var 0*)
                                                  pi 
                                                    (subseq wn (ppair (var 0) n) )
                                                    (*u :=  var 1, m := var 0*)
                                                     (getstore w (var 1))).

 (*nats*)
(*mysterious error Definition if_z (n: term False) := ppi1 n. *)

 Definition nth w n: term False := app (ppi1 w) n.


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




