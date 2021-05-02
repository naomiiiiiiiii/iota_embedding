
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

Definition lt_bool m n := if_z (app (app minus m) (nsucc n)).

(*uses default value of w2*)

(*Definition cons w1 x :=
  pend w1 (ppair (lam (let n := var 0 in bite (if_z n) x default_f)) one).*)

Definition cons w1 x :=
  ppair (lam ( (*n := 0*)
             let n := var 0 in
             bite (lt_bool n (len w1))
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
                     nzero (leq_t (var 2) n1)
                     (all nzero (fut preworld) (*i = 3, l = 2, h = 1, u= 0*)
                          (eqtype (app3 w1 (var 3) (var 0) (var 2))
                          (app3 w2 (var 3) (var 0) (var 2)))
                     ))
                 )).


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
(*make_ref: (translation of tau into target) -> (translation of ref tau into target)*)
 Definition make_ref: term False -> term False := fun As =>
lam
  (sigma nattp ( (*wl1:= 1, i := 0*)
           let l1 := ppi2 (var 1) in
           let i := (var 0) in
            prod (ltpagetp i l1)
                 (all preworld nzero (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let W := (var 3) in
            let w := ppi1 W in
            let l1 := ppi2 W in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (nth W i) (next v)) (next lv))
                 (fut (app As (ppair v lv)))
                      )
         )))
   ).



 Definition move (A: source.term False): term False :=
   match A with
     source.oper _ operator _ =>
     match operator with
       oper_nat _ => lam (lam (var 1))
     | oper_arrow_m _ =>
lam ( (*m := 0*)
lam ( (* m:= 1, f:= 0*)
       lam ( (*m:= 2 f := 1 m':= 0*)
           lam (*m := 3 f:= 2 m' := 1, x:= 0*)
             ( (*let m := var 3 in*)
               let f := var 2 in
              (* let m' := var 1 in*)
             let x := var 0 in
                            app (app f make_subseq) x (*compose_sub m' m*)
  ))))
     | oper_comp_m _ => lam (lam (* m= 1, c:= 0,*) (
                           lam (*m = 2, c:= 1, m' := 0*)
                             (lam (*m = 3, c:= 2, m' := 1, s := 0*)
                                ( (*let m := var 3 in*)
                                 let c:= var 2 in
                                 (*let m' := var 1 in*)
                                let s := var 0 in
                                app (app c make_subseq) s (*compose_sub m' m*)
                             )
                         )))
     | oper_reftp_m _ => lam (lam (*R := 0*)
                        (let i := ppi1 (var 0) in
                         ppair i (ppair triv triv)
                        ))
     | oper_unittp_m _ => lam (lam (var 0))
     | _ => triv (*not a type operator, error case*)
     end
   | source.var _ => triv end.

 Definition move_app A m x :=
   app (app (move A) m) x.

 Fixpoint move_gamma (G: source.context) (m: term False) (e: Syntax.term False) :=
   match G with
     nil => e
   | x::xs =>
     match x with
       source.hyp_tm A => move_gamma xs m (subst (
                                              dot (app (app (move A) m) (var 0))
                                                  id) e)

     (*assuming variables are stored in context with 0 first
      DONT need the counter cuz all the other variables get moved down a slot with the
      cons subtitution*)
     end
   end.




