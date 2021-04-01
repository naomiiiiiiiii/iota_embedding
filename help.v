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

 Definition one: (term False) := nsucc nzero.

Definition world: (term False) := rec (prod
                                     (karrow nattp (karrow (fut (var 0)) (univ (one))))
                                     nattp).

Definition len w: (term False) := ppi2 w.

Definition default_w: (term False) := ppair (lam (*n := 0*) (lam (*n:= 1, |> w := 0*) unittp)) nzero.
                                                      

Definition U1 := univ one.

 Definition subseq: (term False) -> (term False) -> (term False) :=
   fun w1 => fun w2 => prod (pi nattp (* 0 : = i
                           *)
                    (pi (ltpagetp (var 0) (len w1))
                        ( (*1:= i, 0 := H*)
                          equal (app (ppi1 w1) (var 1)) (app (ppi1 w2) (var 1)) (karrow
                                                                                (fut world) U1)
                        )
                    )) (leqpagetp (len w1) (len w2)).

 Lemma compose_sub : forall (M M' U1 U2 U3: term False) (G: context),
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof triv (subseq U1 U3)).
 Admitted.

 Definition getstorebc: (term False) := unittp (*lam
                                      ( (*f := var 0*)
                         lam  ((*f := 1, w := 0*)
                             lam ( (*f:= 2, w:= 1, v:= 0*)
                                 let f := var 2 in
                                 let w := var 1 in
                                 let v := var 0 in
                                 unittp

bite (if_cons w) (cons (app (hd w) (next v)) (app (app f (tl w)) v)) unittp
)
)
                                      ))) *).
 (** getstore w v ~:= * (w/v) *)

 Definition getstore: (term False) := app theta getstorebc.

 Definition store: (term False) -> (term False) := fun w => all one world ( (*u := var 0*)
                                                  pi 
                                                    (subseq w (var 0))
                                                    (*u :=  var 1, m := var 0*)
                                                     (app (app getstore w) (var 1))
).

 (*nats*)
(*mysterious error Definition if_z (n: term False) := ppi1 n. *)
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


 Definition lengthbc: (term False) := unittp (*lam 
                                ( (*f:= 0*)
                                  lam ((*f:= 1, L := 0*)
                                      let f:= var 1 in
                                      let L := var 0 in
                                                bite (if_cons L) (nsucc (app f (tl L))) (nzero)
                                                )).*).

 Definition length: (term False) := app theta lengthbc.

(* Definition nth_normalbc: (term False) := lam 
                              ( (*f : = 0*)
                                 lam ((*f:= 1, L := 0*)
                                     lam ( (*f:= 2, L:= 1, n:= 0*)
                                           let f := (var 2) in
                                           let L := (var 1) in
                                           let n := (var 0) in
                                                         bite (if_cons L)
                                                         ( bite (if_z n) (hd L)
                                                            (app (app f (app (ppi2 n) triv)) (app (ppi2 L) triv))
                                                            )
                                                         (lam voidtp)


))).

 Definition nth_normal: (term False) := app theta nth_normalbc.

 (*gets you the nth thing from the back
  all the ref indexes are wrt this*)
 Definition nth := lam 
                ((*L := 0*)
                  lam ((*L = 1, n= 0*)
                                           let L := (var 1) in
                                           let n := (var 0) in
                              app (app nth_normal L) (app (app minus (app length L)) n)
                )).*)

 Definition nth w n: term False := app (ppi1 w) n.
(*make_ref: (translation of tau into target) -> (translation of ref tau into target)*)
 Definition make_ref: term False -> term False := fun As =>
 (lam (*w := 0*)
    (sigma nattp ( (*w:= 1, i := 0*)
      all world one (*w:= 2, i := 1, u := 0*)
          ( let w := (var 2) in
            let i := (var 1) in
            let u := (var 0) in
            prod (leqpagetp i (len w))
          (equal (app (nth w i) (next u))
                 (fut (app As u)) U1))))).

Check nattp_m.

 Definition move (A: source.term False) (m: term False): term False :=
   match A with
     source.oper L operator R =>
     match operator with
       oper_nat _ => lam (var 0)
     | oper_arrow_m =>
lam ( (*f:= 0*)
       lam ( (*f := 1 m:= 0*)
                          lam (*f:= 2 m := 1, x:= 0*)
                            app f ()
                        ))
| _ => lam (var 0)
     end
   | source.var _ => lam (var 0) end.




 Fixpoint move_gamma (G: source.context) (m: term False) (e: Syntax.term False)
          (n: nat) (*counter*) :=
   match G with
     [ ] => e
   | x :: xs =>
     match x with
       hyp_tm A => move_gamma xs m (subst (dot (move A m (var n)) id) e)
     end
   end.



