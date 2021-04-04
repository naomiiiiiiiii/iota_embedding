
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

 Definition one: (term False) := nsucc nzero.

Definition world: (term False) := rec (prod
                                     (karrow nattp (karrow (fut (var 0)) (univ (one))))
                                     nattp).

Definition len w: (term False) := ppi2 w.

Definition default_f: (term False) := (lam (*n:= 1, |> w := 0*) unittp).
(*dfault: world -> U1*)
                                                      

Definition U1 := univ one.

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

Definition leq_bool m n := if_z (app (app minus m) n).

(*uses default value of w2*)
Definition pend w1 w2 :=
  ppair (lam ( (*n := 0*)
             let n := var 0 in
             bite (leq_bool (len w1) n)
                  (app (ppi1 w2) (app (app minus (len w1)) n))
                  (app (ppi1 w1) n)
        ))
        (plus (len w1) (len w2)).

(*Definition cons w1 x :=
  pend w1 (ppair (lam (let n := var 0 in bite (if_z n) x default_f)) one).*)

Definition cons w1 x :=
  pend w1 (ppair (lam x) one).
(*default value after s(len w1) is x*
ie uses default value of w2*)

 Definition subseq: (term False) -> (term False) -> (term False) :=
   fun w1 => fun w2 => prod (exist one world (equal w2 (pend w1 (var 0))
                                              world))
                      (sigma nattp (*j = var 0*) (equal (len w2) (var 0) nattp)).

 Definition getlen_subseq m : term False :=
   ppi1 (ppi2 m).

 Definition make_subseq n: term False := ppair triv (ppair n triv).

 (*M o M'*)
 Definition compose_sub M (M': term False) := make_subseq (getlen_subseq M).

 Lemma compose_sub_works : forall (M M' U1 U2 U3: term False) (G: context),
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof (compose_sub M M') 
                                    (subseq U1 U3)).
 Admitted.



 (*start here*)

 Definition getstorebc: (term False) := unittp (*lam
                                      ( (*f := var 0*)
                         lam  ((*f := 1, w := 0*)
                             lam ( (*f:= 2, w:= 1, v:= 0*)
                                 let f := var 2 in
                                 let w := var 1 in
                                 let v := var 0 in
       bite (if_z (len w)) unittp
                          (ppair (app (app f (tl w)) v) (app (hd w) (next v)))
)
)
                                      )*).
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
             ( let m := var 3 in
               let f := var 2 in
               let m' := var 1 in
             let x := var 0 in
                            app (app f (compose_sub m' m)) x
  ))))
     | oper_comp_m _ => lam (lam (* m= 1, c:= 0,*) (
                           lam (*m = 2, c:= 1, m' := 0*)
                             (lam (*m = 3, c:= 2, m' := 1, s := 0*)
                                (let m := var 3 in
                                 let c:= var 2 in
                                 let m' := var 1 in
                                let s := var 0 in
                                app (app c (compose_sub m' m)) s
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




