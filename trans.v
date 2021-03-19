From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Definition oof (M: term False) := deq M M.

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

 Definition list: (term False) -> (term False) := fun A => wt (opt A) (bite (ppi1 (var 0)) unittp voidtp).

 Definition cons: (term False) -> (term False) -> (term False) := fun x => fun L => ppair (ppair btrue x)
                                                                      (lam L).

 Definition hd: (term False) -> (term False) := fun L => ppi2 (ppi1 L).

 Definition tl: (term False) -> (term False) := fun L => (app (ppi2 L) triv).

 Definition if_cons: (term False) -> (term False) := fun L => ppi1 (ppi1 L).

 Definition one: (term False) := nsucc nzero.

 Definition world: (term False) := rec (list (karrow (fut (var 0)) (univ (one)))).

 Definition tlist: (term False) := list (univ one).

 Definition app_bc: (term False) := lam 
                      ( (*f:= 0*)
                         lam ( (*f:= 1; L1 := 0*)
                               lam ( (*f := 2; L1 := 1; L2 := 0*)
                                     let f := (var 2) in
                                     let L1 := (var 1) in
                                     let L2 := (var 0) in
bite (if_cons L1) (cons (hd L1) (app (app f (tl L1)) L2 )) L2
)
)
).

 Definition pend: (term False) := app theta app_bc.

 Definition subseq: (term False) -> (term False) -> (term False) :=
   fun w1 => fun w2 => exist one world (equal w2 (app (app pend (var 0)) w1)
                                                              world).

 Lemma osub : forall (M M' U1 U2 U3: term False) (G: context),
                         tr G (oof M (subseq U2 U3))
                         -> tr G (oof M' (subseq U1 U2))
                         ->tr G (oof triv (subseq U1 U3)).
 Admitted.

 Definition getstorebc: (term False) := lam
                                      ( (*f := var 0*)
                         lam  ((*f := 1, w := 0*)
                             lam ( (*f:= 2, w:= 1, v:= 0*)
                                 let f := var 2 in
                                 let w := var 1 in
                                 let v := var 0 in
bite (if_cons w) (cons (app (hd w) (next v)) (app (app f (tl w)) v)) unittp
)
)
                                      ).
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
                                                  (nzero)
                                                  (bite (if_z m)
                                                     (n)
                                                    (app (app f (app (ppi2 n) triv)) (app (ppi2 m) triv)))
                                                  ))).
 Definition minus: (term False) := app theta minusbc.


 Definition lengthbc: (term False) := lam 
                                ( (*f:= 0*)
                                  lam ((*f:= 1, L := 0*)
                                      let f:= var 1 in
                                      let L := var 0 in
                                                bite (if_cons L) (nsucc (app f (tl L))) (nzero)
                                                )).

 Definition length: (term False) := app theta lengthbc.

 Definition nth_normalbc: (term False) := lam 
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
                              )).
