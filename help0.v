From Coq Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import Tactics Sequence source subst_src rules_src.
From istari Require Import basic_types0 Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*small abbreviations that will help us later*)
Definition app3 w i u l : term obj :=
 app (app (app w i) u) l.

(*quickly access the nth element of the big tuple in the comp type*)
Definition picomp1 (M: term obj) := ppi1 M.
Definition picomp2 (M: term obj) := ppi1 (ppi1 (ppi2 M) ). 
Definition picomp3 (M: term obj) := ppi2 (ppi1 (ppi2 M)). 
Definition picomp4 (M: term obj) := ppi2 (ppi2 M).
(********************************************)
(*useful types*)

Definition plus L R : (term obj) := sigma booltp (bite (var 0) (subst (sh 1) L)
                                           (subst (sh 1) R) ).
Definition inl L: term obj := ppair btrue L.
Definition inr R: term obj := ppair bfalse R.

Definition opt w: term obj := sigma booltp (bite (var 0) w unittp).

Definition laters A : term obj := rec (plus (shift 1 A) (fut (var 0))).
(*notice similarity w type of nat in logic*)
(********************************************)


(*useful terms*)

(*Unguarded recursion*)
Definition Yc: (term obj) := lam ((*f := 0*)
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
Definition ret: term obj := lam (inl (var 0)).

Definition ret_a x := inl x.

Definition bind : term obj := app Yc
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
