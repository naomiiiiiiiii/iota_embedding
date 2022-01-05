(*Shallow embedding of simple constructs from the monadic language into the store-passing logic*)
From Coq Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import Tactics Sequence source subst_src rules_src.
From istari Require Import basic_types Syntax Subst SimpSub Promote Hygiene
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

(*Computation monad*)
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




(*worlds*)

Definition preworld: (term obj) := rec 
                                   (arrow nattp (karrow (fut (var 0)) (arrow (fut nattp) U0))).

Definition world: (term obj) := sigma preworld nattp.

Definition len w: (term obj) := ppi2 w.

Definition nth w n: term obj := app (ppi1 w) n.

 Definition subseq w1 l1 w2 l2 :=
            prod (leq_t l1 l2)
                 (all nzero (fut preworld)
                 (*u = 0*)
                 (pi (fut nattp) (*u = 1, l = 0*)
                     (pi (nattp) (*u = 2, l = 1, i = 0*)(
                           arrow (lt_t (var 0) (subst (sh 3) l1))
                              (
                          eqtype (app3 (subst (sh 3) w1) (var 0) (var 2) (var 1))
                          (app3 (subst (sh 3) w2) (var 0) (var 2) (var 1))
                              )
                                                   )
                                           )

                 )).



 Definition make_subseq: term obj := ppair triv (lam (lam (lam triv)) ).

 Definition make_subseq_trans l1 l2 l3 M1 M2 :=
  ppair (leq_trans_fn_app l1 l2 l3
                          (ppi1 M1) (ppi1 M2)
        )
        (lam (lam (lam triv))).

 (*transitivity of subseq*)


 (*need to do refl*)

(*mysterious error Definition if_z (n: term obj) := ppi1 n. *)



(********************************************)

 (*memory store*)

 (*gettype w v is a function which, when given an index i, gives the type
  at index i in w *)
 Definition gettype w v lv: (term obj) := pi nattp ((*i = 0*)
                                           let i := var 0 in
                                           app (app (app (shift 1 w) i) (next (shift 1 v))) (next (shift 1 lv))
                                         ).


 (*the type of the store at world <w, l>*)
 Definition store w l := all nzero preworld (pi nattp (*v = 1, l v= 0*) 
                                                (
                                                  (arrow (subseq (shift 2 w) (shift 2 l) (var 1) (var 0))
                                                         (gettype (shift 2 w) (var 1) (var 0))))
                                                ).


(********************************************)

(*moving terms in a world to a future world*)

 (*start here get rid of vacuous cases w program module*)
 Definition move (A: source.term): term obj :=
   match A with
     nattp_m => lam (lam (var 0))
   | arrow_m _ _ =>
lam ( (*m0 := 0*)
lam ( lam (
       lam ( (*m0:= 3, f := 2, l := 1, m:= 0*)
           lam (*m0:= 4, f := 3, l := 2 m:= 1 x := 0*)
             ( (*let m := var 3 in*)
               let f := var 3 in
               let l := var 2 in
             let x := var 0 in
                           app (app (app f l) make_subseq) x (*m o m0*)
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
     | _ => lam (lam triv) (*not a type operator, error case*)
end.

 Definition move_app A (m : term obj) (x: term obj) :=
   app (app (move A) m) x.

 Lemma subst_move: forall A s, (subst s (move A)) = move A.
   intros. induction A; simpsub; simpl; auto. Qed.

Hint Rewrite subst_move: subst1.


Opaque laters preworld U0 subseq leqtp nzero nattp world nth.

(*cons_b w l x is a preworld equal to <w, l> only with x consed onto the back*)



(*translation of source contexts to target contexts (at a given world)*)

(*makes a product type at a world out of a source context *)

Definition cons_b w l x :=lam (let i := (var 0) in
                              bite (ltb_app i (shift 1 l)) (app (shift 1 w) i) (shift 1 x)).

