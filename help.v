(*Shallow embedding of simple constructs from the monadic language into the store-passing logic*)
From Coq Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import Tactics Sequence source subst_src rules_src.
From istari Require Import basic_types0 basic_types subst_help0 help0 Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.



(*\mu n. Nat -> fut n -> fut nat -> U0

nat := z
| S nat


\mu n. z + n

preworld :=
| pw : Nat -> fut preworld -> fut nat -> U0 -> preworld

??

pw \\\.z : preworld



 *)



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

 Definition make_subseq_refl l :=
  ppair (app leq_refl_fn l)
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
 Definition move (A: source.term) l1 l2: term obj :=
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
             app (app (app f l) (make_subseq_trans (subst (sh 5) l1)
                                                   (subst (sh 5) l2)
                                                   l
                                                   (var 4)
                                                   (var 1)) (*m o m0*)

                 ) x )))))
     | comp_m _ => lam (lam (* m0= 1, c:= 0,*) ( lam (
                           lam (*m0 = 3, c:= 2, l = 1, m := 0*)
                             (lam (*m0 = 4, c:= 3, l = 2, m := 1, s := 0*)
                                ( 
                                  let c:= var 3 in
                                  let l:= var 2 in
                                let s := var 0 in
                                app (app (app c l)
                                         (make_subseq_trans (subst (sh 5) l1)
                                                   (subst (sh 5) l2)
                                                   l
                                                   (var 4)
                                                   (var 1))
                                    ) s
                                (*compose_sub m m0*)
                             )
                         ))))
     | reftp_m _ => lam (lam (*R := 0*)
                          (let i := ppi1 (var 0) in
                           let iltl1 := ppi1 (ppi2 (var 0)) in
                             ppair i (ppair (lt_trans_fn_app i (subst (sh 2) l1)
                                                             (subst (sh 2) l2)
                                                             iltl1
                                                             (ppi1 (var 1))
                                            )
                                        (lam triv))
                          ))
     | unittp_m  => lam (lam (var 0))
     | _ => lam (lam triv) (*not a type operator, error case*)
end.

 Definition move_app A l1 l2 (m : term obj) (x: term obj) :=
   app (app (move A l1 l2) m) x.



Opaque laters preworld U0 subseq leqtp nzero nattp world nth.


 Lemma subst_move: forall A l1 l2 s, (subst s (move A l1 l2)) = move A (subst s l1) (subst s l2).
   intros. induction A; unfold make_subseq_trans;
unfold leq_trans_fn_app; unfold leq_trans_fn; simpsub_big; simpl; auto.
   { unfold make_subseq_trans;
unfold leq_trans_fn_app; unfold leq_trans_fn; simpsub_big; simpl; auto.
}
   { unfold make_subseq_trans;
unfold leq_trans_fn_app; unfold leq_trans_fn; simpsub_big; simpl; auto.
}
   { unfold make_subseq_trans;
       unfold lt_trans_fn_app; unfold leq_trans_fn_app;
         unfold leq_trans_fn; simpsub_big; simpl; auto.
}
 Qed.

Hint Rewrite subst_move: core subst1.

 Lemma subst_moveapp s A l1 l2 m1 m2 : (subst s (move_app A l1 l2 m1 m2)) =
                              move_app A (subst s l1) (subst s l2) (subst s m1) (subst s m2).
   unfold move_app. simpsub_big. auto. Qed.

Hint Rewrite subst_moveapp: core subst1.

(*cons_b w l x is a preworld equal to <w, l> only with x consed onto the back*)
Definition cons_b w l x :=lam (let i := (var 0) in
                              bite (ltb_app i (shift 1 l)) (app (shift 1 w) i) (shift 1 x)).

Fixpoint gamma_nth (bundle: Syntax.term obj) i :=
  match i with 0 => (ppi1 bundle)
          | S i' => gamma_nth (ppi2 bundle) i' end.

Fixpoint move_gamma (G: source.context) l1 l2 (m: Syntax.term obj) (gamma: Syntax.term obj) :=
   match G with
     nil => gamma
   | A::xs => ppair (move_app A l1 l2 m (ppi1 gamma)) (move_gamma xs l1 l2 m (ppi2 gamma)) end.

Lemma subst_move_gamma :forall g l1 l2 m s G,
    (subst s (move_gamma G l1 l2 m g)) = move_gamma G (subst s l1) (subst s l2) (subst s m) (subst s g).
  intros. move: g m s. induction G; intros; auto. simpl. simpsub.
  rewrite (IHG (ppi2 g) m s); auto. unfold move_app. simpsub. rewrite subst_move.
  auto. Qed.


Hint Rewrite subst_move_gamma: subst1.
