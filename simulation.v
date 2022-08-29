Require Import Program Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types0 basic_types
     help0 subst_help0.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences.
From istari Require Import Rules Defined DefsEquiv.


Notation store := rules_src.store.

Fixpoint gamma_nth (bundle: Syntax.term obj) i :=
  match i with 0 => (ppi1 bundle)
          | S i' => gamma_nth (ppi2 bundle) i' end.
Fixpoint nat_from_numeral i : (Syntax.term obj) := match i with
                                0 => nzero
                              | i'.+1 =>
                                nsucc (nat_from_numeral i') end.

(*copied out all the rules from trans so that locations can show up at any depth
 need to sh ow trans <= trans_erasure
 store is included to type locations, no other reason *)
Inductive trans_erasure:
  source.context -> (source.term * store) -> source.term -> Syntax.term obj -> Prop :=
| t_loc : forall G S l A bang_l_t,
  trans_erasure G ((nth triv_m S l), S) A bang_l_t ->
  trans_erasure G  (loc_m l, S)
                (reftp_m A)
                (ppair (nat_from_numeral l)
                       (ppair (app leq_refl_fn (nsucc (nat_from_numeral l))) (lam triv))) 
| t_z : forall G S,
    trans_erasure G (z_m, S) nattp_m (lam (lam nzero))
| t_succ : forall G S e ebar,
    trans_erasure G (e, S) nattp_m ebar ->
    trans_erasure G (succ_m e, S) nattp_m
                  (lam (lam (nsucc (app (app (subst (sh 2) ebar) (var 1)) (var 0)))))
| t_triv : forall G S,
    trans_erasure G (triv_m, S) unittp_m (lam (lam triv))
| t_var: forall G i A S,
    Sequence.index i G A ->
    trans_erasure G (source.var i, S) A
          (lam (lam
                  (gamma_nth (var 0) i)
          ))
|  t_bind: forall G S E1 Et1 E2 Et2 A B, (*of_m G (bind_m E1 E2) (comp_m B) -> require typing of E1 and E2 instead*)
                                   trans_erasure G (E1, S) (comp_m A) Et1 ->
                                   trans_erasure (A::G) (E2, S) (comp_m B) Et2 ->
                                   (*E2 wont actually have the same store
                                     but its ok for typing purposes*)
                                   trans_erasure G ((bind_m E1 E2), S) (comp_m B) (
 lam (lam ( lam ( (*l1 : = 2, g: Gamma_at G = 1 l :=0 *) lam ( (*l1 := 3, l := 1, m := 0*)
                           lam ( (*l1 := 4, l := 2, m := 1, s := 0*)
                               let l1 := (var 4) in
                               let g := (var 3) in
                               let l := (var 2) in
                               let m := (var 1) in
                               let s := (var 0) in
let btarg := app (app (app (app (app (shift 5 Et1) l1) g) l) m) s in
make_bind btarg ( lam (*l1 := 5, l := 3, m := 2, s := 1, z1 := 0*)
              (
                               let z1 := (var 0) in (*basically added 6 vars to my context*)
                               let lv := (picomp1 z1) in
                               let mv := (picomp2 z1) in
                               let sv := (picomp3 z1) in
                               let x' := (picomp4 z1) in
                               let l := (shift 1 l) in (*l = 3*)
                               let btarg :=
                                   (*Et2 Gamma@V lv*)
                                   app (app (shift 6 Et2)
                                           lv 
                                            )
                                            (*5: Gamma_at G w
                                              move 5: Gamma_at G v
                                          <x, 5> : Gamma_at A::G v*)
                       (ppair x' (move_gamma G
                                             (var 5) lv
                       (make_subseq_trans_erasure (var 5) (var 3) lv (var 2) mv)
                       (var 4)))                                                 in
                               let e2bar' := app (app (app btarg lv) (make_subseq_refl lv) )
                                                 (*v, z1 <= v, z1*)
                                                 sv in (*e2 is applied to everything*)
                               make_bind e2bar' (lam ( (*l = var 4*)
                                                    let z2 := (var 0) in
                                                    ret_a (ppair (picomp1 z2)
                                                                 (ppair (ppair
             (make_subseq_trans_erasure (shift 1 l) (shift 1 lv) (picomp1 z2) (picomp2 (shift 1 z1)) (picomp2 z2))
                                                                           (*z2 \circ z1*)
                                                      (picomp3 z2)) (picomp4 z2))                         
                                                        )
                                               ))
              )

          )

    ))
                                         ))))
  | t_ref: forall G S E Et A, 
 trans_erasure G (E, S) A Et ->
 trans_erasure G (ref_m E, S)
       (comp_m (reftp_m A)) (lam (lam (lam (lam ( lam ( (*l1, g, l, m, s*)
         let l := var 2 in                                                        
         let m1 := (make_consb_subseq l) in (*u <= u1, consb subseq*)
         let p1 := (ppair m1
                         (lam (lam ( lam ( (*making a value of type store U1, lambdas go l2, m2, i*)
                                         let l1 := var 7 in
                                         let g := var 6 in
                                         let l := var 5 in
                                         let m := var 4 in
                                         let s := var 3 in
                                         let l2 := var 2 in
                                         let m2 := var 1 in
                                         let i := var 0 in
                                         let x := app (app (shift 8 Et) l1) g in
                                         let m12 := (make_subseq_trans_erasure l (nsucc l)
                                                                      l2 (subst (sh 3) m1) m2) (*U <=  U1 <= U2*)
                                         in 
                                         let m02 := make_subseq_trans_erasure l1 l l2 m m12 in (*W <= U + U <= U2 = W <= U2*)
                                         
                                         (*m12 o m : W <= U2*)
                                         bite (ltb_app i l)
                                              (app (app (app s l2) m12) i)
                                              (*move value in s:store(U) to U2*)
                                              (next (move_app A
                                                              l1 l2
                                                              m02 x))
                                   (*move x to be : |> A @ U2*)
                                               ))
                         ))
         ) in
             ret_a (ppair (nsucc l) (*length of new world*)
                          (ppair p1 (*new word is accessible from current world, *)
           (ppair l (ppair (app leq_refl_fn (nsucc l)) (lam triv)) (*ref A @ new world*)
                                 ) 
                          )
                   )))))))
  | t_assign: forall G S R Rt E Et A,
    (*  of_m G R (reftp_m A) ->
      of_m G E A -> *)
      trans_erasure G (R, S) (reftp_m A) Rt ->
      trans_erasure G (E, S) A Et ->
      trans_erasure G ((asgn_m R E), S) (comp_m unittp_m)
            (lam (lam (lam (lam ( lam ( (*l = 4, g = 3, l1 = 2, m = 1, s1 = 0*)
                                      let l := var 4 in
                                      let m := var 1 in
                                      let l1 := var 2 in
                                      let g := var 3 in
                                      let s1 := var 0 in 
                                      let ref := move_app (reftp_m A)
                                                          (var 4) (var 2)
                                                          m (app (app (shift 5 Rt) l) g) in
                                      let i := ppi1 ref in
                                      let p := ppi2 ref in
                                      let store_u1  := lam (lam (lam (*l2 = 2, m1 = 1,j = 0*)
                                                                  (
                                                                    let j := (var 0) in
                                                                    let l2 := var 2 in
                                                                    let m1 := var 1 in
                                                                    let i := shift 3 i in
                                                                    let l := shift 3 l in
                                                                    let l1 := shift 3 l1 in
                                                                    let g := shift 3 g in
                                                                    let m := shift 3 m in
                                                                    bite
                                                                      (app (eq_b j) i)
                                                                      (next (move_app A
                                                                                      l
                                                                                      l2
   (make_subseq_trans_erasure l l1 l2 m m1)
                                                                    (app (app (shift 8 Et) l) g)))
                                                                      (app (app (app (shift 3 s1) l2) m1) j)
                                                                 ))) in
                                      ret_a (ppair l1
                                                   (ppair
                                                      (ppair (make_subseq_refl l1) (*refl u1*)
                                                             store_u1)
                                                      triv))
            ))))))
  | t_deref: forall G S R Rt A,
      (* of_m G R (reftp_m A) -> *)
      trans_erasure G (R, S) (reftp_m A) Rt ->
      trans_erasure G (deref_m R, S) (comp_m A) 
            (lam (lam (lam (lam ( lam ( (*l = 4, g = 3, l1 = 2, m = 1, s = 0*)
                                      let l := var 4 in
                                      let g := var 3 in
                                      let l1 := var 2 in
                                      let m := var 1 in
                                      let s := var 0 in
                                      let ref := move_app (reftp_m A) l l1
                                                          m (app (app (shift 5 Rt) l) g) in
                                      let i := ppi1 ref in
                                      let e := prev (app (app (app s l1)
                                                (make_subseq_refl l1)) i) in
                                     (inr (next (inl (ppair
                                                                            l1
                                                                            (ppair (
                                                                                 ppair (make_subseq_refl l1)
                                                                                       s)
                                                                                   e)
                                                                               )
                                    ))))
            )))))
| t_ap : forall G S E1 Et1 E2 Et2 Targ T2,  
    (*  of_m G E1 (arrow_m Targ T2) -> (*take this out*)
      of_m G E2 Targ -> (*take this out*) *)
      trans_erasure G (E1, S) (arrow_m Targ T2) Et1 ->
      trans_erasure G (E2, S) Targ Et2 ->
      trans_erasure G ((app_m E1 E2), S) T2
           ( lam (lam  (*l = 1, g = 0*)
                   (let Et1 := shift 2 Et1 in
                   let Et2 := shift 2 Et2 in
                   let l := (var 1) in
                   let g := (var 0) in
                   let arg := (app (app Et2 l) g) in
                   (app (app (app (app (app Et1 l) g) l) (make_subseq_refl l)) arg)
                )))
| t_lam : forall G S E Et Targ T2,
     (* of_m (Targ::G) E T2 ->*)
      trans_erasure (Targ::G) (E, S) T2 Et ->
      trans_erasure G ((lam_m E), S) (arrow_m Targ T2) 
            (lam (lam (lam (lam (lam (*l1 =4, g = 3, l = 2
                                      m = 1, x = 0*)
                                   (app (app (shift 5 Et) (var 2))
                                        (ppair (var 0) (move_gamma G (var 4) (var 2)
                                                                   (var 1) (var 3)))

            ))))))
| t_ret : forall G S E Et A,
   (* of_m G E A -> *)
    trans_erasure G (E, S) A Et ->
    trans_erasure G ((ret_m E), S) (comp_m A)
          (lam (lam (lam (lam (lam (*l1 = 4, g = 3, l =2, m = 1, s = 0*)
                                 (let l1 := var 4 in
                                  let g := var 3 in
                                  let l := var 2 in
                            let m := var 1 in
                            let s := var 0 in
                            let e := move_app A l1 l m (app (app (shift 5 Et) l1) g) in
                            inl (
                                (ppair
                                   l
                                   (ppair (ppair (make_subseq_refl l) s) e))
                            )

          )))))).

(* source.context -> (source.term * store) -> source.term ->
Syntax.term obj -> Prop :=
source.context -> (source.term * store) -> source.term -> Syntax.term obj -> Prop :=
 *)
Inductive trans_store : source.context -> store -> Syntax.term obj -> Prop :=
| empty {G} : trans_store G [] (lam (next triv))
| cons {G x xs xt A} : trans_store G xs S ->
                       trans G (x, xs) A xt -> ->
                       trans_store G (x::xs) (lam
                                               let i := (var 0) in
                                               let l := nat_from_numeral (length xs) in
                                               (bite (lt_app i l)
                                                       (app (subst sh1 S) i)
                                                       (next (subst sh1 xt))
                                            )).


(* simple but doesnt match the typed one 
Inductive trans_erasure : source.term -> (Syntax.term obj) -> Prop :=
  t_z: trans_erasure z_m nzero
| t_nsucc {n nbar} : trans_erasure n nbar ->
            trans_erasure (succ_m n) (nsucc nbar)
| t_triv : trans_erasure triv_m triv
| t_var {i} : trans_erasure (source.var i) (var i)
| t_loc {l} : trans_erasure (loc_m l) (nat_from_numeral l) (*cannot be type directed*)
| t_bind {e1 e2 e1bar e2bar}: trans_erasure e1 e1bar ->
           trans_erasure e2 e2bar ->
           trans_erasure (bind_m e1 e2) (lam (*<store, length> = var 0*)
                                   (make_bind (app e1bar (var 0))
                                   (lam (*the computation inside e1bar.
                                          <<store, length>, exp> = var 0*)
                                      (let s1 := ppi1 (var 0) in
                                      let e := ppi2 (var 0) in
                                      app (subst1 e e2bar) s1)
                                   ))
                                )
| t_ref {e ebar} : trans_erasure e ebar ->
          trans_erasure (ref_m e) (lam (*<store, length> = var 0*)
                                           (let l := ppi2 (var 1) in
                             (ret_a (ppair (ppair
                                              (lam (*index into new store = var 0*)
                                           (let i := var 0 in
                                            let s := ppi1 (var 1) in
                                            let l := subst sh1 l in
                                           bite
                                                (ltb_app i l)
                                             (app s i)
                                             (next ebar)
                                              )) (nsucc l))
                                           l)
                          )))
| t_asgn {r e rbar ebar}: trans_erasure r rbar -> (*r should be a location, rbar a nat*)
                trans_erasure e ebar ->
                trans_erasure (asgn_m r e) (lam
                                      (let s := ppi1 (var 0) in
                                       let l := ppi2 (var 0) in
                                       ret_a (ppair (ppair
                                                       (lam (*new store*)
                                                          ( bite (app
                                                                    (eq_b (var 0))
                                                                    (subst (sh 2) rbar))
                                                                 (next ebar)
                                                                 (app (subst sh1 s) (var 0))
                                                       ))
                                                       l (*same length*)
                                                    )
                                                    triv)
                                      ))
| t_deref {r rbar}: trans_erasure r rbar ->
                trans_erasure (deref_m r) (lam
                                      (let s := ppi1 (var 0) in
                               inr (next (inl (ppair (var 0)
                                                                    (prev (app s rbar) ))))
                                   )).
                      | t_lam 
                                     
*)

(*
| t_typed : forall G S St E Et A,
    trans_erasure G E A Et -> (*this wont work because you can hve !l. need to copy out all the rules*)
    trans_erasure_store S St ->
    trans_erasure_erasure G (E, S) A (Et, St) *)
