
Inductive trans: source.context -> source.term -> source.term -> (Syntax.term obj) -> Prop :=
  t_z : forall G,
    trans G z_m nattp_m (lam (lam nzero))
| t_succ : forall G e ebar,
    trans G e nattp_m ebar ->
    trans G (succ_m e) nattp_m (lam (lam (nsucc (app (app (subst (sh 2) ebar) (var 1)) (var 0)))))
| t_triv : forall G,
    trans G triv_m unittp_m (lam (lam triv))
| t_var: forall G i A,
    Sequence.index i G A ->
    trans G (source.var i) A
          (lam (lam
                  (gamma_nth (var 0) i)
          ))
|  t_bind: forall G E1 Et1 E2 Et2 A B, (*of_m G (bind_m E1 E2) (comp_m B) -> require typing of E1 and E2 instead*)
                                   trans G E1 (comp_m A) Et1 ->
                                   trans (A::G) E2 (comp_m B) Et2 ->
                                   trans G (bind_m E1 E2) (comp_m B) (
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
                                                                        (*
in the context (A :: G) Et2 is a function which wants a length
in the context G, Et2 has var 0 free. In context G, (lam Et2) is a function which wants an
x, then a length
make the lambda first before you introduce other variables and it's still the first var
that. you want to bind 
                                                                         *)
                               (*x' lam, floating around in the context as var 0*)
(*et2's var 0 is the x.
 maybe plan is bring the subst outside the lamda so that you type check the lamda in the
 weakened context*)                                                      

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
                       (make_subseq_trans (var 5) (var 3) lv (var 2) mv)
                       (var 4)))                                                 in
                               let e2bar' := app (app (app btarg lv) (make_subseq_refl lv) )
                                                 (*v, z1 <= v, z1*)
                                                 sv in
                               make_bind e2bar' (lam ( (*l = var 4*)
                                                    let z2 := (var 0) in
                                                    ret_a (ppair (picomp1 z2)
                                                                 (ppair (ppair
             (make_subseq_trans (shift 1 l) (shift 1 lv) (picomp1 z2) (picomp2 (shift 1 z1)) (picomp2 z2))
                                                                           (*z2 \circ z1*)
                                                      (picomp3 z2)) (picomp4 z2))                         
                                                        )
                                               ))
              )

          )

    ))
                                         ))))
  | t_ref: forall G E Et A, 
      (*   of_m G (ref_m E) (comp_m (reftp_m A)) -> *)
 trans G E A Et ->
         trans G (ref_m E) (comp_m (reftp_m A)) (lam (lam (lam (lam ( lam ( (*l1, g, l, m, s*)
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
                                         let m12 := (make_subseq_trans l (nsucc l)
                                                                      l2 (subst (sh 3) m1) m2) (*U <=  U1 <= U2*)
                                         in 
                                         let m02 := make_subseq_trans l1 l l2 m m12 in (*W <= U + U <= U2 = W <= U2*)
                                         
                                         (*m12 o m : W <= U2*)
                                         bite (ltb_app i l)
                                              (app (app (app s l2) m12) i) (*move value in s:store(U) to U2*)
                                              (next (move_app A
                                                              l1 l2
                                                              m02 x)) (*move x to be : |> A @ U2*)
                                               ))
                         ))
         ) in
             ret_a (ppair (nsucc l) (*length of new world*)
                          (ppair p1 (*new word is accessible from current world, *)
                                 (ppair l (ppair (app leq_refl_fn (nsucc l)) (lam triv)) (*ref A @ new world*)
                                 ) 
                          )
                   )))))))
  | t_assign: forall G R Rt E Et A,
    (*  of_m G R (reftp_m A) ->
      of_m G E A -> *)
      trans G R (reftp_m A) Rt ->
      trans G E A Et ->
      trans G (asgn_m R E) (comp_m unittp_m)
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
   (make_subseq_trans l l1 l2 m m1)
                                                                    (app (app (shift 8 Et) l) g)))
                                                                      (app (app (app (shift 3 s1) l2) m1) j)
                                                                 ))) in
                                      ret_a (ppair l1
                                                   (ppair
                                                      (ppair (make_subseq_refl l1) (*refl u1*)
                                                             store_u1)
                                                      triv))
            ))))))
  | t_deref: forall G R Rt A,
      (* of_m G R (reftp_m A) -> *)
      trans G R (reftp_m A) Rt ->
      trans G (deref_m R) (comp_m A) 
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
| t_ap : forall G E1 Et1 E2 Et2 Targ T2,  
    (*  of_m G E1 (arrow_m Targ T2) -> (*take this out*)
      of_m G E2 Targ -> (*take this out*) *)
      trans G E1 (arrow_m Targ T2) Et1 ->
      trans G E2 Targ Et2 ->
      trans G (app_m E1 E2) T2
           ( lam (lam  (*l = 1, g = 0*)
                   (let Et1 := shift 2 Et1 in
                   let Et2 := shift 2 Et2 in
                   let l := (var 1) in
                   let g := (var 0) in
                   let arg := (app (app Et2 l) g) in
                   (app (app (app (app (app Et1 l) g) l) (make_subseq_refl l)) arg)
                )))
| t_lam : forall G E Et Targ T2,
     (* of_m (Targ::G) E T2 ->*)
      trans (Targ::G) E T2 Et ->
      trans G (lam_m E) (arrow_m Targ T2) 
            (lam (lam (lam (lam (lam (*l1 =4, g = 3, l = 2
                                      m = 1, x = 0*)
                                   (app (app (shift 5 Et) (var 2))
                                        (ppair (var 0) (move_gamma G (var 4) (var 2)
                                                                   (var 1) (var 3)))

            ))))))
| t_ret : forall G E Et A,
   (* of_m G E A -> *)
    trans G E A Et ->
    trans G (ret_m E) (comp_m A)
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

