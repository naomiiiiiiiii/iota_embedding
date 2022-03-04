Require Import Program Equality Ring Lia Omega.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq eqtype ssrnat.
From istari Require Import lemmas0
     source subst_src rules_src basic_types0 basic_types
     help subst_help0 subst_help trans derived_rules embedded_lemmas proofs.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Equivalences.
From istari Require Import Rules Defined DefsEquiv.

Theorem total G E A: of_m G E A ->
                exists ebar, trans G E A ebar.
  intros He. induction He.
  {exists (lam (lam (gamma_nth (var 0) i))). constructor. assumption.
  }
  { exists (lam (lam nzero)). constructor. 
  }
  {
    destruct IHHe as [mbar Hm].
    exists (lam (lam (app (app (subst (sh 2) mbar) (var 1)) (var 0)))).
    constructor. assumption.
  }
  { destruct IHHe as [Et Hm].
    exists 
      (lam (lam (lam (lam (lam
                             (app (app (shift 5 Et) (var 2))
                                        (ppair (var 0) (move_gamma G (var 4) (var 2)
                                                                   (var 1) (var 3)))

            )))))). constructor. assumption.
  }
  { destruct IHHe1 as [Et1 Het1]. destruct IHHe2 as [Et2 Het2].
    exists ( lam (lam 
                   (let Et1 := shift 2 Et1 in
                   let Et2 := shift 2 Et2 in
                   let l := (var 1) in
                   let g := (var 0) in
                   let arg := (app (app Et2 l) g) in
                   (app (app (app (app (app Et1 l) g) l) (make_subseq_refl l)) arg)
                ))). eapply t_ap. apply Het1. assumption.
  }
  { destruct IHHe as [Et Het].
    exists 
          (lam (lam (lam (lam (lam 
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

          )))))). apply t_ret. assumption.
  }
  { destruct IHHe1 as [Et1 Het1]. destruct IHHe2 as [Et2 Het2].
exists ( lam (lam ( lam ( (*l1 : = 2, g: Gamma_at G = 1 l :=0 *) lam ( (*l1 := 3, l := 1, m := 0*)
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
  )))). eapply t_bind. apply Het1. assumption.
}
  {
    destruct IHHe as [Et Het].
    exists (lam (lam (lam (lam ( lam ( (*l1, g, l, m, s*)
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
                   ))))))). constructor. assumption.

  }
  { destruct IHHe1 as [Et Het1]. destruct IHHe2 as [Rt Het2].
    exists 
            (lam (lam (lam (lam ( lam ( (*l = 4, g = 3, l1 = 2, m = 1, s1 = 0*)
                                      let l := var 4 in
                                      let m := var 1 in
                                      let l1 := var 2 in
                                      let g := var 3 in
                                      let s1 := var 0 in 
                                      let ref := move_app (reftp_m T)
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
                                                                      (next (move_app T
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
            )))))).
    constructor. assumption. assumption. }
  { destruct IHHe as [Rt Het]. 
    exists (lam (lam (lam (lam ( lam (                                       let l := var 4 in
                                      let g := var 3 in
                                      let l1 := var 2 in
                                      let m := var 1 in
                                      let s := var 0 in
                                      let ref := move_app (reftp_m T) l l1
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
            ))))). constructor. assumption.
  }
  { exists (lam (lam triv)). constructor. } Qed.
