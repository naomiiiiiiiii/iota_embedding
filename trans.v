From Coq.Lists Require Import List.
From istari Require Import source subst_src rules_src help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*movegamma almost definitely wrong because it assumes Gamma starts from beginning of
 context (var 0) where as there's probably more stuff at the end
 probably need to pass in a starting index to move Gamma
 best to work this out when you can test in real time whether its working when you're
 at there in a proof*)

(*functions which take in the world and give you the type*)
(*make_ref: tau in source -> (translation of ref tau into target)*)


Definition test : term False := subst1 unittp (var 0).
Compute test. (*sends var 0 to unittp*)

Definition test1 : term False := subst1 unittp (ppair (var 0) (var 1)).
Compute test1. (*sends var 0 to unittp and var 1 to var 0*)

Fixpoint  trans_type (w1 l1: Syntax.term False) (tau : source.term) {struct tau}: (Syntax.term False)                                                                          
  :=
    let W := (ppair w1 l1) in
    match tau with
        nattp_m => nattp
      | unittp_m => unittp
      | arrow_m A B => all nzero preworld (pi nattp (*u := 1, l := 0*)
                                        (let u := var 1 in
                                        let l := var 0 in
                                        let U := ppair u l in
                                        arrow (subseq (shift 2 W) U) (arrow (trans_type u l A) (trans_type u l B))
                                    ))
       | reftp_m tau' => sigma nattp (let l1 := (ppi2 W) in (* i := 0*)
           let i := (var 0) in
            prod (ltpagetp i (subst sh1 l1))
                 (all nzero preworld (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := ppi1 (shift 3 W) in
            let l1 := ppi2 (shift 3 W) in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (nth (shift 3 W) i) (next v)) (next lv))
                 (fut (trans_type v lv tau' ))
                      )
                 ))
            )

      | comp_m tau' => app (lam (all nzero preworld((* l1 = 1, u  := var 0. this substitution must go under.*)
                      pi nattp  (*l1 := 2, u = 1, l := 0*)   (                         
                                                       let l1 := Syntax.var 2 in
                                                       let u := Syntax.var 1 in
                                                       let l := Syntax.var 0 in
                                                       let U := (ppair u l) in
                                                       arrow (subseq (ppair (shift 3 w1) l1) U)
 (*compm1_Type starts here*)                        (arrow (store U)
                         (laters (exist nzero preworld ((* l1 = 3, u := 2, l:= 1, v = 0*)
                                          sigma nattp (*l1 = 4 u := 3, l := 2, v= 1, lv := 0*)
                                          (let u := Syntax.var 3 in
                                              let l := Syntax.var 2 in
                                              let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let U := ppair u l in
                                              let V := ppair v lv in
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq U V) (store V))
                                                     (trans_type v lv tau'))))
                                    )
                       ))
                      ))) l1
      | _ => nattp end.

(*proves the second part of the compm1 to be a type*)


  (*after this return to bind proof, use above for next goal,
   probably should save as hypothesis that W and U are worlds*)

Definition picomp1 (M: term False) := ppi1 M. 
Definition picomp2 (M: term False) := ppi1 (ppi1 (ppi2 M) ). 
Definition picomp3 (M: term False) := ppi2 (ppi1 (ppi2 M)). 
Definition picomp4 (M: term False) := ppi2 (ppi2 M). 

Fixpoint gamma_at (gamma: source.context) (w l: Syntax.term False) :=
  map (fun t => hyp_tm (trans_type w l t)) gamma.

(*make trans_type a meta function
%% can return whatever for terms that aren't types cuz induction on the derivation will
 take care of it
 write up the rest of the translations*)


(*probably want to make the above a function also so that
 Gamma @ w can be calculated*)


(*every time you put stuff under a lambda you probably have to shift it*)
Inductive trans: source.term -> (Syntax.term False) -> Type :=
  t_bind: forall G E1 Et1 E2 Et2 T1 T2, of_m G E1 (comp_m T1) ->
                                  of_m (cons T1 G) E2 (comp_m T2) ->
                                   trans E1 Et1 ->
                                   trans E2 Et2 ->
                                   trans (bind_m E1 E2)(
lam ( (*l1 := 0*) lam ( (*l1 := 1, l :=0 *) lam ( (*l1 := 2, l := 1, m := 0*)
                           lam ( (*l1 := 3, l := 2, m := 1, s := 0*)
                               let l1 := (var 3) in
                               let l := (var 2) in
                               let m := (var 1) in
                               let s := (var 0) in
let btarg := app (app (app (app Et1 l1) l) m) s in
make_bind btarg ( lam (*l1 := 4, l := 3, m := 2, s := 1, z1 := 0*)
              (
                               let z1 := (var 0) in (*basically added 5 vars to my context*)
                               let lv := (picomp1 z1) in
                               let mv := (picomp2 z1) in
                               let sv := (picomp3 z1) in
                               let x' := (picomp4 z1) in
                               let btarg := app (lam (
                                               move_gamma G (make_subseq) (*G is almost definitely
                                                                           the wrong context to put here*)
                                                          (app (subst (sh 5) Et2) lv))) x' in
                               let e2bar' := app (app (app btarg lv) make_subseq) sv in
                               (*start here*)
                               make_bind e2bar' (lam (
                                                    let z2 := (var 0) in
                                                    app ret (ppair (picomp1 z2)
                                                                   (ppair make_subseq (*z2 \circ z1*)
                                                        (ppair (picomp3 z2) (picomp4 z2))                         
                                                        ))
                                               ))
              )

          )

    ))
                                         )))
  | t_ref: forall G E Et T, 
         of_m G E T -> trans E Et ->
         trans (ref_m E)
               (lam ( (*l1  := 0*) lam (*l1 := 1, l := 0*)
                    ( lam (*l1 := 2, l := 1, m := 0*)
                       (  lam (*l1 := 3, l := 2, m := 1, s := 0*)
                            ( let l1 := var 3 in
                              let l := var 2 in
                             let x := app Et l1 in (*all of Et is @ u1 including vars in Gamma*)
                             let m1 := make_subseq (*u <= u1*) in
                             let p1 := ppair m1 (*store u1*)
                                               (lam (*l2*) 
 (*
l1 := 4
l := 3
m: w <= u := 2
s: store u, l := 1
l2: := 0*)                                                
                             (lam (*m2*)     
 (*
l1 := 5
l := 4
m: w <= u := 3
s: store u, l := 2
l2: := 1
  m2: u1 <= u2 := 0*)                                                
               ( lam (*i*)
 (*
l1 := 6
l := 5
m: w <= u := 4
s: store u, l := 3
l2: := 2
  m2: u1 <= u2 := 1
  i := 0*)                                                
                 (let l1 := var 6 in
                 let l := var 5 in
                 let s := var 3 in
                 let l2 := var 2 in
                 let i := var 0 in
                 let x := app Et l1 in (*all of Et is @ u1 including vars in Gamma*)
               let m1 := make_subseq (*u <= u1*) in
               let m12 := make_subseq in (*compose_sub m2 m1 *)
               let m02 := make_subseq in (*compose_sub m12 m *)
                             bite (lt_b i l)
                               (app (app (app s l2) m12) i) (*store u2*)
                               (next (move_app T m02 x)) (*|> tau @ u3*) 
                                               ))
                                               ))
                                         
                                    in
                             ret_t (ppair (nsucc l)
                                          (ppair p1
                                          (ppair l (ppair triv (lam triv)) (*ref*)
                                        )
                            )
                    ))))
                      ) ).

