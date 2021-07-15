From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import basic_types source subst_src rules_src derived_rules help subst_help0 subst_help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

Definition mapi {A B: Type} (f: (nat * A) -> B) (L: seq A) :=
   let enumerated := iota 0 (size L) in
  map f (zip enumerated L).

 Definition foldri {A B: Type} (f: (nat * A) -> B -> B) (acc: B) (L: seq A) :=
   let enumerated := iota 0 (size L) in
  foldr f acc (zip enumerated L).

(*moveGamma almost definitely wrong because it assumes Gamma starts from beginning of
 context (var 0) where as there's probably more stuff at the end
 probably need to pass in a starting index to move Gamma
 best to work this out when you can test in real time whether its working when you're
 at there in a proof*)

(*functions which take in the world and give you the type*)
(*make_ref: tau in source -> (translation of ref tau into target)*)


Coercion var: nat >-> term.

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
                          (*does NOT send the refs to comp ref*)
      | reftp_m tau' => sigma nattp (let l1 := (ppi2 W) in (* i := 0*)
           let i := (var 0) in
            prod (lt_t i (subst sh1 l1))
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

      | comp_m tau' => subst1 l1 (all nzero preworld((* l1 = 1, u  := var 0. this substitution must go under.*) 
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
                      ))
      | _ => unittp end.


(*translation of source contexts to target contexts (at a given world)*)
 Lemma move_works: forall G w1 l1 w2 l2 T,
     tr G (oof (ppair w1 l1) world) ->
     tr G (oof (ppair w2 l2) world) ->
     tr G (oof (move T) (arrow (subseq (ppair w1 l1) (ppair w2 l2))
                               (arrow
                                  (trans_type w1 l1 T)
                                  (trans_type w2 l2 T)
                               )
                        )
          ).
   Admitted.

(*makes a product type at a world out of a source context *)
 Fixpoint Gamma_at (G: source.context) (w l: Syntax.term False) :=
   match G with
     nil => unittp 
   | A::xs => (prod (trans_type w l A) (Gamma_at xs w l)) end
 .

(*make a target context out of a source context*)
 Fixpoint Gamma_at_ctx (G: source.context) (w l: Syntax.term False):=
   mapi (fun pair =>
           match pair with (i, A) => 
           hyp_tm (trans_type (shift i w) (shift i l) A) end) G.

(*making a product value out of the variables in a source context
 assume vars to start at 0*)
 Definition gamma_at (G: source.context ):= foldri (fun pair => fun acc => match pair with (i, A) =>
                                                                   @ppair False (var i) acc end) triv G.


 Definition move_app A (m : term False) (x: term False) :=
   app (app (move A) m) x.

 (*making a pair of type (a big product at U) out of a pair of (a big product at W)
  iterating over the pair
 but how far to go? use the list because it should be the same size as the pair*)
Fixpoint move_gamma (G: source.context) (m: Syntax.term False) (gamma: Syntax.term False) :=
   match G with
     nil => gamma
   | A::xs => ppair (move_app A m (ppi1 gamma)) (move_gamma xs m (ppi2 gamma)) end.

 (*not even doing substituions any more, completely differeent from old move Gamma*)



 (*the actual type of translated terms*)
 Lemma trans_typed1 {D G w A}:
   tr D (oof w preworld) -> 
 tr D
    (deqtype (pi nattp
                 (arrow (Gamma_at G (shift 1 w) (var 0))
                        (trans_type (shift 1 w) (var 0) A)
             ) )
(pi nattp
                 (arrow (Gamma_at G (shift 1 w) (var 0))
                        (trans_type (shift 1 w) (var 0) A)
    ) )).
   Admitted.

 Inductive trans: source.context -> source.term -> source.term -> (Syntax.term False) -> Type :=
  t_bind: forall G E1 Et1 E2 Et2 A B, of_m G (bind_m E1 E2) (comp_m B) ->
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
(ppair x' (move_gamma G make_subseq (var 4)))                                                 in
                               let e2bar' := app (app (app btarg lv) make_subseq) sv in
                               make_bind e2bar' (lam (
                                                    let z2 := (var 0) in
                                                    ret_a (ppair (picomp1 z2)
                                                                   (ppair (ppair make_subseq (*z2 \circ z1*)
                                                      (picomp3 z2)) (picomp4 z2))                         
                                                        )
                                               ))
              )

          )

    ))
                                         ))))
  | t_ref: forall G E Et A, 
         of_m G (ref_m E) (reftp_m A) -> trans G E A Et ->
         trans G (ref_m E) (reftp_m A) (lam (lam (lam (lam ( lam ( (*l1, g, l, m, s*)
         let l := var 2 in                                                        
         let m1 := make_subseq in (*u <= u1)*)
         let p1 := (ppair m1
                         (lam (lam ( lam ( (*making a value of type store U1, lambdas go l2, m2, i*)
                                         let l1 := var 7 in
                                         let g := var 6 in
                                         let l := var 5 in
                                         let s := var 3 in
                                         let l2 := var 2 in
                                         let i := var 0 in
                                         let x := app (app (shift 8 Et) l1) g in
                                         let m12 := make_subseq in (*m2 o m1 : U <= U2*)
                                         let m02 := make_subseq in (*m12 o m : W <= U2*)
                                         bite (lt_b i l)
                                              (app (app (app s l2) m12) i) (*move value in s:store(U) to U2*)
                                              (next (move_app A m02 x)) (*move x to be : |> A @ U2*)
                                               ))
                         ))
         ) in
             ret_a (ppair (nsucc l) (*length of new world*)
                          (ppair p1 (*new word is accessible from current world, *)
                                 (ppair l (ppair triv (lam triv)) (*ref A @ new world*)
                                 ) 
                          )
                   ))))))).


