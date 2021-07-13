From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import basic_types source subst_src rules_src help subst_help0 subst_help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*moveGamma almost definitely wrong because it assumes Gamma starts from beginning of
 context (var 0) where as there's probably more stuff at the end
 probably need to pass in a starting index to move Gamma
 best to work this out when you can test in real time whether its working when you're
 at there in a proof*)

(*functions which take in the world and give you the type*)
(*make_ref: tau in source -> (translation of ref tau into target)*)


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
      | _ => nattp end.

  (*after this return to bind proof, use above for next goal,
   probably should save as hypothesis that W and U are worlds*)


(*makes a sigma type out of a source context *)
(*this should be a product actually cuz the translated types never depend
 on any other translated type
 start here*)
 Fixpoint Gamma_at (G: source.context) (w l: Syntax.term False) :=
   match G with
     nil => unittp 
   | A::xs => (prod (trans_type w l A) (Gamma_at xs w l)) end
 .


 Definition mapi {A B: Type} (f: (nat * A) -> B) (L: seq A) :=
   let enumerated := iota 0 (size L) in
  map f (zip enumerated L).

 Definition foldri {A B: Type} (f: (nat * A) -> B -> B) (acc: B) (L: seq A) :=
   let enumerated := iota 0 (size L) in
  foldr f acc (zip enumerated L).

 Fixpoint Gamma_at_ctx (G: source.context) (w l: Syntax.term False):=
   mapi (fun pair =>
           match pair with (i, A) => 
           hyp_tm (trans_type (shift i w) (shift i l) A) end) G.

(*making a sigma value out of the variables in a source context
 assume to start at 0*)
 Definition gamma_at (G: source.context ):= foldri (fun pair => fun acc => match pair with (i, A) =>
                                                                   @ppair False (var i) acc end) triv G.


 Definition move_app A (m : term False) (x: term False) :=
   app (app (move A) m) x.
 (*making a pair of one type out of a pair of a different type
  iterating over the pair
  but how far to go? use the list because it should be the same size as the pair*)

Fixpoint move_gamma (G: source.context) (m: Syntax.term False) (gamma: Syntax.term False) :=
   match G with
     nil => gamma
   | A::xs => ppair (move_app A m (ppi1 gamma)) (move_gamma xs m (ppi2 gamma)) end.

 (*not even doing substituions any more, completely differeent from old move Gamma*)
 Lemma move_gamma_works: forall D G w1 l1 w2 l2 m Gamma,
     tr D (oof m (subseq (ppair w1 l1) (ppair w2 l2))) ->
     tr D (oof Gamma (Gamma_at G w1 l1)) ->
     tr D (oof (move_gamma G m Gamma) (Gamma_at G w2 l2)).
 Admitted.
Lemma Gamma_at_intro: forall D G A w l x P, 
 tr D (oof (ppair w l) world) ->
 tr D (oof P (Gamma_at G w l)) ->
tr D (oof x (trans_type w l A)) ->
 tr D (oof (ppair x P) (Gamma_at (A::G) w l)). Admitted.

 Lemma Gamma_at_type {D G w l}:
   tr D (oof w preworld) -> tr D (oof l nattp) ->
 tr D
    (deqtype (Gamma_at G w l)
       (Gamma_at G w l)). Admitted.

 Inductive trans: source.context -> source.term -> source.term -> (Syntax.term False) -> Type :=
  t_bind: forall G E1 Et1 E2 Et2 A B (He3: of_m G (bind_m E1 E2) (comp_m B)),
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
         trans G (ref_m E) (reftp_m A)
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
                               (next (move_app A m02 x)) (*|> tau @ u3*) 
                                               ))
                                               ))
                                         
                                    in
                             ret_a (ppair (nsucc l)
                                          (ppair p1
                                          (ppair l (ppair triv (lam triv)) (*ref*)
                                        )
                            )
                    ))))
                      ) ).

(*Problem with below is that lv isn't from G and can't be shifted 5
app (shift 5 (lam (*x' lam*) (
                                                     move_Gamma G (make_subseq)                                                           1 (*ignore x'*) (app Et2 lv))))
*)

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

