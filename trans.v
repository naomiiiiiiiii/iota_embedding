From istari Require Import source subst_src rules_src help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*functions which take in the world and give you the type*)
(*make_ref: (translation of tau into target) -> (translation of ref tau into target)*)
Fixpoint make_ref (tau : term False) (W: term False): (Syntax.term False) :=
sigma nattp (let l1 := (ppi2 W) in (* i := 0*)
           let i := (var 0) in
            prod (ltpagetp i l1)
                 (all preworld nzero (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := ppi1 W in
            let l1 := ppi2 W in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (nth W i) (next v)) (next lv))
                 (fut (app tau (ppair v lv)))
                      )
                 ))
             )
with trans_type (tau : source.term False) (W: Syntax.term False): (Syntax.term False)
  :=  match tau with
        oper (oper_reftp_m tau' => (make_ref tau' W)
      | _ => nattp end.

      | comp_m tau' => 
                                                (lam (*w:= var 0*)
                                                (all world nzero ((*w = 1, u := var 0*)
                                                       let w := Syntax.var 1 in
                                                       let u := Syntax.var 0 in
    arrow (subseq w u) (arrow (store u)
                         (laters (exist world nzero ((*w:= 2, u:= 1, u':= 0*)
                                              let u := Syntax.var 1 in
                                              let u' := Syntax.var 0 in
                                                    prod (prod (subseq u u') (store u'))
                                                    (app Ts u'))
                                    )
                       ))
                                                ))
                                                ).
(*make trans_type a meta function
%% can return whatever for terms that aren't types cuz induction on the derivation will
 take care of it
 write up the rest of the translations*)


(*probably want to make the above a function also so that
 Gamma @ w can be calculated*)

Inductive trans: source.context -> (source.term False) -> (Syntax.term False) -> Type :=
  t_ref: forall G E Es T Ts, trans G E Es ->
         trans_type T Ts ->
         rules_src.tr G (oof_m E T) ->
         trans G (ref_m E)
               (lam ( (*l1  = 0*) lam (*l1 = 1, l = 0*)
                    ( lam (*l1 = 2, l = 1, m = 0*)
                       (  lam (*l1 = 3, l = 2, m = 1, s = 0*)
                            ( let l1 := var 3 in
                              let l := var 2 in
                             let x := app Es l1 in (*all of Es is @ u1 including vars in Gamma*)
                             let m1 := make_subseq (*u <= u1*) in
                             let p1 := ppair m1 (*store u1*)
                                               (lam (*l2*) 
 (*
l1 = 4
l = 3
m: w <= u = 2
s: store u, l = 1
l2: = 0*)                                                
                             (lam (*m2*)     
 (*
l1 = 5
l = 4
m: w <= u = 3
s: store u, l = 2
l2: = 1
  m2: u1 <= u2 = 0*)                                                
               ( lam (*i*)
 (*
l1 = 6
l = 5
m: w <= u = 4
s: store u, l = 3
l2: = 2
  m2: u1 <= u2 = 1
  i = 0*)                                                
                 (let l1 := var 6 in
                 let l := var 5 in
                 let s := var 3 in
                 let l2 := var 2 in
                 let i := var 0 in
                 let x := app Es l1 in (*all of Es is @ u1 including vars in Gamma*)
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
