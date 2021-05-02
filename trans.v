From istari Require Import source subst_src rules_src help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

(*functions which take in the world and give you the type*)
Inductive trans_type: (source.term False) -> (Syntax.term False) -> Type :=
  tt_ref: forall A As, trans_type A As -> trans_type (reftp_m A) (make_ref As)
| tt_comp: forall T Ts, trans_type T Ts -> trans_type (comp_m T)
                                                (lam (*w:= var 0*)
                                                (all world one ((*w = 1, u := var 0*)
                                                       let w := Syntax.var 1 in
                                                       let u := Syntax.var 0 in
    arrow (subseq w u) (arrow (store u)
                         (laters (exist world one ((*w:= 2, u:= 1, u':= 0*)
                                              let u := Syntax.var 1 in
                                              let u' := Syntax.var 0 in
                                                    prod (prod (subseq u u') (store u'))
                                                    (app Ts u'))
                                    )
                       ))
                                                ))
                                                ).
(*probably want to make the above a function also so that
 Gamma @ w can be calculated*)

Inductive trans: source.context -> (source.term False) -> (Syntax.term False) -> Type :=
  t_ref: forall G E Es T Ts, trans G E Es ->
         trans_type T Ts ->
         rules_src.tr G (oof_m E T) ->
         trans G (ref_m E)
(lam ( (*u1  = 0*)
               ( lam (*u1 = 1 m0 = 0*)
                       (  lam (*u1 = 2 m0 = 1, s= 0*)
                            ( let u1 := var 2 in
                              let m1 := var 1 in
                             let x := app Es u1 in (*all of Es is @ u1 including vars in Gamma*)
                             let i := getlen_subseq m1 in
                             let m2 := make_subseq (nsucc i) (*u2 <= u3*) in
                             let p1 := ppair m2 (*u2 <= u3*)
                                               (lam (*store u3*)
 (*
u1 = 3
m1: u1 <= u2 = 2
s= 1
m3: u3 <= u4 = 0*)                                                
                                                  (
                             let u1 := var 3 in
                             let m1 := var 2 in
                             let s := var 1 in
                             let m3 := var 0 in
                             let x := app Es u1 in (*all of Es is @ u1 including vars in Gamma*)
                             let i := getlen_subseq m1 in
                             let m2 := make_subseq (nsucc i) (*u2 <= u3*) in
                             let m14 := compose_sub m3 (compose_sub m2 m1) in
                             ppair
                               (app s (compose_sub m3 m2)) (*store u2*)
                               (next (move_app T m14 x)) (*|> tau @ u3*) 
                                               )
                                               )
                                         
                                    in
                             ret_t (ppair p1
                                          (ppair i (ppair triv triv)) (*ref*)
                                        )
                            )
)))).
