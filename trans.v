From istari Require Import source subst_src rules_src help.
From istari Require Import Sigma Tactics
     Syntax Subst SimpSub Promote Hygiene
     ContextHygiene Equivalence Rules Defined.

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

Inductive trans source.context -> (source.term False) -> (Syntax.term False) -> Type :=
  t_ref: trans E Es ->
         trans_type T Ts ->
         tr G (oof_m E T) ->
         trans (ref E)
               (*unresolved question: need i ever use x?
                yes but move Es straight to u4 m ' o m o m0*)
lam ( (*u1  = 0*)
               ( lam (*u1 = 1 m = 0*)
                       (  lam (*u1 = 2 m = 1, s= 0*)
                            (let m := var 1 in
                             let s := var 0 in
                             let x := app (app (move_context G) triv) Es in
                             ret (ppair (ppair triv (*u2 <= u3*)
                                               (lam (*store*)
 (*
u1 = 3
m: u1 <= u2 = 2
s= 1
m': u3 <= u4 = 0*)
    (ppair (app s triv) (*store u2*)
    (next (app (move_app T) (app Es u1)))(*|> tau @ u3*) )
                                               )

                                 ) )
                             (exist world
        ([u']
         prod (prod (subseq u2 u')
         (store u')) ((make_ref Ts) u'))))   type
(ppair (ppair
       triv   u2 <:= x::u2
        (all world ([uf] lam (subseq (cons (lam (later world)
                                                 ([u] letnext world u ([u'] later(Ts u')))) u2)
                                  uf)
([m'] (ppair (app s triv))
         (ES uf)))
)
                      )   store
(ppair (app length u2) (all world ([_] triv)))
)
)))
                        <- of E T
                        <- trans_type T Ts
                        <- trans E ES.
