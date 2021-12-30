From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import basic_types source subst_src rules_src
     derived_rules help subst_help0 subst_help.
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



Fixpoint  trans_type (w1 l1: Syntax.term obj) (tau : source.term) {struct tau}: (Syntax.term obj)                                                                          
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
      | reftp_m tau' => sigma nattp ( (* i := 0*)
           let i := (var 0) in
            prod (lt_t i (subst sh1 l1))
                 (all nzero preworld (*wl1:= 2, i := 1, v := 0*)
                      (pi nattp (*wl1:= 3, i := 2, v := 1, lv := 0*)
                      (
            let w := (shift 3 w1) in
            let l1 := (shift 3 l1) in
            let i := (var 2) in
            let v := (var 1) in
            let lv := (var 0) in
          eqtype (app (app (app w i) (next v)) (next lv))
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
 (*compm1_Type starts here*)                        (arrow (store u l)
                         (laters (exist nzero preworld ((* l1 = 3, u := 2, l:= 1, v = 0*)
                                          sigma nattp (*l1 = 4 u := 3, l := 2, v= 1, lv := 0*)
                                          (let u := Syntax.var 3 in
                                              let l := Syntax.var 2 in
                                              let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              let U := ppair u l in
                                              let V := ppair v lv in
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq U V) (store v lv))
                                                     (trans_type v lv tau'))))
                                    )
                       ))
                      ))
      | _ => unittp end.

(*no free variables in translation of types*)
Lemma subst_trans_type :forall w l A s,
    (subst s (ppair w l)) = (ppair w l) ->
    (subst s (trans_type w l A)) = (trans_type w l A).
  move => w l A s H. move: w l s H. induction A; intros;simpl; auto; simpsub_big; simpl; try rewrite - subst_ppair;
 try rewrite subst_compose; try rewrite H. 
  - (*arrow*)
    suffices:  ((subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A1)) = (trans_type (var 1) (var 0) A1)) /\ ((subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A2)) = (trans_type (var 1) (var 0) A2)). move => [Heq1 Heq2].
    rewrite Heq1 Heq2. auto.
    split; [eapply IHA1 | eapply IHA2]; simpsub; auto.
  - (*comp*)
 rewrite subst_ppair in H. inversion H. rewrite H1.
rewrite !subst_ppair !subst_compose !H2.
simpsub_big. simpl. suffices: (
            (subst
                            (dot (var 0)
                               (dot (var 1)
                                  (dot (var 2)
                                     (dot (var 3)
                                        (dot 
                                           (subst (sh 4) l)
                                           (compose s (sh 4)))))))
                            (trans_type (var 1) (var 0) A)
            ) = subst
                            (dot (var 0)
                               (dot 
                                 (var 1)
                                 (dot 
                                 (var 2)
                                 (dot 
                                 (var 3)
                                 (dot
                                 (subst (sh 4) l)
                                 (sh 4))))))
                            (trans_type 
                               (var 1) 
                               (var 0) A)

          ).
move => Heq.
rewrite Heq. unfold subst1. auto. repeat rewrite IHA; simpsub; auto.
  - (*ref*)
    rewrite !subst_compose.
    simpsubin H. inversion H. rewrite ! H1 ! H2.
    suffices: (subst
                      (dot (var 0)
                         (dot (var 1)
                            (dot (var 2) (compose s (sh 3)))))
                      (trans_type (var 1) (var 0) A)) =
              (trans_type (var 1) (var 0) A).
    move => Heq. rewrite Heq. auto. simpsub_big.
eapply IHA. simpsub. auto.
Qed.
Ltac simpsub_type := simpl; simpsub_big; simpl; rewrite subst_trans_type; simpl.

  (*start here automate these ugly cases*)
Lemma sh_trans_type : forall w l A s,
    (subst (sh s) (trans_type w l A)) = (trans_type
                                           (subst (sh s) w)
                                           (subst (sh s) l) A).
  induction A; intros; simpl; auto; simpsub_big; repeat rewrite plusE;
repeat rewrite - addnA;
    simpl; change (1 + 1) with 2;
      replace (1 + 0) with 1; auto; repeat rewrite subst_trans_type; auto.
Qed.

(*start here write ltac for these two*)
 Lemma subst1_trans_type : forall w l A s,
    (subst1 s (trans_type w l A)) = (trans_type
                                            (subst1 s w)
                                         (subst1 s l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.

 Lemma subst1_under_trans_type : forall w l A s n ,
    (subst (under n (dot s id)) (trans_type w l A)) = (trans_type
                                            (subst (under n (dot s id)) w)
                                         (subst (under n (dot s id)) l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.

Lemma sh_under_trans_type : forall w l A s n ,
    (subst (under n (sh s)) (trans_type w l A)) = (trans_type
                                            (subst (under n (sh s)) w)
                                         (subst (under n (sh s)) l) A).
  induction A; intros; simpl; auto; simpsub_big; auto; try
                   (simpl; rewrite ! subst_trans_type; auto).
 Qed.



 (*making a pair of type (a big product at U) out of a pair of (a big product at W)
  iterating over the pair
 but how far to go? use the list because it should be the same size as the pair*)

 Fixpoint Gamma_at (G: source.context) (w l: Syntax.term obj) :=
   match G with
     nil => unittp 
   | A::xs => (prod (trans_type w l A) (Gamma_at xs w l)) end
 .


 (*making a pair of type (a big product at U) out of a pair of (a big product at W)
  iterating over the pair
 but how far to go? use the list because it should be the same size as the pair*)
Fixpoint move_gamma (G: source.context) (m: Syntax.term obj) (gamma: Syntax.term obj) :=
   match G with
     nil => gamma
   | A::xs => ppair (move_app A m (ppi1 gamma)) (move_gamma xs m (ppi2 gamma)) end.

(*making a product value out of the variables in a source context
 assume vars to start at 0*)
Fixpoint gamma_at (G: source.context ):= match G with
                                             [::] => triv
                                           | g::gs => @ppair obj (var 0) (shift 1 (gamma_at gs)) end.

Lemma subst_Gamma_at :forall w l s G,
    (subst s (ppair w l)) = (ppair w l) ->
    (subst s (Gamma_at G w l)) = (Gamma_at G w l).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite IHG subst_trans_type; auto. Qed.

Lemma subst_move_gamma :forall g m s G,
    (subst s (move_gamma G m g)) = move_gamma G (subst s m) (subst s g).
  intros. move: g m s. induction G; intros; auto. simpl. simpsub.
  rewrite (IHG (ppi2 g) m s); auto. unfold move_app. simpsub. rewrite subst_move.
  auto. Qed.


Lemma sh_under_Gamma_at: forall G w l s n,
    (subst (under n (sh s)) (Gamma_at G w l)) = (Gamma_at G (subst (under n (sh s)) w)
                                                (subst (under n (sh s)) l)).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite sh_under_trans_type IHG. auto. Qed.


Lemma sh_Gamma_at: forall G w l s,
    (subst (sh s) (Gamma_at G w l)) = (Gamma_at G (subst (sh s) w)
                                                (subst (sh s) l)). intros.
  change (sh s) with (@ under obj 0 (sh s)). apply sh_under_Gamma_at.
Qed.

Hint Rewrite sh_Gamma_at subst_move_gamma: subst1.

 Lemma subst1_Gamma_at: forall G w l s, 
    (subst (dot s id) (Gamma_at G w l)) = (Gamma_at G (subst1 s w)
                                                                (subst1 s l)).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite subst1_trans_type IHG. auto. Qed.

Lemma subst1_under_Gamma_at: forall G w l s n, 
     (subst (under n (dot s id)) (Gamma_at G w l)) =
     (Gamma_at G (subst (under n (dot s id) ) w)
               (subst (under n (dot s id) ) l)).
  intros. induction G. simpl; auto.
  simpl. simpsub. rewrite subst1_under_trans_type IHG. auto.
Qed.

 Inductive trans: source.context -> source.term -> source.term -> (Syntax.term obj) -> Type :=
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
         of_m G (ref_m E) (comp_m (reftp_m A)) -> trans G E A Et ->
         trans G (ref_m E) (comp_m (reftp_m A)) (lam (lam (lam (lam ( lam ( (*l1, g, l, m, s*)
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
                                         bite (ltb_app i l)
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
                   )))))))
  | t_assign: forall G R Rt E Et A,
      of_m G R (reftp_m A) ->
      of_m G E A ->
      trans G R (reftp_m A) Rt ->
      trans G E A Et ->
      trans G (asgn_m R E) (comp_m unittp_m)
            (lam (lam (lam (lam ( lam ( (*l = 4, g = 3, l1 = 2, m = 1, s1 = 0*)
                                      let l := var 4 in
                                      let m := var 1 in
                                      let l1 := var 2 in
                                      let g := var 3 in
                                      let s1 := var 0 in 
                                      let ref := move_app (reftp_m A) m (app (app (shift 5 Rt) l) g) in
                                      let i := ppi1 ref in
                                      let p := ppi2 ref in
                                      let store_u1  := lam (lam (lam (*l2 = 2, m1 = 1,j = 0*)
                                                                  (
                                                                    let j := (var 0) in
                                                                    let l2 := var 2 in
                                                                    let m1 := var 1 in
                                                                    let i := shift 3 i in
                                                                    let l := shift 3 l in
                                                                    let g := shift 3 g in
                                                                    bite
                                                                      (app (eq_b j) i)
                                                                      (next (move_app A (make_subseq)
                                                                    (app (app (shift 8 Et) l) g)))
                                                                      (app (app (app (shift 3 s1) l2) m1) j)
                                                                 ))) in
                                      ret_a (ppair l1
                                                   (ppair
                                                      (ppair make_subseq store_u1)
                                                      triv))
            ))))))
  | t_deref: forall G R Rt A,
      of_m G R (reftp_m A) ->
      trans G R (reftp_m A) Rt ->
      trans G (deref_m R) (comp_m A) 
            (lam (lam (lam (lam ( lam ( (*l = 4, g = 3, l1 = 2, m = 1, s = 0*)
                                      let l := var 4 in
                                      let g := var 3 in
                                      let l1 := var 2 in
                                      let m := var 1 in
                                      let s := var 0 in
                                      let ref := move_app (reftp_m A) m (app (app (shift 5 Rt) l) g) in
                                      let i := ppi1 ref in
                                      let e := prev (app (app (app s l1) make_subseq) i) in
                                     (inr (next (inl (ppair
                                                                            l1
                                                                            (ppair (
                                                                                 ppair make_subseq s)
                                                                                   e)
                                                                               )
                                    ))))
            )))))
| t_ap : forall G E1 Et1 E2 Et2 Targ T2,  
      of_m G E1 (arrow_m Targ T2) ->
      of_m G E2 Targ ->
      trans G E1 (arrow_m Targ T2) Et1 ->
      trans G E2 Targ Et2 ->
      trans G (app_m E1 E2) T2
           ( lam (lam  (*l = 1, g = 0*)
                   (let Et1 := shift 2 Et1 in
                   let Et2 := shift 2 Et2 in
                   let l := (var 1) in
                   let g := (var 0) in
                   let arg := (app (app Et2 l) g) in
                   (app (app (app (app (app Et1 l) g) l) make_subseq) arg)
                )))
| t_lam : forall G E Et Targ T2,
      of_m (Targ::G) E T2 ->
      trans (Targ::G) E T2 Et ->
      trans G (lam_m E) (arrow_m Targ T2) 
            (lam (lam (lam (lam (lam (*l1 =4, g = 3, l = 2
                                      m = 1, x = 0*)
                                   (app (app (shift 5 Et) (var 2))
                                        (ppair (var 0) (move_gamma G (var 1) (var 3)))

            ))))))
| t_ret : forall G E Et A,
    of_m G E A ->
    trans G E A Et ->
    trans G (ret_m E) (comp_m A)
          (lam (lam (lam (lam (lam (*l1 = 4, g = 3, l =2, m = 1, s = 0*)
                                 (let l1 := var 4 in
                                  let g := var 3 in
                                  let l := var 2 in
                            let m := var 1 in
                            let s := var 0 in
                            let e := move_app A m (app (app (shift 5 Et) l1) g) in
                            inl (
                                (ppair
                                   l
                                   (ppair (ppair make_subseq s) e))
                            )

          )))))).

