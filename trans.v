From Coq.Lists Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
From istari Require Import basic_types basic_types0 source subst_src rules_src
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
    match tau with
        nattp_m => nattp
      | unittp_m => unittp
      | arrow_m A B => all nzero preworld (pi nattp (*u := 1, l := 0*)
                                        (let u := var 1 in
                                        let l := var 0 in
                                        arrow (subseq (shift 2 w1) (shift 2 l1) u l) (arrow (trans_type u l A) (trans_type u l B))
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
                                                       arrow (subseq (shift 3 w1) l1 u l)
 (*compm1_Type starts here*)                        (arrow (store u l)
                         (laters (exist nzero preworld ((* l1 = 3, u := 2, l:= 1, v = 0*)
                                          sigma nattp (*l1 = 4 u := 3, l := 2, v= 1, lv := 0*)
                                          (let u := Syntax.var 3 in
                                              let l := Syntax.var 2 in
                                              let v := Syntax.var 1 in
                                              let lv := Syntax.var 0 in
                                              (*u = 4, l = 3, subseq = 2, v = 1, lv = 0*)
                                                    prod (prod (subseq u l v lv) (store v lv))
                                                     (trans_type v lv tau'))))
                                    )
                       ))
                      ))
      | _ => unittp end.

(*no free variables in translation of types*)
Lemma subst_trans_type :forall A w l s,
    subst s w = w ->
    subst s l = l ->
    (subst s (trans_type w l A)) = (trans_type w l A).
   induction A; intros; simpl; auto; simpsub_big; simpl;  try rewrite ! subst_compose ! H ! H0. 
  - (*arrow*)
    suffices:  ((subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A1)) = (trans_type (var 1) (var 0) A1)) /\ ((subst
                (dot (var 0) (dot (var 1) (compose s (sh 2))))
                (trans_type (var 1) (var 0) A2)) = (trans_type (var 1) (var 0) A2)). move => [Heq1 Heq2].
    rewrite Heq1 Heq2. auto. simpsub_big.
     split; [eapply IHA1 | eapply IHA2]; simpsub; auto.
  - (*comp*)
 suffices: (
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
    suffices: (subst
                      (dot (var 0)
                         (dot (var 1)
                            (dot (var 2) (compose s (sh 3)))))
                      (trans_type (var 1) (var 0) A)) =
              (trans_type (var 1) (var 0) A).
    move => Heq. rewrite Heq. auto. simpsub_big.
eapply IHA. simpsub. auto. simpsub. auto.
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
Fixpoint move_gamma (G: source.context) l1 l2 (m: Syntax.term obj) (gamma: Syntax.term obj) :=
   match G with
     nil => gamma
   | A::xs => ppair (move_app A l1 l2 m (ppi1 gamma)) (move_gamma xs l1 l2 m (ppi2 gamma)) end.

(*making a product value out of the variables in a source context
 assume vars to start at 0*)
Fixpoint gamma_at (G: source.context ):= match G with
                                             [::] => triv
                                         | g::gs => @ppair obj (var 0) (shift 1 (gamma_at gs)) end.


Lemma subst_Gamma_at :forall w l s G,
    subst s w = w ->
    subst s l = l ->
    (subst s (Gamma_at G w l)) = (Gamma_at G w l).
   intros. induction G; auto. simpl. move: IHG. simpsub. move => IHG. 
   rewrite IHG subst_trans_type; auto. Qed.

Lemma subst_move_gamma :forall g l1 l2 m s G,
    (subst s (move_gamma G l1 l2 m g)) = move_gamma G (subst s l1) (subst s l2) (subst s m) (subst s g).
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


Definition make_consb_subseq n := ppair (app nsucc_leq_fn n) (lam (lam (lam triv))).

Lemma subst_make_consb_subseq n s : (subst s (make_consb_subseq n)) =
                                    make_consb_subseq (subst s n).
  intros. unfold make_consb_subseq. simpsub_bigs. auto. Qed.
Hint Rewrite subst_make_consb_subseq: core subst1.
Hint Rewrite <- subst_make_consb_subseq : inv_subst.

Fixpoint gamma_nth (bundle: Syntax.term obj) i :=
  match i with 0 => (ppi1 bundle)
          | S i' => gamma_nth (ppi2 bundle) i' end.


Lemma typed_gamma_nth w l G D g A i:
  tr D (oof w preworld) ->
  tr D (oof l nattp) ->
  Sequence.index i G A ->
  tr D (oof g (Gamma_at G w l)) ->
  tr D (oof (gamma_nth g i) (trans_type w l A)).
  intros Hw Hl. move : g G. 
  induction i; intros g G Hindex Hg.
  { simpl. inversion Hindex. subst. simpl in Hg.
    apply (tr_prod_elim1 _ _ (Gamma_at l0 w l)).
    assumption.
  }
  {
    simpl. inversion Hindex. subst.
    suffices: (tr D (oof (ppi2 g)
                         (Gamma_at l0 w l))).
    intros Hg2.
    apply (IHi _ _ H0 Hg2).
    simpl in Hg.
    apply (tr_prod_elim2 _ (trans_type w l x)).
    assumption.
  }
  Qed.



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

