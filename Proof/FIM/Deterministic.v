Require Import LibTactics.
Require Export 
               KeyProperties.

Require Import Arith Lia.
Require Import Coq.Program.Equality.


Lemma subst_env_codom_fresh :
  forall Gamma z u,
    z `notin` (typefv_typ_range Gamma) ->
    subst_env u z Gamma   = Gamma. 
Proof.
  intros Gamma z u HNotIn.
  induction Gamma; auto.
  destruct a; destruct t; simpl in *; eauto.
  -
    forwards* h1: typsubst_typ_fresh_eq t u.
    rewrite h1.
    forwards* h2: IHGamma.
    rewrite h2; auto. 
  -
    forwards* h1: typsubst_typ_fresh_eq t u.
    rewrite h1.
    forwards* h2: IHGamma.
    rewrite h2; auto. 
Qed.




Lemma TWell_weakening : forall T D E F,
    TWell (F ++ D) T ->
    WFEnv (F ++ E ++ D) ->
    TWell (F ++ E ++ D) T.
Proof.
  introv H. remember (F ++ D). gen F.
  induction* H; introv Heq env; subst*.
  pick fresh y.
  apply TWell_forall with (union L
  (union [[A]]
     (union [[B]]
        (union (dom D)
           (union (dom E)
              (union (dom F)
                 (union (typefv_typ_range D)
                    (union (typefv_typ_range E)
                       (typefv_typ_range F)))))))));intros; auto.
  rewrite* app_comm_cons.
  apply H1; auto.
  apply WFPushV; eauto.
Qed.


Lemma WFTyp_weakening : forall T D E F,
    WFTyp (F ++ D) T ->
    WFEnv (F ++ E ++ D) ->
    WFTyp (F ++ E ++ D) T.
Proof.
 introv H. remember (F ++ D). gen F.
  induction* H; introv Heq env; subst*.
  -
    forwards*: disjoint_weakening H1.
  -
  pick fresh y.
  apply w_forall with (union L
  (union [[A]]
     (union [[B]]
        (union (dom D)
           (union (dom E)
              (union (dom F)
                 (union (typefv_typ_range D)
                    (union (typefv_typ_range E)
                       (typefv_typ_range F)))))))));intros; auto.
  forwards*: TWell_weakening H.
  rewrite* app_comm_cons.
  apply H1; auto.
  apply WFPushV; eauto.
Qed.



Lemma WFTyp_weakening_simpl : forall T D E,
    WFTyp D T ->
    WFEnv (E ++ D) ->
    WFTyp (E ++ D) T.
Proof.
  introv h1 h2.
  rewrite_env(nil ++ D) in h1.
  forwards*: WFTyp_weakening h1.
Qed.


Lemma TWell_weakening_simpl : forall T D E,
    TWell D T ->
    WFEnv (E ++ D) ->
    TWell (E ++ D) T.
Proof.
  introv h1 h2.
  rewrite_env(nil ++ D) in h1.
  forwards*: TWell_weakening h1.
Qed.

Lemma TWell_strengthen : forall z U E F ty,
  z `notin` [[ty]] ->
  TWell (E ++ [(z,U)] ++ F) ty ->
  TWell (E ++ F) ty.
Proof.
  intros.
  remember (E ++[(z,U)] ++ F).
  generalize dependent Heql.
  generalize dependent E.
  inductions H0; intros; subst;
  try solve[simpl in *;eauto];
  try solve[forwards*: wfenv_remove H0].
  -
  forwards*: wfenv_remove H0.
  assert(binds X (TyDis A) (E ++ F)) as h1.
  simpl in *.
  analyze_binds H1.
  eauto.
  -
  simpl in *.
  apply TWell_forall with (union L (singleton z)); intros;auto.
  forwards*: H2 X ((X, TyDis A) :: E); auto.
  forwards* h1:  typefv_typ_open_typ_wrt_typ_rec_upper  B (t_tvar_f X) 0.
  unfold open_typ_wrt_typ.
  assert(z `notin` union [[t_tvar_f X]] [[B]]).
  eauto.
  fsetdec.
Qed.
  



Lemma disjoint_strengthen : forall z U E F ty1 ty2,
  z `notin` (union [[ty1]] [[ty2]]) ->
  disjoint (E ++ [(z,U)] ++ F) ty1 ty2 ->
  disjoint (E ++ F) ty1 ty2.
Proof.
  intros.
  remember (E ++ [(z,U)] ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; subst;simpl in *;auto.
  -
     forwards* h1: spl_notin H0.
    inverts h1 as h1 h2.
    forwards* h3: IHdisjoint1.
    eauto.
    forwards* h4: IHdisjoint2.
    eauto.
  -
    forwards* h1: spl_notin H0.
    inverts h1 as h1 h2.
    forwards* h3: IHdisjoint1; eauto.
    forwards* h4: IHdisjoint2; eauto.
  -
    assert(binds X (TyDis A) (E ++ F)) as h1.
    analyze_binds  H0.
    simpl. eauto.
  -
    assert(binds X (TyDis A) (E ++ F)) as h1.
    analyze_binds  H0.
    simpl. eauto.
  -
    apply D_forall with (union (union (union L (singleton z)) [[B1]]) [[B2]]);intros; auto.
    forwards*: H1 X ((X, TyDis (t_and A1 A2)) :: E).
     assert(AtomSetImpl.Subset (typefv_typ (B1 -^ X)) (typefv_typ (t_tvar_f X) `union` typefv_typ B1)) as h5.
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(z `notin` (Metatheory.union [[t_tvar_f X]] [[B1]])). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B2 -^ X)) (typefv_typ (t_tvar_f X) `union` typefv_typ B2)) as h6.
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
   assert(z `notin` (Metatheory.union [[t_tvar_f X]] [[B2]])). auto.
   assert(z `notin` [[B1 -^ X]]); auto.
Qed.


Lemma WFTyp_strengthen : forall z U E F ty,
  z `notin` [[ty]] ->
  WFTyp (E ++ [(z,U)] ++ F) ty ->
  WFTyp (E ++ F) ty.
Proof.
  intros.
  remember (E ++[(z,U)] ++ F).
  generalize dependent Heql.
  generalize dependent E.
  inductions H0; intros; subst;
  try solve[simpl in *;eauto];
  try solve[forwards*: wfenv_remove H0].
  -
    simpl in *.
    forwards* h1: IHWFTyp1.
    forwards* h2: IHWFTyp2.
    forwards*: disjoint_strengthen H0.
  -
    forwards*: wfenv_remove H0.
    assert(binds X (TyDis A) (E ++ F)) as h1.
    simpl in *.
    analyze_binds H1.
    eauto.
  -
    simpl in *.
    apply w_forall with (union L (singleton z)); intros;auto.
    forwards*: TWell_strengthen H0.
    forwards* h1: H2 X ((X, TyDis A) :: E).
    forwards* h1:  typefv_typ_open_typ_wrt_typ_rec_upper  B (t_tvar_f X) 0.
    unfold open_typ_wrt_typ.
    assert(z `notin` union [[t_tvar_f X]] [[B]]).
    eauto.
    fsetdec.
Qed.


Lemma notin_subst_env: forall x y T F,
 x `notin` (dom F) ->
 x `notin` (dom (subst_env T y F)).
Proof.
 intros.
 inductions F;auto.
 destruct a.
 destruct t; auto.
Qed.




Lemma TWell_subst : forall x A D F B T,
    WFEnv (subst_env T x F ++ D) ->
    TWell D T ->
    TWell (F ++ x ~ TyDis A ++ D) (B -^ x) ->
    x `notin` typefv_typ_range D ->
    TWell (subst_env T x F ++ D) [x ~~> T] (B -^ x).
Proof with simpl_env; eauto using wfenv_remove.
  intros. remember (F ++ x ~ TyDis A ++ D) as G. gen F.
  induction* H1; intros; subst; simpl.
  -
    forwards* h1: IHTWell1.
  -
    forwards* h1: IHTWell.
  -
    forwards* h1: IHTWell1.
  -
    case_if.
    +
      subst.
      forwards*: TWell_weakening_simpl H0.
    +
      forwards* h1: TWell_lc_typ H0.
      forwards*: TCW_binds_3 h1 H1.
  -
    apply TWell_forall with (L := union L
    (union (singleton x)
       (union [[A]]
          (union [[B]]
             (union [[T]]
                (union [[A0]]
                   (union [[B0]]
                      (union (dom D)
                         (union (dom F)
                            (union 
                               (typefv_typ_range D)
                               (typefv_typ_range F)))))))))));intros; auto. 
    forwards* h1: H3 X ((X, TyDis A0) :: F); auto.
    simpl.
    apply WFPushV; simpl;auto.
    simpl_env in *.
    forwards* h2: notin_subst_env X x T F; auto.
    assert(X `notin` [[A0]]) as h4; auto.
    assert(X `notin` [[T]]) as h5; auto.
    forwards* h3: typefv_typ_typsubst_typ_notin x h4 h5.
    auto.
    rewrites typsubst_typ_open_typ_wrt_typ_var; eauto.
  -
    forwards* h1: IHTWell.
Qed.



Lemma Well_subst : forall x A D F B T,
    WFEnv (subst_env T x F ++ D) ->
    WFTyp D T ->
    WFTyp (F ++ x ~ TyDis A ++ D) (B -^ x) ->
    disjoint D T A ->
    x `notin` typefv_typ_range D ->
    WFTyp (subst_env T x F ++ D) [x ~~> T] (B -^ x).
Proof with simpl_env; eauto using wfenv_remove.
  intros. remember (F ++ x ~ TyDis A ++ D) as G. gen F.
  induction* H1; intros; subst; simpl.
  -
    forwards* h1: IHWFTyp1.
  -
    forwards* h1: IHWFTyp.
  -
    forwards* h1: IHWFTyp1.
    forwards* h2: IHWFTyp2.
    forwards* h3: disjoint_subst H.
  -
    case_if.
    +
      subst.
      forwards*: WFTyp_weakening_simpl H0.
    +
      forwards* h1: Well_lc_typ H0.
      forwards*: TCW_binds_3 h1 H1.
  -
  apply w_forall with (L := union L
  (union (singleton x)
     (union [[A]]
        (union [[B]]
           (union [[T]]
              (union [[A0]]
                 (union [[B0]]
                    (union (dom D)
                       (union (dom F)
                          (union 
                             (typefv_typ_range D)
                             (typefv_typ_range F)))))))))));intros; auto. 
    forwards* h3: TWell_lc_typ H.
    assert((A0 -^ x) = A0) as h5.
    forwards*: open_typ_wrt_typ_lc_typ h3.
    rewrite <- h5 in H.
    forwards* h2: TWell_subst H5 H.
    rewrite h5 in h2.
    auto.
    forwards* h1: H4 X ((X, TyDis A0) :: F); auto.
    simpl_env in *.
    simpl.
    apply WFPushV; simpl;auto.
    simpl_env in *.
    forwards* h2: notin_subst_env X x T F; auto.
    assert(X `notin` [[A0]]) as h4; auto.
    assert(X `notin` [[T]]) as h5; auto.
    forwards* h3: typefv_typ_typsubst_typ_notin x h4 h5.
    auto.
    rewrites typsubst_typ_open_typ_wrt_typ_var; eauto.
  -
    forwards* h1: IHWFTyp.
Qed.




Lemma TWell_all_open : forall D A B T,
    WFTyp D (t_forall A B) ->
    WFTyp D T ->
    disjoint D T A -> 
    WFTyp D (B ^-^ T).
Proof.
  intros. inverts H.
  pick fresh x.
  rewrite* (typsubst_typ_intro x).
  forwards*: H6 x.
  simpl_env in H.
  rewrite_env (nil ++ x ~ TyDis A ++ D) in H.
  forwards*: Well_subst H0; auto.
  simpl; auto.
  forwards*: WFTyp_WFEnv H0.
Qed.


Lemma Typing_regular_0 : forall e P G dir A,
    Typing P G e dir A -> WFTyp G A.
Proof.
  intros. remember H as Typ. clear HeqTyp. induction* H.
  - 
    apply w_arrow; auto.
    pick fresh x.
    forwards*: H0 x.
    rewrite_env(nil ++ (x, TermV A) :: G) in H2.
    forwards*: WFTyp_strengthen H2; eauto.
  - forwards* h2: IHTyping1.
    forwards* h1: Well_appDist H1.
    inverts* h1.
  -
    forwards*: IHTyping.
    inverts* H0.
  -
    forwards* h2:IHTyping.
    forwards* h1: Well_appDist h2 H0.
    forwards* h3: TWell_all_open h1 H1.
  -
    forwards* h2:IHTyping.
    forwards* h1: Well_appDist h2 H0.
    inverts h1;auto.
Qed.


Lemma Typing_inf_chk: forall G v A P,
 Typing P G v Inf A -> Typing P G v Chk A.
Proof.
  introv typ.
  forwards*: Typing_regular_0 typ.
Qed.

Lemma Cast_unique: forall (v v1 v2 : exp) (A B: typ) P,
    value v ->
    Typing P nil v Chk B ->
    Cast (v) A v1 -> 
    Cast (v) A v2 ->
    v1 = v2.
Proof with (lia; auto).
    introv Val Typ R1 R2.
    lets R1': R1.
    lets R2': R2.
    gen P B v2. 
    inductions R1'; intros;
    try solve [forwards~: casting_toplike R1 R2].
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[exfalso; apply H0; auto];
      try solve[exfalso; apply H1; auto];
      try solve[inverts* H].
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[exfalso; apply H0; auto];
      try solve[exfalso; apply H1; auto];
      try solve[inverts* H].
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h2: split_ord_false H4;
      inverts h2]; try solve[inverts H as h1;inverts h1].
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h2: split_ord_false H2;
      inverts h2]; try solve[inverts H2 as h1;inverts h1];
      try solve[inverts H1].
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h2: split_ord_false H2;
      inverts h2].
    -
       inverts R2' as h4 h5 h6; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h2: split_ord_false h4;
      inverts h2];
      try solve[inverts H1].
      inverts Typ as h7 h8.
      inverts h7 as h7.
      inverts Val as h9; try solve[inverts h9].
      forwards h10: Typing_inf_chk h7.
      forwards h3: IHR1' h10 h5; auto.
      congruence.
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h2: split_ord_false H1;inverts h2];
      try solve[inverts Val as hh0; try solve[inverts hh0];
      inverts Typ as h1;
      inverts h1 as h2 h3; eauto;
      forwards*: Typing_inf_chk h2];
      try solve[inverts H1].
      +
        inverts Val as hh0; try solve[inverts hh0];
        inverts Typ as h1;
        inverts h1 as h2 h3.
        forwards h4: casting_sub H7; auto.
        forwards h5: casting_sub R1'; auto.
        forwards h6: typ_value_ptype h2; auto.
        forwards h7: typ_value_ptype h3; auto.
        rewrite h6 in *.
        rewrite h7 in *.
        forwards h8: disjoint_completeness H13; auto.
        unfold disjointSpec in *.
        forwards h9: h8 h5 h4.
        forwards~: casting_toplike R1 R2.        
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h2: split_ord_false H1;inverts h2];
      try solve[inverts Val as hh0; try solve[inverts hh0];
      inverts Typ as h1;
      inverts h1 as h2 h3; eauto;
      forwards*: Typing_inf_chk h3];
      try solve[inverts H1].
      +
        inverts Val as hh0; try solve[inverts hh0];
        inverts Typ as h1;
        inverts h1 as h2 h3.
        forwards h4: casting_sub H7; auto.
        forwards h5: casting_sub R1'; auto.
        forwards h6: typ_value_ptype h2; auto.
        forwards h7: typ_value_ptype h3; auto.
        rewrite h6 in *.
        rewrite h7 in *.
        forwards h8: disjoint_completeness H13; auto.
        unfold disjointSpec in *.
        forwards h9: h8 h4 h5.
        forwards~: casting_toplike R1 R2.        
    -
      inverts R2'; auto;
      try solve[forwards~: casting_toplike R1 R2];
      try solve[forwards* h1: split_ord_false H;inverts h1];
      try solve[inverts H].
      forwards* h1: split_unique H H0.
      lets(t1&t2): h1. substs.
      forwards* h2: IHR1'1 R1'1 H1.
      forwards* h3: IHR1'2 R1'2 H2.
      substs*.
Qed. 


Lemma pat_uniq_arr: forall A t1 t2 t3 t4,
 appDist A (t_arrow t1 t2) ->
 appDist A (t_arrow t3 t4) ->
 t1 = t3 /\ t2 = t4.
Proof.
  introv pa1 pa2. gen t3 t4.
  inductions pa1; intros;try solve[inverts* pa2].
  inverts H.
  inverts* pa2.
  inverts H1.
  forwards* h1:IHpa1_1 H3.
  forwards* h2:IHpa1_2 H7.
  inverts* h1.
  inverts* h2.
Qed.


Lemma pat_uniq_rcd: forall A t1 t2 t3 t4,
 appDist A (t_rcd t1 t2) ->
 appDist A (t_rcd t3 t4) ->
 t1 = t3 /\ t2 = t4.
Proof.
  introv pa1 pa2. gen t3 t4.
  inductions pa1; intros;try solve[inverts* pa2].
  inverts H.
  inverts* pa2.
  inverts H1.
  forwards* h1:IHpa1_1 H2.
  forwards* h2:IHpa1_2 H6.
  inverts* h1.
  inverts* h2.
Qed.

Lemma pat_uniq_ref: forall A t1 t2,
 appDist A (t_ref t1) ->
 appDist A (t_ref t2) ->
 t1 = t2.
Proof.
  introv pa1 pa2.
  inductions pa1; intros;try solve[inverts* pa2].
  inverts* H.
Qed.


Lemma fill_eq: forall mu E0 e0 E e1 r1 r2 mu1 mu2,
  fill E0 e0 = fill E e1 ->
  step (e0, mu) (r1,mu1) ->
  step (e1, mu) (r2,mu2) ->
  WFTypformed E ->
  WFTypformed E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen mu mu1 mu2 E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros;
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards* h1: step_not_value red1;inverts h1];
  try solve[inductions E; unfold fill in *; inverts* eq];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards* h1: step_not_value red2;inverts h1].
Qed.



Lemma fill_chk: forall F e dir P A,
 Typing P nil  (fill F e) dir A ->
 exists B, ((Typing P nil  e Chk B) \/( 
  (exists e', e = (e_abs e')) \/ (exists e', e = (e_tabs e')) \/ (exists e', e = (e_loc e')) \/ e = e_loct)).
Proof.
  introv typ.
  destruct F; unfold fill in *;
  try solve[inverts typ as h1 h2;
  try solve[forwards* h3: Typing_regular_0 h1 ];
  inverts h1 as h11 h2;
  forwards* h3: Typing_regular_0 h11 ].
  -
    inverts typ as h1 h2.
    forwards* h3: Typing_regular_0 h2.
    inverts h1 as h11 h22;
    forwards* h3: Typing_regular_0 h22.
  -
    inverts typ as h1 h2; try solve[exists; right; left*];
    try solve[exists; right; right; left*];
    try solve[exists; right; right; right*];
    try solve[exists; left*].
    inverts h1 as h11 h22;
    try solve[exists; right; left*];
    try solve[exists; right; right; left*];
    try solve[exists; right; right; right*];
    try solve[exists; left*].
    Unshelve. 
    apply t_top. apply t_top. apply t_top. apply t_top. apply t_top.
    apply t_top. apply t_top. apply t_top.
Qed.


Lemma Merge_uniq: forall A B t1 t2,
 Merge A B t1 ->
 Merge A B t2 ->
 t1 = t2.
Proof.
  introv h1 h2. gen t2.
  inductions h1; intros;try solve[inverts* h2].
Qed.



Lemma appDist_uniq: forall A t1 t2,
 appDist A t1 ->
 appDist A t2 ->
 t1 = t2.
Proof.
  introv h1 h2. gen t2.
  inductions h1; intros;try solve[inverts* h2].
  inverts h2.
  forwards* h5: IHh1_1.
  forwards* h6: IHh1_2.
  subst.
  forwards*: Merge_uniq H H2.
Qed.


Lemma Typing_chk2inf: forall D G v A,
    Typing D G v Chk A -> exists B, Typing D G v Inf B /\ algo_sub B A.
Proof.
  intros D G v A Typ.
  inductions Typ; try solve [inverts Val].
  exists.
  split*.
Qed.


Lemma papp_unique: forall v e e1 e2 A P mu mu1 mu2,
    value v -> value e -> Typing P nil (e_app v e) Inf A -> papp v (arg_exp e) mu e1 mu1 -> papp v (arg_exp e) mu e2 mu2 -> e1 = e2.
Proof with eauto.
  introv Val Val2 Typ P1 P2.
  gen e2 A.
  inductions P1; intros; inverts* P2;
  try solve[forwards* h1: appDist_uniq H0 H4; inverts* h1];
  try solve[inverts* H9];
  try solve[inverts* H];
  try solve[
    inverts Val as h0; try solve[inverts h0 as h0;inverts h0]
  ].
  -
    inverts Typ as h1 h2.
    inverts h1 as h4 h5; try solve[inverts h4 as h4; inverts h4].
    forwards* h1: Cast_unique H1 H11.
    congruence.
  - inverts Val as h0; try solve[inverts h0 as h0;inverts h0].
    inverts Typ.
    lets (?&?&?): Typing_chk2inf H11.
    inverts H6.
    inverts H12.
    forwards* h1: Typing_regular_0 H11.
    forwards* h2: Well_lc_typ h1.
    inversion H9;subst.
    forwards*: IHP1_1 e.
    forwards*: IHP1_2 e.
    congruence.
Qed.




Lemma papp_unique4: forall v1 i5 e1 e2 A P mu mu1 mu2,
 value v1 -> Typing P nil (e_proj v1 i5) Inf A -> papp v1 (arg_la i5) mu e1 mu1 -> papp v1 (arg_la i5) mu e2 mu2 -> e1 = e2.
Proof with eauto.
  introv Val1 Typ P1 P2.
  gen e2 A.
  inductions P1; intros; inverts* P2;
  try solve[inverts H7];
  try solve[inverts H].
  - 
    inverts Val1 as h03. inverts h03.
    inverts Typ as h1 h2. inverts h1 as h3 h4 h5 h6.
    inverts h2 as h7 h8 h9.
    inverts h7 as h71 h71.
    forwards*: IHP1_1 H5 B0; auto.
    forwards*: IHP1_2 H10 B3; auto.
    congruence.
Qed.


Lemma papp_unique2: forall P v1 v2 mu mu1 mu2 e1 e2 A,
    value v1 -> value v2 -> 
    Typing P nil (e_ass v1 v2) Inf A -> papp v1 (arg_exp v2) mu e1 mu1 -> papp v1 (arg_exp v2) mu e2 mu2-> e1 = e2 /\ mu1 = mu2.
Proof with eauto.
  introv Val1 Val2 Typ P1 P2. gen e2 A mu2.
  inductions P1; intros; inverts* P2;
  try solve[forwards* h1: appDist_uniq H0 H4; inverts* h1];
  try solve[inverts H];
  try solve[
    inverts Typ as h1 h2;
    inverts h1
  ].
  -
    inverts Typ as h1 h2.
    inverts h1 as h1; try solve[inverts h1 as h1; inverts h1].
    forwards* h3: Cast_unique H0 H8.
    splits; auto.
    congruence.
Qed.



Lemma papp_unique3: forall P v1 e1 e2 A T
 mu mu1,
    value v1 -> Typing P nil (e_tapp v1 T) Inf A -> papp v1 (arg_typ T) mu e1 mu1 -> papp v1 (arg_typ T) mu e2 mu1 -> e1 = e2.
Proof with eauto.
  introv Val1 Typ P1 P2. gen e2 A.
  inductions P1; intros; inverts* P2.
  -
    inverts Val1 as h0; try solve[inverts h0].
    inverts Typ as h1 h2.
    inverts h1 as h11 h12.
    inverts h2 as h2 h21 h22.
    inverts h2.
    forwards* h4: IHP1_1 H5.
    forwards* h5: IHP1_2 H10.
    congruence.
Qed. 



Theorem step_unique: forall P mu A e r1 r2,
   P |== mu -> Typing P nil e Inf A -> step (e, mu) r1 -> step (e, mu) r2 -> r1 = r2.
Proof with solve_false.
  introv ok Typ Red1.
  gen P A r2.
  lets Red1' : Red1.
  inductions Red1; 
    introv ok Typ Red2.
  - (* fill *)
    inverts* Red2;
    try solve[destruct F; unfold fill in *; inverts H0;
    forwards* h1: step_not_value Red1;
    inverts h1].
    +
      forwards* h1: fill_eq H0.
      lets(h2&h3): h1.
      substs*.
      forwards* h4: fill_chk Typ.
      lets(t&h5):h4.
      inverts h5 as h5.
      *
      inverts h5 as h5.
      forwards* h6: IHRed1 Red1 H4.
      congruence.
      *
      inverts h5 as h5.
      inverts h5 as h5.
      forwards* h6: step_not_abs H4. inverts h6.
      inverts h5 as h5.
      inverts h5 as h5.
      forwards* h6: step_not_tabs H4. inverts h6.
      inverts h5 as h5.
      inverts h5 as h5.
      forwards* h6: step_not_loc H4. inverts h6.
      forwards* h6: step_not_loct Red1. inverts h6.
    +
      destruct F; unfold fill in *; inverts H0.
      inverts Typ as h1.
      inverts h1 as hh1; try solve[inverts hh1 as hh1;inverts hh1].
      forwards*: Well_lc_typ H7.
      forwards* h1: step_not_value Red1.
      inverts h1.
    +
      destruct F; unfold fill in *; inverts H0.
      inverts Typ as h1.
      inverts h1 as hh1; try solve[inverts hh1 as hh1;inverts hh1].
      forwards* h1: step_not_value Red1.
      inverts h1.
  - (* papp*)
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H3;
      forwards* h1: step_not_value H7;
      inverts h1
    ].
    +   
      forwards* h1: papp_unique H2 H10.
      substs*.
  - (* annov*)
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H3;
      forwards* h1: step_not_value H7;
      inverts h1
    ].
    + (* annov*)
      inverts Typ as hh1 hh2; try solve[inverts H0 as hh0;inverts* hh0].
      (* inverts hh1.
      forwards* h1: Typing_inf_chk H2. *)
      forwards* h2: Cast_unique H1 H9.
      inverts* h2.
  - (* deref *)
    inverts* Red2.
    inverts Typ as h2.
    inverts h2 as h3; try solve[inverts h3 as h3;inverts h3].
    forwards*: Well_lc_typ H9.
    destruct F; unfold fill in *; inverts H0;
    forwards* h1: step_not_value H4;
    inverts h1.
  - (* deref *)
    inverts* Red2.
    inverts Typ as h2.
    inverts h2 as h3; try solve[inverts h3 as h3;inverts h3].
    forwards*: Well_lc_typ H8.
    destruct F; unfold fill in *; inverts H0;
    forwards* h1: step_not_value H4;
    inverts h1.
  - (* ref *)
    inverts* Red2.
    +
    destruct F; unfold fill in *; inverts* H1;
    try solve[forwards* h1: step_not_value H5;inverts h1].
  - (* tapp *)
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H3;
      forwards* h1: step_not_value H7;
      inverts h1
    ].
    forwards*: papp_unique3 H2 H10.
    congruence.
  - (* ass *)
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H3;
      forwards* h1: step_not_value H7;
      inverts h1
    ].
    forwards* h1: papp_unique2 H2 H10.
    inverts* h1.
  -
    inverts Red2 as hh0 hh1 hh3; eauto;
    try solve[
      destruct F; unfold fill in *; inverts hh3;
      forwards* h1: step_not_value hh1;
      inverts h1
    ].
    forwards*: papp_unique4 H0 hh1.
    congruence.
Qed.




Theorem step_unique_both: forall P mu A e r1 r2 dir,
   P |== mu -> Typing P nil e dir A -> step (e, mu) r1 -> step (e, mu) r2 -> r1 = r2.
Proof.
 introv ok Typ Red1 Red2.
 destruct dir.
 -
   forwards*: step_unique ok Typ Red1 Red2.
 - 
   inverts Typ as typ sub.
   forwards*: step_unique ok typ Red1 Red2.
Qed.













