Require Import LibTactics.
Require Export 
               KeyProperties
               Deterministic
               IsomorphicSubtyping.

Require Import Coq.Program.Equality.
Import ListNotations.
Require Import Arith Lia.

Lemma fill_appl : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma fill_assl : forall e1 e2,
  (e_ass e1 e2) = (fill (setCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_assr : forall e1 e2,
  (e_ass e1 e2) = (fill (setCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_ref : forall e,
  (e_ref e) = (fill (refCtx) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_get : forall e,
  (e_deref e) = (fill (getCtx) e).
Proof.
  intros. eauto.
Qed.

Lemma fill_anno : forall e1 A,
  (e_anno e1 A) = (fill (annoCtx A) e1).
Proof.
  intros. eauto.
Qed.


Lemma fill_mergel : forall e1 e2,
  (e_merge e1 e2) = (fill (mergeCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_merger : forall e1 e2,
  (e_merge e1 e2) = (fill (mergeCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma fill_tapp : forall e1 A,
  (e_tapp e1 A) = (fill (tappCtx A) e1).
Proof.
  intros. eauto.
Qed.


Lemma fill_rcd : forall i e1,
  (e_rcd i e1) = (fill (rcdCtx i) e1).
Proof.
  intros. eauto.
Qed.


Lemma fill_proj : forall i e1,
  (e_proj e1 i) = (fill (projCtx i) e1).
Proof.
  intros. eauto.
Qed.

Lemma length_less: forall l n,
 l < S n ->
 l = n \/ l < n.
Proof.
  introv les.
  inverts* les.
Qed.


Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.



Lemma Typing_strenthening : forall P G e A1 A2,
    Typing P nil e Inf A1 ->
    Typing P G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 G.
  inductions Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    inverts H0.
  - (* t_app *)
    forwards * h2: IHTy1_1 H2.
    inverts* h2.
    forwards* h1: appDist_uniq H H6.
    inverts* h1.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H5.
    substs*.
  - (* t_ref *)
    forwards*: IHTy1 H2.
    inverts H; auto.
  - (* t_ref *)
    forwards*: IHTy1 H2.
    inverts H; auto.
  - (* t_all *)
    forwards*: IHTy1 H4.
    substs.
    forwards* h1: appDist_uniq H H5.
    inverts*h1.
  - (* t_rcd *)
    forwards*: IHTy1 H2.
    inverts H; auto.
  - (* t_rcd *)
    forwards*: IHTy1 H4.
    substs.
    forwards* h1: appDist_uniq H H5.
    inverts*h1.
Qed.



Lemma inference_unique : forall P G e A1 A2,
    Typing P G e Inf A1 ->
    Typing P G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards* h1: binds_unique H0 H4.
    inverts* h1.
  - (* t_app *)
    forwards * h1: IHTy1_1 H2.
    inverts* h1.
    forwards* h2: appDist_uniq H H6.
    inverts* h2.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H5.
    substs*.
  - (* t_ref *)
    forwards * h1: IHTy1 H2.
    inverts* h1.
  - 
    forwards * h1: IHTy1 H2.
    inverts* h1.
  - (* t_all *)
    forwards * h1: IHTy1 H4.
    inverts* h1.
    forwards* h2: appDist_uniq H H5.
    inverts* h2.
  - (* t_rcd *)
    forwards*: IHTy1 H2.
    inverts H; auto.
  - (* t_rcd *)
    forwards * h1: IHTy1 H4.
    inverts* h1.
    forwards* h2: appDist_uniq H H5.
    inverts* h2.
Qed.


Lemma Typing_chk_sub: forall G e A B P ,
    Typing P G e Chk A -> algo_sub A B -> WFTyp G B -> Typing P G e Chk B.
Proof.
  introv H H0.
  inductions H.
  - eapply Typ_sub.
    apply H.
    auto_sub.
Qed.





Lemma spl_disjoint : forall A B C D,
    WFTyp D A ->
    spl A B C ->
    disjoint D B C.
Proof with eauto.
  introv wf sp. gen D.
  inductions sp; intros;try solve[inverts wf; auto].
  inverts wf.
  apply D_forall with (union L
  (union L0
     (union [[A]]
        (union [[B]]
           (union [[C1]]
              (union [[C2]]
                 (union (dom D) (typefv_typ_range D))))))));intros; auto.
  forwards h2: H6 X; auto.
  forwards h3: H1 h2; auto.
  rewrite_env(nil++ (X, TyDis A) :: D) in h3.
  assert(algo_sub (t_and A A) A) as h6.
  auto.
  forwards h5: disjoint_narrowing h3 h6; auto.
Qed.




Lemma wfenv_app_comm : forall E F, 
WFEnv (F ++ E) -> WFEnv (E ++ F).
Proof.
  intros.
  generalize dependent H.
  generalize dependent F.
  induction* E.
  - intros.
    rewrite app_nil_r in H.
    now simpl.
  - intros.
    destruct a.
    destruct t.
    +
    simpl_env in *.
    apply WFPushV.
    apply IHE; auto.
    forwards*: wfenv_remove H.
    simpl_env.
    assert(a `notin` (union (dom E) [[t]])) as h2.
    apply wfenv_app_r in H.
    inverts* H.
    assert(a `notin` (dom F)) as h3.
    rewrite <- app_assoc in H; auto.
    apply wfenv_app_l in H.
    inductions F; eauto.
    simpl_env in H.
    destruct a0.
    simpl.
    assert(a `notin` (singleton a0)).
    inverts* H; simpl_env in *; eauto.
    apply wfenv_app_r in H.
    forwards*: IHF; auto.
    eauto.
    +
    simpl_env in *.
    apply WFPushT.
    apply IHE; auto.
    forwards*: wfenv_remove H.
    simpl_env.
    assert(a `notin` (dom E)) as h2.
    apply wfenv_app_r in H.
    inverts* H.
    assert(a `notin` (dom F)) as h3.
    rewrite <- app_assoc in H; auto.
    apply wfenv_app_l in H.
    inductions F; eauto.
    simpl_env in H.
    destruct a0.
    simpl.
    assert(a `notin` (singleton a0)).
    inverts* H; simpl_env in *; eauto.
    apply wfenv_app_r in H.
    forwards*: IHF; auto.
    eauto.
Qed.




Lemma WFEnv_bind_weakening : forall x I J D F,
    x `notin` [[J]] ->
    WFEnv (F ++ (x ~ TyDis I) ++ D)  ->
    WFEnv (F ++ (x ~ TyDis J) ++ D) .
Proof with eauto.
  intros.
  apply wfenv_app_comm in H0.
  inverts* H0.
  simpl_env in *.
  assert(WFEnv (x ~ TyDis J ++ D ++ F)) as h1.
  apply WFPushV; auto.
  apply wfenv_app_comm; auto.
Qed.


Lemma TWell_bind_weakening : forall x I J D C F,
    x `notin` [[J]] ->
    TWell (F ++ (x ~ TyDis I) ++ D) C ->
    algo_sub J I ->
    TWell (F ++ (x ~ TyDis J) ++ D) C.
Proof with eauto using WFEnv_bind_weakening.
  intros. remember (F ++ (x ~ TyDis I) ++ D) as G. gen F. induction* H0; intros; subst...
  - analyze_binds H2.
    applys TWell_tvar A...
    apply TWell_tvar with J...
    applys TWell_tvar A ...
  - applys  TWell_forall;intros...
    forwards*: H3 X ((X, TyDis A) :: F).
Qed.


Lemma Well_bind_weakening : forall x I J D C F,
    x `notin` (union [[J]] (union (dom F) (dom D))) ->
    WFTyp (F ++ (x ~ TyDis I) ++ D) C ->
    algo_sub J I ->
    WFTyp (F ++ (x ~ TyDis J) ++ D) C.
Proof with eauto using WFEnv_bind_weakening.
  intros. remember (F ++ (x ~ TyDis I) ++ D) as G. gen F. induction* H0; intros; subst...
  -
    forwards*: disjoint_narrowing H.
  - analyze_binds H0.
    applys w_tvar A...
    apply w_tvar with J...
    applys w_tvar A ...
  - 
    apply  w_forall with (union L
    (union (singleton x)
       (union [[I]]
          (union [[J]]
             (union [[A]]
                (union [[B]]
                   (union (dom D)
                      (union (dom F)
                         (union (typefv_typ_range D)
                            (typefv_typ_range F))))))))));intros...
    forwards*: TWell_bind_weakening H.
    forwards*: H2 X ((X, TyDis A) :: F).
    simpl; eauto.
Qed.



Lemma Typing_narrowing: forall D E P X A B T e dir,
    X `notin` (union [[B]] (union (dom E) (dom D))) ->
    Typing P (D ++ X ~ TyDis A ++ E) e dir T ->
    algo_sub B A ->
    Typing P (D ++ X ~ TyDis B ++ E) e dir T.
Proof with eauto 4 using algo_sub_lc, Well_bind_weakening, TWell_bind_weakening, WFEnv_bind_weakening; try solve_uniq.
  introv nin Typ Sub. remember (D ++ X ~ TyDis A ++ E). gen D. induction Typ; intros; substs; eauto.
  - 
    applys Typ_top... 
  - 
    applys Typ_lit... 
  - 
    apply Typ_var... 
    analyze_binds H0.
  - 
    pick fresh x and apply Typ_abs;intros; auto;
    try solve[forwards*: Well_bind_weakening H1; auto];
    try solve[forwards*: Well_bind_weakening H2; auto];
    try solve[forwards*: Well_bind_weakening H3; auto].
    forwards h1: H0 x ((x, TermV A0) :: D); auto.
  - applys Typ_merge...
    forwards*: disjoint_narrowing H Sub; auto.
  - applys Typ_sub...
  -
    applys Typ_loc...
  - pick fresh Y and apply Typ_tabs;
    try solve[forwards*: TWell_bind_weakening H1; auto].
    forwards~: H0 Y ((Y, TyDis A0) :: D).
  - applys Typ_tapp...
    forwards*: disjoint_narrowing H1 Sub; auto.
  - 
    applys Typ_unit... 
  -
    applys Typ_loct... 
Qed.



Lemma Typing_narrowing_simpl: forall P X A B T e dir,
    X `notin`  [[B]] ->
    Typing P ( X ~ TyDis A ) e dir T ->
    algo_sub B A ->
    Typing P (X ~ TyDis B ) e dir T.
Proof.
 introv h1 h2 h3.
 rewrite_env(nil ++ X ~ TyDis A ++ nil) in h2.
 forwards*: Typing_narrowing h2; auto.
Qed.


Lemma principal_type_checks2: forall v A P,
    value v ->
    Typing P nil v Inf A -> principle_type v = A.
Proof.
  introv val typ. 
  gen P A.
  inductions val; intros; inverts* typ;simpl in *;eauto;
  try solve[inverts* H].
  forwards* h1: IHval1 H1.
  forwards* h2: IHval2 H4.
  rewrite h1 in *. rewrite h2 in *.
  auto.
  forwards* h1: IHval H2.
  rewrite h1 in *.
  auto.
Qed.





Lemma topLike_appDist: forall A B, topLike A -> appDist A B -> topLike B.
Proof.
  intros. induction H0;intros;auto.
  - (* Merge *)
    inversion H0;subst.
    +
    forwards* h1: IHappDist1.
    forwards* h2: IHappDist2.
    +
    forwards* h1: IHappDist1.
    forwards* h2: IHappDist2.
    inverts h1 as h11 h12.
    inverts h2 as h21 h22.
    apply TL_all with (union L L0); intros;auto.
    assert(topLike (A3 -^ X)). auto.
    assert(topLike  (B3 -^ X)). auto.
    eauto.
    +
    forwards* h1: IHappDist1.
    forwards* h2: IHappDist2.
Qed.


Lemma Merge_TWell: forall D A B C,
    Merge A B C -> TWell D A -> TWell D B -> TWell D C.
Proof with eauto using TWell_WFEnv.
  intros. induction* H...
  -
    inverts* H0. inverts* H1.
  - (* forall *)
    inversion H0;subst. inversion H1;subst.
    apply TWell_forall with (union (union (union L L0) [[A1]]) [[B1]]). auto. intros.
    unfold open_typ_wrt_typ.
    assert(TWell ((X, TyDis (t_and A1 B1)) :: D) (A2 -^ X)).
    rewrite_env(nil ++ [(X, TyDis (t_and A1 B1))] ++ D).
    apply TWell_bind_weakening with A1;
    simpl in *; auto.
    assert(TWell ((X, TyDis (t_and A1 B1)) :: D) (B2 -^ X)).
    rewrite_env(nil ++ [(X, TyDis (t_and A1 B1))] ++ D).
    apply TWell_bind_weakening with B1; simpl in *; auto. 
    simpl in *; eauto.
  -
    inverts* H0. inverts* H1.
Qed.

(* #[export] *) Hint Immediate Merge_TWell : core.

Lemma TWell_appDist: forall D A B, TWell D A -> appDist A B -> TWell D B.
Proof.
  intros. induction H0;auto.
  - (* Merge *)
    inversion H;subst.
    forwards*:IHappDist1.
    forwards*:IHappDist2.
Qed.


Lemma Well_Merge: forall D B1 B2 B, 
 Merge B1 B2 B ->
 WFTyp D B1 -> 
 WFTyp D B2 -> 
 disjoint D B1 B2 -> 
 WFTyp D B.
Proof.
  intros. inductions H;eauto.
  -
    forwards* h1: disjoint_arr_inv H4.
    inverts H2.
    inverts* H3.
  -
    inverts H3.
    inverts H4.
    apply w_forall with 
    (union (union ((union (union (dom D) L) L0)) [[A1]]) [[B1]]);intros; auto.
    assert((t_and A2 B2 -^ X) = (t_and (A2-^ X) (B2-^ X) )) as h1.
    unfold open_typ_wrt_typ; auto.
    rewrite h1.
    forwards* h2: H10 X; auto.
    forwards* h3: H11 X; auto.
    assert(algo_sub (t_and A1 B1) A1) as h4.
    auto.
    assert(algo_sub (t_and A1 B1) B1) as h5.
    auto.
    rewrite_env(nil ++ (X, TyDis A1) :: D) in h2.
    forwards* h6: Well_bind_weakening h2; auto.
    rewrite_env(nil ++ (X, TyDis B1) :: D) in h3.
    forwards* h8: Well_bind_weakening h3; auto.
    apply w_and; auto.
    apply disjoint_forall_inv; auto.
    forwards*: WFTyp_WFEnv h6.
  -
     forwards* h1: disjoint_rcd_inv H3.
    inverts H2.
    inverts* H1.
Qed.




Lemma Well_appDist: forall D A B, WFTyp D A -> appDist A B -> WFTyp D B.
Proof.
  intros. induction H0;auto.
  - (* Merge *)
    inversion H;subst.
    forwards*:IHappDist1.
    forwards*:IHappDist2.
    forwards*: Disjoint_appDist H6.
    forwards*: WFTyp_WFEnv H1.
    forwards*: Well_Merge H0.
Qed.



Lemma Typing_regular_1 : forall e P G dir A,
    Typing P G e dir A -> lc_exp e.
Proof with (eauto 3 with LcHd).
  intros e P G dir A H.
  inductions H...
  -
    forwards h2: Well_lc_typ H1.
    pick fresh y.
    forwards h3: H y; auto.
    forwards h5: Typing_regular_0 h3.
    forwards h6: Well_lc_typ h5.
    forwards*: Well_lc_typ H1.
    eauto.
  -
     forwards h2: Typing_regular_0 H.
     forwards h3: Well_lc_typ h2.
     eauto.
  -
    forwards h2: TWell_lc_typ H1.
    pick fresh y.
    forwards h3: H y; auto.
    forwards h5: Typing_regular_0 h3.
    forwards h6: Well_lc_typ h5.
    eauto.
Qed.



Lemma Typing_regular_2 : forall P G e dir T,
    Typing P G e dir T -> WFEnv G.
Proof.
  intros. induction* H.
Qed.


Lemma Typing_lc_typ : forall e D G dir A,
    Typing D G e dir A -> lc_typ A.
Proof.
  intros. forwards*: Typing_regular_0 H.
Qed.



Lemma TWell_strengthen_2 : forall z U E F ty,
  TWell (E ++ [(z,TermV U)] ++ F) ty ->
  TWell (E ++ F) ty.
Proof.
  intros.
  remember (E ++[(z,TermV U)] ++ F).
  generalize dependent Heql.
  generalize dependent E.
  inductions H; intros; subst;
  try solve[simpl in *;eauto];
  try solve[forwards*: wfenv_remove H].
  -
    forwards*: wfenv_remove H.
    assert(binds X (TyDis A) (E ++ F)) as h1.
    simpl in *.
    analyze_binds H0.
    eauto.
  -
    simpl in *.
    apply TWell_forall with (union L (singleton z)); intros;auto.
    forwards*: H1 X ((X, TyDis A) :: E); auto.
Qed.
  


Lemma disjoint_strengthen_2 : forall z U E F ty1 ty2,
  disjoint (E ++ [(z,TermV U)] ++ F) ty1 ty2 ->
  disjoint (E ++ F) ty1 ty2.
Proof.
  intros.
  remember (E ++ [(z,TermV U)] ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H; intros; subst;simpl in *;auto.
  -
    assert(binds X (TyDis A) (E ++ F)) as h1.
    analyze_binds  H.
    simpl. eauto.
  -
    assert(binds X (TyDis A) (E ++ F)) as h1.
    analyze_binds  H.
    simpl. eauto.
  -
    apply D_forall with (union (union (union L (singleton z)) [[B1]]) [[B2]]);intros; auto.
    forwards*: H0 X ((X, TyDis (t_and A1 A2)) :: E).
Qed.


Lemma WFTyp_strengthen_2 : forall z U E F ty,
  WFTyp (E ++ [(z,TermV U)] ++ F) ty ->
  WFTyp (E ++ F) ty.
Proof.
  intros.
  remember (E ++[(z,TermV U)] ++ F).
  generalize dependent Heql.
  generalize dependent E.
  inductions H; intros; subst;
  try solve[simpl in *;eauto];
  try solve[forwards*: wfenv_remove H].
  -
    forwards*: disjoint_strengthen_2 H1.
  -
    forwards*: wfenv_remove H.
    assert(binds X (TyDis A) (E ++ F)) as h1.
    simpl in *.
    analyze_binds H0.
    eauto.
  -
    simpl in *.
    apply w_forall with (union L (singleton z)); intros;auto.
    forwards*: TWell_strengthen_2 H.
    forwards* h1: H1 X ((X, TyDis A) :: E).
Qed.



Lemma Typing_weaken : forall P G E F e dir T,
    Typing P (E ++ G) e dir T ->
    WFEnv (E ++ F ++ G) ->
    Typing P (E ++ F ++ G) e dir T.
Proof with eauto using WFTyp_weakening, TWell_weakening.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos...
    - (* abs *)
      pick fresh x and apply Typ_abs...
      rewrite_env (([(x, TermV A)] ++ E) ++ F ++ G).
      apply~ H0.
      simpl_env.
      apply WFPushT; auto.
    -
      forwards*: disjoint_weakening H.
    -
      pick fresh x and apply Typ_tabs...
      forwards*: H0 G ((x, TyDis A) :: E).
      simpl_env.
      apply WFPushV; auto.
    -
      forwards* h1: WFTyp_weakening H0.
      forwards*: disjoint_weakening H1.
Qed.

Lemma Typing_weakening : forall P (E F : ctx) e dir T,
    Typing P E e dir T ->
    WFEnv (F ++ E) ->
    Typing P (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Typing_weaken.
Qed.




Lemma TLVal_prv: forall A P G,
 ord A ->
 topLike A ->
 WFTyp G A ->
 Typing P G (TLVal A) Inf A.
Proof.
  introv od tl well. gen P.
  induction well; intros;try solve[inverts od;inverts tl]; simpl; eauto.
  -
    inverts* od.
    inverts tl.
    forwards* h1: IHwell2 P.
    forwards* h2: Typing_inf_chk h1.
    pick fresh x and
    apply Typ_abs; eauto.
    simpl_env.
    eapply Typing_weakening.
    forwards* h3: TLVal_lc B.
    forwards* h5: open_exp_wrt_exp_lc_exp (e_var_f x) h3.
    rewrite h5; auto.
    apply WFPushT; auto.
    forwards*: WFTyp_WFEnv well1.
  -
    inverts* od.
    inverts tl.
    pick fresh x and
    apply Typ_tabs; eauto.
    forwards* h1: H5.
    forwards* h2: H7.
    forwards*: H1 P.
    unfold open_typ_wrt_typ in H2.
    forwards h5: ord_lc h1.
    unfold open_exp_wrt_typ.
    rewrite TLVal_open.
    unfold open_typ_wrt_typ.
    forwards*: Typing_inf_chk H2.
  -
   inverts* od.
Qed.




Lemma TLVal_prv_2: forall A P G,
 topLike A ->
 WFTyp G A ->
 Typing P G (TLVal A) Inf A.
Proof.
  introv tl well. gen P.
  induction well; intros;try solve[inverts tl]; simpl; eauto.
  -
    inverts tl.
    forwards* h1: IHwell2 P.
    forwards* h2: Typing_inf_chk h1.
    pick fresh x and
    apply Typ_abs; eauto.
    simpl_env.
    eapply Typing_weakening.
    forwards* h3: TLVal_lc B.
    forwards* h5: open_exp_wrt_exp_lc_exp (e_var_f x) h3.
    rewrite h5; auto.
    apply WFPushT; auto.
    forwards*: WFTyp_WFEnv well1.
  -
    inverts tl.
    pick fresh x and
    apply Typ_tabs; eauto.
    forwards* h1: H5.
    forwards* h2: H0.
    forwards*: H1 P.
    unfold open_typ_wrt_typ in H2.
    unfold open_exp_wrt_typ.
    rewrite TLVal_open.
    unfold open_typ_wrt_typ.
    forwards*: Typing_inf_chk H2.
Qed.


Lemma cast_preservation: forall v v' A B P,
  value v ->
  WFTyp nil A ->
  Typing P nil v Chk B ->
  Cast (v) A v' ->
  exists C, Typing P nil v' Inf C /\ subsub C A.
Proof.
  introv val ok Typ R.
  gen P B.
  inductions R; intros;eauto.
  -
    inverts Typ as h1.
    forwards* h2: principal_type_checks2 h1; auto.
    forwards* h3: TLVal_prv A.
  (* -
    inverts Typ as h1.
    inverts* h1. *)
  -
    inverts Typ as h1.
    forwards* h2: principal_type_checks2 h1.
    rewrite h2 in *.
    subst.
    exists. splits*. 
  - 
    inverts Typ. 
    inverts H1 as hh1; try solve[inverts H0];
    try solve[inverts hh1 as hh1;inverts hh1];
    try solve[forwards h0: split_ord_false H2; auto;inverts h0];
    try solve[exfalso; apply H; auto].
    inverts H10 as hh2; try solve[inverts hh2].
    forwards: algo_sub_lc hh2.
    inverts H0 as hh3; try solve[inverts hh3].
    forwards h1: sub_transitivity hh2 hh3.
    inverts ok.
    exists. splits*.
  -
    inverts Typ as h1. inverts h1 as h1; try solve[inverts* h1].
    inverts H1; try solve[inverts H0];
    try solve[forwards h0: split_ord_false H2; auto;inverts h0];
    try solve[exfalso; apply H; auto].
    inverts ok as ok1 ok2.
    exists. split; auto.
    apply Typ_tabs with (union (union L
    (union L0
       (union (termfv_exp e)
          (union (typefv_exp e)
             (union [[A1]]
                (union [[B1]]
                   (union [[A2]]
                      (union [[B2]] (union [[B]] (typefv_phi P)))))))))) LL); intros; eauto.
    forwards* h2: h1 X.
    forwards* h3: H10 X.
    forwards* h6: ok2 X.
    apply~ Typing_chk_sub.
    forwards*: Typing_narrowing_simpl h2 H9.
    eauto.
  -
    inverts val as h0; try solve[inverts h0].
    inverts Typ as h1. inverts h1 as h1.
    forwards* h2: Typing_inf_chk h1.
    forwards*: IHR h2.
    inverts* ok.
  -
    inverts Typ as h1. inverts h1 as h1.
    forwards* h2: Typing_inf_chk h1.
    forwards*: IHR h2.
  -
    inverts Typ as h1. inverts h1 as h1.
    forwards* h2: Typing_inf_chk H8.
    forwards*: IHR h2.
  -
    forwards* h2: Well_spl H.
    lets (well1&well2):h2.
    forwards* h1: IHR1 Typ.
    forwards* h3: IHR2 Typ.
    lets (t1&h4&subsub1): h1.
    lets (t2&h5&subsub2): h3.
    forwards h8: spl_disjoint ok H; auto.
    exists(t_and t1 t2); splits*.
    applys Typ_merge; auto.
    forwards* h6: subsub2sub subsub1.
    forwards* h7: subsub2sub subsub2.
    inverts h6 as h61 h62.
    inverts h7 as h71 h72.
    forwards h9: disjoint_covariance h8 h72.
    forwards h12: disjoint_symm h9.
    forwards h10: disjoint_covariance h12 h62.
    forwards*: disjoint_symm h10.
Qed.





Lemma subsub_disjoint: forall A1 B1 A2 B2 D,
 subsub A1 A2 ->
 subsub B1 B2 -> 
 disjoint D A2 B2 ->
 disjoint D A1 B1.
Proof.
  introv sub1 sub2 dis.
  forwards* h1: subsub2sub sub1.
  forwards* h2: subsub2sub sub2.
  inverts h1 as h11 h12.
  inverts h2 as h21 h22.
  forwards h3: disjoint_covariance dis h22.
  forwards h4: disjoint_symm h3.
  forwards h5: disjoint_covariance h4 h12.
  forwards h6: disjoint_symm h5; auto.
Qed.


Lemma subsub_disjoint_2: forall A1 B1 A2 B2 D,
 subsub A1 A2 ->
 subsub B1 B2 -> 
 disjoint D A1 B1 ->
 disjoint D A2 B2.
Proof.
  introv sub1 sub2 dis.
  forwards* h1: subsub2sub sub1.
  forwards* h2: subsub2sub sub2.
  inverts h1 as h11 h12.
  inverts h2 as h21 h22.
  forwards h3: disjoint_covariance dis h21.
  forwards h4: disjoint_symm h3.
  forwards h5: disjoint_covariance h4 h11.
  forwards h6: disjoint_symm h5; auto.
Qed.


Lemma Typing_subst_1 : forall P (E F : ctx) e u S S' dir T (z : atom),
    Typing P (F ++ [(z, TermV S)] ++ E) e dir T ->
    Typing P E u Inf S' ->
    subsub S' S ->
    exists T', Typing P (F ++ E) ([z ~> u] e) dir T' /\ subsub T' T.
Proof.
  introv Typ Typv Subsub.
  remember (F ++ [(z,TermV S)] ++ E) as E'.
  generalize dependent F.
  inductions Typ;
    intros F Eq; subst; simpl; autos;
      lets Lc  : Typing_regular_1 Typv;
      lets Uni : Typing_regular_2 Typv;
      lets Lc2  : Typing_lc_typ Typv.
  -
    forwards*: wfenv_remove H.
  -
    forwards*: wfenv_remove H.
  - (* var *)
    case_if...
    +
    substs.
    forwards h3: WFEnv_uniq H.
    assert (A = S) as h1.
    forwards* h2: binds_mid_eq H0 h3.
    inverts* h2.
    substs.
    exists. split.
    apply~ Typing_weakening. eauto.
    forwards*: wfenv_remove H.
    auto.
    +
    forwards* h1:  WFTyp_strengthen_2 H1.
  - (* abs *)
    forwards* h1:  WFTyp_strengthen_2 H1.
    (* forwards* h2:  WFTyp_strengthen_2 H3. *)
    exists. split.
    eapply (Typ_abs (union LL (singleton z))); 
    intros;eauto.
    forwards~(?&h3&h4): H0 x ((x, TermV A) :: F).
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, TermV A)] ++ F) ++ E).
    apply subsub2sub in h4.
    inverts h4 as h41 h42.
    forwards* h6: H x.
    forwards* h7: Typing_regular_0 h6.
    forwards* h5: Typing_chk_sub h3 h41.
    rewrite_env(((x ~ TermV A ++ F) ++ z ~ TermV S ++ E)) in h7.
    forwards* h8:  WFTyp_strengthen_2 h7.
    pick fresh y.
    forwards* h6: H y.
    forwards* h7: Typing_regular_0 h6.
  - (* app *)
    forwards* (?&h1&h2): IHTyp1.
    forwards* (?&h3&h4): IHTyp2.
    forwards* (?&h5&h6): appDist_arr_subsub H h2.
    lets(h7&h8):subsub2sub h4.
    forwards*: Typing_chk_sub h3 h7.
    forwards* h9: Typing_regular_0 Typ2.
    forwards* h10: WFTyp_strengthen_2 h9.
  - (* merge *)
    forwards* (?&h1&h2): IHTyp1.
    forwards* (?&h3&h4): IHTyp2.
    forwards* h5: disjoint_strengthen_2 H.
    forwards* h6: subsub_disjoint h2 h4.
    forwards* h7:Typing_lc_typ Typ1.
    forwards* h8:Typing_lc_typ Typ2.
  - (* anno *)
    forwards* h1: Typing_regular_0 Typ.
    forwards* h2: WFTyp_strengthen_2 h1.
    forwards* h3: Well_lc_typ h2.
    exists A. split*.
    apply Typ_anno.
    forwards* (?&?&?): IHTyp.
    apply subsub2sub in H0.
    forwards*: Typing_chk_sub H H0.
  - (* algo_sub *)
    forwards (?&h1&h2): IHTyp; auto.
    forwards h3: Typing_regular_0 Typ; auto.
    forwards h4: WFTyp_strengthen_2 H0; auto.
    exists B. split.
    apply subsub2sub in h2.
    destruct h2.
    assert (algo_sub x B) by auto_sub.
    forwards: Typ_sub h1 H3; auto.
    forwards* h5: Well_lc_typ h4.
  -
    forwards h1:  WFTyp_strengthen_2 H0.
    forwards*: wfenv_remove H.
  - (* assign *)
    forwards* (t1&h1&h2): IHTyp1.
    forwards* (t2&h3&h4): IHTyp2.
    inverts h2; try solve[inverts H].
    +
    forwards* (h5&h6): subsub2sub h4.
    forwards* h7: Typing_chk_sub h3 h5.
    forwards* h: Typing_regular_0 h1.
    inverts* h.
    +
    forwards* (h5&h6): subsub2sub h4.
    forwards* (h7&h8): subsub2sub H1.
    forwards* h9: sub_transitivity h5 h8.
    forwards* h10: Typing_chk_sub h3 h9.
    forwards* h: Typing_regular_0  h1.
    inverts* h.
  -  (* deref *)
    forwards* (t1&h1&h2): IHTyp.
    inverts h2; try solve[inverts H].
    +
    exists(A). split*.
    +
    exists A0. splits*. 
  - (* ref *)
    forwards* (t1&h1&h2): IHTyp.
  - (* tabs *)
    forwards* h1:  TWell_strengthen_2 H1.
    exists. split.
    eapply (Typ_tabs (union LL (singleton z))); 
    intros;eauto.
    forwards~(?&h3&h4): H0 X ((X, TyDis A) :: F).
    rewrite subst_exp_open_exp_wrt_typ_var; auto.
    rewrite_env (([(X, TyDis A)] ++ F) ++ E).
    apply subsub2sub in h4.
    inverts h4 as h41 h42.
    forwards* h6: H X.
    forwards* h7: Typing_regular_0 h6.
    forwards* h5: Typing_chk_sub h3 h41.
    rewrite_env(((X ~ TyDis A ++ F) ++ z ~ TermV S ++ E)) in h7.
    forwards* h8:  WFTyp_strengthen_2 h7.
    pick fresh y.
    forwards* h6: H y.
    forwards* h7: Typing_regular_0 h6.
  -
    forwards* h0: IHTyp Typv Subsub.
    destruct h0 as [B0 [HT HS] ].
    forwards* (?&?&h1&h2&h3): appDist_forall_subsub_disjoint H HS.
    exists (x0 ^-^ B). split.
    eapply Typ_tapp. 
    apply HT. 
    apply h1.
    forwards*: WFTyp_strengthen_2 H0.
    forwards*: disjoint_strengthen_2 H1.
    apply disjoint_covariance with A1. auto. auto. 
    forwards h4: Well_lc_typ H0.
    forwards h5:h2 h4; auto.
  -
    forwards* (t1&h1&h2): IHTyp.
  -
    forwards* (?&h1&h2): IHTyp.
    forwards* (?&h5&h6): appDist_rcd_subsub H h2.
  -
     forwards*: wfenv_remove H.
  -
    forwards*: wfenv_remove H.
    forwards*: WFTyp_strengthen_2 H0.
Qed.


Lemma typing_c_subst_simpl_1 : forall P E e u S S' dir T z,
  Typing P ([(z,TermV S)] ++ E) e dir T ->
  Typing P E u Inf S' ->
  subsub S' S ->
  exists T', Typing P E ([z ~> u] e) dir T' /\ subsub T' T.
Proof.
  intros P E e u S S' dir T z H1 H2 H3.
  rewrite_env (nil ++ E).
  eapply Typing_subst_1.
    simpl_env. apply H1.
    apply H2.
  auto.
Qed.



Lemma papp_preservation : forall v1 v2 e A Phi mu,
    value v1 -> value v2 ->
    Typing Phi nil (e_app v1 v2) Inf A ->
    papp v1 (arg_exp v2) mu e mu ->
    Typing Phi nil e Inf A.
Proof with eauto.
  introv Val1 Val2 Typ P. gen Phi A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3;
  try solve[inverts Typ1; inverts Typ3];
  try solve[inverts Typ1 as hh1; try solve[inverts hh1 as hh1;inverts hh1];
  try solve[inverts Typ3] ].
  -
    inverts Typ1 as t1.
    forwards (? & p1 & p2): cast_preservation Typ2 H1 ...
    inverts Typ2. inverts Typ3.
    eapply Typ_anno. pick fresh y. rewrite (@subst_exp_intro y)...
    forwards~ t1': (t1 y). 
    lets~ (?&s1&s2): typing_c_subst_simpl_1 t1' p1 p2.
    apply subsub2sub in s2. lets (s4&s5): s2. forwards*: Typing_chk_sub s4.
    forwards* h5: Typing_regular_0 t1'.
    rewrite_env(nil++[(y, TermV A2)]++nil) in h5.
    forwards h6:WFTyp_strengthen h5; auto.
    inverts* Typ3.
    inverts* t1.
    inverts* H2.
  -
     inverts Typ1 as t1 t2; try solve[inverts H as h0 ;inverts h0].
    inverts Typ3.
    inverts t1.
    inverts H.
    +
      inverts H1; try solve[inverts H9;inverts H].
      apply Typ_anno; auto.
      forwards* h1: sub_inversion_arrow H3.
      inverts h1 as h1.
      *
      (* inverts h1 as h1 h2. *)
      eapply Typ_sub.
      eapply Typ_app.
      pick fresh x and
      apply Typ_abs; auto.
      eapply Typ_sub.
      apply Typ_anno; auto.
      apply h1.
      auto.
      apply AD_arr.
      auto.
      auto.
      inverts H4; auto.
    +
      inverts H1; try solve[inverts H4;inverts H];
      try solve[inverts H5].
      apply Typ_anno; auto.
      forwards* h1: sub_inversion_arrow H3.
      inverts h1 as h1.
      *
      (* inverts h1 as h1 h2. *)
      eapply Typ_sub.
      eapply Typ_app.
      apply Typ_anno; auto.
      eapply Typ_sub.
      apply Typ_anno; auto.
      apply h1.
      forwards* h3:  Typing_regular_0 H9.
      inverts h3; auto.
      apply AD_arr.
      auto.
      auto.
      inverts H4; auto.
  -
    forwards* (T & Htyp & Hsub): Typing_chk2inf Typ2.
    inverts Val1 as hh0; try solve[inverts hh0 as hh0;inverts hh0].
    inverts Typ1; inverts Typ3; try solve[inverts H].
    forwards* h1: Typing_regular_0 Typ2. 
    forwards* hh1: Typing_regular_0 Htyp. 
    inverts H5.
    assert(Typing Phi [] (e_app v1 v2) Inf B0) as h2.
    eapply Typ_app. apply H3.
    apply Typ2.
    auto.
    forwards~ h4: IHP1 h2.
    assert(Typing Phi [] (e_app v0 v2) Inf B3) as h3.
    eapply Typ_app. apply H7.
    eapply Typ2.
    auto.
    forwards~ h5: IHP2 h3.
    forwards* h6: Disjoint_appDist H6 H10 H8.
Qed.




Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.





Lemma papp_preservation_rcd : forall v1 i5 e A Phi mu,
    value v1 -> 
    Typing Phi nil (e_proj v1 i5) Inf A ->
    papp v1 (arg_la i5) mu e mu ->
    Typing Phi nil e Inf A.
Proof with eauto.
  introv Val1 Typ P. gen Phi A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3.
  -
    inverts Typ1 as t1 t2; try solve[inverts H as h0 ;inverts h0].
    inverts Typ2 as h1; auto.
  - (* merge *)
    inverts Val1 as h03; try solve[inverts h03].
    inverts Typ1; inverts Typ2.
    inverts H5.
    assert(Typing Phi [] (e_proj v1 i5) Inf B0) as h2.
    eapply Typ_proj. apply H3.
    auto.
    forwards~: IHP1 h2.
    assert(Typing Phi [] (e_proj v2 i5) Inf B3) as h3.
    eapply Typ_proj. apply H7.
    auto.
    forwards~: IHP2 h3.
    forwards h6: Disjoint_appDist H6 H10 H8 ; auto.
Qed.


Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st =  *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. lia.
Qed.


Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.



Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st =  *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st =  *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.


Lemma replace_sto_ok : forall l v st,
 l < length st ->
 value v ->
 sto_ok st ->
 sto_ok (replace l v st).
Proof.
  introv len val ok. gen l v.
  inductions ok; intros;
  try solve[inverts len];
  simpl in *.
  destruct l; simpl; eauto.
  apply sto_ok_push; auto.
  forwards*: IHok l val. lia.
Qed. 



Lemma assign_pres_store_typing : forall ST st l v t,
  l < length st ->
  value v ->
  sto_typing ST st ->
  Typing ST nil v Inf t ->
  subsub t (store_Tlookup l ST) ->
  sto_typing ST (replace l v st).
Proof with auto.
  introv  Hlen val HST Ht sub.
  inverts HST. inverts H0.
  unfold sto_typing.
  split.
  forwards*: replace_sto_ok Hlen val.
  split.
  rewrite length_replace...
  intros l' Hl'.
  destruct (l' == l).
  - (* l' = l *)
    inverts e.
    rewrite lookup_replace_eq in * ...
    exists t.
    splits*.
  - (* l' <> l *)
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H2...
Qed.




Lemma value_ptys: forall v P A,
 value v ->
 Typing P [] v Inf A ->
 WFTyp nil (principle_type v).
Proof.
  introv Val Typ. 
  forwards*: principal_type_checks2 Typ.
  forwards*: Typing_regular_0 Typ.
  rewrite H in *; auto.
Qed.





Lemma papp_preservation2 : forall v1 v2 e A Phi mu1 mu2,
    value v1 -> value v2 ->
    Typing Phi nil (e_ass v1 v2) Inf A ->
    papp v1 (arg_exp v2) mu1 e mu2 ->
    sto_typing Phi mu1 ->
    Typing Phi nil e Inf A /\ sto_typing Phi mu2.
Proof with eauto.
  introv Val1 Val2 Typ P. gen Phi A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3;
  try solve[inverts Typ1; inverts Typ3].
  -
    split.
    eapply Typ_unit; eauto.
    inverts Typ1 as hh1; try solve[inverts hh1 as hh1;inverts hh1].
    lets h0: H1.
    inverts H1 as h6 h7.
    inverts h7 as h71 h72.
    rewrite h71 in H9.
    forwards h4: sto_ok_value H9 h6.
    forwards h8: h72 o; auto.
    lets(?&h9&h10): h8. 
    forwards h5: value_ptys h4 h9; auto.
    forwards h1: cast_preservation Typ2 H0; auto.
    lets(?&h2& h3): h1.
    forwards* h11: principal_type_checks2 h9.
    rewrite <- h11 in h10.
    forwards* h12: subsub_trans h3 h10.
    forwards*: assign_pres_store_typing h2 h12.
    forwards*: casting_prv_value H0.
  -
    splits; auto.
Qed.





Lemma Merge_topLike: forall t1 t2 t3,
 Merge t1 t2 t3 ->
 topLike t1 ->
 topLike t2 ->
 topLike t3.
Proof.
 introv ap tl1 tl2.
 inductions ap; eauto.
 inverts tl1. inverts tl2.
 apply TL_all with (union L L0);intros; auto.
 unfold open_typ_wrt_typ in *; simpl in *; auto.  
Qed.


Lemma appDist_topLike: forall t1 t2,
 appDist t1 t2 ->
 topLike t1 ->
 topLike t2.
Proof.
 introv ap tl.
 inductions ap; eauto.
 forwards*:  Merge_topLike H.
Qed.


Lemma algo_sub_subst_1: forall U Z B A,
  algo_sub B A->
  lc_typ U ->
  algo_sub [Z ~~> U] (B) [Z ~~> U] (A).
Proof.
  intros.
  assert(close_typ_wrt_typ_rec 0 Z A -^ Z = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
  assert(close_typ_wrt_typ_rec 0 Z B -^ Z = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H1 in H.
    rewrite <- H2 in H.
  forwards: algo_sub_disjoint_weakening H0 H. auto.
  assert(typsubst_typ U Z B = open_typ_wrt_typ (close_typ_wrt_typ Z B) U).
    apply typsubst_typ_spec.
  assert(typsubst_typ U Z A = open_typ_wrt_typ (close_typ_wrt_typ Z A) U).
    apply typsubst_typ_spec.
  rewrite H5. rewrite H4. auto.
Qed.


Lemma TWell_subst_1 : forall x A D F B T,
    TWell (F ++ x ~ TyDis A ++ D) B ->
    TWell D T ->
    WFEnv (subst_env T x F ++ D) ->
    x `notin` typefv_typ_range D ->
    TWell (subst_env T x F ++ D) [x ~~> T] B.
Proof with simpl_env; eauto.
  intros. 
  assert(close_typ_wrt_typ_rec 0 x B -^ x = B) as h1. apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- h1 in H.
  forwards h2: TWell_subst H0 H; auto. 
  assert(typsubst_typ T x B = open_typ_wrt_typ (close_typ_wrt_typ x B) T) as h3.
    apply typsubst_typ_spec.
    rewrite h1 in h2.
  auto.
Qed.


Lemma Well_subst_1 : forall x A D F B T,
    WFEnv (subst_env T x F ++ D) ->
    WFTyp D T ->
    WFTyp (F ++ x ~ TyDis A ++ D) (B) ->
    disjoint D T A ->
    x `notin` typefv_typ_range D ->
    WFTyp (subst_env T x F ++ D) [x ~~> T] (B).
Proof.
  intros. 
  assert(close_typ_wrt_typ_rec 0 x B -^ x = B) as h1. apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- h1 in H1.
  forwards h2: Well_subst H0 H1; auto. 
  assert(typsubst_typ T x B = open_typ_wrt_typ (close_typ_wrt_typ x B) T) as h3.
    apply typsubst_typ_spec.
    rewrite h1 in h2.
  auto.
Qed.



Lemma appDist_subst : forall A B Z U,
    appDist A B ->
    lc_typ U ->
    appDist [Z ~~> U] (A) [Z ~~> U] (B).
Proof with eauto 3 using typsubst_typ_lc_typ.
  intros. induction* H; simpl; eauto with lngen.
  -
    inverts H.
    assert(lc_typ ([Z ~~> U] (A1))) as h0.
    forwards*: typsubst_typ_lc_typ H3 H0.
    pick fresh y.
    assert(lc_typ ([Z ~~> U] (A2) -^ y)) as h1.
    rewrite typsubst_typ_open_typ_wrt_typ_var; auto.
    forwards*: typsubst_typ_lc_typ H4 H0.
    (* forwards*: lc_t_forall_exists h0 h1. *)
  -
  apply AD_and with ([Z ~~> U] (B1)) ([Z ~~> U] (B2))...
  forwards(?&?): appDist_lc H1.
  forwards(?&?): appDist_lc H2.
  forwards(?&?): appDist_lc IHappDist1.
  forwards(?&?): appDist_lc IHappDist2.
  inversion H;subst;simpl.
  apply M_arrow. apply typsubst_typ_lc_typ. auto. auto. apply typsubst_typ_lc_typ. auto. auto. apply typsubst_typ_lc_typ. auto. auto.
  apply M_forall. simpl in H8. auto. simpl in H10. auto. apply typsubst_typ_lc_typ. auto. auto. apply typsubst_typ_lc_typ. auto. auto.
  apply M_rcd. apply typsubst_typ_lc_typ. auto. auto. apply typsubst_typ_lc_typ. auto. auto. 
  Unshelve.
  pick fresh yy.
  apply yy.
  pick fresh yy.
  apply yy.
Qed.



Lemma TCW_binds_4: forall A0 C D E X J X1, X `notin` (typefv_typ_range D) -> lc_typ J -> binds X1 (TermV A0) (E ++ [(X,TyDis C)] ++ D)
-> X <> X1-> binds X1 (TermV (typsubst_typ J X A0)) ( subst_env J X E  ++ D).
Proof.
  intros.
  apply binds_app_1 in H1. destruct H1. 
    -
    induction E;auto. inversion H1;subst. 
    unfold subst_env.
    simpl_env in *.
    fold subst_env.
    eauto.
    destruct a.
    destruct t.
    +
      analyze_binds H1.
      *
      unfold subst_env.
      simpl_env in *.
      fold subst_env.
      forwards*: IHE.
    +
      unfold subst_env.
      simpl_env in *.
      fold subst_env.
      forwards*: IHE.
    -
      analyze_binds H1.
      induction D. simpl. auto. 
      destruct a. simpl.
      inverts  BindsTac as h1.
      inverts h1.
      simpl_env in *.
      rewrite typsubst_typ_fresh_eq; auto.
      simpl in *. auto.
      destruct t.
      simpl in *.
      forwards* h2: IHD; eauto.
      simpl_env in *.
      eauto.
      simpl_env in *; eauto.
      simpl in *.
      forwards* h2: IHD; eauto.
      simpl_env in *; eauto.
Qed.


Lemma notin_phi: forall x p o,
  x `notin` (typefv_phi p) ->
  x `notin` [[store_Tlookup o p]].
Proof.
 intros.
 inductions p; simpl in *;eauto.
 -
   unfold store_Tlookup; 
   simpl; eauto.
   destruct(o); subst; simpl in *; eauto.
  -
    unfold store_Tlookup; 
    simpl; eauto.
    destruct(o); subst; simpl in *; eauto.
Qed.



Lemma Typing_subst_2 : forall P E F e dir T S U Z,
    Typing P (E ++ Z ~ TyDis S ++ F) e dir T ->   
    Z `notin` (union (typefv_typ_range F) (typefv_phi P)) ->
    WFTyp [] U ->
    disjoint F U S ->
    WFEnv (subst_env U Z E ++ F) ->
    Typing P (subst_env U Z E ++ F) (typsubst_exp U Z e) dir (typsubst_typ U Z T).
Proof with auto.
  introv Typ.
  remember (E ++ Z ~ TyDis S ++ F) as E'. gen E.
  inductions Typ; intros E Eq nin TW TD TCW; subst; simpl;
  try solve [ constructor; eauto;
              rewrite_env ([] ++ F ++ []);
              applys TWell_subst; eauto ].
  -
    assert(Z <> x).
    forwards* h0: WFTyp_WFEnv H1.
    forwards* h1: WFEnv_uniq h0.
    assert(Z `notin` union (dom E) (dom F)) as h2.
    solve_uniq.
    analyze_binds H0.
    assert(x `in` dom E).
    eauto.
    unfold not;intros nt.
    inverts* nt.
    assert(x `in` dom F).
    eauto.
    unfold not;intros nt.
    inverts* nt.
    forwards* h3: Well_lc_typ TW.
    forwards*: TCW_binds_4 H0.
    forwards*: Well_subst_1 TCW H1.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards*: wfenv_app_r TCW; auto.
  - pick fresh x and apply Typ_abs.
    forwards~ h1: H0 x ((x, TermV A) :: E ); simpl in *;auto.
    apply WFPushT; auto.
    simpl_env.
    forwards*: notin_subst_env x Z U E; auto.
    rewrites typsubst_exp_open_exp_wrt_exp in h1.
    assert(typsubst_exp U Z (e_var_f x) = (e_var_f x)) as h2.
    simpl; auto.
    rewrite h2 in h1.
    forwards* h3: H.
     forwards*: Well_lc_typ TW.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards*: wfenv_app_r TCW; auto.
    forwards*: Well_subst_1 TCW H3.
  -
    forwards h1: IHTyp2...
    applys Typ_app...
    forwards: appDist_subst Z U.
    applys H.
    forwards~: Well_lc_typ TW.
    simpls...
  -
    applys Typ_merge...
    forwards*: disjoint_subst H TD.
    forwards*: Typing_regular_2 Typ1.
  - 
    forwards~: Well_lc_typ TW.
    applys Typ_sub...
    applys algo_sub_subst_1...
    forwards*:Well_subst_1 TCW H0.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards*: wfenv_app_r TCW; auto.
  -
    forwards* h2: Well_lc_typ H0.
    forwards* h1: Well_subst_1 H0 TD.
    forwards*: wfenv_app_r TCW.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards* h6: Well_lc_typ TW.
    forwards* h5: algo_sub_subst_1 Z H2 h6; simpl; auto.
    simpl in *.
    assert(Z `notin` [[(store_Tlookup o L)]]).
    forwards*: notin_phi L.
     assert([Z ~~> U] (store_Tlookup o L) = (store_Tlookup o L)) as h7.
     rewrite typsubst_typ_fresh_eq; auto.
     rewrite h7 in h5.
     eauto.
  -
    forwards h1: IHTyp1...
    applys Typ_ass...
    simpl in *.
    auto.
  -
    forwards* h0: Well_lc_typ TW.
    pick fresh X and apply Typ_tabs.
    forwards~ h1: H0 X ((X, TyDis A) :: E).
    simpl.
    apply WFPushV; auto.
    simpl_env.
    forwards*: notin_subst_env X Z U E; auto.
    assert(X `notin` [[[Z ~~> U] (A)]]) as h2.
    forwards*: typefv_typ_typsubst_typ_notin A U Z X; auto.
    auto.
    rewrites typsubst_typ_open_typ_wrt_typ_var...
    simpl in h1.
    rewrites typsubst_exp_open_exp_wrt_typ_var...
    forwards*: TWell_subst_1 H1.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards*: wfenv_app_r TCW; auto.
  -
    rewrites typsubst_typ_open_typ_wrt_typ...
    forwards~: IHTyp.
    applys Typ_tapp.
    apply H2.
    forwards~: appDist_subst Z U H.
    forwards~: Well_lc_typ TW.
    simpl in H3. applys H3.
    forwards*:Well_subst_1 TCW H0.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards*: wfenv_app_r TCW; auto.
    forwards*: disjoint_subst H1 TD.
    forwards~: Well_lc_typ TW.
  -
    forwards~: IHTyp.
    applys Typ_proj.
    apply H0.
    forwards~: appDist_subst Z U H.
    forwards~: Well_lc_typ TW.
  -
    forwards* h2: Well_lc_typ H0.
    forwards*: WFTyp_weakening_simpl F TW; simpl_env in *;auto.
    forwards*: wfenv_app_r TCW; auto.
    forwards*: Well_subst_1 TCW H0.
    forwards: topLike_subst_1 Z U H1; auto.
    forwards* h3: Well_lc_typ H2. 
Qed.



Lemma papp_preservation3 : forall P v T e A mu,
    value v ->
    Typing P nil (e_tapp v T) Inf A ->
    papp v (arg_typ T) mu e mu ->
    WFTyp [] T ->
    Typing P nil e Inf A.
Proof with simpls; eauto.
  introv Val1 Typ Pa TW. gen A.
  inductions Pa; intros; inverts Typ as Typ1 Typ2 Typ3.
  - inverts Typ2; inverts Typ1; try solve[inverts H6 as h0;inverts h0]...
    pick fresh X.
    forwards~ h1: H8 X.
    unfold open_typ_wrt_typ; simpl.
    applys Typ_anno.
    rewrite_env ([] ++ X ~ (TyDis A2) ++ []) in h1.
    forwards~ h2: Typing_subst_2 h1 H7.
    simpl in h2.
    rewrites typsubst_exp_open_exp_wrt_typ in h2...
    rewrites typsubst_typ_open_typ_wrt_typ in h2...
    case_if.
    rewrites typsubst_exp_fresh_eq in h2...
    rewrites typsubst_typ_fresh_eq in h2...
  - inverts Typ1; inverts Typ2.
    inverts H4.
    forwards h1: IHPa1...
    forwards h2: IHPa2...
    forwards h3: Typ_merge h1 h2...
    forwards h4: Disjoint_appDist H5 H10 H7; auto.
    pick fresh y.
    forwards h5: disjoint_forall_inv h4 y; auto.
    rewrite_env(nil ++ [(y, TyDis (t_and A0 B0))] ++ nil) in h5.
    apply disjoint_symm in H8.
    forwards* h6:  disjoint_disjoint_weakening h5 H8; auto. 
    simpl_env; eauto.
    apply WFPushV; auto.
Qed.





Ltac indExpDirSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : dirflag |- _ ] => (gen h) end;
  repeat match goal with | [ h : exp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

Definition size_dir dir :=
  match dir with
  | Inf => 0
  | Chk => 1
  end.


Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.


Lemma extends_refl : forall E,
  extends E E.
Proof. 
 intros_all~.
 inductions E; eauto. 
Qed.


Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply lt_n_S. apply IHextends. lia.
Qed.


Lemma store_weakening : forall G ST ST' t dir T,
  extends ST' ST ->
  Typing  ST G t dir T ->
  Typing  ST' G t dir T.
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    apply Typ_loc; eauto.
    eapply length_extends...
    rewrite <- (extends_lookup _ _ ST') in H3 ...
Qed.


Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.


Hint Resolve extends_refl extends_app store_weakening: core.



Lemma sto_ok_app: forall st1 st2,
 sto_ok st1 ->
 sto_ok st2 ->
 sto_ok (st1 ++ st2).
Proof.
  introv ok1 ok2.
  inductions ok1; simpl; eauto.
Qed.


Lemma add_sym : forall m,
 1 + m = m + 1.
Proof.
  introv. 
  inductions m; intros; eauto.
  simpl.
  rewrite <- IHm.
  simpl.
  reflexivity.
Qed.

Lemma store_well_typed_app : forall ST st t1 T1,
  value t1 ->
  sto_typing ST st ->
  Typing ST nil   t1 Inf T1 ->
  sto_typing (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto.
  intros.
  unfold sto_typing in *.
  destruct H0. destruct H2. 
  rewrite app_length. simpl.
  rewrite app_length. simpl.
  split;eauto.
  - apply sto_ok_app;eauto.
  - (* types match. *)
    split;eauto.
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      rewrite !app_nth1; try solve[lia].
      *
      forwards* h3: H3 l. lia.
      (* lets(t&h1&h2): h3.
      unfold store_lookup in *.
      unfold store_Tlookup in *.
      exists t. splits.
      apply store_weakening with ST. apply extends_app.
      auto.
      auto. *)
    + (* l = length st *)
      assert(1 + length st = S (length st)).
      simpl;eauto.
      rewrite add_sym in H4.
      rewrite H4 in *.
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- H2.
      rewrite minus_diag. simpl.
      exists T1. splits.
      apply store_weakening with ST...
      rewrite app_nth2; [|lia].
      rewrite minus_diag. simpl.
      forwards*: Typing_lc_typ H1.
Qed.



Lemma Preservation_subsub: forall e e' A dir P mu mu',
  P |== mu ->
  Typing P nil e dir A ->
  step (e, mu) (e', mu') ->
  exists T P', extends P' P /\ Typing P' nil e' dir T /\ subsub T A /\ P' |== mu'.
Proof with (simpl; try lia; auto; try eassumption; eauto).
  introv ok Typ J. gen mu A e'.
  indExpDirSize ((size_exp e) + (size_dir dir)).
  inverts keep Typ as Ht1 Ht2 Ht3 Ht4;
    try solve [inverts J]; repeat simpl in SizeInd; 
    try solve[forwards h1: step_not_value J;inverts h1];
    try solve[inverts Ht2].
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2.
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2.
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2. 
  -
    inverts J.
    +
      destruct F; unfold fill in *; inverts* H.
      *
      inverts H2. 
      forwards* h1: IH H4. simpl in *; lia.
      lets(t&p'&h2&h3&h4&h5): h1.
      forwards* h6: appDist_arr_subsub Ht3 h4.
      *
      inverts H2.
      inverts Typ. 
      forwards* h1: IH H4. simpl in *. 
      forwards* h2: size_exp_min e1. lia.
      lets(t&p'&h2&h3&h4&h5): h1.
      forwards* (h6&h7): subsub2sub h4.
      forwards* h8: Typing_chk_sub h6.
      forwards*: Typing_regular_0 H6.
      forwards*: store_weakening h2 Ht1.
      exists A p'. splits*.
      forwards*: appDist_lc Ht3.
    +
      forwards* h1: papp_preservation H7.
      exists A P.
      splits*.
      forwards*: Typing_lc_typ Typ.
  -
    inverts J.
    +
    destruct F; unfold fill in *; inverts* H.
    *
    forwards* h1: IH H4. simpl in *; lia.
    lets(t1&p1'&h2&h3&h4&h5):h1.
    forwards*: Typing_lc_typ Ht2.
    forwards*: Typing_lc_typ Ht1.
    assert(subsub B B) as h6; auto.
    forwards* h8: subsub_disjoint h4 h6.
    *
    forwards* h1: IH H4. simpl in *; lia.
    lets(t1&p1'&h2&h3&h4&h5):h1.
    forwards*: Typing_lc_typ Ht2.
    forwards*: Typing_lc_typ Ht1.
    assert(subsub A0 A0) as h6; auto.
    forwards* h8: subsub_disjoint h6 h4.
  -
    inverts J.
    +
    destruct F; unfold fill in *; inverts* H.
    forwards*: size_typ_min A.
    forwards* h1: IH H4. 
    simpl in *; lia.
    lets(t1&p1'&h2&h3&h4&h5):h1.
    forwards(h6&h7): subsub2sub h4.
    forwards*: Typing_regular_0 Ht1.
    forwards* h8: Typing_chk_sub h3 h6.
    +
    inverts Typ; try solve[inverts H5 as hh0;inverts hh0]. inverts H2.
    forwards* h1: cast_preservation H6.
  -
    forwards (?&?&h1&h2&h3&h4): IH Ht1 J; simpl in *; auto.
    lia.
    forwards(?&?): subsub2sub h3.
    assert (algo_sub x A) by auto_sub.
    exists* A x0.
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2.
  -
    inverts J.
    +
    destruct F; unfold fill in *; inverts* H.
    *
    forwards* h1: IH H4. simpl in *. lia.
    lets(t&p'&h2&h3&h4&h5): h1.
    inverts* h4; try solve[inverts* H].
    forwards* h6:subsub2sub H1.
    forwards* h7: Typing_regular_0 h3. inverts h7.
    forwards* h: Typing_chk_sub A Ht2.
    *
    forwards* h1: IH H4. simpl in *. 
    forwards* h: size_exp_min e1. lia.
    lets(t&p'&h2&h3&h4&h5): h1.
    forwards* (h6&h7): subsub2sub h4.
    forwards* h8: Typing_chk_sub h3 h6.
    forwards*: Typing_regular_0 Ht2.
    +
    forwards* h1: papp_preservation2 H7.
  -
    inverts J.
    +
    destruct F; unfold fill in *; inverts* H.
    forwards* h1: IH H4. simpl in *. lia.
    lets(t&p'&h2&h3&h4&h5): h1.
    inverts* h4; try solve[inverts* H].
    +
    lets ok':ok.
    inverts ok'.
    inverts H1.
    inverts Ht1 as hh0; try solve[inverts hh0 as hh0;inverts hh0].
    rewrite H2 in *.
    forwards* h1: H3 H10.
    lets(t&h2&h3):h1.
    forwards* (h4&h5): subsub2sub h3.
    assert(algo_sub (store_Tlookup o P) A).
    inverts* H11; try solve[inverts* H4];
    try solve[inverts* H1].
    forwards* h6: sub_transitivity h4 H1.
    + (* deref *)
      inverts Typ as h1 h2.
      inverts h1 as h1 h2 h3; try solve[inverts h1 as h1;inverts h1].
      inverts h3 as h3.
      forwards* h4: TLVal_prv_2 P h3.
  -
    inverts J.
    +
    destruct F; unfold fill in *; inverts* H.
    forwards* h1: IH H4. simpl in *. lia.
    +
    forwards*: principal_type_checks2 Ht1.
    rewrite <- H in *.
    forwards*: Typing_regular_0 Ht1.
    lets ok':ok.
    inverts ok'.
    lets(h1&h2): H3.
    rewrite <- h1.
    exists (t_ref (principle_type e0)) (P ++ (principle_type e0) :: nil).
    splits*.
    eapply Typ_loc; eauto.
    rewrite app_length. simpl. lia.
    apply S_ref.
    unfold store_Tlookup.
    rewrite nth_eq_last; eauto.
    unfold store_Tlookup.
    rewrite nth_eq_last; eauto.
    forwards*: store_well_typed_app Ht1.
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2.
  -
    inverts J.
    +
    destruct F; unfold fill in *; inverts* H.
    forwards* h1: IH H4. simpl in *. lia.
    lets(t&p'&h2&h3&h4&h5): h1.
    forwards* (C1' & C2' & HAD & HSS  & HAS): appDist_forall_subsub_disjoint Ht2 h4.
    exists  (C2' ^-^ B) p'. splits; auto.
    applys Typ_tapp. apply h3. apply HAD.
    auto.
    apply disjoint_covariance with A1. auto. auto. 
    forwards*: Well_lc_typ Ht3.
    +
    forwards* h1: papp_preservation3 H7.
    forwards*: Typing_lc_typ h1.
  -
    inverts J as hh1 hh2 hh3.
    +
    destruct F; unfold fill in *; inverts* hh3.
    forwards* h1: IH hh2. simpl in *. lia.
  -
    inverts J as hh1 hh2 hh3.
    +
    destruct F; unfold fill in *; inverts* hh3.
    forwards* h1: IH hh2. simpl in *. lia.
    lets(t&p'&h2&h3&h4&h5): h1.
    forwards(h6&h7): subsub2sub h4.
    forwards* h9: Typing_regular_0 Ht1.
    forwards* : appDist_rcd_subsub Ht2 .
    +
    forwards* h12: appDist_lc Ht2.
    inverts h12 as h12 h13.
    inverts h13 as h13.
    forwards* h15: papp_preservation_rcd Typ hh2.
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2.
  -
    forwards* h1: Typing_regular_1 Typ.
    forwards* h2: step_not_value J. inverts h2.
Qed.


(* we rely on for some lemmas JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y but it is safe. *)

Lemma Preservation: forall e e' A dir P mu mu',
  P |== mu ->
  Typing P nil e dir A ->
  step (e, mu) (e', mu') ->
  exists P', extends P' P /\ Typing P' nil e' Chk A /\ P' |== mu'.
Proof.
  introv ok Typ J.
  forwards* h:
  Preservation_subsub ok Typ J.
  inverts h as h.
  inverts h as h.
  inverts h as h1 h.
  inverts h as h2 h.
  inverts h as h3 h.
  destruct dir.
  -
    forwards* (h5&h6): subsub2sub h3.
    forwards* h7: Typing_regular_0 Typ.
  -
    forwards* (h5&h6): subsub2sub h3.
    forwards* h7: Typing_regular_0 Typ.
    forwards* h8: Typing_chk_sub h2 h5.
Qed.


Lemma Cast_progress: forall P v A,
    value v -> Typing P nil v Chk A -> 
    exists v', Cast v A v'.
Proof.
  introv Val TypC. 
  lets (B&Typ&Sub): Typing_chk2inf TypC. clear TypC. gen v.
  induction Sub; intros;
    try solve [inverts Typ; try solve[inverts Val as h0;inverts h0]; eauto].
  -
     forwards h1: value_lc Val.
     exists.
     apply cast_top; auto.
     forwards h2: principal_type_checks2 Typ; auto.
     rewrite h2; auto.
  - 
     inverts Typ as hh0; inverts Val as h0; try solve[ inverts h0 ];
     try solve[inverts hh0 as hh0;inverts hh0]...
     +
      forwards: algo_sub_lc Sub1; auto.
      lets [?|?]: toplike_decidable B; auto.
      *
        forwards h2: toplike_sub Sub2; auto.
        exists.
        apply cast_top; eauto.
      *
         exists.
         apply cast_ref; auto. 
     +
       inverts H5 as h1.
       forwards h2: toplike_sub Sub1; auto.
       exists. 
       apply cast_top; auto.
  - inverts Typ; inverts Val as h0; try solve[inverts h0].
      forwards (?&?): IHSub H3; auto. 
      forwards: value_lc H5; auto.
      exists.
      apply cast_mergel; auto.
      apply H1.
  - inverts Typ; inverts Val as h0; try solve[inverts h0].
    forwards (?&?): IHSub H7; auto. 
      forwards: value_lc H5; auto.
      exists.
      apply cast_merger; auto.
      apply H1.
  - 
    forwards: ord_lc H.
    lets [?|?]: toplike_decidable D; auto.
    +
      forwards: value_lc Val; auto.
      forwards: algo_sub_lc Sub1; auto.
      forwards h1: principal_type_checks2 Typ; auto.
      exists. 
      apply cast_top; auto.
      rewrite h1; auto.
    +
      clear IHSub1 IHSub2. gen C.
      induction v; intros; inverts Typ; try solve [inverts Val as h0; try solve[inverts h0] ]...
      *
        forwards h1: value_lc Val; auto.
        forwards h2: algo_sub_lc Sub1; auto.
        inverts h1 as h1 hh1.
        exists.
        eapply cast_lam; eauto.
        simpl; eauto.
      *
        forwards h1: value_lc Val; auto.
        forwards h2: algo_sub_lc Sub1; auto.
        inverts h1 as h1 hh1.
        inverts Val as h3 h4.
        exists.
        eapply cast_lam; eauto.
        simpl; eauto.
  -
    forwards* (?&?): IHSub1 Typ.
    forwards* (?&?): IHSub2 Typ.
  -
    forwards: algo_sub_lc Sub.
    pick fresh y.
    forwards h1: H y; auto.
    forwards h2: ord_lc h1.
    lets [?|?]: toplike_decidable (t_forall B1 B2); auto.
    +
      forwards: value_lc Val; auto.
      exists. 
      apply cast_top; auto.
      forwards h5: principal_type_checks2 Typ; auto.
      rewrite h5; auto.
    +
      clear IHSub. gen B2.
      induction v; intros; inverts Typ as hh0; try solve [inverts Val as h0 hh1; try solve[inverts hh0 as hh0;inverts hh0];
      try solve[inverts h0] ]; try solve[inverts hh0]...
      forwards: value_lc Val; auto.
      forwards: algo_sub_lc Sub; auto.
      exists.
      apply cast_tabs; auto.
  -
    inverts Typ as h0 h1; try solve[inverts Val as hh0; try solve[inverts hh0] ].
    inverts Val as h2; try solve[inverts h2].
    forwards* h3: IHSub h0.
Qed.



Lemma papp_progress: forall v1 v2 A P mu,
     value v1 -> value v2 -> Typing P nil (e_app v1 v2) Inf A 
    -> exists e, papp v1 (arg_exp v2) mu e mu.
Proof with eauto.
  introv Val1 Val2 Typ. gen A.
  induction Val1; intros;
    try solve [exists*];
    try solve[inverts Typ as h1 h2 h3;
    inverts h1 as h1; inverts h3].
  - 
    inverts Typ as h1 h2 h3. inverts H as h4 h5.
    +
      inverts h1 as h1; try solve[inverts h1 as h1;inverts h1].
      inverts h3.
      forwards (v2'&h3): Cast_progress h2; auto.
      exists. 
      apply pap_beta; auto.
      apply h3.
    +
      exists*.
  - 
    inverts Typ as h1 h2 h3.
    inverts h1 as h4 h5 h6; inverts h3 as h3 ...
    + 
      inverts h3 as h3.
      forwards*: Typ_app v1 v2 H2.
      forwards*: Typ_app v0 v2 H4.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
Qed.



Lemma papp_progress2: forall v1 v2 A P mu,
     P |== mu -> value v1 -> value v2 -> Typing P nil (e_ass v1 v2) Inf A 
    -> exists e mu', papp v1 (arg_exp v2) mu e mu'.
Proof with eauto.
  introv ok Val1 Val2 Typ. gen A.
  induction Val1; intros;
  forwards Lc : Typing_regular_1 Typ;
  inverts Lc; try solve[inverts Typ as h1;
  inverts h1 as h1];
  try solve[
    inverts Typ as h1 h2;
    inverts H; try solve[inverts h1]
  ].
  -
    inverts Typ as h1 h2.
    inverts h1 as h1; try solve[inverts h1 as h1;inverts h1].
    forwards: Well_lc_typ H8.
    lets ok':ok.
    inverts ok as h3 h4.
    inverts h4 as h4 h5.
    rewrite h4 in H9.
    forwards* h6: sto_ok_value h3.
    forwards* h7: h5 o.
    inverts h7 as h7.
    inverts h7 as h7 h8. 
    forwards* h9: principal_type_checks2 h7.
    rewrite <- h9 in *.
    apply subsub2sub in h8.
    inverts h8 as h81 h82.
    forwards* h10: value_ptys h6.
    assert(algo_sub A1 (store_Tlookup o P) ) as h11.
    inverts* H10; try solve[
      exfalso; apply hh0; auto
    ];
    try solve[
      forwards hh: split_ord_false H1;auto; inverts* hh
    ].
    forwards* h12: sub_transitivity h11 h82.
    forwards* h18: Typing_chk_sub h2 h12.
    forwards* h19: Cast_progress h18.
    inverts h19 as h19.
    exists.
    apply pap_ass; auto.
    apply h19.
  -
    inverts Typ as h1 h2; auto.
    exists*.
Qed.


Lemma papp_progress3: forall v1 T A P mu,
    value v1 -> Typing P nil (e_tapp v1 T) Inf A -> exists e, papp v1 (arg_typ T) mu e mu.
Proof with eauto.
  introv Val1 Typ. gen A.
  induction Val1; intros;
  forwards Lc : Typing_regular_1 Typ;
  inverts Lc;
  try solve[
    inverts Typ as h1;
    inverts h1 as h1;
    inverts H4
  ];
  try solve[
    inverts Typ as h1 h2;
    inverts H; try solve[inverts h1; inverts h2]
  ];
  try solve[
    inverts Typ as h1 h2;
    inverts h1 as h1; try solve[inverts h1 as h1;inverts h1];eauto
  ].
  -
    inverts Typ as h1 h2.
    inverts h1 as h1 h3; inverts h2 as h2...
    + inverts h2 as h2.
      forwards (?&?): disjoint_andr_inv A0 B0 H8; auto.
      forwards: Typ_tapp h1...
      forwards: Typ_tapp h3...
      forwards (?&?): IHVal1_1...
      forwards (?&?): IHVal1_2...
Qed.




Lemma papp_progress_rcd: forall v1 i5 A P mu,
     value v1 -> Typing P nil (e_proj v1 i5) Inf A 
    -> exists e, papp v1 (arg_la i5) mu  (e)  mu.
Proof with eauto.
  introv Val1 Typ. gen A.
  induction Val1; intros;
    try solve [exists*];
    try solve[
      inverts Typ;
    inverts* H3; inverts* H4
    ];
    try solve[ inverts Typ as h1 h2;
    inverts h1 as h1; inverts h2 as h2; eauto].
  - 
    inverts Typ as h1 h2. inverts h1; try solve[inverts H];
    try solve[inverts* h2].
    inverts* H.
    inverts* H0.
    inverts H.
    inverts h2.
  - 
    inverts Typ as h1 h3.
    inverts h1 as h1 h2 ; inverts h3 as h3...
    inverts h3.
    forwards*: Typ_proj v1 i5 H2.
    forwards*: Typ_proj v2 i5 H4.
    forwards* (?&?): IHVal1_1.
    forwards* (?&?): IHVal1_2.
Qed.





Lemma fvalue_decidable: forall v,
 lc_exp v ->
 fvalue v \/ not(fvalue v).
Proof.
  introv lc.
  inductions lc; try solve[left*]; try solve[
    right; unfold not;intros nt;inverts nt
  ].
  inverts* IHlc; try solve[left*]; try solve[
    right; unfold not;intros nt;inverts nt
  ].
  destruct A; try solve[left*]; try solve[
    right; unfold not;intros nt;inverts nt
  ].
  destruct A; try solve[left*]; try solve[
    right; unfold not;intros nt;inverts nt
  ].
  inductions lc; try solve[left*]; try solve[
    right; unfold not;intros nt;inverts nt as h0;inverts h0
  ].
  right; unfold not;intros nt;inverts nt as h0;inverts h0.
  apply H1; auto.
  apply H1; auto.
Qed.


Lemma value_decidable: forall v,
 lc_exp v ->
 value v \/ not(value v).
Proof.
 introv lc.
  inductions lc; try solve[left*]; try solve[
    right; unfold not;intros nt;
  inverts nt as h03; inverts h03
  ].
  -
    inverts* IHlc1; try solve[left*]; try solve[
      right; unfold not;intros nt;inverts nt as h0; try solve[ inverts h0];
   try solve[exfalso; apply H; auto]
    ].
    inverts* IHlc2; try solve[left*]; try solve[
      right; unfold not;intros nt;inverts nt as h0; try solve[ inverts h0];
   try solve[exfalso; apply H0; auto]
    ].
  -
    forwards* h1: fvalue_decidable lc.
    inverts h1 as h1.
    +
    destruct A; try solve[left*]; try solve[
      right; unfold not;intros nt;inverts nt as h0; inverts h0
    ].
    inverts h1 as h1; try solve[
      right; unfold not;intros nt;inverts nt as h0; inverts h0 as h0; eauto
    ].
    inverts h1 as h1; try solve[
      right; unfold not;intros nt;inverts nt as h0; inverts h0 as h0; eauto
    ].
    +
    destruct A; try solve[left*]; try solve[
      right; unfold not;intros nt;inverts nt as h0; inverts h0
    ]; try solve[left*];
    try solve[
      inductions lc; try solve[
        right; unfold not;intros nt;inverts nt as h0; inverts h0 as h0;inverts h0]; try solve[left*];
        try solve[
          right; unfold not;intros nt;inverts nt as h0;
          inverts* h0 
        ]
    ].
  -
    inverts* IHlc; try solve[left*]; try solve[
        right; unfold not;intros nt;inverts nt as h0; try solve[ inverts h0];
    try solve[exfalso; apply H; auto]
      ].
Qed.



Lemma progress : forall P mu e dir T,
  P |== mu ->
  Typing P nil  e dir T ->
  value e \/ exists e' mu', step (e, mu) (e', mu').
Proof.
  introv wel Typ.
  lets Typ': Typ.
  inductions Typ;
  lets Lc: Typing_regular_1 Typ';
    try solve [left*];
    try solve [right*];
    try solve [inverts* wel];
    try solve [inverts* H0]; eauto.
  - (* app *)
    right.
    forwards hh1:  IHTyp1;auto.
    forwards hh2:  IHTyp2;auto.
    inverts hh1 as hh1.
    inverts hh2 as hh2.
    +
    forwards* h1: papp_progress mu Typ'.
    inverts wel.
    lets e h5: h1.
    exists*.
    +
    inverts hh2 as hh2.
    inverts hh2 as hh2.
    inverts wel.
    rewrite fill_appr.  exists*.
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel. inverts Lc.
    rewrite fill_appl. exists*.
  - (* merge *)
    forwards hh1:  IHTyp1;auto.
    forwards hh2:  IHTyp2;auto.
    inverts hh1 as hh1.
    inverts hh2 as hh2.
    +
      eauto.
    +
    inverts hh2 as hh2.
    inverts hh2 as hh2.
    inverts wel.
    rewrite fill_merger. right. exists*.
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel. inverts Lc.
    rewrite fill_mergel. right. exists*.
  - (* anno *)
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1.
    +
    destruct(value_decidable (e_anno e A)); auto.
    forwards* h1: Cast_progress Typ.
    inverts* h1.
    inverts wel.
    right.
    exists*.
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel.
    rewrite fill_anno. right. exists*.
  -
    right. 
    forwards hh1:  IHTyp1;auto.
    forwards hh2:  IHTyp2;auto.
    inverts hh1 as hh1.
    inverts hh2 as hh2.
    +
      forwards* h1: papp_progress2 wel Typ'.
      lets wel': wel.
      inverts wel.
      lets e mu' h5: h1.
      exists*.
    +
      inverts hh2 as hh2.
      inverts hh2 as hh2.
      inverts wel.
      rewrite fill_assr. 
      exists*.
    +
      inverts hh1 as hh1.
      inverts hh1 as hh1.
      inverts wel.
      forwards*: Typing_regular_1 Typ2.
      rewrite fill_assl. exists*.
  -
    right. 
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1.
    +
    lets wel': wel.
    inverts wel.
    inverts Typ; try solve[inverts hh1 as hh1; inverts* hh1].
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    rewrite fill_get. 
    inverts wel. 
    exists*. 
  -
    right. 
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1.
    + inverts* wel. 
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel. 
    rewrite fill_ref.  exists*.
  -
    right. 
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1.
    +
      forwards* h1: papp_progress3 mu Typ'.
      lets wel': wel.
      inverts wel.
      lets e0 h5: h1.
      exists*.
    +
      inverts hh1 as hh1.
      inverts hh1 as hh1.
      lets wel': wel.
      inverts wel.
      rewrite fill_tapp. exists*.
  -
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1; eauto.
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel.
    rewrite fill_rcd. right. exists*.
  -
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1; eauto.
    +
    forwards* hh2: papp_progress_rcd Typ'.
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel.
    rewrite fill_proj. right. exists*.
Qed.

