Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Import ListNotations.
Require Import Arith Lia.


Require Import syntax_ott
                rules_inf
                Infrastructure
                Wellformedness
                SubtypingInversion
                Value
                Disjointness
               KeyProperties
               Deterministic
               IsomorphicSubtyping.
               

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
  (e_set e1 e2) = (fill (setCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_assr : forall e1 e2,
  (e_set e1 e2) = (fill (setCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_ref : forall e,
  (e_ref e) = (fill (refCtx) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_get : forall e,
  (e_get e) = (fill (getCtx) e).
Proof.
  intros. eauto.
Qed.

(* Lemma fill_anno : forall e1 A,
  (e_anno e1 A) = (fill (annoCtx A) e1).
Proof.
  intros. eauto.
Qed. *)



Lemma nfill_appl : forall e1 e2,
  (e_app e1 e2) = (nfill (nappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma nfill_appr : forall e1 e2,
  (e_app e1 e2) = (nfill (nappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma nfill_assl : forall e1 e2,
  (e_set e1 e2) = (nfill (nsetCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma nfill_assr : forall e1 e2,
  (e_set e1 e2) = (nfill (nsetCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma nfill_ref : forall e,
  (e_ref e) = (nfill (nrefCtx) e).
Proof.
  intros. eauto.
Qed.


Lemma nfill_get : forall e,
  (e_get e) = (nfill (ngetCtx) e).
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




Lemma Typing_weaken : forall P G E F e dir T,
    Typing P (E ++ G) e dir T ->
    uniq (E ++ F ++ G) ->
    Typing P (E ++ F ++ G) e dir T.
Proof with eauto.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos...
    - (* abs *)
      pick fresh x and apply Typ_abs...
      rewrite_env (([(x, A1)] ++ E) ++ F ++ G).
      apply~ H0.
      simpl_env.
      solve_uniq.
    -
      pick fresh x and apply Typ_abst...
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      simpl_env.
      solve_uniq.
Qed.


Lemma Typing_weakening : forall P (E F : ctx) e dir T,
    Typing P E e dir T ->
    uniq (F ++ E) ->
    Typing P (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Typing_weaken.
Qed.


Lemma fv_in_dom: forall P G e dir T,
    Typing P G e dir T -> fv_exp e [<=] dom G.
Proof.
  introv H.
  induction H; simpl; try fsetdec.
  - (* Typing_var *) 
    apply binds_In in H0.
    fsetdec.
  - (* Typing_abs*)
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A1)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - (* Typing_abs*)
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.  
Qed.


Lemma value_no_fv : forall P v dir T,
    Typing P [] v dir T -> fv_exp v [<=] empty.
Proof.
  introv.
  pose proof (fv_in_dom P [] v).
  intuition eauto.
Qed.


Lemma subst_value : forall P v T dir z u,
    Typing P [] v dir T -> subst_exp u z v = v.
Proof.
  introv Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.


Lemma Typing_subst_1 : forall P (E F : ctx) e u S dir T (z : atom),
    Typing P (F ++ [(z, S)] ++ E) e dir T ->
    Typing P E u Inf S ->
    Typing P (F ++ E) ([z ~> u] e) dir T.
Proof.
  introv Typ Typv.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  inductions Typ;
    intros F Eq; subst; simpl; autos;
      lets Lc  : Typing_regular_1 Typv; eauto.
  - (* var *)
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ Typing_weakening.
    solve_uniq.
  - (* abs *)
    pick fresh x and apply Typ_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A1)] ++ F) ++ E).
    apply~ H0.
  (* -
    forwards* h1: subst_value z u Typ.
    rewrite h1; eauto. *)
  - 
  pick fresh x and apply Typ_abst; eauto.
  rewrite subst_exp_open_exp_wrt_exp_var; auto.
  rewrite_env (([(x, A)] ++ F) ++ E).
  apply~ H0.
Qed.


Lemma typing_c_subst_simpl_1 : forall P E e u S dir T z,
  Typing P ([(z, S)] ++ E) e dir T ->
  Typing P E u Inf S ->
  Typing P E ([z ~> u] e) dir T.
Proof.
  introv H1 H2.
  rewrite_env (nil ++ E).
  eapply Typing_subst_1.
    simpl_env. apply H1.
    apply H2.
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



Lemma assign_pres_store_typing : forall ST st l v,
  l < length st ->
  value v ->
  sto_typing ST st ->
  Typing ST nil v Inf (store_Tlookup l ST) ->
  sto_typing ST (replace l v st).
Proof with auto.
  introv  Hlen val HST Ht.
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
  - (* l' <> l *)
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H2...
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
    forwards* h1: length_extends H.
    forwards* h2: extends_lookup H.
    rewrite <- h2; eauto.
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
      apply store_weakening with ST...
      rewrite app_nth2; [|lia].
      rewrite minus_diag. simpl.
      auto.
Qed.


Lemma value_unique: forall p1 p2 v t1 t2,
  value v ->
  Typing p1 [] v Inf t1 ->
  Typing p2 [] v Inf t2 ->
  t1 = t2.
Proof.
 introv val ty1 ty2. gen p1 p2 t1 t2.
 inductions val; intros;try solve[inverts ty1; inverts ty2; auto];eauto.
Qed.



Lemma both_sto: forall G p1 p2 mu e t dir, 
   p1 |== mu ->
   p2 |== mu ->
   Typing p1 G e dir t ->
   Typing p2 G e dir t.
Proof.
 introv ok1 ok2 typ. 
 gen mu p2.
 inductions typ;intros; eauto.
   inverts ok1 as h3 h4.
   inverts h4 as h41 h42.
   inverts ok2 as h5 h6.
   inverts h6 as h61 h62.
   rewrite h41 in *.
   rewrite <- h61 in *.
   forwards* h7: h62 o.
   forwards* h8: h42 o.
   forwards* h11: sto_ok_value o h3.
   rewrite <- h61; auto.
   forwards* h12: value_unique h7 h8.
   inverts h12.
   eauto.
Qed.


(* 
Lemma abs_false: forall L e A,
 Typing L [] (e_abs e) Chk A ->
 False.
Proof.
 introv ty.
 inductions ty;eauto; try solve[inverts ty].
Qed. *)




Lemma Typing_strenthening : forall P G e A1 A2,
    Typing P nil e Inf A1 ->
    Typing P G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 G.
  inductions Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2);
  try solve[inverts* H4];
  try solve[inverts* H0].
  - (* t_app *)
    forwards * h2: IHTy1_1 H3.
    inverts* h2.
  - (* t_ref *)
    forwards*: IHTy1 H2.
    inverts H; auto.
  - (* t_ref *)
    forwards*: IHTy1 H2.
    inverts H; auto.
Qed.



Lemma inference_unique : forall P G e A1 A2,
    Typing P G e Inf A1 ->
    Typing P G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2);
  try solve[inverts* H4];
  try solve[inverts* H0].
  - (* t_var *)
    forwards* h1: binds_unique H0 H5.
  - (* t_app *)
    forwards * h1: IHTy1_1 H3.
    inverts* h1.
  - (* t_ref *)
    forwards * h1: IHTy1 H2.
    inverts* h1.
  - 
    forwards * h1: IHTy1 H2.
    inverts* h1.
Qed.



Lemma val_chk:forall L e A t,
 Typing L [] (e_anno e A) Chk t ->
 Typing L [] e Chk A /\ algo_sub A t.
Proof.
 introv typ.
 inductions typ;eauto.
 -
 inverts typ;eauto.
 -
 forwards*h2:IHtyp1.
 forwards*h3:IHtyp2.
Qed.



Lemma anno_chk_sub:forall L e A t,
 Typing L [] (e_anno e A) Chk t ->
 Typing L [] e Chk A /\ algo_sub A t.
Proof.
 introv typ.
 inductions typ;eauto.
 -
 inverts typ;eauto.
 -
 forwards*h2:IHtyp1.
 forwards*h3:IHtyp2.
Qed.

Lemma Typing_chk_sub_gen: forall G e A B P n,
    size_typ A + size_typ B < n ->
    Typing P G e Chk A -> algo_sub A B -> Typing P G e Chk B.
Proof.
  introv sz H H0. gen G e A B.
  induction n; intros;try solve[lia].
  inverts H as h1 h2; intros.
  -
    inverts H0; auto.
    +
    pick fresh x and apply Typ_abst; eauto.
    forwards h3: h1 x; auto.
    forwards h4: IHn h3; auto.
    simpl in *; lia.
    +
    forwards: sub_transitivity H3 h2.
    pick fresh x and apply Typ_abs; auto.
    forwards h3: h1 x; auto.
    forwards: IHn h3 H5.
    simpl in *; lia.
    eauto.
    +
    forwards h4: split_decrease_size H.
    
    forwards h6: IHn G (e_abs e0 A1) H1; auto.
    eauto.
    simpl in *; lia.
    forwards h7: IHn G (e_abs e0 A1) H2; auto.
    eauto.
    simpl in *; lia.
    eauto.
  - eapply Typ_sub.
    apply h1.
    auto_sub.
  -
    forwards h3: ord_or_split B.
    inverts h3 as h3.
    +
    forwards h4: split_decrease_size H2.
    forwards h5: sub_inversion_split_l H0 H2; auto.
    inverts h5 as h5.
    *
    forwards h6: IHn h1 h5; auto.
    simpl in *; lia.
    *
    forwards h6: IHn h2 h5; auto.
    simpl in *; lia.
    +
    inverts h3 as h3.
    inverts h3 as h3.
    forwards h4: split_decrease_size h3.
    forwards h5: sub_r_spl_l h3 H0; auto.
    forwards h6: sub_r_spl_r h3 H0; auto.
    forwards h7: IHn G e h5; auto.
    eauto.
    simpl in *; lia.
    forwards h8: IHn G e h6; auto.
    eauto.
    simpl in *; lia.
    eauto.
  -
    inverts H0; auto.
    eauto.
    forwards h4: split_decrease_size H.
    
    forwards h6: IHn G (e_abs e0 A0) H1; auto.
    eauto.
    simpl in *; lia.
    forwards h7: IHn G (e_abs e0 A0) H2; auto.
    eauto.
    simpl in *; lia.
    eauto.
Qed.


Lemma Typing_chk_sub: forall G e A B P,
    Typing P G e Chk A -> algo_sub A B -> Typing P G e Chk B.
Proof.
  introv H H0. 
  eapply Typing_chk_sub_gen; eauto.
Qed.

Lemma ppvalue_inf: forall p L t,
 ppvalue p ->
 Typing L [] p Chk t ->
 exists t1, Typing L [] p Inf t1 /\ algo_sub t1 t.
Proof.
 introv pval typ.
 inductions typ; try solve[inverts pval]; eauto.
 forwards* h1: IHtyp1 pval.
 forwards* h2: IHtyp2 pval.
 inverts h1 as h1.
 inverts h2 as h2.
 inverts h1 as h1 h3.
 inverts h2 as h2 h4.
 forwards* h5: inference_unique h1 h2.
 inverts h5; auto.
 exists*. 
Qed.


Lemma loc_inf: forall o L t,
 Typing L [] (e_loc o) Chk t ->
 exists t1, Typing L [] (e_loc o) Inf t1 /\ algo_sub t1 t.
Proof.
 introv typ.
 inductions typ; try solve[inverts pval]; eauto.
 forwards* h1: IHtyp1.
 forwards* h2: IHtyp2.
 inverts h1 as h1.
 inverts h2 as h2.
 inverts h1 as h1 h3.
 inverts h2 as h2 h4.
 forwards* h5: inference_unique h1 h2.
 inverts h5; auto.
 exists*. 
Qed.

Lemma app_preservation: forall L e A0 mu A1 A2 p C n,
  size_typ A1 + size_typ A2 < n ->
  L |== mu ->
  Typing L [] (e_abs e A0) Chk (t_arrow A1 A2) ->
  Typing L [] (e_anno p C) Chk A1 ->
  pvalue p ->
  exists P' : phi,
  extends P' L /\
  Typing P' [] (e_anno (e ^^ e_anno p A0) A2) Inf A2 /\ P' |== mu.
Proof.
 introv sz ok typ1 typ2 pval. gen A1 A2.
 inductions n; intros; try solve[lia].
 inverts typ1 as h1 h2; try solve[inverts h1].
 -
   forwards* h3: val_chk typ2.
   inverts h3 as h3 h4.
   forwards* h5: Typing_chk_sub h3 h4.
   forwards* h6: Typing_chk_sub h5 h2.
  exists. splits*.
  apply Typ_anno; auto.
  pick_fresh xx.
  rewrite* (@subst_exp_intro xx).
  forwards* h10: h1 xx.
  forwards* h11: typing_c_subst_simpl_1 (e_anno p A0) h10; auto.
 -
   inverts H1 as h3.
   forwards* h4: split_decrease_size h3.
   forwards* h5: IHn h1.
   simpl in *; lia.
   forwards* h6: IHn h2.
   simpl in *; lia.
   lets(p1&ext1&ttyp1&wf1): h5.
   lets(p2&ext2&ttyp2&wf2): h6.
   inverts ttyp1 as h7.
   inverts ttyp2 as h8.
   forwards* h9: both_sto wf1 wf2 h7.
Qed.


(* we rely on for some lemmas JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y but it is safe. *)
Lemma Preservation: forall e e' A dir P mu mu',
  P |== mu ->
  Typing P nil e dir A ->
  step (e, mu) (e', mu') ->
  exists P', extends P' P /\ Typing P' nil e' dir A /\ P' |== mu'.
Proof with (simpl; try lia; auto; try eassumption; eauto).
  introv ok Typ J. gen mu mu' e'.
  lets typ: Typ.
  inductions Typ; intros; auto; 
  try solve[forwards h1: step_not_value J; auto;inverts h1];
  try solve [inverts H0].
  - 
    inverts J as h1 h2 h3.
    destruct F; unfold fill in *;inverts h3.
    inverts* h3.
  -
    inverts J as h1 h2 h3.
    destruct F; unfold fill in *;inverts h3.
    inverts* h3.
    lia.
  -
    inverts J as h1 h2 h3.
    +
    destruct F; unfold fill in *;inverts h3.
    +
    destruct i5; try solve[inverts H0].
    inverts* h3.
  -
    inverts J as h1 h2 h3.
    +
    destruct F; unfold fill in *;inverts h3.
    +
    inverts h2.
    (* exists*. *)
  - (* app *)
    inverts J as h1 h2 h3; try solve[inverts h2].
    +
      destruct F; unfold fill in *; inverts* h3.
      *
      inverts h1. 
      forwards* h1: IHTyp1 h2. 
      *
      inverts h1. 
      forwards* h1: IHTyp2 h2. 
    +
      inverts Typ1 as h3 h4 h5.
      forwards*: app_preservation h3 Typ2.
    +
      inverts Typ1 as h4 h5 h6.
      exists*.
  - (* anno *)
    inverts J as h1 h2 h3; try solve[inverts h2].
    +
    destruct F; unfold fill in *; inverts* h3.
    +
    forwards* h4: IHTyp Typ.
    +
    forwards*h5: val_chk Typ.
    inverts h5 as h5 h6.
    forwards* h7: Typing_chk_sub h5 h6.
    (* +
    inverts* typ. *)
  - (* sub *)
    forwards (?&h1&h2&h3): IHTyp  J; simpl in *; auto.
    exists x.
    splits; eauto.
  - (* loc *)
    inverts J as h1 h2 h3;try solve[inverts* h2].
    destruct F; unfold fill in *;inverts h3.
    inverts* h3.
    lets ok': ok.
    inverts ok as h4 h5.
    inverts h5 as h51 h52.
    rewrite h51 in *.
    forwards* h6: h52.
    rewrite <- H2 in h6.
    inverts* h6.
  - (* ass *)
    inverts J as h1 h2 h3; try solve[inverts h2].
    +
    destruct F; unfold fill in *; inverts* h3. 
    *
    forwards* h4: IHTyp1 h2.
    *
    forwards* h4: IHTyp2 h2.
    +
    inverts Typ1 as h3 h4 h5.
    forwards h6: loc_inf H4; eauto.
    inverts h6 as h6 h7.
    inverts h6 as h6 h62.
    inverts h6 as h6.
    inverts h62 as h15 h16; try solve[inverts h15].
    forwards h8: val_chk Typ2.
    inverts h8 as h8 h9.
    forwards* h17: sub_transitivity h9 h16.
    lets ok': ok.
    inverts ok as h19 h20.
    inverts h20 as h20 h21.
    rewrite h20 in *.
    forwards* h22: h21 o.
    forwards* h24: sto_ok_value H3.
    lets h22': h22.
    rewrite <- h3 in h22.
    inverts h22.
    forwards* h25: length_replace o (e_anno p (store_Tlookup o L)) mu.
    forwards* h26: assign_pres_store_typing (e_anno p (store_Tlookup o L)).
    forwards* h27: Typing_chk_sub h8 h17.
    +
    inverts Typ1.
    exists*.
  - (* deref *)
    inverts J as h1 h2 h3; try solve[inverts h2].
    +
    destruct F; unfold fill in *; inverts* h3.
    forwards* h4: IHTyp h2. 
    +
    lets ok':ok.
    inverts ok' as h3 h4.
    inverts h4 as h4 h5.
    inverts typ as hh0.
    inverts hh0 as hh0 hh1 hh2.
    inverts hh0 as hh2 hh3 hh4; try solve[inverts hh4].
    rewrite <- h4 in *.
    inverts hh2 as hh2.
    forwards* h6: h5 o.
    inverts hh3 as h7 h8; try solve[inverts h7].
    rewrite h4 in *.
    forwards* h9: sto_ok_value h1.
  - (* ref *)
    inverts J as h1 h2 h3; try solve[inverts h2].
    +
    destruct F; unfold fill in *; inverts* h3.
    forwards* h4: IHTyp h2. 
    +
    lets ok':ok.
    inverts ok' as h3 h4.
    inverts h4 as h4 h5.
    rewrite <- h4.
    inverts typ as hh1.
    inverts hh1.
    exists (L ++ A :: nil).
    splits*.
    eapply Typ_anno; eauto.
    eapply Typ_sub.
    apply Typ_loc; auto.
    rewrite app_length. simpl. lia.
    apply S_ref.
    unfold store_Tlookup.
    rewrite nth_eq_last; eauto.
    unfold store_Tlookup.
    rewrite nth_eq_last; eauto.
    forwards*: store_well_typed_app Typ.
  -
    inverts J as h1 h2 h3.
    destruct F; unfold fill in *;inverts h3.
    inverts* h3.
  - (* intro *)
    forwards* h1: IHTyp1 Typ1.
    lets(p1&h2&h3&h4): h1.
    forwards* h10: IHTyp2 Typ2.
    lets(p2&h6&h7&h8): h10.
    forwards h15: both_sto h4 h8 h3.
    assert(Typing p2 [] e' Chk (t_and A B)) as h16.
    eapply Typ_intro; auto.
    apply h15.
    apply h7.
    eauto.
  -
    forwards* h1: step_not_abs J.
    inverts h1.
Qed.


Lemma chk_arr: forall L p A1 A2,
 pvalue p -> 
 Typing L [] p Chk (t_arrow A1 A2) ->
 exists e t1, p = (e_abs e t1).
Proof.
  introv pval typ.
  inductions typ; try solve[inverts* pval].
  -
    clear IHtyp.
    inductions H; try solve[inverts pval; inverts typ].
    +
    inverts* H.
    forwards*: IHalgo_sub1.
  -
    inverts H.
    inverts pval;try solve[ inverts typ; inverts H as h1; try solve[inverts h1]]; eauto.
Qed.


Lemma chk_ref: forall L p A,
 pvalue p -> 
 Typing L [] p Chk (t_ref A) ->
 exists o, p = (e_loc o).
Proof.
 introv pval typ.
 inductions typ; try solve[inverts* H].
 -
    inverts pval;try solve[ inverts typ; inverts H as h1; try solve[inverts h1]]; eauto.
Qed.


Lemma pvalue_decidable: forall v,
 lc_exp v ->
 pvalue v \/ not(pvalue v).
Proof.
  introv lc.
  inductions lc; try solve[left*]; try solve[
    right; unfold not;intros nt;inverts nt
  ].
Qed.


Lemma tymu_progress: forall p mu t L,
 L |== mu ->
 Typing L [] p Inf t ->
 pvalue p ->
 exists t', tymu p mu t'.
Proof.
 introv ok typ pval.
 inverts* pval; try solve[inverts* typ].  
 inverts typ.
 inverts ok as ok1 ok2.
 inverts ok2 as ok21 ok22.
 rewrite ok21 in *.
 forwards* h1: ok22 H3.
 forwards* h2: sto_ok_value ok1.
 inverts h2; try solve[inverts* h1].
 rewrite <- H in h1.
 inverts h1.
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
    try solve[inverts* wel;inverts* Lc; right; exists*];
    try solve [inverts* H0]; eauto. 
  - (* app *)
    right.
    forwards hh1:  IHTyp1;auto.
    forwards hh2:  IHTyp2;auto.
    inverts hh1 as hh1.
    inverts hh2 as hh2.
    +
    inverts hh1 as h1; try solve[inverts Typ1].
    inverts Typ1 as h2 h3 h4.
    forwards* h5: chk_arr h2.
    inverts h5 as h5.
    inverts h5 as h5.
    lets wel': wel.
    inverts* wel.
    inverts h1.
    inverts hh2 as hh2; eauto.
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
  - (* anno *)
    forwards hh1:  IHTyp;auto.
    inverts hh1 as hh1; try solve[inverts hh1;inverts* wel].
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    *
    inverts wel.
    inverts Lc.
    forwards* h1: pvalue_decidable e.
    inverts h1 as h1; eauto.
  - (* loc *)
    forwards* h1: tymu_progress wel.
    inverts* wel.
  -
    right. 
    forwards hh1:  IHTyp1;auto.
    forwards hh2:  IHTyp2;auto.
    inverts hh1 as hh1.
    inverts hh2 as hh2.
    +
      inverts hh1 as h1; try solve[inverts Typ1].
      inverts Typ1 as h2 h3 h4.
      forwards* h5: chk_ref h2.
      inverts h5 as h5.
      lets wel': wel.
      inverts wel as ok1 ok2.
      inverts h2 as h2; try solve[inverts H1].
      inverts h2.
      inverts* hh2.
      inverts ok2 as ok2 ok3.
      rewrite <- ok2 in *.
      forwards* h7: ok3 x.
      rewrite ok2 in *. 
      forwards* h6: sto_ok_value ok1.
      inverts h6 as h61 h62; try solve[inverts* h7].
      rewrite <- h62 in *.
      inverts* h7.
      exists*.
      eapply Step_ass; auto.
      apply h62.
      rewrite <- h62 in *.
      inverts* h7.
    +
      inverts hh2 as hh2.
      inverts hh2 as hh2.
      *
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
    inverts hh1 as hh1.
    forwards* h5: chk_ref H1.
    inverts h5 as h5;eauto.
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
      inverts* hh1.
      inverts Typ.
    +
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts wel. 
    rewrite fill_ref.  exists*.
Qed.


Lemma erase_lc2: forall e1 e2,
 erase e1 e2 ->
 lc_exp e2.
Proof.
 introv ed.
 inductions ed; eauto. 
Qed.


Lemma erase_lc: forall e1 e2,
 erase e1 e2 ->
 lc_exp e1.
Proof.
 introv ed.
 inductions ed; eauto. 
Qed.


Lemma pvalue_nvalue: forall v1 v2,
 pvalue v1 -> 
 erase v1 v2 ->
 nvalue v2.
Proof.
 introv pval er.
 forwards*: erase_lc2 er.
 inverts pval as h1 h2; try solve[inverts er as h3;
 inverts h3; eauto]; try solve[inverts* er];eauto.
Qed.



Lemma value_nvalue: forall v1 v2,
 value v1 -> 
 erase v1 v2 ->
 nvalue v2.
Proof.
 introv val er.
 inverts val as h1.
 inverts er as h2.
 -
 forwards*: pvalue_nvalue h1.
 -
 forwards*: erase_lc2 er.
 inverts* er.
Qed.


Lemma erase_length : forall mu1 mu2,
 erasem mu1 mu2 ->
 length mu1 = length mu2.
Proof.
 introv er.
 inductions er; simpl ;eauto.
Qed.


Lemma erase_ok : forall mu1 mu2,
 sto_ok mu1 ->
 erasem mu1 mu2 ->
 sto_okn mu2.
Proof.
 introv ok er.
 inductions er; simpl ;eauto.
 inverts ok as h1 h2.
 forwards* h3: value_nvalue H.
Qed.


Lemma erase_lookup : forall mu1 mu2 o,
 sto_ok mu1 ->
 erasem mu1 mu2 ->
 erase (store_lookup o mu1) (store_lookup o mu2).
Proof.
 introv ok er. gen o.
 inductions er;  intros;simpl in *; eauto.
 -
   unfold store_lookup.
   destruct o; simpl in *; eauto.
 -
   inverts ok as h2 h3.
   forwards* h1: IHer o.
   destruct o; simpl in *;
   try solve[unfold store_lookup in *; eauto].
Qed.


Lemma erase_replace : forall mu1 mu2 v1 v2 o,
 erasem mu1 mu2 ->
 erase v1 v2 ->
 erasem (replace o v1 mu1) (replace o v2 mu2).
Proof.
 introv erm er. gen o v1 v2.
 inductions erm; intros; 
 try solve[inductions o; try solve[unfold replace; eauto]]; eauto.
Qed.


Lemma erase_extend: forall mu1 mu2 mu3 mu4,
 erasem mu1 mu2 ->
 erasem mu3 mu4 ->
 erasem (mu1 ++ mu3) (mu2 ++ mu4).
Proof.
 introv em1 em2. gen mu3 mu4.
 inductions em1; intros;simpl;eauto.
Qed.



Lemma erase_subst: forall x e1 e2 e3 e4,
 erase e1 e2 ->
 erase e3 e4 ->
 erase (subst_exp e3 x e1) (subst_exp e4 x e2).
Proof.
  introv ed1 ed2.
  inductions ed1; simpl in *; eauto.
  -
    destruct(x0 == x); try solve[inverts* e];eauto.
  -
    forwards*: erase_lc ed2.
    forwards*: erase_lc2 ed2.
    pick fresh xx and apply ed_abs.
    forwards* h1: H0 xx.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed.


Lemma erase_exists: forall e1,
 lc_exp e1 ->
 exists e2, erase e1 e2.
Proof.
  introv lc. 
  inductions lc; intros;try solve[exists*];
  try solve[inverts IHlc1; inverts* IHlc2];
  try solve[inverts* IHlc];eauto.
  -
    pick fresh x.
    forwards* h1:H0 x.
    inverts h1 as h1.
    exists (e_abs (close_exp_wrt_exp x x0 ) t).
    pick fresh y and apply ed_abs.
    assert(erase (e_var_f y) (e_var_f y)) as h3; auto.
   forwards* h2:  erase_subst x h1 h3.
   forwards* h4: subst_exp_spec x0 (e_var_f y) x.
   rewrite h4 in h2.
   rewrite (@subst_exp_intro x); auto.
Qed.


Lemma erase_step: forall e1 e2 e1' mu1 mu1' mu2,  
 erase e1 e2 ->
 erasem mu1 mu2 ->
 step (e1, mu1) (e1', mu1') ->
 exists e2' mu2', nsteps (e2, mu2) (e2', mu2') /\ erase e1' e2' /\ erasem mu1' mu2'.
Proof.
 introv er erm red. gen e2 mu2.
 inductions red; intros;try solve[inverts* er].
 -
   destruct F; simpl in *.
   +
   inverts er as h1 h2.
   inverts H as h3.
   forwards* h4:erase_lc2 h2.
   forwards* h5: IHred h1.
   lets(ee1&mmu1&hh1&hh2&hh3): h5.
   rewrite nfill_appl.
   forwards* h6: multi_red_appn h4 hh1.
   +
   inverts er as h1 h2.
   inverts H as h3.
   forwards* h4:value_nvalue h1.
   forwards* h5: IHred h2.
   lets(ee1&mmu1&hh1&hh2&hh3): h5.
   rewrite nfill_appr.
   forwards* h6: multi_red_app2n h4 hh1.
   +
   inverts er as h1.
   forwards* h5: IHred h1.
   lets(ee1&mmu1&hh1&hh2&hh3): h5.
   rewrite nfill_ref.
   forwards* h6: multi_red_refn  hh1.
   +
   inverts er as h1.
   forwards* h5: IHred h1.
   lets(ee1&mmu1&hh1&hh2&hh3): h5.
   rewrite nfill_get.
   forwards* h6: multi_red_getn  hh1.
   +
   inverts er as h1 h2.
   inverts H as h3.
   forwards* h4:erase_lc2 h2.
   forwards* h5: IHred h1.
   lets(ee1&mmu1&hh1&hh2&hh3): h5.
   rewrite nfill_assl.
   forwards* h6: multi_red_setn h4 hh1.
   +
   inverts er as h1 h2.
   inverts H as h3.
   forwards* h4:value_nvalue h1.
   forwards* h5: IHred h2.
   lets(ee1&mmu1&hh1&hh2&hh3): h5.
   rewrite nfill_assr.
   forwards* h6: multi_red_set2n h4 hh1.
   (* +
   inverts er as h1.
   forwards* h2: IHred h1. *)
  -
   inverts er as h1 h2.
   forwards* h5: IHred h1.
  -
   inverts er as h1 h2.
   inverts h1 as h1 h3.
   inverts h2 as h2 h4.
   inverts h1 as h1 h5.
   (* inverts h1 as h1. *)
   forwards* h3: erase_ok erm.
   forwards* h4: pvalue_nvalue h2.
   exists (e' ^^ e2') mu2.
   splits*.
   apply ed_anno.
   pick fresh y.
   rewrite (@subst_exp_intro y); auto.
   assert((e' ^^ e2') = [y ~> e2'] (e' ^ y)) as h6.
   rewrite (@subst_exp_intro y); auto.
   rewrite h6.
   forwards* h7: h1 y.
   assert(erase (e_anno p A1) e2') as h9; eauto.
   forwards* h8: erase_subst h7 h9.
 -
    inverts er as h1.
    inverts h1 as h1.
    exists*.
 (* -
    inverts er as h1.
    inverts h1 as h1.
    exists*. *)
 -
   inverts er as h1.
   inverts h1 as h1.
   inverts h1 as h1.
   forwards* h2: erase_lookup o erm.
   forwards* h3: erase_ok erm.
   exists (store_lookup o mu2) mu2.
   splits*.
 -
   inverts er as h1. 
   forwards* h2: value_nvalue h1.
   forwards* h3: erase_length erm.
   forwards* h4: erase_ok erm.
   rewrite h3.
   assert(erasem [e_anno v t] [e1']) as h5; simpl.
   eapply edm_cons; eauto.
   forwards* h6: erase_extend erm h5.
   exists (e_loc (length mu2)) (mu2 ++ [e1']).
   splits*.
 -
   inverts er as h1 h2.
   inverts h1 as h1.
   inverts h2 as h2.
   inverts h1 as h1.
   forwards* h3: pvalue_nvalue h2.
   assert(erase (e_anno p t) e2') as h6; eauto.
   forwards* h4: erase_replace o erm h6.
   forwards* h5: erase_ok erm.
   exists e_unit (replace o e2' mu2); simpl.
   splits*.
Qed.




Lemma erase_step_v: forall e1 e2 e1' mu1 mu1' mu2,  
 erase e1 e2 ->
 erasem mu1 mu2 ->
 steps (e1, mu1) (e1', mu1') ->
 value e1' ->
 exists e2' mu2', nsteps (e2, mu2) (e2', mu2') /\ erase e1' e2' /\ erasem mu1' mu2' /\ nvalue e2'.
Proof.
  introv er erm reds val. gen e2 mu2.
  inductions reds; intros.
  -
    forwards* h1:value_nvalue er.
  -
    forwards* h1: erase_step H.
    lets(ee1&mmu1& h2& h3& h4): h1.
    forwards* h5: IHreds h3.
    lets(ee2&mmu2& h6& h7& h8 & h9): h5.
    exists. splits.
    eapply nstars_trans.
    apply h2.
    apply h6.
    auto.
    auto.
    auto.
Qed.

