Require Import LibTactics.
Require Import Lia.
Require Export Wellformedness.
Require Import Coq.Program.Equality.

(*********************************** ord & split *******************)
(* #[export] *) Hint Extern 1 (ord _) =>
progress match goal with
         | H: forall X : atom, X `notin` _ -> ord (?B -^ X) |- ord (t_forall _ ?B) => applys O_forall H
         | |- ord (t_forall _ _) => detect_fresh_var_and_apply ord_forall_exists
         | _ => applys O_var + applys O_top + applys O_int + applys O_arrow + applys O_rcd 
         end : core.

(* #[export] *) 
Hint Extern 1 (spl _ _ _) => applys Sp_arrow + applys Sp_and + applys Sp_rcd : core.

(* #[export] *) 
Hint Extern 1 (spl (t_forall _ _)  _ _) => applys Sp_forall : core.


Lemma ord_or_split: forall A,
    lc_typ A -> ord A \/ exists B C, spl A B C.
Proof with (subst~; simpl in *; eauto).
  introv Lc. induction Lc...
  - (* arrow *)
    forwards* [?|(?&?&?)]: IHLc2.
  - (* forall *)
    pick fresh x.
    forwards* [?|(?&?&?)]: H0 x.
  - (* rcd *)
    forwards* [?|(?&?&?)]: IHLc.
Qed.


(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)

Lemma split_ord_false : forall T T1 T2,
     lc_typ T -> spl T T1 T2 -> ord T -> False.
Proof with eauto.
  introv Lc Spl Ord. gen T1 T2.
  induction Ord; intros; inverts Spl...
  pick fresh X. eauto.
Qed.

(* #[export] *)
Hint Resolve split_ord_false : falseHd.


Ltac solve_false := try intro; try solve [false; eauto with falseHd].



Lemma split_unique : forall T A1 A2 B1 B2,
    spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with eauto.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts s2 as h1 h2; eauto;
    try solve [forwards* (eq1&eq2): IHs1; subst*].
  pick fresh X.
  forwards* HS: h2 X.
  forwards* (eq1&eq2): H1 HS.
  assert (HR0: C0 = close_typ_wrt_typ X (C0 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR1: C1 = close_typ_wrt_typ X (C1 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR2: C2 = close_typ_wrt_typ X (C2 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR3: C3 = close_typ_wrt_typ X (C3 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  rewrite HR0. rewrite HR1. rewrite HR2. rewrite HR3.
  rewrite eq1. rewrite eq2. split*.
Qed.

Ltac split_unify :=
  repeat match goal with
         | [ H1: spl ?A _ _ , H2: spl ?A _ _ |- _ ] =>
           (progress forwards (?&?): split_unique H1 H2;
            subst; clear H2)
         | [ H: spl (t_and _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_arrow _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_ref _) _ _ |- _ ] => inverts H
         | [ H: spl (t_forall _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_rcd _ _) _ _ |- _ ] => inverts H
         end;
  auto.


(* #[export] *)
Hint Extern 1 (spl _ _ _) =>
match goal with
| H: spl ?A _ _ |- spl (t_arrow _ ?A) _ _ => applys Sp_arrow H
| H: spl ?A _ _ |- spl (t_rcd _ ?A) _ _ => applys Sp_rcd H
| |- spl (t_and _ _) _ _ => applys Sp_and
end : core.


(********************************* toplike ************************************)

Ltac inverts_for_toplike u :=
  repeat match goal with
         | H: topLike ?A |- _ => match A with
                                 | u => exact H
                                 | context [ u ] => inverts H
                                 end
         end.

(* #[export] *) Hint Extern 1 (topLike ?A) => progress inverts_for_toplike A : core.

(* #[export] *) Hint Extern 1 (topLike (?A -^ _) ) =>
destruct_conj;
  progress match A with
           | t_and ?A1 ?A2 => inverts_for_toplike A1; inverts_for_toplike A2
           | _ => inverts_for_toplike A
           end : core.

(* #[export] *) Hint Extern 1 (topLike _) =>
applys TL_top +
applys TL_and +
applys TL_arr +
applys TL_rcd: core.

(* #[export] *)
 Hint Extern 1 (topLike ?A) =>
match goal with
| H: forall X : atom, X `notin` _ -> topLike _ |- (topLike _ -^ ?Y) =>
  instantiate_cofinite_with H Y
end : core.

(* #[export] *) Hint Extern 2 (topLike (t_forall _ _)) => pick_fresh_applys_and_instantiate_cofinites TL_all : ForallHd2.

Lemma topLike_spl_combine: forall A B C,
    spl C A B -> topLike A -> topLike B -> topLike C.
Proof.
  introv s. induction s;intros; eauto.
  - (* forall *) inverts H2. inverts H3.
    applys~ TL_all (L \u L0 \u L1).
Qed.

Lemma topLike_split_inv: forall  A B C,
    topLike C -> spl C A B -> topLike A /\ topLike B.
Proof.
  introv tl s. 
  induction s; intros; eauto.
  - inversion tl;subst. 
    forwards*: IHs.
  - (* forall *)  inverts tl. split.
    applys~ TL_all (L \u L0).
    intros. assert (topLike  (C1 -^ X)/\ topLike (C2 -^ X)). auto.
    destruct H3. auto.
    applys~ TL_all (L \u L0).
    intros. assert (topLike (C1 -^ X)/\ topLike (C2 -^ X)). auto.
    destruct H3. auto.
  -
    inversion tl;subst. 
    forwards*: IHs.
Qed.

(* this hint make use of the above lemmas, but do not guess the split part *)
(* #[export] *)
 Hint Extern 2 (topLike ?A) =>
match goal with
| H1: spl A _ _  |- _ => apply (topLike_spl_combine _ _ _ H1)
end : core.

(* #[export] *)
 Hint Extern 1 (topLike ?A) =>
match goal with
| H1: spl ?C A  _, H2: topLike ?C |- _ => lets (?&?): topLike_split_inv H2 H1; trivial
| H1: spl ?C _  A, H2: topLike ?C |- _ => lets (?&?): topLike_split_inv H2 H1; trivial
end : core.


(******************************* proper types *********************************)
Lemma rfun : forall B, R B -> forall A, R A -> R (t_arrow A B).
Proof with eauto.
  intros B RB.
  induction RB; intros...
Qed.

Lemma rref : forall A, R A-> R (t_ref A).
Proof with eauto.
  intros A RA.
  induction RA; intros...
Qed.


Lemma rrcd : forall i5, forall A, R A -> R (t_rcd i5 A).
Proof with eauto.
  introv RB.
  induction RB; intros...
Qed.

(* #[local]  *)
Hint Resolve rfun rref rrcd: core.

(* depends on ord_or_split *)
Lemma rforall : forall A B X,
    R A -> R B
    -> R (t_forall A (close_typ_wrt_typ X B)).
Proof with eauto.
  introv RA RB. gen A.
  lets RB': RB.
  inductions RB; intros;
    try solve [
          applys~ R_ordAll; introv Fr1; clear Fr1];
    try solve [
          applys~ R_ordAll; introv Fr1; clear Fr1;
          [applys ord_rename X | applys~ proper_rename X]; try applys notin_close;
          try rewrite open_typ_wrt_typ_close_typ_wrt_typ;
          eauto].
  - (* spl *)
    rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ _ X)in H.
    applys R_spl...
    Unshelve.
    applys empty. applys empty. applys empty. applys empty. applys empty. applys empty. applys empty.
    applys empty.
Qed.

(* #[local]  *)
Hint Resolve rforall : core.

Lemma lc_types_are_proper : forall A, lc_typ A -> R A.
Proof with auto.
  introv H. induction* H.
  - remember (typefv_typ B). pick fresh X. subst.
    forwards* RB: H1 X.
    forwards* RF: rforall A X RB.
    rewrite (close_typ_wrt_typ_open_typ_wrt_typ _ X) in RF...
Qed.

Ltac proper_ind A := assert (Hlc: lc_typ A) by eauto; assert (r: R A) by applys lc_types_are_proper A Hlc; clear Hlc; induction r.


(******************************************************************************)
(******************************* subtyping ************************************)

Ltac try_algo_sub_constructors :=
  applys S_var +
  applys S_int +
  match goal with
  | H: spl ?B _ _ |- algo_sub _ ?B => applys S_and H
  | H: spl ?B _ _ |- algo_sub _ (t_arrow _ ?B) => applys S_and
  | H: spl ?B _ _ |- algo_sub _ (t_rcd _ ?B) => applys S_and
  | |- algo_sub _ (t_and _ _) => applys S_and
  | |- algo_sub _ (t_arrow _ (t_and _ _)) => applys S_and
  | |- algo_sub _ (t_rcd _ (t_and _ _)) => applys S_and
  | |- algo_sub _ (t_forall _ (t_and _ _)) => applys S_and
  | H: topLike ?B |- algo_sub _ ?B => applys S_top H
  | H: topLike _ |- _ => applys S_top
  | H: algo_sub ?A ?B |- algo_sub (t_and ?A _) ?B => applys S_andl
  | H: algo_sub ?A ?B |- algo_sub (t_and  _ ?A) ?B => applys S_andr
  | |- _ =>  applys S_arr +
             applys S_ref +
             applys S_rcd +
             applys S_forall
  end.

(* #[local]  *)
Hint Extern 2 (algo_sub _ _) => progress try_algo_sub_constructors : core.



(* topLike specification eqv *)
Lemma topLike_super_top: forall A,
    algo_sub t_top A -> topLike A.
Proof with eauto.
  introv H.
  - inductions H...
Qed.



Lemma uniq_dom_binds:forall (A:typ) D F x, uniq(F ++ [(x,A)]++ D) -> x # (F ++ D).
Proof.
  intros. induction F. simpl in H. simpl. inversion H;subst. auto.
    destruct a. simpl in H. inversion H;subst. apply IHF in H2.
      assert(a<>x). eauto. auto.
Qed.
(* 
Lemma TWell_bind_weakening_2 : forall x I J D C F,
    TWell (F ++ (x ~ I) ++ D) C ->
    TWell (F ++ (x ~ J) ++ D) C.
Proof with eauto.
  intros. remember (F ++ (x ~ I) ++ D) as G. gen F. induction* H; intros; subst.
  - analyze_binds H.
    applys TWell_tvar A...
    applys TWell_tvar J...
    applys TWell_tvar A.
    simpl_env.
    rewrite_env (nil ++ x ~ J ++ D).
    applys binds_weaken...
  - apply TWell_forall with (L);intros; eauto...
    forwards*: H1 X ((X, A) :: F).
Qed. *)

Lemma uniq_bind_weakening : forall x (I J:typ) D F,
    uniq (F ++ (x ~ I) ++ D) ->
    uniq (F ++ (x ~ J) ++ D) .
Proof with eauto.
  intros. induction F. simpl. simpl in H. inversion H;subst. auto.
    destruct a. inversion H;subst. apply IHF in H2. simpl. apply uniq_push. auto. auto.
Qed.




Lemma toplike_sub : forall A B,
    topLike A -> algo_sub A B -> topLike B.
Proof with eauto.
  introv TL S.
  induction S; inverts~ TL;try solve[apply topLike_spl_combine with B1 B2; auto; eauto; eauto];eauto.
  -
    forwards h1: IHS2 H3.
    forwards h2: algo_sub_lc S1; auto.
  -
    pick fresh x.
    forwards h1: H1 x; auto.
    forwards h2:IHS1; eauto.
  - 
    forwards h1: algo_sub_lc S; auto.
    apply TL_all with (union L L0); auto. 
Qed.

(* #[export] *) Hint Immediate topLike_spl_combine toplike_sub : core.

(* #[export] *) Hint Extern 0 (algo_sub ?A ?B) =>
match goal with
| H1: topLike ?C, H2: algo_sub ?C B |- _ => applys S_top; [ | | applys toplike_sub H1 H2]
end : core.

Lemma Typ_decidable: forall A B:typ, {A = B}+{~A = B}.
Proof.
  repeat decide equality.
Qed.

Lemma binds_typ_dec: forall x E (A:typ),
 {binds x A E} + {~ binds x A E}.
Proof.
  intros. apply binds_dec. apply Typ_decidable.
Qed.



Lemma open_wrt_A: forall A X Y,t_tvar_f X = A -^ Y -> ((A = t_tvar_b 0 /\ X = Y)\/A = t_tvar_f X).
Proof.
  intros. destruct A;inversion H.
    unfold open_typ_wrt_typ in H. simpl in H.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion H. inversion H;subst. auto.
    inversion H. subst.
    auto.
Qed.

Lemma open_comm: forall A n n0 X Y,
n0 <= n ->
open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A) =
open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A).
Proof.
  intros A. induction A;intros;simpl;auto.
    - (* var_b *)
    simpl. destruct(lt_eq_lt_dec n (S n0)). destruct s. simpl.
      destruct(lt_eq_lt_dec n n1). destruct s.
      simpl. destruct(lt_eq_lt_dec n n0). destruct s. auto. subst.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction. simpl. auto.
      simpl. destruct(lt_eq_lt_dec (n-1) n0). destruct s. auto.
      assert(~n < (S n0)). lia. contradiction. assert(~n < (S n0)). lia. contradiction.
      subst. destruct(lt_eq_lt_dec (S n0) n1). destruct s.
      assert(~n1<=n0). lia. contradiction. assert(~n1<=n0). lia. contradiction.
      simpl. destruct (lt_eq_lt_dec (n0 - 0) n0). destruct s.
      assert(~n0 - 0 < n0). lia. contradiction. auto.
      assert(~n0 < n0 - 0). lia. contradiction.
      simpl. destruct(lt_eq_lt_dec n n1). destruct s.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction.
      destruct(lt_eq_lt_dec (n - 1) n1). destruct s.
      assert(~n1 <= n0). lia. contradiction.
      assert(~n1 <= n0). lia. contradiction.
      simpl. destruct(lt_eq_lt_dec (n - 1) n0). destruct s.
      assert(~(S n0) < n). lia. contradiction. assert(~(S n0) < n). lia. contradiction. auto.
   -  (* arrow *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H0. rewrite H1. auto.
    -  (* and *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H0. rewrite H1. auto.
    -  (* ref *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
      rewrite H0. auto.
   -  (* forall *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) (open_typ_wrt_typ_rec (S (S n)) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec (S n) (t_tvar_f X) (open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) A2))).
      apply IHA2. lia. rewrite H0. rewrite H1. auto.
   - (* rcd *)
     assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
        rewrite H0. auto.
Qed.

Lemma lc_subst: forall A X Y, lc_typ(A -^ X) -> lc_typ(A -^ Y).
Proof.
  intros. apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H0. auto.
Qed.

Lemma lc_subst_2: forall A X Y, lc_typ(A) -> lc_typ(typsubst_typ (t_tvar_f X) Y A).
Proof.
  intros. apply degree_typ_wrt_typ_of_lc_typ in H.
    assert(degree_typ_wrt_typ 0 (typsubst_typ (t_tvar_f X) Y A)).
  apply typsubst_typ_degree_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H0. auto.
Qed.

Lemma subst_spl: forall A B C X Y, spl A B C -> spl (typsubst_typ (t_tvar_f X) Y A) (typsubst_typ (t_tvar_f X) Y B) (typsubst_typ (t_tvar_f X) Y C).
Proof.
  intros. induction H; try solve[simpl; auto].
(*   
  - (* and *)
    simpl. assert(lc_typ(typsubst_typ (t_tvar_f X) Y A)). apply lc_subst_2. auto.
    assert(lc_typ(typsubst_typ (t_tvar_f X) Y B)). apply lc_subst_2. auto.
    auto.
    -(* arrow *)
    simpl. assert(lc_typ(typsubst_typ (t_tvar_f X) Y A)). apply lc_subst_2. auto. auto. *)
    -(* forall *)
    simpl. apply Sp_forall with (Metatheory.union L (Metatheory.singleton Y)). apply lc_subst_2. auto. intros.
      assert(X0 <> Y). auto.
    assert(spl [Y ~~> t_tvar_f X] (B -^ X0) [Y ~~> t_tvar_f X] (C1 -^ X0)
       [Y ~~> t_tvar_f X] (C2 -^ X0)). apply H1. auto.
    assert([Y ~~> t_tvar_f X] (B -^ X0)  = [Y ~~> t_tvar_f X] (B) ^-^  [Y ~~> t_tvar_f X] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Y ~~> t_tvar_f X] (C1 -^ X0)  = [Y ~~> t_tvar_f X] (C1) ^-^  [Y ~~> t_tvar_f X] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Y ~~> t_tvar_f X] (C2 -^ X0)  = [Y ~~> t_tvar_f X] (C2) ^-^  [Y ~~> t_tvar_f X] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H5 in H4. rewrite H6 in H4. rewrite H7 in H4.
    assert([Y ~~> t_tvar_f X] (t_tvar_f X0) = (t_tvar_f X0)).
    apply typsubst_typ_fresh_eq. auto. rewrite H8 in H4. auto.
  (* -
    simpl.  auto.  *)
Qed.

Lemma open_spl: forall A B C X, spl (A -^ X) B C -> exists D1 D2, forall Y, spl (A -^ Y) (D1 -^ Y) (D2 -^ Y).
Proof.
  intros. dependent induction H.
  - (* and *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    exists A1 A2. intros.
    unfold open_typ_wrt_typ. simpl. subst. apply Sp_and. apply lc_subst with X. auto.
    apply lc_subst with X. auto.
    - (* arrow *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    forwards: IHspl H3. destruct H1. destruct H1. exists (t_arrow A1 x0) (t_arrow A1 x1). subst.
    unfold open_typ_wrt_typ. simpl. intros. apply Sp_arrow.
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A1 -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H2. auto. eauto.
    - (* forall *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    subst. pick fresh X0.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f X) A2 -^ X0 = A2 -^ X0 -^ X).
    apply open_comm. auto.
    assert(exists D1 D2 : typ, forall Y : typevar, spl ((A2 -^ X0) -^ Y) (D1 -^ Y) (D2 -^ Y)).
    apply H1 with X0 X. auto. auto. destruct H3. destruct H3.
    exists (t_forall A1 (close_typ_wrt_typ X0 x0)) (t_forall A1 (close_typ_wrt_typ X0 x1)). intros.
    unfold open_typ_wrt_typ. simpl. apply Sp_forall with L.
      apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A1 -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H4. auto. intros.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) A2 -^ X1 = A2 -^ X1 -^ Y).
    apply open_comm. auto. rewrite H5.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) (close_typ_wrt_typ X0 x0) -^ X1 = (close_typ_wrt_typ X0 x0) -^ X1 -^ Y).
    apply open_comm. auto. rewrite H6.
    assert(open_typ_wrt_typ_rec 1 (t_tvar_f Y) (close_typ_wrt_typ X0 x1) -^ X1 = (close_typ_wrt_typ X0 x1) -^ X1 -^ Y).
    apply open_comm. auto. rewrite H7.
    assert(typsubst_typ (t_tvar_f X1) X0 x0 = (close_typ_wrt_typ X0 x0 -^ X1)).
     apply typsubst_typ_spec_rec. rewrite <- H8.
    assert(typsubst_typ (t_tvar_f X1) X0 x1 = (close_typ_wrt_typ X0 x1 -^ X1)).
     apply typsubst_typ_spec_rec. rewrite <- H9.
    assert([X0 ~~> t_tvar_f X1] (A2 -^ X0)  = [X0 ~~> t_tvar_f X1] (A2) ^-^  [X0 ~~> t_tvar_f X1] (t_tvar_f X0)).
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([X0 ~~> t_tvar_f X1] (t_tvar_f X0) = (t_tvar_f X1)). simpl. unfold " x == y ".
      destruct(EqDec_eq_of_X X0 X0). auto. contradiction.
    rewrite H11 in H10. pick fresh Z.
      assert(spl ((A2 -^ X0) -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
    assert(spl ([X0 ~~> t_tvar_f X1]((A2 -^ X0) -^ Z)) ([X0 ~~> t_tvar_f X1](x0 -^ Z)) ([X0 ~~> t_tvar_f X1](x1 -^ Z))).
      apply subst_spl. auto.
    clear H H1 H0 H2 H3 H4 H5 H6 H7 H8 H9 H11 x.
      assert([X0 ~~> t_tvar_f X1] (A2) = A2). apply typsubst_typ_fresh_eq. auto. rewrite H in H10. clear H Fr H12.
    assert([X0 ~~> t_tvar_f X1] ((A2 -^ X0) -^ Z) = [X0 ~~> t_tvar_f X1](A2 -^ X0) ^-^[X0 ~~> t_tvar_f X1] (t_tvar_f Z)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H in H13. rewrite H10 in H13. clear H H10.
    assert([X0 ~~> t_tvar_f X1] (x0 -^ Z) = [X0 ~~> t_tvar_f X1]x0 ^-^[X0 ~~> t_tvar_f X1] (t_tvar_f Z)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([X0 ~~> t_tvar_f X1] (x1 -^ Z) = [X0 ~~> t_tvar_f X1]x1 ^-^[X0 ~~> t_tvar_f X1] (t_tvar_f Z)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H in H13. rewrite H0 in H13. clear H H0.
    assert([X0 ~~> t_tvar_f X1] (t_tvar_f Z) = t_tvar_f Z).
      apply typsubst_typ_fresh_eq. auto. rewrite H in H13. clear H.
    assert(spl ([Z ~~> t_tvar_f Y]((A2 -^ X1) -^ Z)) ([Z ~~> t_tvar_f Y]([X0 ~~> t_tvar_f X1] (x0) -^ Z))
        ([Z ~~> t_tvar_f Y]([X0 ~~> t_tvar_f X1] (x1) -^ Z))).
    apply subst_spl. auto.
    assert([Z ~~> t_tvar_f Y] ((A2 -^ X1) -^ Z) = ([Z ~~> t_tvar_f Y] (A2 -^ X1)) ^-^ ([Z ~~> t_tvar_f Y](t_tvar_f Z))).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x0) -^ Z) = ([Z ~~> t_tvar_f Y] [X0 ~~> t_tvar_f X1] (x0)) ^-^ ([Z ~~> t_tvar_f Y](t_tvar_f Z))).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x1) -^ Z) = ([Z ~~> t_tvar_f Y] [X0 ~~> t_tvar_f X1] (x1)) ^-^ ([Z ~~> t_tvar_f Y](t_tvar_f Z))).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite H0 in H. rewrite H1 in H. rewrite H2 in H. clear H0 H1 H2.
      assert([Z ~~> t_tvar_f Y] (A2 -^ X1) = (A2 -^ X1)).
      apply typsubst_typ_fresh_eq.
      assert(AtomSetImpl.Subset (typefv_typ (A2 -^ X1)) (typefv_typ (t_tvar_f X1)`union`  typefv_typ A2)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(Z `notin` (Metatheory.union [[t_tvar_f X1]] [[A2]])). auto. eauto.
      assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x0)) = ([X0 ~~> t_tvar_f X1] (x0))).
      apply typsubst_typ_fresh_eq. apply typsubst_typ_fresh_mutual. auto. auto.
      assert([Z ~~> t_tvar_f Y] ([X0 ~~> t_tvar_f X1] (x1)) = ([X0 ~~> t_tvar_f X1] (x1))).
      apply typsubst_typ_fresh_eq. apply typsubst_typ_fresh_mutual. auto. auto.
    rewrite H0 in H. rewrite H1 in H. rewrite H2 in H. clear H0 H1 H2.
    assert([Z ~~> t_tvar_f Y] (t_tvar_f Z) = (t_tvar_f Y)). simpl. unfold "==".
    destruct EqDec_eq_of_X. auto. contradiction. rewrite H0 in H. auto.
    - (* rcd *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
  forwards: IHspl H2. destruct H0. destruct H0. subst. exists (t_rcd l0 x0) (t_rcd l0 x1). subst.
  unfold open_typ_wrt_typ. simpl. intros. apply Sp_rcd. eauto.
Qed.

Lemma split_fv: forall X A B C, X `notin` [[A]]-> spl A B C -> X `notin` [[B]] /\X `notin` [[C]].
Proof.
  intros. induction H0;simpl in H;simpl;auto.
  - (* forall *)
    pick fresh X0.
    assert( X `notin` [[C1 -^ X0]] /\ X `notin` [[C2 -^ X0]]). apply H2.
    auto. assert(AtomSetImpl.Subset (typefv_typ (B -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B]])). simpl in H. auto.
    eauto. destruct H3.
      assert(AtomSetImpl.Subset (typefv_typ (C1)) (typefv_typ (C1 -^ X0))).
    apply typefv_typ_open_typ_wrt_typ_lower.
      assert( X `notin` [[C1]]). eauto.
      assert(AtomSetImpl.Subset (typefv_typ (C2)) (typefv_typ (C2 -^ X0))).
    apply typefv_typ_open_typ_wrt_typ_lower.
      assert( X `notin` [[C2]]). eauto.
    simpl in H. simpl. auto.
Qed.


Definition TyEnvMatch {A} (f : typ -> A) (tyenv : TyEnv) : A :=
  match tyenv with
    | TyDis d => f d
    | TermV ty => f ty
  end.


(* Lemma no_effect_subst: forall X E T,
  X `notin` (typefv_typ_range E) ->
  (map (typsubst_typ T X) E) = E.
Proof.
  intros.
  induction E. auto.
    simpl. destruct a.
  forwards: IHE. simpl in H. auto. rewrite H0.
  simpl in H.
  assert([X ~~> T] t = t).
    apply typsubst_typ_fresh_eq. auto. rewrite H1.
  auto.
Qed. *)

Lemma topLike_subst_2: forall X Y A, topLike A -> topLike (typsubst_typ (t_tvar_f Y) X A).
Proof.
  intros. induction H;simpl;auto.
(*   
  -(* andL *)
    assert(lc_typ [X ~~> t_tvar_f Y] B). apply typsubst_typ_lc_typ. auto. auto. eauto with lngen. *)
  -(* andR *)
    assert(lc_typ [X ~~> t_tvar_f Y] A). apply typsubst_typ_lc_typ. auto. auto.
    apply TL_all with (L := union L
    (union (singleton X)
       (union (singleton Y) (union [[A]] [[B]]))));intros; auto.
    forwards*: H1 X0.
    rewrite typsubst_typ_open_typ_wrt_typ_var; eauto. 
Qed.


Lemma topLike_subst_1: forall X Y A, topLike A -> 
 lc_typ Y ->
 topLike (typsubst_typ Y X A).
Proof.
  intros. induction H;simpl;auto.
  -(* andR *)
    assert(lc_typ [X ~~> Y] A). apply typsubst_typ_lc_typ. auto. auto.
    eapply TL_all with (L := union L
    (union (singleton X)
       (union [[Y]] (union [[A]] [[B]]))));intros; auto.
    forwards*: H1 X0.
    rewrite typsubst_typ_open_typ_wrt_typ_var; eauto. 
Qed.

Lemma topLike_rename: forall X Y B,
 X `notin` [[B]]  ->
 Y `notin`  [[B]] -> 
 topLike (open_typ_wrt_typ  B (t_tvar_f X)) ->
 topLike (open_typ_wrt_typ  B (t_tvar_f Y)).
Proof.
  introv nin1 nin2 tl. 
  destruct (X == Y); try solve[subst*].
  rewrite (typsubst_typ_intro X); eauto.
  forwards*: topLike_subst_2 tl.
Qed.



Lemma toplike_decidable : forall A,
    lc_typ A -> topLike A \/ ~topLike A.
Proof with jauto.
  introv lc. 
  inductions lc; eauto; try solve[right; unfold not;intros nt;inverts* nt];
  try solve[left;exists*];
  try solve[inverts IHlc2; eauto];
  try solve[ inverts IHlc1;
  inverts IHlc2; eauto];
  try solve[inverts IHlc; eauto].
  -
    pick fresh X.
    forwards* h1: H0 X.
    inverts h1 as h1 h2.
    +
      left.
      apply TL_all with (L := (union (singleton X) (union [[A]] [[B]]))) ;
      intros; eauto.
      forwards*: topLike_rename X0 h1.
    +
      right; unfold not;intros nt;inverts* nt.
      apply h1.
      pick fresh Y.
      forwards*: H4.
      forwards*: topLike_rename X H1.
Qed.

(* #[export] *) Hint Extern 3 (algo_sub t_top _) => applys topLike_super_top : core.
(* #[export] *) Hint Immediate topLike_super_top toplike_sub : core.
(* #[export] *) Hint Extern 2 (topLike ?C) =>
match goal with
| H: algo_sub t_top C |- _ => applys topLike_super_top; exact H
| H: topLike (t_arrow _ ?A), HS: algo_sub ?A ?B |- topLike (t_arrow _ ?B) =>
  inverts H; applys TL_arr; try applys toplike_sub HS
end : core.


(* 

Lemma TW_not_in: forall D A X, TWell D A -> X `notin` (dom D) -> X `notin` [[A]].
Proof.
  intros. induction H;auto.
    assert({X=X0}+{~X=X0}). auto.
    destruct H1. subst.
    forwards: binds_dom_contradiction H H0. contradiction.
    auto.
    simpl. pick fresh Y.
    assert(X `notin` [[B -^ Y]]). auto.
    assert(AtomSetImpl.Subset (typefv_typ B) (typefv_typ (B -^ Y))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto.
Qed. *)

(************************ msub <-> algo_sub ***********************************)


(* generalize S_top *)
(* Lemma sub_top : forall A B,
    lc_typ B -> topLike A -> algo_sub B A.
Proof with eauto.
  introv LC TL.
  proper_ind A; try solve [inverts TL; applys* S_top]...
Qed. *)


(* generalize S_andl *)
Lemma sub_l_andl : forall A B C,
    lc_typ B -> algo_sub A C -> algo_sub (t_and A B) C.
Proof with eauto.
  introv lc s. induction s; try solve [applys S_andl; eauto];
  try solve[forwards* h1: algo_sub_lc s2];
  try solve[forwards* h1: algo_sub_lc s1];
  try solve[forwards* h1: algo_sub_lc IHs]...
Qed.

(* generalize S_andr *)
Lemma sub_l_andr : forall A B C,
    lc_typ A ->  algo_sub B C -> algo_sub (t_and A B) C.
Proof with eauto.
introv lc s. induction s; try solve [applys S_andr; eauto];
try solve[forwards* h1: algo_sub_lc s2];
try solve[forwards* h1: algo_sub_lc s1];
try solve[forwards* h1: algo_sub_lc IHs]...
Qed.

(* generalize S_arr *)
Lemma sub_fun : forall A B C D,
    algo_sub B D -> algo_sub C A -> algo_sub (t_arrow A B) (t_arrow C D).
Proof with eauto.
  introv s. induction s; intros; try solve [applys S_arr; eauto]; 
  try solve[forwards* h1: algo_sub_lc s2];
  try solve[forwards* h1: algo_sub_lc s1];
  try solve[forwards* h1: algo_sub_lc IHs];
  try solve[forwards*: algo_sub_lc]...
Qed.


Lemma sub_inversion_arrow : forall A B C D,
    algo_sub (t_arrow A B) (t_arrow C D) -> (algo_sub C A /\ algo_sub B D).
Proof with (simpl in *; solve_false; split_unify; try eassumption; eauto 3).
  introv s.
  inductions s; eauto.
  inverts H as h1.
  forwards* h2:IHs1.
  forwards* h3:IHs2.
Qed.


Lemma sub_inversion_rcd : forall A B C D,
    algo_sub (t_rcd A B) (t_rcd C D) -> (algo_sub B D).
Proof with (simpl in *; solve_false; split_unify; try eassumption; eauto 3).
  introv s.
  inductions s; eauto.
  inverts H as h1.
  forwards* h2:IHs1.
Qed.


Lemma sub_rcd : forall A B l,
    algo_sub A B -> algo_sub (t_rcd l A) (t_rcd l B).
Proof with eauto.
  introv H. induction H; try solve [forwards* h1: algo_sub_lc H;applys S_rcd; eauto];
  try solve [forwards* h1: algo_sub_lc H1;applys S_rcd; eauto]...
  try solve [forwards* h1: algo_sub_lc H0;applys S_rcd; eauto]...
  try solve [forwards* h1: algo_sub_lc H0;applys S_rcd; eauto]...
Qed.

(* #[export]  *)
Hint Resolve sub_rcd : core.



Lemma algo_subst_2: forall X Y A B, algo_sub A B -> algo_sub (typsubst_typ (t_tvar_f Y) X A)  (typsubst_typ (t_tvar_f Y) X B).
Proof.
  intros. induction H;simpl;auto.
  (* -
    forwards*: lc_subst_2 H. *)
  -(* andL *)
    assert(lc_typ [X ~~> t_tvar_f Y] B). apply typsubst_typ_lc_typ. auto. auto. eauto with lngen.
(*     
  -(* andR *)
    assert(lc_typ [X ~~> t_tvar_f Y] A). apply typsubst_typ_lc_typ. auto. auto. eauto with lngen.
  - 
    forwards*: typsubst_typ_split_typ H. *)
  -
    apply S_forall with (union L (singleton X));intros; eauto.
    forwards*: H X0.
    rewrite typsubst_typ_open_typ_wrt_typ_var; eauto.
    forwards*: H2 X0.
    rewrite typsubst_typ_open_typ_wrt_typ_var; eauto.
    rewrite typsubst_typ_open_typ_wrt_typ_var; eauto.
  -
    destruct(X0 == X); subst*.
Qed.

Lemma algo_sub_subst:forall X Y A B ,
 X `notin`  (Metatheory.union [[A]] [[B]]) ->
 algo_sub (A -^ X) (B -^ X) ->
 algo_sub (A -^ Y) (B -^ Y).
Proof.
  introv nin1 tl. 
  destruct (X == Y); try solve[subst*].
  rewrite 1 (typsubst_typ_intro X); eauto.
  assert((B -^ Y) = [X ~~> t_tvar_f Y] (B -^ X)) as h1.
  rewrite (typsubst_typ_intro X); eauto.
  rewrite h1.
  forwards*: algo_subst_2 X Y tl.
Qed.




(* generalize S_arr *)

Lemma algosub_forall_exists_1 : forall X A1 A2 B1 B2,
    algo_sub A2 B2
    -> algo_sub  B1 A1
    -> algo_sub  (t_forall A1 (close_typ_wrt_typ X A2)) (t_forall B1 (close_typ_wrt_typ X B2)).
Proof with auto.
  introv s. lets s': s.
  dependent induction s; intros;
    try solve [
          applys~ S_forall; intros Y FrY;
          repeat rewrite <- typsubst_typ_spec;
          try applys typsubst_typ_ord_typ;
          try applys typsubst_typ_split_typ;
          eauto].
(*           
  -  (* toplike *)
     unfold close_typ_wrt_typ. 
     apply S_forall with (union (singleton X)
     (union [[A1]]
        (union [[B1]]
           [[A]]))). intros. rewrite <- typsubst_typ_spec.
      applys typsubst_typ_ord_typ. auto. auto. intros.
    assert(close_typ_wrt_typ_rec 0 X A -^ X = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H2 in s'.
    assert(close_typ_wrt_typ_rec 0 X t_top -^ X = t_top). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in s'.
    apply algo_sub_subst with X. auto. auto.  *)
  - (* ref *)
    apply S_forall with ([[A1]]); intros; auto.
    apply ord_rename with X; auto.  rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    forwards*: algo_sub_lc s1.
    apply algo_sub_subst with X. auto. 
    rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto.
  - (* andl  *)
    unfold close_typ_wrt_typ. simpl. apply S_forall with ([[A]]). intros.
    assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in H0. apply ord_rename with X. auto. auto. auto.
    intros. assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in s'.
    apply algo_sub_subst with X. auto. 
      unfold open_typ_wrt_typ. simpl.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. auto.
  - (* andr *)
    unfold close_typ_wrt_typ. simpl. apply S_forall with ([[A]]). intros.
    assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in H0. apply ord_rename with X. auto. auto. auto.
    intros. assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H3 in s'.
    apply algo_sub_subst with X. auto. 
      unfold open_typ_wrt_typ. simpl.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. auto.
  - (* arrow *) 
    unfold close_typ_wrt_typ. simpl. apply S_forall with ([[A]]); intros; auto.
    assert(close_typ_wrt_typ_rec 0 X D -^ X = D). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H2 in H. apply ord_rename with X. auto. unfold open_typ_wrt_typ. simpl.
        rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. forwards: algo_sub_lc s1. destruct H3. auto.  
        apply algo_sub_subst with X. auto. 
      unfold open_typ_wrt_typ. simpl. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec. rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec.
      auto.
  - (* spl *) 
  assert(algo_sub (t_forall A1 (close_typ_wrt_typ X A))
  (t_forall B1 (close_typ_wrt_typ X B))). auto.
    assert(algo_sub (t_forall A1 (close_typ_wrt_typ X A))
  (t_forall B1 (close_typ_wrt_typ X C))). auto.
    assert(spl (t_forall B1 (close_typ_wrt_typ X D)) (t_forall B1 (close_typ_wrt_typ X B)) (t_forall B1 (close_typ_wrt_typ X C))).
    apply Sp_forall with {}. forwards*:algo_sub_lc H0.  
    intros.
    assert(close_typ_wrt_typ_rec 0 X D -^ X = D). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H4 in H.
    assert(close_typ_wrt_typ_rec 0 X B -^ X = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H5 in H.
    assert(close_typ_wrt_typ_rec 0 X C -^ X = C). apply open_typ_wrt_typ_close_typ_wrt_typ.
      rewrite <- H6 in H.
    apply split_rename with X. auto. auto. eauto.
  - (* forall *)
    apply S_forall with {}; intros; auto.
    apply ord_rename with X. auto. 
    rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    forwards* lc1:algo_sub_lc s. 
    apply algo_sub_subst with X. auto. 
    rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto.
  - (* x *)
    apply S_forall with {}; intros; auto. 
    unfold close_typ_wrt_typ. simpl.
    unfold "==". 
    destruct(EqDec_eq_of_X X X0). subst. auto. auto.  
    unfold close_typ_wrt_typ. simpl.
    unfold "==". destruct(EqDec_eq_of_X X X0). subst.
    unfold open_typ_wrt_typ. simpl. 
    apply S_var. auto.
  -
    apply S_forall with {}; intros; auto.
    apply ord_rename with X. auto. 
    rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    forwards* lc1:algo_sub_lc s. 
    apply algo_sub_subst with X. auto. 
    rewrite open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite open_typ_wrt_typ_close_typ_wrt_typ. auto.
    Unshelve.   applys empty.
    applys empty.
    applys empty.
Qed.


(* alternative formulation of algosub_forall_exists_1 *)
Lemma algosub_forall_exists_2 : forall X A1 A2 B1 B2,
    X \notin ([[A2]] \u [[B2]]) ->
    algo_sub  (A2-^X) (B2-^X) ->
    algo_sub  B1 A1 ->
    algo_sub  (t_forall A1 A2) (t_forall B1 B2).
Proof with eauto.
  introv Fr s2 s1.
  forwards*: algosub_forall_exists_1 X s2 s1.
  rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.


(* generalize S_arr *)
Lemma sub_forall : forall L A1 A2 B1 B2,
    ( forall X , X \notin  L  -> algo_sub ( open_typ_wrt_typ A2 (t_tvar_f X) )
                                           ( open_typ_wrt_typ B2 (t_tvar_f X) ))
    -> algo_sub B1 A1
    -> algo_sub (t_forall A1 A2) (t_forall B1 B2).
Proof with eauto.
  introv s2 s1.
  pick fresh X.
  forwards* Hs2: s2 X.
  pick_fresh_applys_and_instantiate_cofinites algosub_forall_exists_2.
Qed.


(* sub_top *)

(* #[export] *)
 Hint Immediate  algosub_forall_exists_2 : core.
(* #[export] *)
 Hint Resolve sub_fun sub_forall algosub_forall_exists_1 : core.


(* this hint has higher priority than try_algo_sub_constructors *)
(* #[export] *) Hint Extern 1 (algo_sub _ _) =>
match goal with
  | H: algo_sub ?A ?B |- algo_sub (t_and ?A _) ?B => applys sub_l_andl
  | H: algo_sub ?A ?B |- algo_sub (t_and  _ ?A) ?B => applys sub_l_andr
  | |- algo_sub (t_and ?B _) ?B => applys sub_l_andl
  | |- algo_sub (t_and _ ?B) ?B => applys sub_l_andr
end : core.


(*********************** algorithmic subtyping relexivity *********************)
Lemma sub_reflexivity : forall A,
    lc_typ A -> algo_sub A A.
Proof.
  introv Lc. inductions Lc;auto.
  apply sub_forall with ([[A]]); intros; eauto.


Qed.

(* #[export] *) Hint Extern 1 (algo_sub _ _) =>
match goal with
  | |- algo_sub ?A ?A => applys sub_reflexivity
end : core.

(************************ around split and subtyping **************************)
Lemma spl_sub_l : forall A B C,
    spl A B C -> algo_sub A B.
Proof.
  introv H. inductions H;intros;auto.
  apply sub_forall with (L); intros; eauto. 
Qed.


Lemma spl_sub_r : forall A B C,
    spl A B C -> algo_sub A C.
Proof.
  introv H. induction H;intros;auto.
  apply sub_forall with L; intros; eauto. 
Qed.

(* #[export] *) Hint Immediate spl_sub_l spl_sub_r : core.


(* splitting does not lose or add information to a type *)
Lemma split_sub: forall A B C,
    spl A B C -> algo_sub A (t_and B C) /\ algo_sub (t_and B C) A.
Proof.
  intros A B C H.
  split.
  - lets~: spl_sub_l H. lets~: spl_sub_r H. 
  - inductions H;intros; auto.
      assert(spl (t_forall A B) (t_forall A C1) (t_forall A C2)). eauto.
      apply S_and with (t_forall A C1) (t_forall A C2). auto. auto. auto.
Qed.



(********************** some subtyping inversion lemmas ***********************)
(* inversion on left split *)
Lemma sub_inversion_split_l : forall A B A1 A2,
    algo_sub  A B -> spl A A1 A2 -> ord B -> algo_sub A1 B \/ algo_sub  A2 B.
Proof with auto.
  introv H. gen A1 A2.
  induction H; intros; split_unify;
  try solve[forwards* h1: split_ord_false H;inverts h1]...
  - (* arrow *)
    forwards*: IHalgo_sub2. intuition eauto.
  - (* forall *)
    pick fresh X. forwards: H10 X. solve_notin.
    forwards [?|?]: H2 X H3. solve_notin. inverts H4...
    + left. applys* algosub_forall_exists_2. solve_notin. 
    + right. applys* algosub_forall_exists_2. solve_notin.
    - (* record *)
    forwards*: IHalgo_sub. intuition eauto.
Qed.


(* inversion on right split *)
Lemma sub_r_spl_l : forall A B B1 B2,
    spl B B1 B2 -> algo_sub A B -> algo_sub A B1.
Proof.
  introv Hspl Hsub.
  inverts Hsub; split_unify;
  try solve[forwards* h1: split_ord_false Hspl;inverts h1];
  try solve[forwards* h1: split_ord_false H;inverts h1].
  pick fresh x.
  forwards* h1: H x.
  forwards* h2:H7 x.
  forwards* h3: split_ord_false h1.
  inverts h3.
Qed.

Lemma sub_r_spl_r : forall A B B1 B2,
    spl B B1 B2 -> algo_sub A B -> algo_sub A B2.
Proof.
  introv Hspl Hsub.
  inverts Hsub; split_unify;
  try solve[forwards* h1: split_ord_false Hspl;inverts h1];
  try solve[forwards* h1: split_ord_false H;inverts h1].
  pick fresh x.
  forwards* h1: H x.
  forwards* h2:H7 x.
  forwards* h3: split_ord_false h1.
  inverts h3.
Qed.


Lemma sub_inversion_split_r : forall A B B1 B2,
    algo_sub A B -> spl B B1 B2 -> algo_sub A B1 /\ algo_sub A B2.
Proof.
  introv Hsub Hspl. gen B1 B2.
  inductions Hsub; intros; split_unify;
  try solve[forwards* h1: split_ord_false Hspl; inverts h1];
  try solve[
    forwards* h1: split_ord_false H5; inverts h1
  ].
  - pick fresh x.
  forwards* h1: H x.
  forwards* h2: H7.
  forwards* h3: split_ord_false h2.
  inverts h3.
  -
  forwards* h1: IHHsub H4.
Qed.

(* #[export] *)
 Hint Immediate sub_r_spl_l sub_r_spl_r : core.




(* we do not need type A B C to be locally closed because subtyping relation could imply which is shown in `algo_sub_lc`. *)
Lemma sub_transitivity : forall A B C,
    algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof with ( split_unify; eauto 4).
  introv S1 S2.
  assert (Lc: lc_typ B).
  forwards*: algo_sub_lc S1.
  assert (r: R B) by applys* (lc_types_are_proper B).
  clear Lc. gen A C.
  induction r; (* <- proper_ind B *)
    intros; try solve [inductions S2; auto].
  - inductions S2... 
    forwards h1:algo_sub_lc S1. destruct h1.  auto.
  (* -
     forwards h1:algo_sub_lc S1. destruct h1.
     forwards h2: toplike_sub S2; auto.  *)
  -
    inductions S2...
    forwards h1:algo_sub_lc S1. destruct h1.
    auto.
  -
    inductions S2...
    forwards h1:algo_sub_lc S1. destruct h1.
    auto.
  - (* arrow *)
    inductions S2... forwards:algo_sub_lc S1. destruct H1. auto.
    clear IHS2_1 IHS2_2.
    inductions S1; auto. 
    (* +
    inversion H2;subst. 
    forwards:toplike_sub H7 S2_2.
      assert(topLike (t_arrow B0 D)); auto. 
      forwards* h1:algo_sub_lc S2_1. *)
    +
    forwards*: IHS1 B.
    +
    forwards*: IHS1 B.
    +
    forwards:algo_sub_lc S2_1.
    forwards:algo_sub_lc S2_2.
    forwards h1: split_ord_false H1; auto. inverts h1.
  -
    inductions S2...
    forwards* h1:algo_sub_lc S1.
    clear IHS2_1 IHS2_2.
    inductions S1; auto.
    (* +
    forwards:toplike_sub S2_1; auto. *)
    +
    forwards*: IHS1 A.
    +
    forwards*: IHS1 A.
    +
    forwards:algo_sub_lc S2_1.
    forwards h1: split_ord_false H; auto. inverts h1.
  - (* forall *)
    inductions S2... 
    forwards:algo_sub_lc S1; eauto. 
    clear H4 IHS2.
    inductions S1; auto.
    (* +
    inverts H5.
    assert(topLike (t_forall B1 B2)) as h1.
    apply TL_all with (union L1 L0); intros; auto.
    forwards* h2: algo_sub_lc S2.
    forwards* h3: H10 X.
    forwards* h4: H3 X.
    eauto. *)
    +
    forwards*: IHS1.
    +
    forwards*: IHS1.
    +
    forwards h1: split_ord_false H4; auto.
    inverts h1.
    +
    pick_fresh_applys_and_instantiate_cofinites algosub_forall_exists_2.
    apply H1.  auto. auto. 
  -
    assert (Lc: lc_typ C0) by eauto with LcHd.
    assert (r: R C0) by applys* (lc_types_are_proper C0).
    clear Lc. gen A B.
    induction r; (* <- proper_ind C0, the type at the end *)
      introv S1 S2 Hspl HRb IH;
      try solve [ (* if C0 is an ordinary type *)
            forwards (?&?): sub_inversion_split_r S1 Hspl;
            forwards [?|?]: sub_inversion_split_l S2 Hspl;
            [eauto | applys~ IH | applys~ IHr2 ] ].
    + (* splittable type *)
      forwards (?&?): sub_inversion_split_r S2 H.
      applys S_and H. applys~ IHr1 S1 Hspl. applys~ IHr3 S1 Hspl.
  - (* rcd *)
      inductions S2... forwards:algo_sub_lc S1. destruct H1. auto.
    clear IHS2.
    inductions S1; auto. 
    (* +
    inversion H2;subst. 
    forwards:toplike_sub H7 S2_2.
      assert(topLike (t_arrow B0 D)); auto. 
      forwards* h1:algo_sub_lc S2_1. *)
    +
    forwards*: IHS1 B.
    +
    forwards*: IHS1 B.
    +
    forwards:algo_sub_lc S1_1.
    forwards:algo_sub_lc S2.
    forwards h1: split_ord_false H1; auto. inverts h1.
Qed.

(* #[export] *)
 Hint Immediate sub_transitivity : core.




 (* #[export] *)
 Hint Extern 1 (algo_sub ?A ?B) =>
 match goal with
 | |- algo_sub (t_and B _) B => applys sub_l_andl
 | |- algo_sub (t_and _ B) B => applys sub_l_andr
 | |- algo_sub A A  => applys sub_reflexivity
 | H: algo_sub A ?C |- _  => applys sub_transitivity H
 end : SubHd.
 
 Ltac auto_sub :=
   try (trivial ;
        match goal with
        | [ |- algo_sub ?A ?A ] => (applys sub_reflexivity)
        | [ |- algo_sub (t_and ?A1 _) ?A1 ] => (applys sub_l_andl; eauto with LcHd)
        | [ |- algo_sub (t_and _ ?A2) ?A2 ] => (applys sub_l_andr; eauto with LcHd)
        | [ H : algo_sub ?A (t_and ?A1 _) |- algo_sub ?A ?A1 ] => (applys sub_transitivity H; auto_sub)
        | [ H : algo_sub ?A (t_and _ ?A2) |- algo_sub ?A ?A2 ] => (applys sub_transitivity H; auto_sub)
        | [ |- algo_sub (t_and ?C ?D) (t_and ?A ?B) ] => (eapply S_and; try apply Sp_and)
        | [ |- algo_sub (t_and (t_arrow ?A ?B) (t_arrow ?A ?C)) (t_arrow ?A (t_and ?B ?C)) ] => (eapply S_and)
        | [ H1: algo_sub ?A ?B, H2: algo_sub ?B ?C |- algo_sub ?A ?C ] =>
          (forwards: sub_transitivity H1 H2; auto)
        (* | [ H: topLike ?A |- algo_sub _ ?A ] =>
          (applys sub_top H; auto) *)
        (* | [ H: algo_sub t_top ?A |- algo_sub _ ?A ] =>
          (apply topLike_super_top in H; apply sub_top; auto) *)
        | [ H: topLike ?A |- algo_sub _ (t_arrow _ ?A) ] =>
          (apply TL_arr in H; apply S_top; auto)
 
        | [ H: spl ?A _ _ |- algo_sub _ ?A ] => (applys S_and H)
 
        | [ H1: spl ?A ?B ?C, H2: ord ?D, H3: algo_sub ?A ?D |- _ ] => (
            forwards [?|?]: sub_inversion_split_l H1 H2 H3;
            clear H3)
        | [ H1: spl ?A ?B ?C |- _ ] => (
            forwards : split_sub H1;
            forwards : spl_sub_l H1;
            forwards : spl_sub_r H1;
            clear H1)
        | [ |- algo_sub (t_arrow ?A ?B) (t_arrow ?C ?D) ] => apply sub_fun
        | [ H1: algo_sub ?A ?B |- algo_sub ?A ?C ] =>
          assert ( algo_sub B C ) by auto
        end).





