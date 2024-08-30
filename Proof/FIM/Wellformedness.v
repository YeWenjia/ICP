Require Import LibTactics.
Require Export Infrastructure.


(******************************************************************************)
(* WFTypformedness *)

(* some hypothesis that cannot be true *)
(* #[export] *)
 Hint Extern 1 =>
match goal with
| H: TWell _ (t_tvar_b _) |- _ => inverts H
| H:  _ (t_tvar_b _) |- _ => inverts H
end : FalseHd.


(* TWell: type *)
Lemma TWell_lc_typ: forall D A,
    TWell D A -> lc_typ A.
Proof.
  introv H. induction H; eauto with lngen.
Qed.

(* #[export] *) Hint Immediate TWell_lc_typ: core.

Lemma Well_lc_typ: forall D A,
    WFTyp D A -> lc_typ A.
Proof.
  introv H. induction H; eauto with lngen.
Qed.

(* #[export] *) Hint Immediate Well_lc_typ: core.




(* TCWell: type context *)
Lemma WFEnv_uniq: forall D,
    WFEnv D -> uniq D.
Proof.
  intros. inductions H; auto. 
Qed.


(* #[export] *) 
Hint Immediate WFEnv_uniq : core.



(* 


Lemma TWell_in : forall X A D,
    In (X, A) D -> TWell D (t_tvar_f X).
Proof.
  introv H.
  induction D; inverts* H.
  intuition eauto.
Qed.


Lemma Well_in : forall X A D,
    In (X, A) D -> WFTyp D (t_tvar_f X).
Proof.
  introv H.
  induction D; inverts* H.
  intuition eauto.
Qed.

#[local] Hint Resolve TWell_in Well_in : core.



(* it helps when the type in the goal is a subterm of the type in the hypothesis *)
Ltac inverts_all_TWell :=
  repeat match goal with
         | H: TWell _ (t_ref _ ) |- _ => inverts H
         | H: TWell _ (t_and _ _) |- _ => inverts H
         | H: TWell _ (t_arrow _ _) |- _ => inverts H
         | H: TWell _ (t_forall _ _) |- _ => inverts H
         | H: WFTyp _ (t_ref _) |- _ => inverts H
         | H: WFTyp _ (t_and _ _) |- _ => inverts H
         | H: WFTyp _ (t_arrow _ _) |- _ => inverts H
         | H: WFTyp _ (t_forall _ _) |- _ => inverts H
         end.

(* it is possible for the context in H and goal to mismatch *)
Ltac inverts_for_TWell A :=
  repeat match goal with
         | H: TWell _ ?B |- _ => match B with
                                 | A => exact H
                                 | context [ A ] => inverts H
                                 end
         end.

(* #[export] *) Hint Extern 1 (TWell _ ?A ) =>
destruct_conj; progress inverts_for_TWell A : core.
(* #[export] *) Hint Extern 1 (WFTyp _ ?A ) =>
destruct_conj; progress inverts_for_TWell A : core.


Lemma CWell_TWell: forall G x A,
    TCWell G -> binds x A G -> TWell G A.
Proof.
  introv HG H.
  inductions HG.
  -
  inverts H.
  -
  destruct H1.
  injection H1.
  intros eq1 eq2; subst*.
  +
  rewrite_env (nil++G) in H.
  forwards: TWell_weakening [(x, A)] H.
  simpl_env in *; auto.
  +
  assert(binds x A G).
  inductions HG; eauto.
  forwards: IHHG H2.
  rewrite_env (nil++G) in H3.
  forwards: TWell_weakening [(x0, A0)] H3.
  simpl_env in *; auto.
Qed.






(* TCWell: type context *)
Lemma TCWell_uniq: forall D,
    TCWell D -> uniq D.
Proof.
  intros. induction H. auto. auto.
Qed.


Lemma CWell_uniq: forall D,
    CWell D -> uniq D.
Proof.
  intros. induction H. auto. auto.
Qed.


(* #[export] *) 
Hint Immediate TCWell_uniq CWell_uniq: core.


Lemma TCWell_weakening: forall E D x T,
    x # (E ++ D) ->
    TWell D T ->
    TCWell (E ++ D) ->
    TCWell (E ++ [(x, T)] ++ D).
Proof.
  intros. induction* E; intros; simpl_env.
  - constructor*.
  - destruct a. constructor*.
    + inverts* H1. forwards ~: IHE.
    + inverts* H1. apply~ TWell_weakening.
    + inverts* H1. apply uniq_push.
      apply uniq_insert_mid. inversion H7;subst. auto.
      unfold "#" in H. simpl in H. rewrite dom_app in H.
      unfold not. intros. assert(x `in` add a (union (dom E) (dom D))). auto.
      auto.
      unfold "#" in H. simpl in H. rewrite dom_app in H.
      unfold not. intros. assert(x `in` add a (union (dom E) (dom D))). auto.
      auto.
      unfold "#". inversion H7;subst. rewrite dom_app. rewrite dom_app. simpl.
      unfold "#" in H8. rewrite dom_app in H8.
      unfold "#" in H. rewrite dom_app in H. simpl in H.
      assert(x = a\/~x = a). eauto. destruct H1;subst.
      assert(a `in` union (add a (dom E)) (dom D)). auto. contradiction.
      assert(a `notin` (add x empty)). eauto.
      assert(a `notin` union (dom E) (dom D)). auto.
      assert(a `notin` union (dom E) (union (add x empty) (dom D))). auto. auto.
Qed.



(* #[export] *) Hint Immediate TCWell_weakening : core.


Lemma TCWell_TWell: forall D x A,
    TCWell D -> binds x A D -> TWell D A.
Proof.
  introv Hw Hb. induction Hw; induction Hb. injects H1.
  - rewrite_env (nil ++ [(x, A)] ++ G).
    apply TWell_weakening. apply H.
  - apply IHHw in H1.
    rewrite_env (nil ++ [(x0, A0)] ++ G).
    apply TWell_weakening. apply H1.
Qed.


(* it helps when A is bound in D *)
Ltac solve_TWell_by_TCWell :=
  match goal with
  | H: CWell ?D |- TWell ?D ?A => applys TCWell_TWell H
  end.

(* #[export] *)
 Hint Extern 1 (TWell _) => solve_TWell_by_TCWell : core.



Lemma TCWell_cons_TWell: forall D x A,
    TCWell ((x, A) :: D) -> TWell D A.
Proof.
  introv H. inverts* H.
Qed.

Lemma TCWell_inv: forall D x A,
    TCWell ((x, A) :: D) -> TCWell D.
Proof.
  introv H. inverts* H.
Qed.


Lemma CWell_cons_Well: forall D x A,
    CWell ((x, A) :: D) -> WFTyp D A.
Proof.
  introv H. inverts* H.
Qed.


Lemma CWell_inv: forall D x A,
    CWell ((x, A) :: D) -> CWell D.
Proof.
  introv H. inverts* H.
Qed.


(* #[export] *) Hint Immediate TCWell_inv CWell_inv: core.


Lemma disjoint_weakening: forall y X D E A B,
    TWell D X ->
    y # (E ++ D) ->
    disjoint (E ++ D) A B ->
    disjoint (E ++ [(y, X)] ++ D) A B.
Proof.
  intros. remember (E ++ D). gen E.
  induction H1; eauto; intros; subst;
    try solve [eauto using TWell_weakening].
  - 
    (* pick fresh xx and apply D_forall. *)
    apply D_forall with (L := union L
    (union (singleton y)
       (union (dom D)
          (union (dom E)
             (union [[X]]
                (union [[A1]]
                   (union [[A2]]
                      (union [[B1]]
                         (union [[B2]]
                            (union (dom D)
                               (union (dom E)
                                  (union (typefv_typ_range D)
                                     (typefv_typ_range E)))))))))))));intros; eauto.
    forwards*: TWell_weakening H1.
    forwards*: TWell_weakening H2.
    forwards*: H4 X0 ((X0, t_and A1 A2) :: E). 
    solve_notin.
Qed.


(* #[export] *) Hint Immediate disjoint_weakening : core.

Lemma WFTyp_TWell: forall G A,
 WFTyp G A ->
 TWell G A.
Proof.
  introv WFTyp.
  inductions WFTyp; eauto.
Qed.


Lemma CWell_CTWell: forall G,
 CWell G ->
 TCWell G.
Proof.
  introv WFTyp.
  inductions WFTyp; eauto.
  forwards*: WFTyp_TWell H.
Qed.

(* #[export] *) Hint Immediate WFTyp_TWell CWell_CTWell: core.




Lemma Well_weakening : forall T D y X F,
    WFTyp (F ++ D) T ->
    WFTyp D X ->
    y # (F ++ D) ->
    WFTyp (F ++ [(y, X)] ++ D) T.
Proof.
  introv H. remember (F ++ D). gen F.
  induction* H; introv h1 h2 Heq; subst*.
  -
    forwards*: WFTyp_TWell h2.
  -
  apply w_forall with (L := union L
  (union (singleton y)
     (union (dom D)
        (union (dom F)
           (union [[X]]
              (union [[A]]
                 (union [[B]]
                    (union (dom D)
                       (union (dom F)
                          (union 
                             (typefv_typ_range D)
                             (typefv_typ_range F)))))))))));intros; eauto. 
  forwards*: TWell_weakening H.
  rewrite app_comm_cons.
  forwards*: H1 h2.
  simpl_env; auto.
  eauto.
Qed.



Lemma CWell_weakening: forall E D x T,
    x # (E ++ D) ->
    WFTyp D T ->
    CWell (E ++ D) ->
    CWell (E ++ [(x, T)] ++ D).
Proof.
  intros. induction* E; intros; simpl_env.
  - constructor*.
  - destruct a. constructor*.
    + inverts* H1. forwards ~: IHE.
    + inverts* H1. 
      apply~ Well_weakening.
    + inverts* H1. apply uniq_push.
      apply uniq_insert_mid. inversion H7;subst. auto.
      unfold "#" in H. simpl in H. rewrite dom_app in H.
      unfold not. intros. assert(x `in` add a (union (dom E) (dom D))). auto.
      auto.
      unfold "#" in H. simpl in H. rewrite dom_app in H.
      unfold not. intros. assert(x `in` add a (union (dom E) (dom D))). auto.
      auto.
      unfold "#". inversion H7;subst. rewrite dom_app. rewrite dom_app. simpl.
      unfold "#" in H8. rewrite dom_app in H8.
      unfold "#" in H. rewrite dom_app in H. simpl in H.
      assert(x = a\/~x = a). eauto. destruct H1;subst.
      assert(a `in` union (add a (dom E)) (dom D)). auto. contradiction.
      assert(a `notin` (add x empty)). eauto.
      assert(a `notin` union (dom E) (dom D)). auto.
      assert(a `notin` union (dom E) (union (add x empty) (dom D))). auto. auto.
Qed.


(* #[export] *) Hint Immediate Well_weakening CWell_weakening:core.



Lemma CWell_Well: forall G x A,
    CWell G -> binds x A G -> WFTyp G A.
Proof.
  introv HG H.
  inductions HG.
  -
  inverts H.
  -
  destruct H1.
  injection H1.
  intros eq1 eq2; subst*.
  +
  lets H':H.
  rewrite_env (nil++G) in H.
  inverts H0.
  forwards: Well_weakening H H'.
  simpl_env in *; auto.
  simpl_env; eauto.
  +
  assert(binds x A G).
  inductions HG; eauto.
  forwards: IHHG H2.
  lets H3':H3.
  rewrite_env (nil++G) in H3.
  forwards: Well_weakening H3 H.
  inverts* H0.
  simpl_env in *; auto.
Qed.


(* typing *)



Lemma Typing_weakening_1: forall E D y X P e dir A,
    Typing P (E ++ D) e dir A ->
    WFTyp D X ->
    y # (E ++ D) ->
    Typing P (E ++ [(y, X)] ++ D) e dir A.
Proof with eauto using CWell_weakening, Well_weakening.
  intros. remember (E ++ D). gen E.
  induction H; intros; subst; try solve [
                                    constructor*;
                                    apply~ CWell_weakening;
                                    solve_uniq ]; eauto.
  - pick fresh x and apply Typ_abs ...
    forwards*: H2 ((x, A) :: E).
    solve_notin.
  -
    forwards*: disjoint_weakening X H3.
  - pick fresh x and apply Typ_tabs...
    forwards*: H2 x ((x, A) :: E). solve_notin.
    forwards*: TWell_weakening H3.
  -
    forwards*: disjoint_weakening X H4. 
Qed.


Lemma Typing_CWell: forall D G e dir A,
    Typing D G e dir A -> CWell G.
Proof.
  introv H. induction* H; pick_fresh x.
  - forwards*: H0 x.
  - forwards*: H0 x.
Qed.

Lemma Typing_TCWell: forall D G e dir A,
    Typing D G e dir A -> TCWell G.
Proof.
  introv H. 
  forwards*: Typing_CWell H.
Qed.
 *)

Lemma binds_trivial : forall x (A: typ) G,
    binds x A ((x, A) :: G).
  eauto.
Qed.
(* 
(* get lc_typ A from typing related hypotheses *)
(* #[export] *) Hint Extern 1 (lc_typ ?A) =>
match goal with
| H: binds _ A _ |- _ => applys TWell_lc_typ; applys CWell_TWell H
| H: TWell _ ((_, A) :: _) |- _ => applys TWell_lc_typ; applys CWell_TWell H; try applys binds_trivial
| H: Typing _ ((_, A) :: _) _ _ _ |- _ => apply Typing_CWell in H; applys Well_lc_typ; applys CWell_Well H; try applys binds_trivial
end : core. *)



(******************************************************************************)
(* inversion lemmas for lc *)

Create HintDb LcHd.



Ltac try_lc_typ_constructors :=
  applys lc_t_tvar_f +
  applys lc_t_int +
  applys lc_t_top +
  applys lc_t_arrow +
  applys lc_t_and +
  applys lc_t_ref +
  applys lc_t_rcd +
  match goal with (* pick fresh first if no atom exists *)
  | x : atom |- _ =>
    (* use the lemma from rule_inf.v instead of lc_t_forall *)
    applys lc_t_forall_exists x;
    instantiate_cofinites_with x
  | |- _ =>
    let x := fresh in pick fresh x;
                      applys lc_t_forall_exists x;
                      instantiate_cofinites_with x
  end.

Ltac try_lc_exp_constructors :=
  applys lc_e_var_f +
  applys lc_e_lit +
  applys lc_e_top +
  applys lc_e_app +
  applys lc_e_tapp +
  applys lc_e_merge +
  applys lc_e_anno +
  applys lc_e_ref +
  applys lc_e_rcd +
  applys lc_e_proj +
  match goal with
  | x : atom |- _ =>
    (* instead of constructors that contain forall *)
    applys lc_e_abs_exists +
    applys lc_e_tabs_exists;
    instantiate_cofinites_with x
  | |- _ =>
    let x := fresh in pick fresh x;
                      applys lc_e_abs_exists x +
                      applys lc_e_tabs_exists x;
                      instantiate_cofinites_with x
  end.

(* #[export] *) Hint Extern 1 (lc_typ _ ) => try_lc_typ_constructors : core.

(* #[export] *) Hint Extern 1 (lc_exp _ ) => try_lc_exp_constructors : core.

(* destruct hypotheses *)
Ltac inverts_all_lc :=
  repeat match goal with
         | H: lc_typ (t_and _ _) |- _ => inverts H
         | H: lc_typ (t_ref _) |- _ => inverts H
         | H: lc_typ (t_arrow _ _) |- _ => inverts H
         | H: lc_typ (t_forall _ _) |- _ => inverts H
         | H: lc_typ (t_rcd _ _) |- _ => inverts H
         end.


Ltac inverts_for_lc u :=
  repeat match goal with
         | H: lc_exp ?e |- _ => match e with
                                  context [ u ] => inverts H
                                end
         | H: lc_typ ?B |- _ => match B with
                                | u => try exact H
                                | context [ u ] => inverts H
                                end
         end.

(* #[export] *) Hint Extern 1 (lc_typ ?A ) =>
destruct_conj; progress inverts_for_lc A : core.

(* #[export] *) Hint Extern 1 (lc_exp ?e ) =>
destruct_conj; progress inverts_for_lc e : core.

(* #[export] *) Hint Extern 1 (lc_typ (?A -^ _) ) =>
destruct_conj;
  progress match A with
           | t_and ?A1 ?A2 => inverts_for_lc A1; inverts_for_lc A2
           | _ => inverts_for_lc A
           end : core.

(* ********************************************************************** *)
(** ** Regularity of relations: type related *)

Lemma ord_lc : forall A, ord A -> lc_typ A.
Proof.
  introv H.
  induction~ H.
Qed.

Lemma split_lc : forall A B C, spl A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof.
  introv H.
  induction H; repeat split*.
  all: instantiate_cofinites; eauto.
Qed.



Lemma topLike_lc : forall A, topLike A -> lc_typ A.
Proof.
  introv h1. 
  inductions h1; eauto. 
Qed.


(* get lc_typ information from existing hypotheses *)
Ltac solve_lc_1 A :=
  match goal with
  | H: ord A |- _ => lets: ord_lc H; assumption
  | H: spl A _ _ |- _ => lets (?&?&?): split_lc H; assumption
  | H: spl _ A _ |- _ => lets (?&?&?): split_lc H; assumption
  | H: spl _ _ A |- _ => lets (?&?&?): split_lc H; assumption
  | H: topLike A |- _ => lets: topLike_lc H; assumption
  (* | H: botLike A |- _ => lets: botLike_lc H; assumption *)
  end.

(* #[export] *) Hint Extern 1 (lc_typ ?A ) => progress solve_lc_1 A : core.


(* R: proper types *)
Lemma r_lc : forall A, R A -> lc_typ A.
Proof with firstorder.
  introv H.
  induction H; lets: split_lc...
Qed.


(* Lemma disjoint_axiom_lc: forall A B,
    disjoint_axiom A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H. inverts* H.
Qed. *)

Ltac solve_lc_2 A :=
  match goal with
  | H: R A |- _ => lets: r_lc H; assumption
  (* | H: disjoint_axiom A _ |- _ => lets (?&?): disjoint_axiom_lc H; assumption
  | H: disjoint_axiom _ A |- _ => lets (?&?): disjoint_axiom_lc H; assumption  *)
  (* | H: appDist A _ |- _ => lets (?&?): appDist_lc H; assumption
  | H: appDist _ A |- _ => lets (?&?): appDist_lc H; assumption
  | H: Merge _ _ A |- _ => applys merge_lc H; assumption*)
  end.

(* #[export] *) 
Hint Extern 1 (lc_typ ?A ) => progress solve_lc_2 A : core.






(* ********************************************************************** *)
(** ** Regularity of relations: typing *)

(* TODO:
I think We dont need lc_typ A since it can be implied by TWell D A
maybe we can get one regularity lemma for typing *)


(* #[export] *) Hint Extern 3 (lc_typ ?A) =>
match goal with
| H: forall x : atom, x `notin` _ -> _ |- _ =>
  progress instantiate_cofinites
end : LcHd.




(* 


(* 
Lemma TWell_bind_weakening : forall x I J D C F,
    TWell (F ++ (x ~ I) ++ D) (C -^ x) ->
    TWell (F ++ (x ~ J) ++ D) (C -^ x).
Proof with eauto.
  intros. remember (F ++ (x ~ I) ++ D) as G. gen F. induction* H; intros; subst.
  - analyze_binds H.
    applys TWell_tvar A...
    applys TWell_tvar J...
    applys TWell_tvar A ...
    (* simpl_env.
    rewrite_env (nil ++ x ~ J ++ D).
    applys binds_weaken... *)
  -  applys  TWell_forall;intros...
    forwards*: H1 X ((X, A) :: F).
Qed. *)


Lemma TWell_spl_2 : forall A B C D,
    spl A B C -> TWell D B -> TWell D C -> TWell D A.
Proof with eauto.
  introv Hs Hw1 Hw2. gen D.
  induction Hs; intros...
  - inverts Hw1. inverts Hw2.
    pick fresh xx.
    apply TWell_forall with (L := union L
    (union L0
       (union L1
          (union (dom D)
             (union [[A]]
                (union [[B]]
                   (union [[C1]]
                      (union [[C2]]
                         (union (dom D)
                            (typefv_typ_range D))))))))));intros...
Qed.


(* #[export] *) Hint Immediate TWell_spl_2  : core.

(* #[export] *) Hint Extern 2 (TWell ?D ?A) =>
match goal with
| H: spl A _ _ |- _ => applys TWell_spl_2 H
end : core. *)


Lemma algo_sub_lc : forall A B, algo_sub A B -> lc_typ A /\ lc_typ B.
Proof.
  introv h1.
  inductions h1; eauto.
Qed.

(* #[export] *) Hint Immediate algo_sub_lc  : core.


(* Lemma disjoint_lc: forall D A B,
    disjoint D A B -> lc_typ A /\ lc_typ B.
Proof.
  introv h1. 
  inductions h1; eauto;
  try solve[forwards*: algo_sub_lc H0].
Qed. *)


Lemma fvalue_lc_typ : forall v,
    fvalue v -> lc_typ (principle_type v).
Proof.
  introv H. induction* H; 
  simpl in *; try solve[inverts* H].
Qed.

Lemma value_lc_typ : forall v,
    value v -> lc_typ (principle_type v).
Proof.
  introv H. induction* H; 
  simpl in *; try solve[inverts* H].
Qed.



(* get all lc_typ information from existing hypotheses *)
Ltac get_all_lc :=
  repeat match goal with
         | H: ord _ |- _ => lets: ord_lc H; clear H
         | H: topLike _ |- _ => lets: topLike_lc H; clear H
         | H: algo_sub _ _ |- _ => lets (?&?): algo_sub_lc H; clear H
         (* | H: disjoint _ _ _ |- _ => lets (?&?): disjoint_lc H; clear H *)
         | H: R _ |- _ => lets: r_lc H; clear H
         | H: value _ |- _ => lets: value_lc_typ H; clear H
         | H: TWell _ _ |- _ => lets: TWell_lc_typ H; clear H 
         | H: WFTyp _ _ |- _ => lets: Well_lc_typ H; clear H 
         end.

(* #[export] *)
 Hint Extern 2 (lc_typ _ )=> progress get_all_lc; inverts_all_lc : LcHd.
(* #[export] *)
 Hint Extern 2 (lc_exp _ )=> progress get_all_lc; inverts_all_lc : LcHd.


(* 
(* #[export] *) 
Hint Extern 0 (TWell ?D ?A) =>
match goal with
| H: disjoint D A _ |- _ => lets (?&?): disjoint_regular H
| H: disjoint D _ A |- _ => lets (?&?): disjoint_regular H
end : core. *)

(* 
Lemma TWell_subst : forall x A D F B T,
    TWell D T ->
    TWell (F ++ x ~ A ++ D) (B -^ x) ->
    TWell (map (typsubst_typ T x) F ++ D) [x ~~> T] (B -^ x).
Proof with simpl_env; eauto.
  intros. remember (F ++ x ~ A ++ D) as G. gen F. induction* H0; intros; subst; simpl.
  -
    forwards*: IHTWell1.
  -
    forwards*: IHTWell.
  -
    forwards*: IHTWell1.
  - case_if.
    applys (TWell_weakening T D (map (typsubst_typ T x) F) nil)...
    analyze_binds H0...
  - 
    apply TWell_forall with (L := union L
    (union (singleton x)
       (union (dom D)
          (union (dom F)
             (union [[A]]
                (union [[B]]
                   (union [[T]]
                      (union [[A0]]
                         (union [[B0]]
                            (union 
                               (dom D)
                               (union 
                                  (dom F)
                                  (union
                                  (typefv_typ_range D)
                                  (typefv_typ_range F))))))))))))); intros.
    forwards*: IHTWell.
    forwards*: H2 X ((X, A0) :: F).
    rewrites typsubst_typ_open_typ_wrt_typ_var...
Qed.

 *)

(* 


Lemma TWell_all_open : forall D A B T,
    TWell D (t_forall A B) ->
    TWell D T ->
    TWell D (B ^-^ T).
Proof.
  intros. inverts H.
  pick fresh x.
  rewrite* (typsubst_typ_intro x).
  forwards*: H5 x.
  forwards*: TWell_subst H0.
  rewrite_env (nil ++ x ~ A ++ D) in H. applys H.
  forwards*: TWell_weakening.
  eauto. 
  Unshelve. apply nil. 
Qed.




Lemma TWell_strengthen : forall z U E F ty,
  z `notin` [[ty]] ->
  TWell (E ++ ((z,U) :: nil) ++ F) ty ->
  TWell (E ++ F) ty.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - eapply TWell_arrow.
    subst.
    apply IHTWell1; simpl in *; eauto; reflexivity.
    subst.
    apply IHTWell2; simpl in *; eauto; reflexivity.
  - eapply TWell_and.
    subst.
    apply IHTWell1; simpl in *; eauto; reflexivity.
    subst.
    apply IHTWell2; simpl in *; eauto; reflexivity.
  - subst; eapply TWell_tvar.
    apply in_or_app.
    repeat apply in_app_or in H0.
    inversion H0.
    left; apply H1.
    apply in_app_or in H1.
    inversion H1.
    inversion H2.
    inversion H3.
    subst.
    exfalso; apply H; simpl.
    eauto.
    inversion H3.
    auto.
  - subst.
    simpl in H.
    assert(TWell (E++F) A). apply IHTWell. auto. auto.
    apply TWell_forall with (L := union L
    (union (singleton z)
       (union (dom F)
          (union (dom E)
             (union [[U]]
                (union [[A]]
                   (union [[B]]
                      (union (dom F)
                         (union (dom E)
                            (union 
                               (typefv_typ_range F)
                               (typefv_typ_range E))))))))))).
                               auto.
    intros.
    rewrite_env (((X, A) :: E) ++ F).
    apply H2. auto. assert(z <> X). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ X)) (typefv_typ (t_tvar_f X) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(z `notin` (Metatheory.union [[t_tvar_f X]] [[B]])). auto. auto.
    auto.
Qed.


Lemma TCWell_strengthen : forall z U E F,
  z `notin` (typefv_typ_range  E) ->
  TCWell (E ++ ((z,U) :: nil) ++ F) ->
  TCWell (E ++ F) .
Proof.
  introv notin cw. 
  gen F z U.
  inductions E; intros;simpl in *;eauto.
  destruct a.
  
  inverts* cw.
  forwards*: IHE.
  apply wc_var; auto.
  forwards*:  TWell_strengthen H3.
    inverts* H4.
Qed. *)


Lemma spl_notin: forall A B C,
 spl A B C ->
 [[B]] [<=] [[A]] /\ [[C]] [<=] [[A]].
Proof.
  introv spl.
  inductions spl; simpl in *;
  try solve[splits*;fsetdec].
  pick fresh X.
  forwards* h1: H1 X.
  inverts h1 as h1 h2.
  assert( [[C1]] [<=] [[B]]) as h3.
  assert(C1 = close_typ_wrt_typ X (open_typ_wrt_typ C1 (t_tvar_f X))) as h5.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ; eauto.
  rewrite h5.
  assert(B = close_typ_wrt_typ X (open_typ_wrt_typ B (t_tvar_f X))) as h6.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ; eauto.
  rewrite h6.
  forwards* h7: typefv_typ_close_typ_wrt_typ (C1 -^ X) X.
  rewrite h7.
  forwards* h8: typefv_typ_close_typ_wrt_typ (B -^ X) X.
  rewrite h8.
  fsetdec.
  assert( [[C2]] [<=] [[B]]) as h4.
  assert(C2 = close_typ_wrt_typ X (open_typ_wrt_typ C2 (t_tvar_f X))) as h5.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ; eauto.
  rewrite h5.
  assert(B = close_typ_wrt_typ X (open_typ_wrt_typ B (t_tvar_f X))) as h6.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ; eauto.
  rewrite h6.
  forwards* h7: typefv_typ_close_typ_wrt_typ (C2 -^ X) X.
  rewrite h7.
  forwards* h8: typefv_typ_close_typ_wrt_typ (B -^ X) X.
  rewrite h8.
  fsetdec.
  splits;try solve[
  fsetdec].
Qed.



Lemma TWell_spl : forall A B C D,
    TWell D A ->
    spl A B C ->
    (TWell D B) /\ (TWell D C).
Proof with eauto.
  intros. gen D. induction H0; intros; eauto.
  -
    inverts* H1.
  - inverts H1.
    forwards*: IHspl.
  - inverts H2.
    splits.
    pick fresh x.
    apply TWell_forall with (L := union L
    (union L0
       (union (dom D)
          (union [[A]]
             (union [[B]]
                (union [[C1]]
                   (union [[C2]]
                     (union 
                     (dom D)
                     (typefv_typ_range
                     D)))))))));intros...
    forwards*: H7 X.
    forwards*: H1 H3.
    apply TWell_forall with (L := union L
    (union L0
       (union (dom D)
          (union [[A]]
             (union [[B]]
                (union [[C1]]
                   (union [[C2]]
                     (union 
                     (dom D)
                     (typefv_typ_range
                     D)))))))));intros...
    forwards*: H7 X.
    forwards*: H1 H3.
  -
    inverts H.
    forwards*: IHspl.
Qed.



Lemma Well_spl : forall A B C D,
    WFTyp D A ->
    spl A B C ->
    (WFTyp D B) /\ (WFTyp D C).
Proof with eauto.
  intros. gen D. induction H0; intros; eauto.
  -
    inverts* H1.
  - inverts H1.
    forwards*: IHspl.
  - inverts H2.
    splits.
    pick fresh x.
    apply w_forall with (L := union L
    (union L0
       (union (dom D)
          (union [[A]]
             (union [[B]]
                (union [[C1]]
                   (union [[C2]]
                     (union 
                     (dom D)
                     (typefv_typ_range
                     D)))))))));intros...
    forwards*: H7 X.
    forwards*: H1 H3.
    apply w_forall with (L := union L
    (union L0
       (union (dom D)
          (union [[A]]
             (union [[B]]
                (union [[C1]]
                   (union [[C2]]
                     (union 
                     (dom D)
                     (typefv_typ_range
                     D)))))))));intros...
    forwards*: H7 X.
    forwards*: H1 H3.
  -
    inverts H.
    forwards*: IHspl.
Qed.



(* 

Lemma Merge_TWell: forall D A B C,
    Merge A B C -> TWell D A -> TWell D B -> TWell D C.
Proof.
  intros. induction* H.
  - (* forall *)
    inversion H0;subst. inversion H1;subst.
    apply TWell_forall with (union L L0). auto. intros.
    unfold open_typ_wrt_typ.
    assert(TWell ((X, t_and A1 B1) :: D) (A2 -^ X)).
    rewrite_env(nil ++ [(X, t_and A1 B1)] ++ D).
    apply TWell_bind_weakening with A1. apply H5. auto.
    assert(TWell ((X, t_and A1 B1) :: D) (B2 -^ X)).
    rewrite_env(nil ++ [(X, t_and A1 B1)] ++ D).
    apply TWell_bind_weakening with B1. apply H7. auto.
    simpl. auto.
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
 *)


(* ********************************************************************** *)
(** ** Regularity of relations: term related *)

Lemma fvalue_lc : forall v,
    fvalue v -> lc_exp v.
Proof.
  introv H. induction* H.
Qed.


Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  introv H. induction* H.
  forwards*: fvalue_lc H.
Qed.


