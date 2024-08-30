Require Import LibTactics.
Require Import Metalib.Metatheory.

(* Require Import Coq.Program.Equality. *)
Require Import syntax_ott
               rules_inf
               Infrastructure
               Wellformedness
               Lia.

(* 
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
Hint Extern 1 (spl (t_forall _ _)  _ _) => applys Sp_forall : core. *)


Lemma ord_or_split: forall A,
    ord A \/ exists B C, spl A B C.
Proof with (subst~; simpl in *; eauto).
  introv. induction A...
  - (* arrow *)
    forwards* [?|(?&?&?)]: IHA2.
Qed.


(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)

Lemma split_ord_false : forall T T1 T2,
     spl T T1 T2 -> ord T -> False.
Proof with eauto.
  introv Spl Ord. gen T1 T2.
  induction Ord; intros; inverts Spl...
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
Qed.

Ltac split_unify :=
  repeat match goal with
         | [ H1: spl ?A _ _ , H2: spl ?A _ _ |- _ ] =>
           (progress forwards (?&?): split_unique H1 H2;
            subst; clear H2)
         | [ H: spl (t_and _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_arrow _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_ref _) _ _ |- _ ] => inverts H
         (* | [ H: spl (t_forall _ _) _ _ |- _ ] => inverts H
         | [ H: spl (t_rcd _ _) _ _ |- _ ] => inverts H *)
         end;
  auto.


(* #[export] *)
Hint Extern 1 (spl _ _ _) =>
match goal with
| H: spl ?A _ _ |- spl (t_arrow _ ?A) _ _ => applys Sp_arrow H
(* | H: spl ?A _ _ |- spl (t_rcd _ ?A) _ _ => applys Sp_rcd H *)
| |- spl (t_and _ _) _ _ => applys Sp_and
end : core.

(* 
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
end : core. *)


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



(* #[local]  *)
Hint Resolve rfun rref : core.


(******************************************************************************)
(******************************* subtyping ************************************)

Ltac try_algo_sub_constructors :=
  applys S_int +
  match goal with
  | H: spl ?B _ _ |- algo_sub _ ?B => applys S_and H
  | H: spl ?B _ _ |- algo_sub _ (t_arrow _ ?B) => applys S_and
  | |- algo_sub _ (t_and _ _) => applys S_and
  | |- algo_sub _ (t_arrow _ (t_and _ _)) => applys S_and
  | H: algo_sub ?A ?B |- algo_sub (t_and ?A _) ?B => applys S_andl
  | H: algo_sub ?A ?B |- algo_sub (t_and  _ ?A) ?B => applys S_andr
  | |- _ =>  applys S_arr +
             applys S_ref 
  end.

(* #[local]  *)
Hint Extern 2 (algo_sub _ _) => progress try_algo_sub_constructors : core.


(* 

Lemma uniq_dom_binds:forall (A:typ) D F x, uniq(F ++ [(x,A)]++ D) -> x # (F ++ D).
Proof.
  intros. induction F. simpl in H. simpl. inversion H;subst. auto.
    destruct a. simpl in H. inversion H;subst. apply IHF in H2.
      assert(a<>x). eauto. auto.
Qed. *)
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
(* 
Lemma uniq_bind_weakening : forall x (I J:typ) D F,
    uniq (F ++ (x ~ I) ++ D) ->
    uniq (F ++ (x ~ J) ++ D) .
Proof with eauto.
  intros. induction F. simpl. simpl in H. inversion H;subst. auto.
    destruct a. inversion H;subst. apply IHF in H2. simpl. apply uniq_push. auto. auto.
Qed. *)



(* 
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
end : core. *)

Lemma Typ_decidable: forall A B:typ, {A = B}+{~A = B}.
Proof.
  repeat decide equality.
Qed.

Lemma binds_typ_dec: forall x E (A:typ),
 {binds x A E} + {~ binds x A E}.
Proof.
  intros. apply binds_dec. apply Typ_decidable.
Qed.


(* generalize S_andl *)
Lemma sub_l_andl : forall A B C,
    algo_sub A C -> algo_sub (t_and A B) C.
Proof with eauto.
  introv s. induction s; try solve [applys S_andl; eauto];
  try solve[forwards* h1: algo_sub_lc s2];
  try solve[forwards* h1: algo_sub_lc s1];
  try solve[forwards* h1: algo_sub_lc IHs]...
Qed.

(* generalize S_andr *)
Lemma sub_l_andr : forall A B C,
     algo_sub B C -> algo_sub (t_and A B) C.
Proof with eauto.
introv  s. induction s; try solve [applys S_andr; eauto];
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





(* #[export] *)
 Hint Resolve sub_fun  : core.


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
    algo_sub A A.
Proof.
  introv. inductions A;auto.
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
Qed.


Lemma spl_sub_r : forall A B C,
    spl A B C -> algo_sub A C.
Proof.
  introv H. induction H;intros;auto.
Qed.

(* #[export] *) Hint Immediate spl_sub_l spl_sub_r : core.


(* splitting does not lose or add information to a type *)
Lemma split_sub: forall A B C,
    spl A B C -> algo_sub A (t_and B C) /\ algo_sub (t_and B C) A.
Proof.
  intros A B C H.
  split.
  - lets~: spl_sub_l H. lets~: spl_sub_r H.
  - eauto.
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
Qed.


(* inversion on right split *)
Lemma sub_r_spl_l : forall A B B1 B2,
    spl B B1 B2 -> algo_sub A B -> algo_sub A B1.
Proof.
  introv Hspl Hsub.
  inverts Hsub; split_unify;
  try solve[forwards* h1: split_ord_false Hspl;inverts h1];
  try solve[forwards* h1: split_ord_false H;inverts h1].
Qed.

Lemma sub_r_spl_r : forall A B B1 B2,
    spl B B1 B2 -> algo_sub A B -> algo_sub A B2.
Proof.
  introv Hspl Hsub.
  inverts Hsub; split_unify;
  try solve[forwards* h1: split_ord_false Hspl;inverts h1];
  try solve[forwards* h1: split_ord_false H;inverts h1].
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
  -
  forwards* h1: IHHsub2 H4.
Qed.

(* #[export] *)
 Hint Immediate sub_r_spl_l sub_r_spl_r : core.


Lemma sub_transitivity_gen : forall A B C n,
    size_typ A + size_typ B + size_typ C < n ->
    algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof with ( split_unify; eauto 4).
  introv sz S1 S2.
  gen A B C.
  inductions n; intros;try solve[lia].
  inductions S2; 
    intros; try solve [inductions S1;auto ].
  -
    clear IHS2_1 IHS2_2.
    inverts S1;auto...
    +
    forwards h1: IHn A1 A0 B; auto.
    simpl in *; lia.
    forwards h2: IHn B A0 A1; auto.
    simpl in *; lia.
    +
    forwards h1: IHn A1 (t_ref A0) (t_ref B); auto.
    simpl in *; lia.
    +
    forwards h1: IHn B0 (t_ref A0) (t_ref B); auto.
    simpl in *; lia.
  -
    forwards h1: sub_r_spl_l S1; auto.
    forwards h2: IHn A A0 C; auto.
    simpl in *; lia.
  -
    forwards h1: sub_r_spl_r S1; auto.
    forwards h2: IHn A B C; auto.
    simpl in *; lia.
  -
    inverts S1 as h1 h2 h3;auto...
    +
    forwards* h4: IHn A1 (t_arrow A0 C) (t_arrow B D). simpl in *. lia.
    +
    forwards* h4: IHn B0 (t_arrow A0 C) (t_arrow B D). simpl in *. lia.
    +
    simpl in *.
    forwards h4: IHn S2_1 h2.
    lia.
    forwards h5: IHn h3 S2_2.
    lia.
    eauto.
    +
    forwards h1: sub_inversion_split_l S2_2 H4; auto.
    inverts h1 as h1 h2.
    *
    forwards h5 :split_decrease_size H4.
    forwards h4: IHn A (t_arrow A0 C1) (t_arrow B D); auto.
    simpl in *; eauto.
    lia.
    *
    forwards h5 :split_decrease_size H4.
    forwards h4: IHn A (t_arrow A0 D0) (t_arrow B D); auto.
    simpl in *; eauto.
    lia.
  -
    forwards h1 :split_decrease_size H.
    forwards h2: IHn S1 S2_1.
    simpl in *; lia.
    forwards h3: IHn S1 S2_2.
    simpl in *; lia.
    eauto.
  -
    inverts S1;auto; try solve[inverts H]...
    +
    forwards h1: IHn A0 t_pos t_int; auto.
    simpl in *; lia.
    +
    forwards h1: IHn B t_pos t_int; auto.
    simpl in *; lia.
Qed.


(* we do not need type A B C to be locally closed because subtyping relation could imply which is shown in `algo_sub_lc`. *)
Lemma sub_transitivity : forall A B C,
    algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof with ( split_unify; eauto 4).
  introv S1 S2.
  eapply sub_transitivity_gen; eauto.
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





