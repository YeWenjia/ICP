Require Import LibTactics.
Require Export Value
               Disjointness.
Require Export Lia.

Require Import Lia.

Create HintDb common.
(* #[export] *) 
Hint Extern 1 (exists _, _) => exists : common.
(* #[export] *) 
Hint Extern 1 => match goal with
                   [ h : exists _ , _ |- _ ] => destruct h
                 end : common.


(* #[export] *) 
Hint Extern 0 => match goal with
                   | [ H: value (e_app _ _) |- _ ] => inverts H
                   | [ H: value (e_ref _ ) |- _ ] => inverts H
                   | [ H: value (e_ass _ _ ) |- _ ] => inverts H
                   | [ H: prevalue (e_app _ _) |- _ ] => inverts H
                   | [ H: prevalue (e_ref _) |- _ ] => inverts H
                   | [ H: prevalue (e_ass _ _) |- _ ] => inverts H
                   | [ H: fvalue (e_tabs _) |- _ ] => inverts H
                   | [ H: fvalue (e_loc _ _ ) |- _ ] => inverts H
                   | [ H: fvalue (e_rcd _ _ ) |- _ ] => inverts H
                 end : falseHd.

Lemma typ_value_ptype: forall e A L G,
    value e -> Typing L G e Inf A ->  principle_type e = A.
Proof.
  introv Val H. 
  inductions H; intros; simpl in *;
  try solve [ inverts Val as h1;inverts* h1]; eauto.
  - inverts Val;try solve[
    forwards*: IHTyping1;
    forwards*: IHTyping2;
    subst*]; try solve[inverts H2]; try solve[inverts Val as h1;inverts* h1].
  -
    inverts Val;try solve[
    forwards*: IHTyping1;
    forwards*: IHTyping2;
    subst*]; try solve[inverts H2]; try solve[inverts Val as h1;inverts* h1];  try solve[inverts H0].
    forwards* h1: IHTyping.
    rewrite h1; auto.
Qed.

(* #[export] *) Hint Immediate typ_value_ptype : core.



(* casting *)

(* #[export] *) Hint Immediate casting_prv_value : core.





Lemma casting_top_normal : forall B (v v': exp),
    Cast v B v' -> ord B -> topLike B -> v' = TLVal B.
Proof.
  introv H od tl.
  inductions H; auto;
  try solve[inverts* tl];
  try solve[exfalso; apply H0;auto];
  try solve[exfalso; apply H;auto];
  try solve[inverts H;inverts od;simpl in *;inverts* tl].
  -
    simpl in *.
    inverts* H.
    inverts* tl.
    forwards* h1: IHCast.
    rewrite h1.
    auto.
  -
    forwards* h1: split_ord_false A.
    inverts h1.
Qed.


Lemma spl_lc_1: forall A B C,
 spl A B C ->
 lc_typ A.
Proof.
 introv sp.
 inductions sp; eauto.
Qed.


Lemma casting_toplike : forall A v1 v2 v1' v2',
    topLike A -> value v1 -> value v2 -> Cast v1 A v1' -> Cast v2 A v2' -> v1' = v2'.
Proof with (split_unify; solve_false; auto).
  intros A v1 v2 v1' v2' TL Val1 Val2 Red1 Red2.
  gen  v1' v2'.
  proper_ind A; intros; try solve [ inverts TL
                                  | forwards*: HH Val1 Red1;
                                    forwards*: HH Val2 Red2;
                                    subst* ].
  -
     forwards* h1: casting_top_normal Red1.
     forwards* h2: casting_top_normal Red2.
     substs*.
  -
     forwards* h1: casting_top_normal Red1.
     forwards* h2: casting_top_normal Red2.
     substs*.
  -
     forwards* h1: casting_top_normal Red1.
     forwards* h2: casting_top_normal Red2.
     substs*.
  -
    forwards* h1: casting_top_normal Red1.
     forwards* h2: casting_top_normal Red2.
     substs*.
  -
  inverts Red1; try solve[
    forwards h1: split_ord_false H;auto; inverts h1
  ]; try solve[inverts TL]; try solve[inverts H].
  inverts Red2;try solve[
    forwards h1: split_ord_false H;auto; inverts h1
  ];try solve[inverts TL]; try solve[inverts H].
  split_unify.
  forwards*: IHr1 H1 H4.
  forwards*: IHr2 H2 H5.
  congruence.
  -
  forwards* h1: casting_top_normal Red1.
  forwards* h2: casting_top_normal Red2.
  substs*.
Qed.



Lemma casting_sub: forall v v' A,
    value v -> Cast v A v' -> algo_sub (principle_type v) A.
Proof with eauto with common.
  introv Val Red. 
  induction Red; intros; simpl in *;try solve [ inverts Val; eauto]; try solve[
    rewrite H2; auto
  ].
  -
    inverts Val as h1; try solve[inverts h1].
    forwards*: IHRed.
    (* forwards*: value_lc_typ H4. *)
  -
   inverts Val as h1; try solve[inverts h1].
    forwards*: IHRed.
    forwards*: value_lc_typ H4.
  -
    inverts Val as h1; try solve[inverts h1].
     forwards*: IHRed.
     forwards*: value_lc_typ h1.
  -
    forwards* h1: IHRed1.
Qed.


Lemma sto_ok_value: forall l mu,
 l < Datatypes.length mu ->
 sto_ok mu ->
 value ((store_lookup l mu)).
Proof.
  introv len ok. gen l.
  inductions ok; intros; try solve[inverts len];
  simpl in *.
  destruct l; simpl; eauto.
  forwards*: IHok l.
  lia.
Qed.








