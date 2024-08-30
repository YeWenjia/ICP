Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Lia.
Require Import syntax_ott
                rules_inf
                Infrastructure
                Wellformedness
                SubtypingInversion
                Disjointness
                Value.


Create HintDb common.
(* #[export] *) 
Hint Extern 1 (exists _, _) => exists : common.
(* #[export] *) 
Hint Extern 1 => match goal with
                   [ h : exists _ , _ |- _ ] => destruct h
                 end : common.

(* 
(* #[export] *) 
Hint Extern 0 => match goal with
                   | [ H: value (e_app _ _) |- _ ] => inverts H
                   | [ H: value (e_ref _ ) |- _ ] => inverts H
                   | [ H: value (e_set _ _ ) |- _ ] => inverts H
                   | [ H: prevalue (e_app _ _) |- _ ] => inverts H
                   | [ H: prevalue (e_ref _) |- _ ] => inverts H
                   | [ H: prevalue (e_set _ _) |- _ ] => inverts H
                   | [ H: fvalue (e_tabs _) |- _ ] => inverts H
                   | [ H: fvalue (e_loc _ _ ) |- _ ] => inverts H
                   | [ H: fvalue (e_rcd _ _ ) |- _ ] => inverts H
                 end : falseHd. *)

(* Lemma value_ptype: forall e A L G,
    value e -> Typing L G e Inf A ->  principle_type e = A.
Proof.
  introv Val H. 
  inductions H; intros; simpl in *;
  try solve [ inverts Val as h1;inverts* h1]; eauto.
Qed. *)



(* #[export] *) 
(* Hint Immediate typ_value_ptype : core. *)







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








