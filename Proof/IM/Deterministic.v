Require Import Metalib.Metatheory.
Require Import LibTactics.


Require Import Arith Lia.
Require Import Coq.Program.Equality.
Require Import syntax_ott
                rules_inf
                Infrastructure
                Wellformedness
                SubtypingInversion
                Disjointness 
                Value
               KeyProperties.


Lemma anno_chk: forall G t e dir A P,
 Typing P G (e_anno e t) dir A -> 
 exists B0 : typ,
 Typing P G e Chk B0.
Proof.
  introv typ.
  inductions typ; eauto;
  try solve[exists; right; left*];
    try solve[exists; right; right; left*];
    try solve[exists; right; right; right*];
    try solve[exists; left*].
Qed.



Lemma ref_chk: forall G v dir A P,
 Typing P G (e_ref v) dir A -> exists t, Typing P G v Chk t.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



Lemma deref_chk: forall G v dir A P,
 Typing P G (e_get v) dir A -> exists t, Typing P G v Chk t.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.


Lemma app_chk: forall G v1 v2 dir A P,
 Typing P G (e_app v1 v2) dir A -> exists t1 t2, Typing P G v1 Chk t1 /\
 Typing P G v2 Chk t2.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



Lemma ass_chk: forall G v1 v2 dir A P,
 Typing P G (e_set v1 v2) dir A -> exists t1 t2, Typing P G v1 Chk t1 /\
 Typing P G v2 Chk t2.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



(* 
Lemma value_chk: forall G v t1 dir A P,
 value v ->
 Typing P G (e_anno v t1) dir A -> exists t, Typing P G v Chk t.
Proof.
  introv val typ.
  inductions typ; eauto; try solve[inverts val as h0; inverts h0].
Qed. *)



(* 


Lemma Typing_chk2inf: forall D G v A,
    Typing D G v Chk A -> exists B, Typing D G v Inf B /\ algo_sub B A.
Proof.
  intros D G v A Typ.
  inductions Typ; try solve [inverts Val].
  -
  exists.
  split*.
  -
  forwards h1: IHTyp1; auto.
  forwards h2: IHTyp2; auto.
  inverts h1 as h1.
  inverts h2 as h2.
  inverts h1 as h11 h12.
  inverts h2 as h21 h22.
  forwards* h3: inference_unique h11 h21.
  inverts h3.
  forwards*: algo_sub_lc h12.
Qed. *)





Lemma Typing_regular_1 : forall e P G dir A,
    Typing P G e dir A -> lc_exp e.
Proof with (eauto).
  introv H.
  inductions H...
Qed.


Lemma Typing_regular_2 : forall P G e dir T,
    Typing P G e dir T -> uniq G.
Proof.
  intros. induction* H; eauto.
  pick fresh x.
  forwards* h1: H0 x.
  inverts* h1.
  pick fresh x.
  forwards* h1: H0 x.
  inverts* h1.
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
 exists B, (Typing P nil  e Chk B).
Proof.
  introv typ.
  destruct F; unfold fill in *;
  try solve[ forwards* h1: app_chk typ];
  try solve[ forwards* h1: merge_chk typ];
  try solve[ forwards* h1: rcd_chk typ];
  try solve[ forwards* h1: prj_chk typ];
  try solve[ forwards* h1: ref_chk typ];
  try solve[ forwards* h1: deref_chk typ];
  try solve[ forwards* h1: ass_chk typ];
  try solve[ forwards* h1: tapp_chk typ];
  try solve[ forwards* h1: anno_chk typ]
  .
Qed.


Lemma tymu_eq: forall mu p t1 t2,
 tymu p mu t1 ->
 tymu p mu t2 ->
 t1 = t2.
Proof.
  introv ty1 ty2.
  inductions ty1; try solve[inverts* ty2]; try solve[inverts* ty2; lia].
  inverts* ty2.
  rewrite <- H in *.
  inverts* H1.
Qed.


Theorem step_unique: forall P mu A e r1 r2,
   P |== mu -> Typing P nil e Chk A -> step (e, mu) r1 -> step (e, mu) r2 -> r1 = r2.
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
      *
      forwards* h6: IHRed1 Red1 H4.
      congruence.
    +
      forwards* h1: Typing_regular_1 Typ.
      destruct F; unfold fill in *; inverts H0;
      try solve[
      inverts h1 as h1 h2;
      inverts h1 as h1 h3;
      inverts h1 as h1;
      forwards* h0: step_not_value Red1;
      inverts h0].
    +
      destruct F; unfold fill in *; inverts H5.
  -
     inverts Red2 as h2 h3;
    try solve[destruct F; unfold fill in *; inverts H0;
    forwards* h1: step_not_value Red1;
    inverts h1];
    try solve[inverts h3];
    try solve[inverts H].
    +
    forwards* h4: anno_chk Typ.
    inverts h4 as h4.
    forwards* h5: IHRed1 Red1 h4.
    inverts* h5. 
    +
    forwards* h1: step_not_value Red1.
    inverts h1.
  - (* beta *)
    forwards* h1: Typing_regular_1 Typ.
    inverts h1 as h1 h2.
    inverts h1 as h1 h3.
    inverts h1 as h1.
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards* h0: step_not_value H5;
      inverts h0
    ];try solve[inverts H4].
  -
    forwards* h1: Typing_regular_1 Typ.
    inverts h1 as h1 h2.
    inverts h1 as h1 h3.
    inverts h1 as h1.
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H2;
      forwards* h0: step_not_value H6;
      inverts h0
    ];try solve[inverts H7].
  - (* annov*)
    inverts* Red2;
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards* h1: step_not_value H5;
      inverts h1
    ];
    try solve[
      forwards* h1: step_not_value H6;
      inverts h1
    ];try solve[inverts H4].
  - (* deref *)
    inverts* Red2; try solve[inverts H3].
    forwards* h1: Typing_regular_1 Typ.
    inverts h1 as h2.
    inverts h2 as h3.
    destruct F; unfold fill in *; inverts H0;
    forwards* h1: step_not_value H4;
    inverts h1.
  - (* deref *)
    inverts* Red2; try solve[inverts H4].
    forwards* h1: Typing_regular_1 Typ.
    inverts h1 as h2.
    destruct F; unfold fill in *; inverts H1;
    forwards* h1: step_not_value H5;
    inverts h1.
  - (* set *)
    inverts* Red2; try solve[inverts H5].
    +
    destruct F; unfold fill in *; inverts* H2;
    try solve[forwards* h1: step_not_value H6;inverts h1].
    +
    rewrite <- H1 in H10.
    inverts H10; auto.
  - (* set *)
    inverts* Red2; try solve[inverts H6].
    +
    destruct F; unfold fill in *; inverts* H1;
    try solve[forwards* h1: step_not_value H5;inverts h1].
  - (* p *)
    inverts* Red2; try solve[inverts H0].
    +
    destruct F; unfold fill in *; inverts* H0;
    try solve[forwards* h1: step_not_abs H5;inverts h1].
    +
    forwards* h1:tymu_eq H1 H7.
    inverts* h1.
Qed.
















