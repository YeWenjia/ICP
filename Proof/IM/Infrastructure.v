Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import syntax_ott 
               rules_inf
               Lia.




Definition irred e mu mu' : Prop := forall b, ~(step (e, mu) (b, mu')).



Lemma nstars_one:
forall a b mu1 mu2, nstep (a,mu1) (b,mu2) -> nsteps (a,mu1) (b,mu2).
Proof.
introv red.
eauto using nsteps.
Qed.

Lemma nstars_trans:
forall a b mu1 mu2, nsteps (a,mu1) (b,mu2) -> forall c mu3, nsteps (b,mu2) (c,mu3) -> nsteps (a,mu1) (c,mu3).
Proof.
  introv H.
  inductions H; eauto using nsteps.
Qed.


Lemma stars_one:
forall a b mu1 mu2, step (a,mu1) (b,mu2) -> steps (a,mu1) (b,mu2).
Proof.
introv red.
eauto using steps.
Qed.

Lemma stars_trans:
forall a b mu1 mu2, steps (a,mu1) (b,mu2) -> forall c mu3, steps (b,mu2) (c,mu3) -> steps (a,mu1) (c,mu3).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.

(************************************ Ltac ************************************)

(* try solve the goal by contradiction *)
Create HintDb FalseHd.
Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    end
         end.

(* Ltac from Alvin *)
Ltac detect_fresh_var_and_do t :=
  match goal with
  | Fr : ?x `notin` ?L1 |- _ => t x
  | _ =>
    let x := fresh "x" in
    pick fresh x; t x
  end.

Ltac instantiate_cofinite_with H X :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
    let H1 := fresh "H" in
    assert (H1 : X `notin` L) by solve_notin;
    specialize (H X H1); clear H1
  end.

Ltac instantiate_cofinites_with x :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> _ |- _ =>
    instantiate_cofinite_with H x
         end;
  destruct_conj.

Ltac instantiate_cofinites :=
  detect_fresh_var_and_do instantiate_cofinites_with.

Ltac applys_and_instantiate_cofinites_with H x :=
  applys H x; try solve_notin; instantiate_cofinites_with x.

Ltac pick_fresh_applys_and_instantiate_cofinites H :=
  let X:= fresh in
  pick fresh X; applys_and_instantiate_cofinites_with H X.

Ltac detect_fresh_var_and_apply H :=
  let f x := applys_and_instantiate_cofinites_with H x in
  detect_fresh_var_and_do f.

(************************ Notations related to types **************************)
(* Notation "[ z ~~> u ] t" := (typsubst_typ u z t) (at level 0).
Notation "t ^-^ u"       := (open_typ_wrt_typ t u) (at level 67).
Notation "t -^ x"        := (open_typ_wrt_typ t (t_tvar_f x))(at level 67).
Notation "[[ A ]]"         := (typefv_typ A) (at level 0). *)

(***************************** Other notations ********************************)

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).
Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.


(*********************** Locally nameless related defns ***********************)

(* Fixpoint typefv_typ_range (E : (list (atom * TyEnv)))
  : atoms :=
  match E with
    | nil => empty
    | (_, (TermV A)) :: E' => (typefv_typ A) \u (typefv_typ_range E')
    | (_, (TyDis A)) :: E' => (typefv_typ A) \u (typefv_typ_range E')
  end.

Fixpoint typefv_sto (E : sto)
  : atoms :=
  match E with
    | nil => empty
    | e :: E' => (typefv_exp e) \u (typefv_sto E')
  end.

Fixpoint typefv_phi (E : phi)
  : atoms :=
  match E with
    | nil => empty
    | A :: E' => (typefv_typ A) \u (typefv_phi E')
  end. *)

(* redefine gather_atoms for pick fresh *)
Ltac gather_atoms ::= (* for type var *)
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let C':= gather_atoms_with (fun x : exp => fv_exp x) in
  (* let D := gather_atoms_with (fun x : exp => typefv_exp x) in *)
  (* let E := gather_atoms_with (fun x : typ => typefv_typ x) in *)
  let G := gather_atoms_with (fun x : ctx => dom x) in
  (* let G' := gather_atoms_with (fun x : ctx => typefv_typ_range x) in *)
  (* let F := gather_atoms_with (fun x : sto => typefv_sto x) in
  let F' := gather_atoms_with (fun x : phi => typefv_phi x) in *)
  constr:(A `union` B `union` C `union` C' `union` G).



(******************************************************************************)


(******************************* proper types *********************************)

Inductive R : typ -> Prop :=
| R_int : R t_int
| R_pos : R t_pos
| R_top : R t_top
| R_unit : R t_unit
(* | R_x : forall X, R (t_tvar_f X) *)
| R_ordFun : forall A B, ord B -> R A -> R B -> R (t_arrow A B)
| R_ordRef : forall A, R A -> R (t_ref A)
(* | R_ordAll : forall L A B,
    ( forall X , X \notin L -> ord  ( open_typ_wrt_typ B (t_tvar_f X) )  )
    -> R A ->
    ( forall X , X \notin L -> R  ( open_typ_wrt_typ B (t_tvar_f X) )  )  -> R (t_forall A B) *)
| R_spl : forall B C A, spl A B C -> R B -> R C -> R A
(* | R_ordRcd : forall i5 B, ord B -> R B -> R (t_rcd i5 B) *)
.

(* (* #[export] *)  *)
Hint Constructors R : core.

(* 

(******************************* free vars *********************************)

Lemma notin_close : forall X A,
    X `notin` typefv_typ (close_typ_wrt_typ X A).
Proof.
  introv HF.
  apply typefv_typ_close_typ_wrt_typ in HF.
  applys* remove_iff X.
Qed.

(* (* #[export] *)  *)
Hint Resolve notin_close : core. *)


(********************* rename & subst **********************************)

(* 
(* lc_exp *)
Lemma lc_exp_rename : forall e x y,
    x \notin (termfv_exp e) -> lc_exp (e ^ x) -> lc_exp (e ^ y).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: lc_exp ( [x ~> (e_var_f y)] (e ^ x) )).
  applys~ subst_exp_lc_exp.
  simpl in H. rewrite subst_exp_spec in H.
  rewrite close_exp_wrt_exp_open_exp_wrt_exp in H...
Qed.

Lemma abs_lc_open : forall e v,
    lc_exp (e_abs e) -> lc_exp v -> lc_exp (e ^^ v).
Proof.
  introv H H0.
  inverts H.
  apply~ lc_body_exp_wrt_exp.
Qed.

(* lc_typ *)
Lemma lc_typ_rename : forall A X Y,
    X \notin (typefv_typ A) -> lc_typ (A -^ X) -> lc_typ (A -^ Y).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: lc_typ [X ~~> (t_tvar_f Y)] (A -^ X)).
  applys~ typsubst_typ_lc_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.


Lemma lc_typ_rename_2: forall A X Y, lc_typ(A -^ X) -> lc_typ(A -^ Y).
Proof.
  intros. apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A -^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto. auto.
    apply lc_typ_of_degree in H0. auto.
Qed.


Lemma lc_forall_inv : forall X A B,
    lc_typ (t_forall A B) -> lc_typ (B -^ X).
Proof.
  intros. inverts* H.
Qed.

(* (* #[export] *)  *)
Hint Extern 1 (lc_exp ?e ^ _) =>
match goal with
  H: lc_exp e ^ ?x |- _ => let Fr := fresh in
                           assert (Fr: x \notin (termfv_exp e)) by solve_notin;
                             applys lc_exp_rename Fr H
end : core.

(* (* #[export] *)  *)
Hint Extern 1 (lc_typ ?A ^ _) =>
match goal with
  H: lc_typ A ^ ?x |- _ => let Fr := fresh in
                           assert (Fr: x \notin (typefv_typ A)) by solve_notin;
                             applys lc_typ_rename Fr H
end : core.

(* (* #[export] *)  *)
Hint Immediate lc_typ_rename_2 abs_lc_open lc_forall_inv : core.

(* rename / typsubst in ord & split *)
(* #[local]  *)
Hint Resolve typsubst_typ_lc_typ : core.

(*********************************)
(* some useful lemmas            *)
(* for proving typsubst lemmas:  *)
(* lc_t_forall_exists            *)
(* typsubst_typ_spec             *)
(* typsubst_typ_open_typ_wrt_typ *)
(*********************************)

Lemma typsubst_typ_ord_typ : forall A X Y,
  ord A ->
  ord ( [X ~~> (t_tvar_f Y)] A ).
Proof with (simpl in *; eauto).
  introv Ord. gen X Y. induction Ord; intros...
  - destruct (X==X0)...
  - applys~ (O_forall (L \u {{X}})).
    introv Fr. forwards* Ord: H1 X0 X Y.
    rewrite typsubst_typ_open_typ_wrt_typ in Ord...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H2 in Ord...
Qed.



Lemma typsubst_typ_toplike_typ : forall A X Y,
  topLike A ->
  topLike ( [X ~~> (t_tvar_f Y)] A ).
Proof with (simpl in *; eauto).
  introv Ord. gen X Y. induction Ord; intros...
  - applys~ (TL_all (L \u {{X}})).
    introv Fr. forwards* Ord: H1 X0 X Y.
    rewrite typsubst_typ_open_typ_wrt_typ in Ord...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H2 in Ord...
Qed.

Lemma typsubst_typ_split_typ : forall A B C X Y,
  spl A B C->
  spl ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B) ([X ~~> (t_tvar_f Y)] C).
Proof with (simpl in *; eauto).
  introv Spl. gen X Y.
  induction Spl; intros...
  - applys~ (Sp_forall (L \u {{X}})).
    introv Fr. forwards* Spl: H1 X0 X Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in Spl...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H2 in Spl...
Qed.

(* #[export] *) 
Hint Resolve typsubst_typ_ord_typ typsubst_typ_split_typ : core.


Lemma ord_rename : forall A X Y,
    X \notin (typefv_typ A) -> ord ( A -^ X ) -> ord ( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: ord [X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ typsubst_typ_ord_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.



Lemma split_rename : forall A B C X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) \u (typefv_typ C)->
    spl ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    spl ( A -^ Y ) ( B -^ Y ) ( C -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: spl [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X) [X ~~> (t_tvar_f Y)] (C -^ X)).
  applys~ typsubst_typ_split_typ.
  simpl in H. rewrite 3 typsubst_typ_spec in H.
  rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.


(* #[export] *)
Hint Extern 1 (ord ( ?A -^ ?Y )) =>
  match goal with
  | H: ord ( A -^ ?X ) |- _ => let Fr := fresh in
                               assert (Fr: X \notin (typefv_typ A)) by solve_notin;
                                 applys ord_rename Fr H
  end : core.

(* #[export] *)
Hint Extern 1 (spl ( ?A -^ ?Y ) _ _) =>
  match goal with
| H: spl ( A -^ ?X ) ( ?B -^ ?X ) ( ?C -^ ?X ) |- _ => applys split_rename H
end : core.

(* #[local]  *)
Hint Resolve ord_rename split_rename : core.

Lemma ord_forall_exists : forall X A B,
  X `notin` typefv_typ B ->
  lc_typ A ->
  ord (open_typ_wrt_typ B (t_tvar_f X)) ->
  ord (t_forall A B).
Proof with (simpl in *; eauto).
  introv Fr Lc Ord.
  applys~ O_forall (typefv_typ B).
Qed.

(* #[export] *)
Hint Extern 1 =>
match goal with
| H: ord (open_typ_wrt_typ ?B (t_tvar_f ?X)) |- ord (t_forall _ ?B) =>
  applys~ ord_forall_exists H; solve_notin
end : core.


Lemma split_forall_exists : forall X A B B1 B2,
  X `notin` typefv_typ B ->
  lc_typ A ->
  spl (B -^ X) B1 B2->
  spl (t_forall A B) (t_forall A (close_typ_wrt_typ X B1)) (t_forall A (close_typ_wrt_typ X B2)).
Proof with (simpl in *; eauto).
  introv Fr Lc Ord.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B1 X) in Ord.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B2 X) in Ord.
  applys~ Sp_forall.
  Unshelve. applys empty.
Qed.


(* (* #[export] *) *)
Hint Extern 2 =>
match goal with
| H: spl (?B -^ ?X) ?B1 ?B2 |-
  spl (t_forall ?A ?B) (t_forall ?A (close_typ_wrt_typ ?X ?B1)) (t_forall ?A (close_typ_wrt_typ ?X ?B2)) =>
  applys split_forall_exists H; solve_notin
| H: spl (?B -^ ?X) _ _ |-
  spl (t_forall ?A ?B) _ _ =>
  applys split_forall_exists H; solve_notin
end : core.




Lemma typsubst_typ_proper_typ : forall A X Y,
  R A ->
  R [X~~> (t_tvar_f Y)] A.
Proof with (simpl in *; eauto).
  introv Hr. gen X Y.
  induction Hr; intros...
  - destruct (X==X0)...
  - applys~ (R_ordAll (L \u {{X}}) ).
    + (* goal1: ord *)
      intros X0 Fr0. forwards* Ord0: H.
      eapply (typsubst_typ_ord_typ _ X Y) in Ord0.
      rewrite typsubst_typ_open_typ_wrt_typ in Ord0...
      case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
      rewrite H2 in Ord0...
    + (* goal2: r *)
      intros X0 Fr0. forwards* R0: H1 X0 X Y.
      rewrite typsubst_typ_open_typ_wrt_typ in R0...
      case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
      rewrite H2 in R0...
Qed.

Lemma proper_rename : forall A X Y,
    X \notin (typefv_typ A) -> R ( A -^ X ) -> R ( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: R [X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ typsubst_typ_proper_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.
 *)

(************************ type sizes **************************)
(** defines size on types and proves some related
lemmas. It aims to make later proofs easier if they do
induction on the size of types *)

Lemma split_decrease_size: forall A B C,
    spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
Qed.



Ltac spl_size :=
  try repeat match goal with
         | [ H: spl _ _ _ |- _ ] =>
           ( lets (?&?): split_decrease_size H; clear H)
             end.

(********************************************)
(*                                          *)
(*               Ltac elia                  *)
(*  enhanced lia with split_decrease_size   *)
(*                                          *)
(********************************************)
(* Ltac elia :=
  try solve [pose proof (size_typ_min);
             spl_size; simpl in *;
             try repeat rewrite size_typ_open_typ_wrt_typ_var;
             try repeat rewrite size_exp_open_exp_wrt_typ_var;
             try repeat rewrite size_exp_open_exp_wrt_exp_var;
             try lia]. *)
(* eauto with typSize lngen ? *)

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].


(* 
Lemma step_not_fvalue: forall (v:exp) mu mu',
    fvalue v -> irred v mu mu'.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;
  destruct F; unfold fill in H0; inverts* H0];
  try solve[inverts H0 as h0;inverts h0].
  -
    inverts* H;
    try solve[
    destruct F; unfold fill in *; inverts H0];
    try solve[inverts H7 as h0;inverts h0].
    destruct F; unfold fill in *; inverts H0.
    inverts* H7;
    try solve[destruct F; unfold fill in *; inverts H].
Qed.



Lemma step_not_tabs: forall e mu mu',
     irred (e_tabs e) mu mu'.
Proof.
  introv.
  unfold irred.
  unfold not;intros;
  try solve[inverts* H;
  destruct F; unfold fill in H0; inverts* H0].
Qed.


Lemma step_not_loc: forall e mu mu',
     irred (e_loc e) mu mu'.
Proof.
  introv.
  unfold irred.
  unfold not;intros;
  try solve[inverts* H;
  destruct F; unfold fill in H0; inverts* H0].
Qed.

Lemma step_not_loct: forall mu mu',
     irred (e_loct) mu mu'.
Proof.
  introv.
  unfold irred.
  unfold not;intros;
  try solve[inverts* H;
  destruct F; unfold fill in H0; inverts* H0].
Qed. *)


Lemma pvalue_lc : forall v,
    pvalue v -> lc_exp v.
Proof.
  introv H. 
  induction* H.
Qed.


Lemma ppvalue_lc : forall v,
    ppvalue v -> lc_exp v.
Proof.
  introv H. 
  induction* H.
Qed.


Lemma ppvalue_pvalue : forall v,
    ppvalue v -> pvalue v.
Proof.
  introv H. 
  induction* H.
Qed.

Hint Resolve ppvalue_pvalue : core.


Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  introv H. induction* H.
  forwards*: pvalue_lc H.
Qed.


Lemma step_not_abs: forall e t mu mu',
     irred (e_abs e t) mu mu'.
Proof.
  introv.
  unfold irred.
  unfold not;intros;
  try solve[inverts* H;
  destruct F; unfold fill in H0; inverts* H0].
  inverts* H;
  try solve[
  destruct F; unfold fill in H0; inverts* H0];
  try solve[inverts H5].
Qed.



Lemma step_not_value: forall (v:exp) mu mu',
    value v -> irred v mu mu'.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;
  destruct F; unfold fill in H0; inverts* H0];
  try solve[inverts H0 as h0;inverts h0].
  -
    forwards*: step_not_abs H.
  -
    inverts* H;
    try solve[
    destruct F; unfold fill in *; inverts H0];
    try solve[inverts H6 as h0;inverts h0].
    inverts* H1; try solve[inverts* H7].
Qed.



Lemma multi_red_app2n : forall v t t' mu1 mu2,
    nvalue v -> nsteps (t, mu1) (t', mu2) -> nsteps ((e_app v t),mu1) ((e_app v t'), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(Wformed (nappCtxR v)) as h0. eauto.
  forwards*:  nstep_eval H.
Qed.


Lemma multi_red_appn : forall v t t' mu1 mu2,
    lc_exp v -> nsteps (t, mu1) (t', mu2) -> nsteps ((e_app t v),mu1) ((e_app t' v), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(Wformed (nappCtxL v)) as h0. eauto.
  forwards*:  nstep_eval H.
Qed.



Lemma multi_red_set2n : forall v t t' mu1 mu2,
    nvalue v -> nsteps (t, mu1) (t', mu2) -> nsteps ((e_set v t),mu1) ((e_set v t'), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(Wformed (nsetCtxR v)) as h0. eauto.
  forwards*:  nstep_eval H.
Qed.


Lemma multi_red_setn : forall v t t' mu1 mu2,
    lc_exp v -> nsteps (t, mu1) (t', mu2) -> nsteps ((e_set t v),mu1) ((e_set t' v), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(Wformed (nsetCtxL v)) as h0. eauto.
  forwards*:  nstep_eval H.
Qed.


Lemma multi_red_getn : forall t t' mu1 mu2,
    nsteps (t, mu1) (t', mu2) -> nsteps ((e_get t),mu1) ((e_get t'), mu2).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(Wformed (ngetCtx)) as h0. eauto.
  forwards*:  nstep_eval H.
Qed.


Lemma multi_red_refn : forall t t' mu1 mu2,
    nsteps (t, mu1) (t', mu2) -> nsteps ((e_ref t),mu1) ((e_ref t'), mu2).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(Wformed (nrefCtx)) as h0. eauto.
  forwards*:  nstep_eval H.
Qed.




Lemma multi_red_app2 : forall v t t' mu1 mu2,
    value v -> steps (t, mu1) (t', mu2) -> steps ((e_app v t),mu1) ((e_app v t'), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed (appCtxR v)) as h0. eauto.
  forwards*:  step_eval H.
Qed.


Lemma multi_red_app : forall v t t' mu1 mu2,
    lc_exp v -> steps (t, mu1) (t', mu2) -> steps ((e_app t v),mu1) ((e_app t' v), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed (appCtxL v)) as h0. eauto.
  forwards*:  step_eval H.
Qed.



Lemma multi_red_set2 : forall v t t' mu1 mu2,
    value v -> steps (t, mu1) (t', mu2) -> steps ((e_set v t),mu1) ((e_set v t'), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed (setCtxR v)) as h0. eauto.
  forwards*:  step_eval H.
Qed.


Lemma multi_red_set : forall v t t' mu1 mu2,
    lc_exp v -> steps (t, mu1) (t', mu2) -> steps ((e_set t v),mu1) ((e_set t' v), mu2).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed (setCtxL v)) as h0. eauto.
  forwards*:  step_eval H.
Qed.


Lemma multi_red_get : forall t t' mu1 mu2,
    steps (t, mu1) (t', mu2) -> steps ((e_get t),mu1) ((e_get t'), mu2).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed (getCtx)) as h0. eauto.
  forwards*:  step_eval H.
Qed.


Lemma multi_red_ref : forall t t' mu1 mu2,
    steps (t, mu1) (t', mu2) -> steps ((e_ref t),mu1) ((e_ref t'), mu2).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed (refCtx)) as h0. eauto.
  forwards*:  step_eval H.
Qed.

(* 
Lemma multi_red_anno : forall tt t t' mu1 mu2,
    steps (t, mu1) (t', mu2) -> steps ((e_anno t tt),mu1) ((e_anno t' tt), mu2).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(WFTypformed  (annoCtx tt)) as h0. eauto.
  forwards*:  step_eval h0 H.
Qed.
 *)

