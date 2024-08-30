(**
   Lemmas about subst on some relations &
   Lemmas about values and prevalues
 *)
 Require Import LibTactics.
 Require Import Lia.
 Require Export Wellformedness.


Lemma value_merge_l_inv : forall v1 v2,
    value (e_merge v1 v2) -> value v1.
Proof.
  introv H.
  inverts~ H;
  try solve[inverts H0].
Qed.


Lemma value_merge_r_inv : forall v1 v2,
    value (e_merge v1 v2) -> value v2.
Proof.
  introv H.
  inverts~ H;
  try solve[inverts H0].
Qed.


(* 
(* relys on lemmas about lc in wellformedness *)
#[local]
 Hint Extern 3 (lc_typ _) =>
progress (solve_lc; trivial) : LcHd. *)



Lemma open_comm_00: forall A n n0 X Y,
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
    -  (* rcd *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
      rewrite H0. auto.
   -  (* forall *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A1)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) (open_typ_wrt_typ_rec (S (S n)) (t_tvar_f X) A2)) =
        (open_typ_wrt_typ_rec (S n) (t_tvar_f X) (open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) A2))).
      apply IHA2. lia. rewrite H0. rewrite H1. auto.
  -
     assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) (t_tvar_f X) A)) =
        (open_typ_wrt_typ_rec n (t_tvar_f X) (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))) as h1. eauto.
      rewrite h1. auto.
Qed.



Lemma TLVal_open: forall m B X,
  (open_exp_wrt_typ_rec m (t_tvar_f X) (TLVal B) ) =  TLVal (open_typ_wrt_typ_rec m (t_tvar_f X) B).
Proof.
  introv. gen m.
  inductions B;intros; try solve[unfold TLVal
   in *; eauto].
  -
    simpl; eauto.
    destruct(lt_eq_lt_dec n m); eauto.
    destruct(s); eauto.
  -
    simpl.
    forwards* h1:IHB2 m.
    elia.
    rewrite h1.
    auto.
  - 
    simpl.
    forwards* h1:IHB2 X (m).
    forwards* h2:IHB1 X (m).
    fequal; auto.
  -
    simpl.
    forwards* h1:IHB2 (S m).
    elia.
    rewrite h1.
    auto.
  -
    simpl.
    forwards* h1:IHB m.
    elia.
    rewrite h1.
    auto. 
Qed. 



(* Lemma TLVal_no_fv: forall A,
 termfv_exp (TLVal A) = empty.
Proof.
  introv.
  inductions A; simpl; eauto.
  forwards* h1:IHA1.
  forwards* h2:IHA2.
  rewrite h1. rewrite h2.
Qed. *)


Lemma TLVal_value: forall A,
 lc_typ A ->
 value (TLVal A).
Proof.
 introv lc.
 inductions lc; simpl; eauto.
 -
    forwards* h2: value_lc IHlc2.
    apply value_f;eauto.
    apply fvalue_abs; auto.
    apply lc_e_abs; intros;eauto.
    forwards* h3:  open_exp_wrt_exp_lc_exp (e_var_f x) h2.
    rewrite h3; auto.
  -
    apply value_tabs; auto.
    apply lc_e_tabs; intros; auto.
    unfold open_exp_wrt_typ.
    rewrite TLVal_open; auto.
    forwards* h2: H0 X; auto.
    unfold open_typ_wrt_typ in h2.
    forwards*: value_lc h2.
Qed.



Lemma TLVal_lc: forall A,
 lc_typ A ->
 lc_exp (TLVal A).
Proof.
  introv LC.
  forwards* h1: TLVal_value LC.
  forwards*: value_lc h1.
Qed.



Lemma casting_prv_value: forall v A v',
    value v -> Cast v A v' -> value v'.
Proof with eauto with lngen.
  introv Val Red.
  induction Red; auto; inverts Val;
  try solve[forwards* h1: ord_lc H0; forwards*: TLVal_value h1];
  try solve[simpl;inverts* H2];
  try solve[forwards*: 
  algo_sub_lc H3];
  try solve[forwards*: 
  algo_sub_lc H1];
  try solve[forwards*: 
  algo_sub_lc H];
  try solve[forwards*: 
  algo_sub_lc H0];
  try solve[ inverts H0 as h1;
  inverts h1];
  try solve[ inverts H1 as h1;
  inverts h1];eauto;
  try solve[ inverts H2 as h1;
  inverts h1];eauto.
Qed.


(* #[export] *) Hint Immediate value_merge_l_inv value_merge_r_inv value_lc casting_prv_value : core.



(* ********************************************************************** *)
(** ** Regularity of relations: term related *)



Lemma fvalue_lc : forall v,
    fvalue v -> lc_exp v.
Proof.
  intros v H.
  inductions H; eauto.
Qed.


Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  inductions H; eauto.
  forwards*: fvalue_lc H.
Qed.
