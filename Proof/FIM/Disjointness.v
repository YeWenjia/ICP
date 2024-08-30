(* Require Import LibTactics. *)
Require Import LibTactics.
Require Import Lia.
Require Export
            SubtypingInversion.
Require Import Coq.Program.Equality.
(* Subtyping must be the last one to import to keep the gather_atom definition *)


(***************************** disjointness axiom ***********************************)

Ltac try_disjoint_axiom_constructors :=
  match goal with
  | |- disjoint_axiom t_int (t_ref _) => applys Dax_Intref
  | |- disjoint_axiom t_int (t_arrow _ _) => applys Dax_intArr
  | |- disjoint_axiom t_int (t_forall _ _) => applys Dax_intForall
  | |- disjoint_axiom (t_arrow _ _) (t_ref _) => applys Dax_Arrref
  | |- disjoint_axiom (t_arrow _ _) (t_forall _ _) => applys Dax_arrForall
  | |- disjoint_axiom (t_rcd _ _) (t_rcd _ _) => applys Dax_rcd
  | |- disjoint_axiom (t_arrow _ _) (t_rcd _ _) => applys Dax_arrRcd
  | |- disjoint_axiom (t_ref _) (t_rcd _ _) => applys Dax_refRcd
  end.

(* #[export] *) Hint Extern 1 (disjoint_axiom _ _) => try_disjoint_axiom_constructors : core.

(* #[export] *) Hint Extern 0 => try match goal with
                               | [ H: topLike _ _ |- _ ] =>
                                 inverts H; fail
                               | [ H: disjoint_axiom _ _ |- _ ] =>
                                 inverts H; fail
                              end : FalseHd.


Lemma disjoint_axiom_symm: forall A B,
    disjoint_axiom A B ->
    disjoint_axiom B A.
Proof.
  introv H.
  induction* H.
Qed.

(* #[export] *) Hint Immediate disjoint_axiom_symm : core.




Ltac try_disjoint_constructors :=
  match goal with
  |  H: topLike ?A |- disjoint _ ?A ?B => applys D_topL H
  |  H: topLike ?B |- disjoint _ ?A ?B => applys D_topR H
  |  H: disjoint_axiom ?A ?B |- disjoint _ ?A ?B => applys D_axiom H
  |  |- disjoint _ t_int (t_arrow _ _) => applys D_axiom; try applys Dax_intArr
  |  |- disjoint _ (t_arrow _ _) t_int => applys D_axiom; try applys Dax_arrInt
  |  |- disjoint _ t_int (t_ref _) => applys D_axiom; try applys Dax_Intref
  |  |- disjoint _ (t_ref _ ) t_int => applys D_axiom; try applys Dax_refInt
  (* too many cases for disjoint axioms... *)
  (* the following two lines try to cover all disjoint axioms cases *)
  |  |- _ => applys D_axiom; [ | | try_disjoint_axiom_constructors]
  |  |- disjoint _ (t_and _ _) _ => applys D_andL
  |  |- disjoint _ _ (t_and _ _) => applys D_andR
  |  H: spl ?A ?A1 ?A2 |- disjoint _ ?A _ => applys D_andL H
  |  H: spl ?A ?A1 ?A2 |- disjoint _ _ ?A => applys D_andR H
  |  |- disjoint _ (t_forall _ _) _ => applys D_forall; try eassumption
  |  |- disjoint _ _ (t_forall _ _) => applys D_forall; try eassumption
  |  |- disjoint _ (t_arrow _ _) _ => applys D_ArrArr
  |  |- disjoint _ _ (t_arrow _ _) => applys D_ArrArr
  (* |  H: ?l1 <> ?l2 |- disjoint _ (t_rcd ?l1 _) (t_rcd ?l2 _) => applys D_ax; try applys Dax_rcdNeq H *)
  (* |  |- disjoint _ (t_rcd _ _) (t_rcd _ _) => applys D_rcdEq *)
  |  |- disjoint _ (t_tvar_f _) _ => applys D_varL
  |  |- disjoint _ _ (t_tvar_f _) => applys D_varR
  end.

(* #[export] *) Hint Extern 0 (disjoint _ _ _) => try_disjoint_constructors : core.


Ltac split_toplike :=
  match goal with
  | H1: spl ?A _ _, H2: topLike ?A |- _ => forwards (?&?): topLike_split_inv H2 H1
  end
.
(* 
Ltac solve_TWell_by_split :=
  match goal with
  | H1 : TWell ?D ?B, H2 : spl ?B ?A _ |- _ => forwards(?&?): TWell_spl H1 H2; assumption
  | H1 : TWell ?D ?B, H2 : spl ?B _ ?A |- _ => forwards(?&?): TWell_spl H1 H2; assumption
  | H1 : TWell ?D (t_arrow ?A _) |- TWell ?D (t_arrow ?A _) => forwards(?&?): TWell_spl H1
  | H1 : TWell ?D (t_forall ?A _) |- TWell ?D (t_forall ?A _) => forwards(?&?): TWell_spl H1
  | H1 : TWell ?D _ |- TWell ?D _ => forwards(?&?): TWell_spl H1
  end.

(* #[export] *) Hint Extern 1 (TWell _ _) => solve_TWell_by_split : core. *)



Lemma disjoint_andl_inv: forall D A A1 A2 B,
    spl A A1 A2 -> disjoint D A B -> disjoint D A1 B /\ disjoint D A2 B.
Proof with (split_unify).
  introv Hspl Hdis. gen A1 A2.
  induction Hdis; intros;
  try solve[forwards* h1: split_ord_false Hspl; inverts h1];
  eauto...
  - inverts Hspl; try solve[inverts* H].
  - forwards: IHHdis1; try eassumption.
    forwards: IHHdis2; try eassumption; jauto.
  -
    forwards h1: IHHdis H4.
    inverts h1 as h1 h2.
    split.
    apply D_ArrArr; auto.
    apply D_ArrArr; auto.
  - split; try_disjoint_constructors; auto; intros X HN;
      instantiate ( 1 := (L `union` L0) ) in HN;
      instantiate_cofinites_with X;
      forwards* (?&?): H0 H7.
  -
     forwards h1: IHHdis H3.
    inverts h1 as h1 h2.
    split.
    apply D_rcdeq; auto.
    apply D_rcdeq; auto.
Qed.


Lemma disjoint_andr_inv: forall D A A1 A2 B,
    spl A A1 A2 -> disjoint D B A -> disjoint D B A1 /\ disjoint D B A2.
Proof with (split_unify).
  introv Hspl Hdis. gen A1 A2.
  induction Hdis; intros;
  try solve[forwards* h1: split_ord_false Hspl; inverts h1]; eauto...
  -
    inverts Hspl; try solve[inverts* H].
  - forwards: IHHdis1; try eassumption.
    forwards: IHHdis2; try eassumption; jauto.
  -
    forwards h1: IHHdis H4.
    inverts h1 as h1 h2.
    split.
    apply D_ArrArr; auto.
    apply D_ArrArr; auto.
  - split; try_disjoint_constructors; auto; intros X HN;
      instantiate ( 1 := (L `union` L0) ) in HN;
      instantiate_cofinites_with X;
      forwards* (?&?): H0 H7.
  -
    forwards h1: IHHdis H3.
    inverts h1 as h1 h2.
    split.
    apply D_rcdeq; auto.
    apply D_rcdeq; auto.
Qed.



(* #[export] *) Hint Extern 0 (ord _) =>
match goal with
| H: ord (t_arrow _ ?A) |- ord ?A => inverts H
end : core.



Lemma disjoint_arr_inv: forall D A1 A2 B1 B2,
    disjoint D (t_arrow A1 A2) (t_arrow B1 B2) -> disjoint D A2 B2.
Proof with (split_unify; auto with LcHd SubHd).
  introv H.
  inductions H...
  -
    inverts* H.
  -
    applys* D_andL.
  - applys* D_andR.
Qed.



Lemma disjoint_rcd_inv: forall D i A2 B2,
    disjoint D (t_rcd i A2) (t_rcd i B2) -> disjoint D A2 B2.
Proof with (split_unify; auto with LcHd SubHd).
  introv H.
  inductions H...
  -
    inverts* H.
    exfalso; apply H1; auto.
  -
    applys* D_andL.
  - applys* D_andR.
Qed.


Lemma open_comm_2: forall A n n0 X Y,
n0 <= n ->
lc_typ X ->
open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A) =
open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A).
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
      assert(~n0 - 0 < n0). lia. contradiction.
      apply open_typ_wrt_typ_rec_degree_typ_wrt_typ.
        apply degree_typ_wrt_typ_of_lc_typ in H0.
        apply degree_typ_wrt_typ_O. auto.
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
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A1)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A2)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H1. rewrite H2. auto.
   -  (* and *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A1)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A2)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A2))). eauto.
      rewrite H1. rewrite H2. auto.
   -  (* rcd *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
      rewrite H1. auto.
   -  (* forall *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A1)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A1))). eauto.
      assert((open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) (open_typ_wrt_typ_rec (S (S n)) X A2)) =
        (open_typ_wrt_typ_rec (S n) X (open_typ_wrt_typ_rec (S n0) (t_tvar_f Y) A2))).
      apply IHA2. lia. auto. rewrite H1. rewrite H2. auto.
  -  (* rcd *)
      assert((open_typ_wrt_typ_rec n0 (t_tvar_f Y) (open_typ_wrt_typ_rec (S n) X A)) =
        (open_typ_wrt_typ_rec n X (open_typ_wrt_typ_rec n0 (t_tvar_f Y) A))). eauto.
      rewrite H1. auto.
Qed.


Lemma open_spl_2: forall A B C L, (forall X, X `notin` L -> spl (A -^ X) (B -^ X) (C -^ X)) -> forall Y, lc_typ Y -> spl (A ^-^ Y) (B ^-^ Y) (C ^-^ Y).
Proof.
  intros. pick fresh X.
    assert(spl (A -^ X) (B -^ X) (C -^ X)). auto. clear H.
      dependent induction H1;auto.
  -  destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
      simpl in Fr.
      forwards*:open_typ_wrt_typ_rec_inj H3; try solve_notin.
      forwards*:open_typ_wrt_typ_rec_inj H4; try solve_notin. subst.
    apply Sp_and.
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (A1 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H1. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H1.
    assert(degree_typ_wrt_typ 0 (A2 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto.
  -    destruct C;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x0. inversion x0. inversion x0.
    destruct B;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. unfold open_typ_wrt_typ. simpl.
      simpl in Fr.
      forwards*:open_typ_wrt_typ_rec_inj H5; try solve_notin.
      forwards*:open_typ_wrt_typ_rec_inj H7; try solve_notin.
      subst.
    apply Sp_arrow.
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (B1 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto.
    forwards*: IHspl A2 B2 C2 X.
    simpl in *; eauto.
  -    destruct C;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x0. inversion x0. inversion x0.
    destruct B;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. unfold open_typ_wrt_typ. simpl.
      simpl in Fr.
      forwards*:open_typ_wrt_typ_rec_inj H6; try solve_notin.
      forwards*:open_typ_wrt_typ_rec_inj H8; try solve_notin.
      subst.
    apply Sp_forall with (union L0 (union L (singleton X))).
    apply degree_typ_wrt_typ_of_lc_typ in H. apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H.
    assert(degree_typ_wrt_typ 0 (B1 ^-^ Y)). apply degree_typ_wrt_typ_open_typ_wrt_typ. auto.
    apply degree_typ_wrt_typ_of_lc_typ in H0. auto.
    apply lc_typ_of_degree. auto. intros.
    assert(open_typ_wrt_typ_rec 1 Y A2 -^ X0 = A2 -^ X0 ^-^ Y).
    apply open_comm_2. auto. auto. rewrite H4.
    assert(open_typ_wrt_typ_rec 1 Y B2 -^ X0 = B2 -^ X0 ^-^ Y).
    apply open_comm_2. auto. auto. rewrite H5.
    assert(open_typ_wrt_typ_rec 1 Y C4 -^ X0 = C4 -^ X0 ^-^ Y).
    apply open_comm_2. auto. auto. rewrite H7.
    apply H1 with X0 X. auto. auto.
    assert(X<>X0). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A2 -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ A2)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[A2]])). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B2 -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ B2)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B2]])). auto.
    assert(AtomSetImpl.Subset (typefv_typ (C4 -^ X0)) (typefv_typ (t_tvar_f X0)`union`  typefv_typ C4)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[C4]])). auto.
    assert(X `notin` [[A2 -^ X0]]). auto.
    assert(X `notin` [[B2 -^ X0]]). auto.
    assert(X `notin` [[C4 -^ X0]]). auto. auto.
    apply open_comm. auto.
    apply open_comm. auto.
    apply open_comm. auto.
  -
  destruct C;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x0. inversion x0. inversion x0.
destruct B;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
subst. unfold open_typ_wrt_typ. simpl.
  simpl in Fr.
  apply Sp_rcd.
  forwards*: IHspl A B C.
Qed.


Lemma open_spl_all: forall A B C X, spl (A -^ X) B C -> exists D1 D2, forall Y, lc_typ Y -> spl (A ^-^ Y) (D1 ^-^ Y) (D2 ^-^ Y).
Proof.
  intros. apply open_spl in H. destruct H. destruct H.
    exists x x0. apply open_spl_2 with {}. auto.
Qed.




Lemma topLike_rename : forall A X Y,
    topLike (A -^ X) -> 
    topLike (A -^ Y).
Proof with (simpl in *; eauto).
  introv Lc.
  inductions Lc; 
  try solve[unfold open_typ_wrt_typ in *; simpl in *;
  inverts Lc;eauto ].
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
     unfold open_typ_wrt_typ. simpl; auto.
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. 
    assert(topLike (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A1)).
    apply IHLc1 with X; auto. 
    unfold open_typ_wrt_typ; auto. 
    assert(topLike (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A2)).
    apply IHLc2 with X; auto.
    eauto.
  -
      destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. 
    assert(topLike (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A2)) as h1.
    apply IHLc with X; auto. 
    forwards*: lc_typ_rename_2 H.
  (* -    
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. 
    apply TL_ref.
    apply IHLc with X; auto.  *)
  -
     destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. simpl in H0. simpl in H.
    forwards*: lc_typ_rename_2 Y H.
      apply TL_all with (union L (union (singleton X) (singleton Y)));
       intros; auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f Y) A2 -^ X0) = (A2 -^ X0) -^ Y) as h1.
      apply open_comm. auto. rewrite h1.
    assert([X ~~> t_tvar_f Y] (A1 -^ X)  = [X ~~> t_tvar_f Y] (A1) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)) as h2.
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    apply H1 with X0 X; auto. 
      apply open_comm. auto. 
  -
      destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl. subst. 
    assert(topLike (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A)) as h1.
    apply IHLc with X; auto. 
    eauto.
  - (* ref *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
  unfold open_typ_wrt_typ. simpl. subst. 
  assert(topLike (open_typ_wrt_typ_rec 0 (t_tvar_f Y) A)) as h1.
  apply IHLc with X; auto. 
  eauto.
Qed.


Fixpoint subst_env  (u : typ) (z : atom)  (Gamma : ctx) :=
  match Gamma with
    | nil => nil
    | (x, (TyDis d)) :: tl => (x, TyDis (typsubst_typ u z d)) ::
                           (subst_env u z tl)
    | (x, (TermV ty)) :: tl => (x, TermV (typsubst_typ u z ty)) :: (subst_env u z tl)
  end.



Lemma wfenv_app_l : forall E F , WFEnv (E ++ F) -> WFEnv E.
Proof.
  intros E; induction E; intros; auto.
  inversion H;
  subst.
  eapply WFPushV; auto.
  now apply IHE with (F := F).
  apply WFPushT; auto.
  now apply IHE with (F := F).
Qed.  

Lemma wfenv_app_r : forall E F , WFEnv (E ++ F) -> WFEnv F.
Proof.
  intros E.
  induction E; intros.
  - rewrite app_nil_l in H.
    auto.
  - inversion H; subst;
    apply (IHE _ H2).    
Qed.

Lemma wfenv_remove : forall E F G ,
                    WFEnv (E ++ G ++ F) -> WFEnv (E ++ F).
Proof.
  intros.
  inductions E; simpl in *;eauto.
  -
    apply wfenv_app_r in H; auto.
  -
    inverts* H.
Qed.




Lemma TCW_binds_2: forall A0 C D E X Y X1, X `notin` (typefv_typ_range D) -> 
binds X1 (TyDis  A0) (E ++ [(X,TyDis C)] ++ D)
-> 
X <> X1
-> 
binds X1 (TyDis  (typsubst_typ (t_tvar_f Y) X A0)) (subst_env (t_tvar_f Y) X E ++ [(Y,TyDis C)] ++ D).
Proof.
  intros.
    apply binds_app_1 in H0. destruct H0. 
    -
    induction E;auto. inversion H0;subst. 
    unfold subst_env.
    simpl_env in *.
    fold subst_env.
    eauto.
    destruct a.
    destruct t.
    +
      analyze_binds H0.
      *
      inverts BindsTacVal.
      unfold subst_env.
      simpl_env in *.
      fold subst_env.
      eauto.
      *
      unfold subst_env.
      simpl_env in *.
      fold subst_env.
      forwards* h1: IHE.
    +
      unfold subst_env.
      simpl_env in *.
      fold subst_env.
      forwards*: IHE.
    -
      analyze_binds H0.
      induction D. simpl. auto. 
      destruct a. simpl.
      inverts  BindsTac as h1.
      inverts h1.
      simpl in *.
      rewrite typsubst_typ_fresh_eq; auto.
      destruct t.
      simpl in *.
      forwards* h2: IHD; eauto.
      simpl_env in *.
      rewrite_env((subst_env (t_tvar_f Y) X E ++
      Y ~ TyDis C) ++ D) in h2.
      forwards*: binds_weaken (a ~ TyDis t) h2.
      simpl_env in *; eauto.
      simpl in *.
      forwards* h2: IHD; eauto.
      rewrite_env((subst_env (t_tvar_f Y) X E ++
      Y ~ TyDis C) ++ D) in h2.
      forwards*: binds_weaken (a ~ TermV t) h2.
      simpl_env in *; eauto.
Qed.



Lemma TCW_binds_3: forall A0 C D E X J X1, X `notin` (typefv_typ_range D) -> lc_typ J -> binds X1 (TyDis A0) (E ++ [(X,TyDis C)] ++ D)
-> X <> X1-> binds X1 (TyDis (typsubst_typ J X A0)) ( subst_env J X E  ++ D).
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
      inverts BindsTacVal.
      unfold subst_env.
      simpl_env in *.
      fold subst_env.
      eauto.
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


Lemma disjoint_subst_alternative:forall n X Y (A B C:typ) D E,
size_typ A + size_typ B <= n
-> X `notin`  (union (Metatheory.union [[A]] [[B]])  (typefv_typ_range D))
-> Y `notin` (Metatheory.union (dom D) (dom E))
-> disjoint (E ++ [(X , TyDis C)] ++ D) (A -^ X) (B -^ X)
-> WFEnv (E ++ [(X , TyDis C)] ++ D) 
-> disjoint (subst_env (t_tvar_f Y) X E ++ [(Y , TyDis C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros n. induction n. intros. destruct A;inversion H.
  intros. dependent induction H2.
  - (* axiom *)
    assert(disjoint_axiom (A -^ Y) (B -^ Y)) as h1; eauto.
    inductions H2;eauto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    + 
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
    +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  +
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
  unfold open_typ_wrt_typ. simpl. subst. auto.
  - (* topl *)
    assert(topLike (A -^ Y)) as h1. apply topLike_rename with X; auto. 
    auto.
  - (* topr *)
     assert(topLike (B -^ Y)) as h1. apply topLike_rename with X; auto. 
    auto.
  -
    clear IHdisjoint1 IHdisjoint2.
    forwards h1: open_spl H2. 
    lets(t1&t2& h2): h1.
    assert(spl (A -^ X) (t1 -^ X) (t2 -^ X)) as h3.  auto.
    assert(spl (A -^ Y) (t1 -^ Y) (t2 -^ Y)) as h4. auto.
    pick fresh Z.
    assert(spl (A -^ Z) (t1 -^ Z) (t2 -^ Z)). auto.
    forwards h5: split_unique H2 h3. destruct h5;subst.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y, TyDis C)] ++ D) (t1 -^ Y) (B -^ Y)) as h6.
    apply IHn. 
    apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H2. rewrite size_typ_open_typ_wrt_typ_var in H2. lia.
    assert(X `notin` [[(A -^ Z)]]) as h7. assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ A)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[A]])). auto. auto.
    forwards h8: split_fv h7 H4. destruct h8.
    assert(AtomSetImpl.Subset (typefv_typ t1) (typefv_typ (t1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto.
    auto.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y, TyDis C)] ++ D) (t2 -^ Y) (B -^ Y)).
    apply IHn. apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H5. rewrite size_typ_open_typ_wrt_typ_var in H5. lia.
    assert(X `notin` [[(A -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ A)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[A]])). auto. auto.
    forwards h9: split_fv H5 H4. destruct h9.
    assert(AtomSetImpl.Subset (typefv_typ t2) (typefv_typ (t2 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto. auto.
    auto.
  -
    clear IHdisjoint1 IHdisjoint2.
    forwards h1: open_spl H2. 
    lets(t1&t2& h2): h1.
    assert(spl (B -^ X) (t1 -^ X) (t2 -^ X)) as h3.  auto.
    assert(spl (B -^ Y) (t1 -^ Y) (t2 -^ Y)) as h4. auto.
    pick fresh Z.
    assert(spl (B -^ Z) (t1 -^ Z) (t2 -^ Z)). auto.
    forwards h5: split_unique H2 h3. destruct h5;subst.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y, TyDis C)] ++ D) (A -^ Y) (t1 -^ Y) ) as h6.
    apply IHn. 
    apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H2. rewrite size_typ_open_typ_wrt_typ_var in H2. lia.
    assert(X `notin` [[(B -^ Z)]]) as h7. assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards h8: split_fv h7 H4. destruct h8.
    assert(AtomSetImpl.Subset (typefv_typ t1) (typefv_typ (t1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto.
    auto.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y, TyDis C)] ++ D) (A -^ Y) (t2 -^ Y) ).
    apply IHn. apply split_decrease_size in H2. destruct H2.
    rewrite size_typ_open_typ_wrt_typ_var in H5. rewrite size_typ_open_typ_wrt_typ_var in H5. lia.
    assert(X `notin` [[(B -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards h9: split_fv H5 H4. destruct h9.
    assert(AtomSetImpl.Subset (typefv_typ t2) (typefv_typ (t2 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual.
    auto. auto. auto. auto.
    auto.
  - (* arrow arrow *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y,TyDis C)] ++ D) (A4 -^ Y) (B4 -^ Y)). apply IHdisjoint; intros; auto. auto.
      simpl in H. simpl. lia. simpl in H0. auto. auto. auto. auto. unfold open_typ_wrt_typ. simpl. subst. auto.
  - (* varl *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x;subst.
    assert(A0 = C) as h2.
    assert(binds X (TyDis C) (E ++ X ~ TyDis C ++ D)) as h1; eauto.
    forwards* h3: binds_unique H2 h1; eauto.
    inverts* h3.
    inverts h2.
    assert((B -^ Y) = (typsubst_typ (t_tvar_f Y) X (B -^ X))) as h4.
    unfold open_typ_wrt_typ.
    rewrite <- typsubst_typ_intro_rec; auto.
    assert((typsubst_typ (t_tvar_f Y) X C) = C) as h5.
    rewrite typsubst_typ_fresh_eq; auto.
    forwards h6: wfenv_app_r H4.
    inverts* h6.
    apply D_varL with C; auto.
    rewrite h4.
    forwards : 
    algo_subst_2 X Y H3.
    rewrite h5 in H5.
    auto.
    inversion x. subst.
    assert(X<>X1). simpl in H0. auto.
    assert((t_tvar_f X1 -^ Y) = t_tvar_f X1) as h1.
    unfold open_typ_wrt_typ; simpl; auto.
    rewrite h1.
    assert(algo_sub (typsubst_typ (t_tvar_f Y) X A0) (B -^ Y)/\binds X1 (TyDis (typsubst_typ (t_tvar_f Y) X A0)) ((subst_env (t_tvar_f Y) X E) ++ [(Y,TyDis C)] ++ D)) as h2.
    split.
    forwards h3: 
    algo_subst_2 X Y H3; auto.
    assert((B -^ Y) = (typsubst_typ (t_tvar_f Y) X (B -^ X))) as h4.
    unfold open_typ_wrt_typ.
    rewrite <- typsubst_typ_intro_rec; auto.
    rewrite h4; auto.
    forwards* h5: TCW_binds_2 H2.
    inverts* h2.
  -
    (* varr *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x;subst.
    assert(A0 = C) as h2.
    assert(binds X (TyDis C) (E ++ X ~ TyDis C ++ D)) as h1; eauto.
    forwards* h3: binds_unique H2 h1; eauto.
    inverts* h3.
    inverts h2.
    assert((A -^ Y) = (typsubst_typ (t_tvar_f Y) X (A -^ X))) as h4.
    unfold open_typ_wrt_typ.
    rewrite <- typsubst_typ_intro_rec; auto.
    assert((typsubst_typ (t_tvar_f Y) X C) = C) as h5.
    rewrite typsubst_typ_fresh_eq; auto.
    forwards h6: wfenv_app_r H4.
    inverts* h6.
    apply D_varR with C; auto.
    rewrite h4.
    forwards : 
    algo_subst_2 X Y H3.
    rewrite h5 in H5.
    auto.
    inversion x. subst.
    assert(X<>X1). simpl in H0. auto.
    assert((t_tvar_f X1 -^ Y) = t_tvar_f X1) as h1.
    unfold open_typ_wrt_typ; simpl; auto.
    rewrite h1.
    assert(algo_sub (typsubst_typ (t_tvar_f Y) X A0) (A -^ Y)/\binds X1 (TyDis (typsubst_typ (t_tvar_f Y) X A0)) ((subst_env (t_tvar_f Y) X E) ++ [(Y,TyDis C)] ++ D)) as h2.
    split.
    forwards h3: 
    algo_subst_2 X Y H3; auto.
    assert((A -^ Y) = (typsubst_typ (t_tvar_f Y) X (A -^ X))) as h4.
    unfold open_typ_wrt_typ.
    rewrite <- typsubst_typ_intro_rec; auto.
    rewrite h4; auto.
    forwards* h5: TCW_binds_2 H2.
    inverts* h2.
  - (*forall forall*)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    subst.
    assert(disjoint (E ++ X ~ TyDis C ++ D) (t_forall A3 A4 -^ X) (t_forall B3 B4 -^ X)) as h1.
    unfold open_typ_wrt_typ. simpl. subst. eauto.
    unfold open_typ_wrt_typ. simpl.
    apply D_forall with (union (union (union (union (Metatheory.union (Metatheory.union L (Metatheory.singleton Y)) (Metatheory.singleton X)) (dom D)) (dom E)) [[A3]]) [[B3]]);intros; auto.
  assert((open_typ_wrt_typ_rec 1 (t_tvar_f Y) A4 -^ X0) = (A4 -^ X0) -^ Y) as h2.
    apply open_comm. auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f Y) B4 -^ X0) = (B4 -^ X0) -^ Y) as h3.
    apply open_comm. auto.
    rewrite h2. rewrite h3.
    assert((X0, TyDis (t_and (A3 -^ Y) (B3 -^ Y))) :: subst_env (t_tvar_f Y) X E
      = subst_env (t_tvar_f Y) X ((X0,TyDis (t_and (A3 -^ X) (B3 -^ X))):: E) ).
    simpl.
    assert([X ~~> t_tvar_f Y] (A3 -^ X)  = [X ~~> t_tvar_f Y] (A3) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)) as h4.
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite h4.
    assert([X ~~> t_tvar_f Y] (B3 -^ X)  = [X ~~> t_tvar_f Y] (B3) ^-^  [X ~~> t_tvar_f Y] (t_tvar_f X)) as h5.
    apply typsubst_typ_open_typ_wrt_typ_rec. auto.
    rewrite h5.
    assert([X ~~> t_tvar_f Y] A3 = A3) as h6.
    apply typsubst_typ_fresh_eq. simpl in H0. auto.
    assert([X ~~> t_tvar_f Y] B3 = B3) as h7.
    apply typsubst_typ_fresh_eq. simpl in H0. auto.
    rewrite h6. rewrite h7.
    assert([X ~~> t_tvar_f Y] (t_tvar_f X) = t_tvar_f Y ) as h8.
    simpl. unfold "==". destruct(EqDec_eq_of_X X X);subst;auto.
    contradiction.
    rewrite h8. auto.
    assert(disjoint
  (subst_env (t_tvar_f Y) X ((X0,TyDis (t_and (A3 -^ X) (B3 -^ X))) :: E) ++
   [(Y, TyDis C)] ++ D) ((A4 -^ X0) -^ Y) ((B4 -^ X0) -^ Y)) as h9.
   apply IHn. rewrite size_typ_open_typ_wrt_typ_var. rewrite size_typ_open_typ_wrt_typ_var. simpl in H. lia.
    assert(X <> X0). auto. assert(X `notin` [[(t_tvar_f X0)]]). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ A4)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X0)) (typefv_typ (t_tvar_f X0) `union` typefv_typ B4)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    simpl in H0.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[A4]])). auto.
    assert(X `notin` [[A4 -^ X0]]). auto.
    assert(X `notin` (Metatheory.union [[t_tvar_f X0]] [[B4]])). auto.
    assert(X `notin` [[B4 -^ X0]]). auto.
    auto. simpl.
    assert(X0 <> Y). auto. auto.
    assert(disjoint
       ((X0,
        TyDis (t_and (open_typ_wrt_typ_rec 0 (t_tvar_f X) A3)
          (open_typ_wrt_typ_rec 0 (t_tvar_f X) B3))) :: E ++ [(X ,TyDis C)] ++ D)
       (open_typ_wrt_typ_rec 1 (t_tvar_f X) A4 -^ X0)
       (open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0)).
    auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f X) A4 -^ X0) = (A4 -^ X0) -^ X) as h10.
    apply open_comm. auto.
    assert((open_typ_wrt_typ_rec 1 (t_tvar_f X) B4 -^ X0) = (B4 -^ X0) -^ X) as h11.
    apply open_comm. auto.
    rewrite h10 in H8. rewrite h11 in H8. auto.
    simpl_env.
    assert(AtomSetImpl.Subset (typefv_typ (A3 -^ X)) (typefv_typ (t_tvar_f X) `union` typefv_typ A3)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(AtomSetImpl.Subset (typefv_typ (B3 -^ X)) (typefv_typ (t_tvar_f X) `union` typefv_typ B3)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    simpl in H0.
    assert(X0 `notin` (Metatheory.union [[t_tvar_f X]] [[A3]])). auto.
    assert(X0 `notin` [[A3 -^ X]]). 
    auto.
    assert(X0 `notin` (Metatheory.union [[t_tvar_f X]] [[B3]])). auto.
    assert(X0 `notin` [[B3 -^ X]]). auto.
    apply WFPushV; auto.
    simpl_env in *.
    rewrite <- H7 in h9. auto.
    inverts H2 as h12 h13.
    forwards h14: lc_typ_rename_2 Y h12.
    forwards h15: lc_typ_rename_2 Y h13.
    eauto.
  - (* rcd *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y,TyDis C)] ++ D) (A -^ Y) (B -^ Y)). apply IHdisjoint. auto.
      simpl in H. lia. simpl in H. auto. auto. auto. auto. unfold open_typ_wrt_typ. simpl. subst. auto.
    auto.
      subst.
    unfold open_typ_wrt_typ. simpl. subst. auto.
  - (* ref *)
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n0 0). destruct s. inversion x0. inversion x0. inversion x0.
    assert(disjoint (subst_env (t_tvar_f Y) X E ++ [(Y,TyDis C)] ++ D) (A -^ Y) (B -^ Y)). apply IHdisjoint. auto.
      simpl in H. lia. simpl in H. auto. auto. auto. auto. unfold open_typ_wrt_typ. simpl. subst. auto.
    auto.
      subst.
    unfold open_typ_wrt_typ. simpl. subst. auto.
Qed.



Lemma disjoint_subst_0:forall X Y (A B C:typ) (D E:ctx),
X `notin`  (union (Metatheory.union [[A]] [[B]])  (typefv_typ_range D))
-> Y `notin` (Metatheory.union (dom D) (dom E))
-> disjoint (E ++ [(X , TyDis C)] ++ D) (A -^ X) (B -^ X)
-> WFEnv (E ++ [(X , TyDis C)] ++ D)
-> disjoint ((subst_env (t_tvar_f Y) X E) ++ [(Y ,TyDis C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros. forwards*: disjoint_subst_alternative H H0 H1. 
Qed.

Lemma disjoint_simpl_subst:forall X Y (A B C:typ) (D E:ctx),
X `notin`  (union (Metatheory.union [[A]] [[B]]) (typefv_typ_range D))
-> Y `notin`  (dom D)
-> disjoint ([(X , TyDis C)] ++ D) (A -^ X) (B -^ X)
-> WFEnv ([(X , TyDis C)] ++ D) 
-> disjoint ([(Y ,TyDis C)] ++ D) (A -^ Y) (B -^ Y).
Proof.
  intros.
    assert(nil ++ [(X ,TyDis C)] ++ D = [(X ,TyDis C)] ++ D ). auto.
    rewrite <- H3 in H1.
  apply disjoint_subst_0 with X Y A B C D nil in H1. auto. auto. auto.
  simpl; eauto.
Qed.



Lemma disjoint_forall_inv: forall D B1 C1 B2 C2,
  disjoint D (t_forall B1 C1) (t_forall B2 C2) ->
  WFEnv D -> 
  (forall X, X#D -> disjoint (cons (X, TyDis(t_and B1 B2)) D) (C1 -^ X) (C2 -^ X)).
Proof.
  intros. dependent induction H;subst; eauto.
    -
    inversion H.
    -
    inverts* H.
    pick fresh y.
    forwards*: H5 y.
    forwards*: topLike_rename y X H.
    -
    inverts* H.
    pick fresh y.
    forwards*: H5 y.
    forwards*: topLike_rename H;eauto.
  -
    inversion H;subst.
    assert(disjoint ((X, TyDis (t_and B1 B2)) :: G) (C0 -^ X) (C2 -^ X)). auto.
    assert(disjoint ((X, TyDis (t_and B1 B2)) :: G) (C3 -^ X) (C2 -^ X)). auto.
    assert(spl (C1 -^ X) (C0 -^ X) (C3 -^ X)). apply open_spl_2 with L. auto. auto. auto.
  -
    inversion H;subst.
    assert(disjoint ((X, TyDis (t_and B1 B2)) :: G) (C1 -^ X) (C0 -^ X)). auto.
    assert(disjoint ((X, TyDis (t_and B1 B2)) :: G) (C1 -^ X) (C3 -^ X)). auto.
    assert(spl (C2 -^ X) (C0 -^ X) (C3 -^ X)). apply open_spl_2 with L. auto. auto. auto.
  -
    pick fresh y.
    forwards* h1: H y.
    forwards*: disjoint_simpl_subst h1; auto.
    apply WFPushV; auto.
Qed.


Ltac disjoint_solve_by_inv :=
  match goal with
  | H: disjoint ?D (t_arrow _ ?A) (t_arrow _ ?B) |- disjoint ?D ?A ?B => applys~ disjoint_arr_inv H
  | H: disjoint ?D (t_rcd _ ?A) (t_rcd _ ?B) |- disjoint ?D ?A ?B => applys~ disjoint_rcd_inv H
  |  H: disjoint ?D (t_forall ?A _) ?B |- disjoint ?D (t_forall ?A _) ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D (t_arrow ?A _) ?B |- disjoint ?D (t_arrow ?A _) ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D ?B (t_and ?A _) |- disjoint ?D ?A ?B => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D ?B (t_and _ ?A) ?B |- disjoint ?D ?A _ => forwards (?&?): disjoint_andl_inv H
  |  H: disjoint ?D ?B (t_and _ _) ?B |- disjoint ?D ?A _ => forwards (?&?): disjoint_andl_inv H
  |  Hspl: spl ?A ?A1 _, H: disjoint ?D ?B ?A ?B |- disjoint ?D ?A1 ?B => forwards (?&?): disjoint_andl_inv Hspl H
  |  Hspl: spl ?A _ ?A1, H: disjoint ?D ?B ?A ?B |- disjoint ?D ?A1 ?B => forwards (?&?): disjoint_andl_inv Hspl H
  |  H: disjoint ?D ?B (t_forall ?A _) |- disjoint ?D ?B (t_forall ?A _) => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_arrow ?A _) |- disjoint ?D ?B (t_arrow ?A _) => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_and ?A _) |- disjoint ?D _ ?A => forwards (?&?): disjoint_andr_inv H
  |  H: disjoint ?D ?B (t_and _ ?A) |- disjoint ?D _ ?A => forwards (?&?): disjoint_andr_inv H
  |  Hspl: spl ?A ?A1 _, H: disjoint ?D ?B ?A |- disjoint ?D ?B ?A1 => forwards (?&?): disjoint_andr_inv Hspl H
  |  Hspl: spl ?A _ ?A1, H: disjoint ?D ?B ?A |- disjoint ?D ?B ?A1 => forwards (?&?): disjoint_andr_inv Hspl H
  end.

(* #[export] *) Hint Extern 1 (disjoint _ _ _) => disjoint_solve_by_inv : core.


Ltac inverts_for_disjointness :=
  match goal with
  | H: disjoint_axiom _ _ |- _ => inverts H
  | H: disjoint _ (t_and _ _) _ |- _ => forwards(?&?): disjoint_andl_inv H; clear H
  | H: disjoint _ _ (t_and _ _) |- _ => forwards(?&?): disjoint_andr_inv H; clear H
  | H: disjoint _ ?A _ , Hspl: spl ?A _ _ |- _ => forwards(?&?): disjoint_andl_inv Hspl H
  | H: disjoint _ _ ?A , Hspl: spl ?A _ _ |- _ => forwards(?&?): disjoint_andl_inv Hspl H
  | H: disjoint _ (t_arrow _ _) (t_arrow _ _) |- _ => forwards: disjoint_arr_inv H
  | H: disjoint _ (t_rcd _ _) (t_rcd _ _) |- _ => forwards: disjoint_rcd_inv H
  end.

(************************************************************************)



Lemma disjoint_narrowing : forall X Q F E P S T,
  X `notin` (union (dom F) (dom E)) ->
  disjoint (F ++ [(X, TyDis Q)] ++ E) S T ->
  algo_sub P Q ->
  disjoint (F ++ [(X, TyDis P)] ++ E) S T.
Proof with repeat ( try eassumption; auto).
  introv nin Hdis Hsub.
  inductions Hdis.
  - (* axiom *)
    applys~ D_axiom... 
  - applys~ D_topL...
  - applys~ D_topR...
  - (* spl L *)
    try_disjoint_constructors...
    applys* IHHdis1.
    applys* IHHdis2.
  - (* spl R *)
    try_disjoint_constructors...
    applys* IHHdis1.
    applys* IHHdis2.
  - (* arrow *)
    try_disjoint_constructors...
    applys* IHHdis.
  - (* fvar L *)
    destruct(X0 == X).
    inverts e.
    +
      analyze_binds H;  
      eauto.
      inverts BindsTacVal; eauto.
    +
      analyze_binds H;
      try solve[apply D_varL with A; auto].
  - (* fvar L *)
    destruct(X0 == X).
    inverts e.
    +
      analyze_binds H;  
      eauto.
      inverts BindsTacVal; eauto.
    +
      analyze_binds H;
      try solve[apply D_varR with A; auto].
  - (* forall *)
    apply D_forall with (union (singleton X) L); auto.
    intros Y HN; auto.
    instantiate_cofinites_with Y.
    rewrite_env (((Y,  TyDis (t_and A1 A2)) :: F) ++ X ~ TyDis P ++ E).
    applys* H0; auto. 
  -
    forwards*: IHHdis.
  - (* ref *)
    forwards*: IHHdis.
Qed.



Ltac narrow :=
  match goal with
    | H: disjoint ((?X,?A) :: ?D) ?B ?C |- disjoint ((?X,?A') :: ?D) ?B ?C => (
        rewrite_env ( nil ++ [(X, A')] ++ D );
        rewrite_env ( nil ++ [(X, A)] ++ D ) in H;
        applys~ disjoint_narrowing H;
        auto with SubHd LcHd
      )
    (* | H: TWell ((?X,?A) :: ?D) ?B |- TWell ((?X,?A') :: ?D) ?B => (
        rewrite_env ( nil ++ [(X, A')] ++ D );
        rewrite_env ( nil ++ [(X, A)] ++ D ) in H;
        applys~ TWell_bind_weakening_2 H;
        auto with SubHd LcHd
      ) *)
  end.



Lemma disjoint_eqv_context : forall X D A1 A2 B1 B2,
    X `notin` (dom D) ->
    disjoint ((X, TyDis A1) :: D) B1 B2 -> algo_sub  A2 A1 ->
    disjoint ((X, TyDis A2) :: D) B1 B2.
Proof.
  introv nin Hdis Hsub.
  narrow.
Qed.




Lemma disjoint_symm: forall D A B,
    disjoint D A B -> disjoint D B A.
Proof with auto with SubHd LcHd.
  introv H.
  inductions H...
  - try_disjoint_constructors; eauto.
  - try_disjoint_constructors; eauto.
  - apply D_forall with (union L (dom G)); auto.
    introv HN. forwards: H0 X; auto.
    applys~ disjoint_eqv_context H2...
    (* apply S_and with A1 A2... *)
Qed.


Lemma disjoint_covariance : forall D A B C,
    disjoint D A B -> algo_sub B C  -> disjoint D A C.
Proof with (split_unify; auto with LcHd SubHd).
  introv HD HS. gen D.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts HS; intros...
  -
    inverts HD.
    +
     inverts H1; try solve[apply D_axiom; auto].
    +
      eauto.
    + (* ref *)
      inverts H1 as h1.
      forwards* h2: toplike_sub h1.
    +
      assert(algo_sub (t_ref A0) (t_ref B0)) as h1.
      auto.
      forwards: IH h1 H2; auto.
      simpl in *.
      assert(size_typ A2 < size_typ A). 
      forwards*: split_decrease_size H1.
      lia.
      assert(algo_sub (t_ref A0) (t_ref B0)) as h2.
      auto.
      forwards: IH h1 H3; auto.
      simpl in *.
      assert(size_typ A3 < size_typ A). 
      forwards*: split_decrease_size H1.
      lia.
    +
      forwards: algo_sub_lc H.
      forwards h1: split_ord_false H1; auto. inverts h1.
    +
      assert(algo_sub (t_ref A0) (t_ref B0)) as h1.
      auto.
      forwards* h2: sub_transitivity H2 h1.
    +
      forwards*: IH H H4.
      simpl in *.
      lia.
  - (* andl *)
    forwards: algo_sub_lc H1; auto.
    assert(spl (t_and A0 B0) A0 B0). eauto.
    forwards h1: disjoint_andr_inv H3 HD. destruct h1. simpl in SizeInd.
    forwards: IH H1 H4; auto. lia. 
  - (* andr *)
    forwards: algo_sub_lc H1; auto.
    assert(spl (t_and A0 B0) A0 B0). eauto.
    forwards h1: disjoint_andr_inv H3 HD. destruct h1. simpl in SizeInd.
    forwards: IH H1 H5; auto. lia. 
  - (* arrow *)
    inverts HD; auto.
    +
      inverts H2; try solve[apply D_axiom; auto].
    +
      inverts H2.
      forwards: toplike_sub H1; auto.
      forwards*: algo_sub_lc H0.
    +
      forwards: algo_sub_lc H1.
      assert(algo_sub (t_arrow A0 C0) (t_arrow B0 D0)) as h1.
      auto.
      forwards: IH h1 H3; auto.
      simpl in *.
      assert(size_typ A2 < size_typ A). 
      forwards*: split_decrease_size H2.
      lia.
      assert(algo_sub (t_arrow A0 C0) (t_arrow B0 D0)) as h2.
      auto.
      forwards: IH h1 H4; auto.
      simpl in *.
      assert(size_typ A3 < size_typ A). 
      forwards*: split_decrease_size H2.
      lia.
    +
      forwards: algo_sub_lc H0.
      forwards: algo_sub_lc H1.
      inverts H2.
      forwards~ [?|?]: sub_inversion_split_l H1 H12.
      *
      assert(algo_sub (t_arrow A0 C) (t_arrow B0 D0)) as h1; auto.
      forwards h2:IH h1 H3; auto.
      assert(size_typ C < size_typ C0). 
      forwards*: split_decrease_size H12.
      simpl in *.
      lia.
      *
      assert(algo_sub (t_arrow A0 D1) (t_arrow B0 D0)) as h1; auto.
      forwards h2:IH h1 H4; auto.
      assert(size_typ D1 < size_typ C0). 
      forwards*: split_decrease_size H12.
      simpl in *.
      lia.
    +
      forwards h2:IH H1 H5; auto.
      simpl in *; lia.
    +
      applys* D_varL. auto with SubHd.
  - (* spl C *)
      applys~ D_andR H.  
      all: applys IH; try eassumption; elia; eauto.
  - (* forall *)
    inverts HD; auto.
    +
      inverts H2; try solve[
      apply D_axiom; auto].
    +
      assert(algo_sub (t_forall A1 A2) (t_forall B1 B2)); eauto.
    +
      forwards : algo_sub_lc H0.
      assert(ord (t_forall B1 B2)); auto.
      assert(algo_sub (t_forall A1 A2) (t_forall B1 B2)) as h1; auto.
      forwards h2: split_decrease_size H2; auto.
      inverts h2.
      forwards: IH h1 H3; auto.
      assert(size_typ A3 < size_typ A); eauto.
      simpl in *; lia.
      forwards: IH h1 H4; auto.
      assert(size_typ A4 < size_typ A); eauto.
      simpl in *; lia.
    +
      forwards: algo_sub_lc H0. 
      assert (Hord: ord (t_forall B1 B2)) by eauto.
      assert (HS: algo_sub (t_forall A1 A2) (t_forall B1 B2)) by eauto.
      forwards~ [Hi|Hi]: sub_inversion_split_l HS H2 Hord.
      * applys IH Hi; try eassumption; elia.
      * applys IH Hi; try eassumption; elia.
    +
      applys* D_varL. eauto with SubHd.
    +
      forwards: algo_sub_lc H0.
      apply D_forall with (union (union L L0) (dom D)); intros;auto. 
      assert(disjoint ((X, TyDis (t_and A0 B1)) :: D) (B0 -^ X) (A2 -^ X)).
      rewrite_env(disjoint (nil++[(X, TyDis (t_and A0 B1))]++D) (B0 -^ X) (A2 -^ X)).
      apply disjoint_narrowing with (t_and A0 A1); simpl; auto. 
      (* apply S_and with A0 A1; eauto. *)
      forwards h1: H1 X; auto.
      forwards*: IH h1 H4. 
      rewrite size_typ_open_typ_wrt_typ_var.
      rewrite size_typ_open_typ_wrt_typ_var.
      rewrite size_typ_open_typ_wrt_typ_var. simpl in SizeInd. lia.
   -
   inverts HD.
   + inverts H1; forwards: algo_sub_lc H0;auto.
   + forwards: algo_sub_lc H0; destruct H0; auto.
   + inverts* H1.
   + try_disjoint_constructors; auto.
     applys IH H2; try eassumption; elia; eauto.
     applys IH H3; try eassumption; elia. eauto.
   (* + applys* D_varl. auto with SubHd. *)
   (* + applys~ D_andl H1; applys IH; try eassumption; elia; eauto. *)
   + inverts H1. forwards~ [?|?]: sub_inversion_split_l H0 H8.
     * applys IH H2; try eassumption; elia. eauto.
     * applys IH H3; try eassumption; elia. eauto.
   +
    applys* D_varL. auto with SubHd.
   +
     forwards*: IH H0 H4.
     simpl in *; lia.
Qed.


Inductive varLike : atom -> typ -> Prop :=    
 | VA_self :
     forall X,
     varLike X (t_tvar_f X)
 | VA_andl : forall X (A B:typ),
     varLike X  A ->
     varLike X (t_and A B)
 | VA_andr : forall X (A B:typ),
     varLike X  B ->
     varLike X  (t_and A B).

(* #[export] *) Hint Constructors varLike : core.


Lemma bot_or_var: forall X A, algo_sub A (t_tvar_f X) -> varLike X A.
Proof.
  intros. induction A;try solve[inversion H;subst;auto;inversion H1;inversion H0];
  try solve[inverts* H].
Qed.


Lemma bot_or_var_2: forall X A B, varLike X B -> algo_sub A B -> varLike X A.
Proof.
  intros. induction H. 
  - 
    apply bot_or_var. auto.
  -
    inverts H0; try solve[inverts H1];
    try solve[inverts H2].
    inverts* H1.
  -
    inverts H0; try solve[inverts H1];
    try solve[inverts H2].
    inverts* H1.
Qed.


(* 
Lemma TW_in: forall D X A, TWell D A-> varLike X A -> exists B, binds X B D.
Proof.
  intros. induction H0. inversion H;subst. eauto.
    inversion H;subst. auto.
    inversion H;subst. auto.
Qed. *)


Lemma TCW_no_rec: forall D X A, WFEnv D -> varLike X A -> binds X (TyDis A) D -> False.
Proof.
  intros.
  inductions H; try solve[inverts* H1].
  -
    apply binds_cons_iff in H2. destruct H2.
    +
    destruct H2. subst.
    inverts* H3.
    assert(x `notin` [[A0]] ) as h1.
    eauto.
    assert(x `in` ([[A0]])).
    inductions H1; simpl in *;eauto.
    apply h1;auto.
    +
    auto.
  -
    analyze_binds H2.
Qed.


Lemma disjointSpec_complete_to_disjoint_axiom : forall A B,
     disjoint_axiom A B -> disjointSpec A B.
Proof with auto.
  intros A B Dis C S1 S2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  forwards [?|(?&?&?)]: ord_or_split C. 
  forwards*: algo_sub_lc S1.
  - inverts~ Dis;
    try solve[
      inversion S1;subst;auto; inversion S2;subst;auto;
      try solve[
      forwards: ord_lc H; 
      forwards h1:split_ord_false H0; auto;
      inverts h1];
      try solve[
      forwards: ord_lc H; 
      forwards h1:split_ord_false H2; auto;
      inverts h1];
      try solve[
      forwards: toplike_sub S1; auto
      ]
    ].
    inversion S1;subst;auto; inversion S2;subst;auto;
      try solve[
      forwards: ord_lc H; 
      forwards h1:split_ord_false H1; auto;
      inverts h1];
      try solve[
      forwards: ord_lc H; 
      forwards h1:split_ord_false H2; auto;
      inverts h1];
      try solve[
      forwards: toplike_sub S1; auto
      ];
      try solve[exfalso; apply H0; auto].
  - (* splittable C *)
    applys topLike_spl_combine H; applys* IH Dis; elia.
Qed.


Lemma disjoint_completeness: forall D A B,
   WFEnv D -> disjoint D A B -> disjointSpec A B.
Proof with intuition eauto.
  intros D A B WFE Dis C S1 S2. gen D.
  indTypSize (size_typ A + size_typ B + size_typ C).
  forwards [?|(?&?&?)]: ord_or_split C.
  forwards*: algo_sub_lc S1.
  -
    lets dis: Dis.
    inverts Dis.
    +
      forwards*: disjointSpec_complete_to_disjoint_axiom H0.
    +
      forwards*: toplike_sub S1.
    +
      forwards*: toplike_sub S2.
    +
      forwards h1: sub_inversion_split_l S1 H0 H.
      forwards h2: split_decrease_size H0. inverts h2 as h2 h3.
      inverts h1 as h4 h5.
      *
      forwards*: IH h4 S2... lia.
      *
      forwards*: IH h4 S2... lia.
    +
      forwards h1: sub_inversion_split_l S2 H0 H.
      forwards h2: split_decrease_size H0. inverts h2 as h2 h3.
      inverts h1 as h4 h5.
      *
      forwards*: IH S1 h4... lia.
      *
      forwards*: IH S1 h4... lia.
    +
      inversion S1;subst;auto;
      try solve[inversion S2;subst;auto].
      *
        inversion S2;subst;auto;
        try solve[inverts H1];
        try solve[
          forwards h1: split_ord_false H1; auto;
        inverts h1
        ].
        forwards h1:IH H6 H10 H0; auto.
        simpl in *; lia.
        forwards*: ord_lc H.
      *
        forwards h1: split_ord_false H1; auto.
        inverts h1.
    +
      inversion S1;subst;auto;
      try solve[inversion S2;subst;auto].
      *
        forwards h1: split_ord_false H2; auto.
        inverts h1.
      * 
        forwards h1: bot_or_var S2.
        forwards h2: bot_or_var_2 h1 H1. 
        forwards h3: TCW_no_rec H0; auto.
        inverts h3.
    +
      inversion S2;subst;auto;
      try solve[inversion S1;subst;auto].
      *
        forwards h1: split_ord_false H2; auto.
        inverts h1.
      *
        forwards h1: bot_or_var S1.
        forwards h2: bot_or_var_2 h1 H1.
        forwards h3: TCW_no_rec H0; auto.
        inverts h3.
    +
      inversion S1;subst;auto;
      try solve[
        forwards h1: split_ord_false H2; auto;
        inverts h1
      ]. 
      *
      inversion S2;subst;auto;
      try solve[forwards h1: split_ord_false H2; auto;
      inverts h1].
      forwards h1: ord_lc H; auto.
      inverts h1.
      apply TL_all with (
        union (union (union L (union L0 L1)) [[(t_and A1 A2)]] )
        (dom D)
      ); auto.
      intros.
      forwards h2: H0 X; auto.
      forwards h3: H7 X; auto.
      forwards h4: H11 X; auto.
      forwards* h5: IH h3 h4 h2.
        rewrite size_typ_open_typ_wrt_typ_var.
        rewrite size_typ_open_typ_wrt_typ_var.
        rewrite size_typ_open_typ_wrt_typ_var. 
        simpl in SizeInd. lia.
        simpl in *.
      apply WFPushV; simpl;auto.
    +
     inversion S1;subst;auto;
     try solve[inversion S2;subst;auto].
     * 
     forwards h1: split_ord_false H1; auto.
     inverts h1.  
     *
       inverts S2; auto.
       forwards h1: split_ord_false H1; auto.
       inverts h1.
       forwards: IH H5 H7 H0; auto. 
       simpl in *; lia.
    +
     inversion S1;subst;auto;
     try solve[inversion S2;subst;auto].
     *
       inverts S2; auto;
       try solve[inverts H1].
       forwards: IH H2 H5 H0; auto. 
       simpl in *; lia.
     *
       forwards h1: split_ord_false H1; auto.
       inverts h1.
  -
    forwards: sub_inversion_split_r S1 H. destruct H0.
    forwards: sub_inversion_split_r S2 H. destruct H2.
    forwards: split_decrease_size H. destruct H4.
    forwards: IH H0 H2 Dis; auto. lia.
    forwards: IH H1 H3 Dis; auto. lia. 
Qed.


Lemma WFEnv_bind_weakening : forall x I J D F,
    WFEnv (F ++ (x ~ TyDis I) ++ D) ->
    x `notin` [[J]]  ->
    WFEnv (F ++ (x ~ TyDis J) ++ D).
Proof with eauto.
  intros.
  inductions F; simpl in *; eauto.
  -
    inverts* H.
  -
    inverts* H. 
Qed.


Lemma TWell_bind_weakening_2 : forall x I J D C F,
    TWell (F ++ (x ~ TyDis  I) ++ D) C ->
    x `notin` [[J]]  ->
    TWell (F ++ (x ~ TyDis  J) ++ D) C.
Proof with eauto using WFEnv_bind_weakening.
  intros. remember (F ++ (x ~ TyDis I) ++ D) as G. gen F. induction* H; intros; subst...
  - analyze_binds H1.
    applys TWell_tvar A...
    applys TWell_tvar...
    applys TWell_tvar A...
  - apply TWell_forall with (union (union (union (union (dom F) (dom D)) [[J]]) L) (singleton x));intros; eauto...
    forwards*: H2 X ((X, TyDis A) :: F).
Qed.


Lemma Well_bind_weakening : forall x I J D C F,
    WFTyp (F ++ (x ~ TyDis I) ++ D) (C -^ x) ->
    algo_sub J I ->
    x `notin` (union (union (dom F) (dom D)) [[J]])  ->
    WFTyp (F ++ (x ~ TyDis J) ++ D) (C -^ x).
Proof with eauto using WFEnv_bind_weakening.
  intros. remember (F ++ (x ~ TyDis I) ++ D) as G. gen F. induction* H; intros; subst; eauto using WFEnv_bind_weakening.
  -
    forwards:  disjoint_narrowing H2 H0; auto.
  - analyze_binds H1.
    applys w_tvar A...
    applys w_tvar J...
    applys w_tvar A ...
  -  
    apply w_forall with (union (union (union (union (dom F) (dom D)) [[J]]) L) (singleton x));      intros...
     apply TWell_bind_weakening_2 with I; auto.
     simpl in *.
    forwards*: H2 X ((X, TyDis A) :: F); simpl;auto.
Qed.


Lemma Merge_Disjoint_arrow: forall D A1 A2 B1 B2 B,
 Merge B1 B2 B ->
 disjoint D (t_arrow A1 A2) B1 ->
 disjoint D (t_arrow A1 A2) B2 ->
 disjoint D (t_arrow A1 A2) B.
Proof.
  introv mer dis1 dis2.
  inductions mer; eauto.
Qed.


Lemma Merge_Disjoint_arrow_r: forall D A1 A2 B1 B2 B,
 Merge B1 B2 B ->
 disjoint D B1 (t_arrow A1 A2)  ->
 disjoint D B2 (t_arrow A1 A2) ->
 disjoint D B (t_arrow A1 A2) .
Proof.
  introv mer dis1 dis2.
  inductions mer; eauto.
Qed.


Lemma Merge_Disjoint_rcd_r: forall D i A2 B1 B2 B,
 Merge B1 B2 B ->
 disjoint D B1 (t_rcd i A2)  ->
 disjoint D B2 (t_rcd i A2) ->
 disjoint D B (t_rcd i A2) .
Proof.
  introv mer dis1 dis2.
  inductions mer; eauto.
Qed.

Lemma Merge_Disjoint_rcd: forall D i A2 B1 B2 B,
 Merge B1 B2 B ->
 disjoint D (t_rcd i A2) B1 ->
 disjoint D  (t_rcd i A2) B2 ->
 disjoint D (t_rcd i A2) B.
Proof.
  introv mer dis1 dis2.
  inductions mer; eauto.
Qed.

Lemma Merge_Disjoint_ref_l: forall D A B1 B2 B,
 Merge B1 B2 B ->
 disjoint D (t_ref A) B1 ->
 disjoint D (t_ref A) B2 ->
 disjoint D (t_ref A) B.
Proof.
  introv mer dis1 dis2.
  inductions mer.
  -
     apply D_axiom; auto.
  -
     apply D_axiom; auto.
  -
     apply D_axiom; auto.
Qed.



Lemma Merge_Disjoint_ref_r: forall D A B1 B2 B,
 Merge B1 B2 B ->
 disjoint D B1 (t_ref A)  ->
 disjoint D B2 (t_ref A)  ->
 disjoint D B (t_ref A) .
Proof.
  introv mer dis1 dis2.
  inductions mer; eauto.
Qed.



Lemma spl_lc: forall A B C,
 spl A B C ->
 lc_typ B /\ lc_typ C.
Proof.
 introv sp.
 inductions sp; eauto.
Qed.


Lemma Merge_lc: forall A B C,
 Merge A B C ->
 lc_typ A /\ lc_typ B /\ lc_typ C.
Proof.
 introv sp.
 inductions sp; auto.
 inverts H.
 inverts H0.
 splits; auto.
 apply lc_t_forall; intros;auto.
 unfold open_typ_wrt_typ in *; simpl in *; auto.
Qed.

(* #[export] *) 
Hint Resolve spl_lc Merge_lc : core.

Lemma appDist_lc: forall A B,
  appDist A B ->
 lc_typ A /\ lc_typ B.
Proof.
 introv sp.
 inductions sp; eauto.
 forwards h1: Merge_lc H; auto.
Qed.

(* #[export] *) 
Hint Resolve  appDist_lc : core.

Lemma Merge_Disjoint_all: forall D A1 A2 B1 B2 B,
 WFEnv D ->
 Merge B1 B2 B ->
 disjoint D (t_forall A1 A2) B1 ->
 disjoint D (t_forall A1 A2) B2 ->
 lc_typ A1 ->
 disjoint D (t_forall A1 A2) B.
Proof.
  introv wfe mer dis1 dis2 lc.
  inductions mer; eauto.
  inverts H as h1 h2.
  inverts H0 as h3 h4.
  apply D_forall with ((union (union (union (dom D) [[A1]]) [[A0]]) [[B1]]));intros; auto; auto.
  assert(t_and A3 B2 -^ X = t_and (A3 -^ X) (B2 -^ X)) as h5.
  unfold open_typ_wrt_typ; simpl; auto.
  rewrite h5.
  assert(spl (t_and A1 (t_and A0 B1)) A1 (t_and A0 B1)) as h11; auto.
  forwards h12: spl_sub_r h11.
  forwards h13: spl_sub_l h11.
  forwards h14:sub_r_spl_r h12; auto.
  forwards h16:sub_r_spl_l h12; auto.
  assert(algo_sub (t_and A1 (t_and A0 B1)) (t_and A1 B1)) as h9; auto.
  (* applys S_and;auto. *)
  assert(algo_sub (t_and A1 (t_and A0 B1)) (t_and A1 A0)) as h10.
  applys S_and;auto.
  forwards h17: disjoint_forall_inv dis1; auto.
  forwards h18: disjoint_forall_inv dis2; auto.
  forwards h19: disjoint_eqv_context h17 h10; auto.
  forwards h20: disjoint_eqv_context h18 h9; auto.
Qed.


Lemma Merge_Disjoint_all_r: forall D A1 A2 B1 B2 B,
 WFEnv D ->
 Merge B1 B2 B ->
 disjoint D B1 (t_forall A1 A2)  ->
 disjoint D B2 (t_forall A1 A2)  ->
 lc_typ A1 ->
 disjoint D B (t_forall A1 A2).
Proof.
  introv wfe mer dis1 dis2 lc.
  inductions mer; eauto.
  inverts H as h1 h2.
  inverts H0 as h3 h4.
  apply D_forall with ((union (union (union (dom D) [[A1]]) [[A0]]) [[B1]]));intros; auto; auto.
  assert(t_and A3 B2 -^ X = t_and (A3 -^ X) (B2 -^ X)) as h5.
  unfold open_typ_wrt_typ; simpl; auto.
  rewrite h5.
  assert(spl (t_and (t_and A0 B1) A1) (t_and A0 B1) A1) as h11; auto.
  forwards h12: spl_sub_l h11.
  forwards h13: spl_sub_r h11.
  forwards h14:sub_r_spl_r h12; auto.
  forwards h16:sub_r_spl_l h12; auto.
  assert(algo_sub (t_and (t_and A0 B1) A1) (t_and B1 A1)) as h9; auto.
  (* eapply S_and;auto. *)
  assert(algo_sub (t_and (t_and A0 B1) A1) (t_and A0 A1)) as h10.
  applys S_and;auto.
  forwards h17: disjoint_forall_inv dis1; auto.
  forwards h18: disjoint_forall_inv dis2; auto.
  forwards h19: disjoint_eqv_context h17 h10; auto.
  forwards h20: disjoint_eqv_context h18 h9; auto.
Qed.


Lemma Merge_Disjoint: forall D A0 A B1 B2 B,
 WFEnv D ->
 Merge B1 B2 B ->
 appDist A0 A ->
 disjoint D B1 A ->
 disjoint D B2 A ->
 disjoint D B A.
Proof.
  introv wfe mg pat dis1 dis2. gen A0 D B1 B2 B.
  inductions A; intros;try solve[inverts pat as h1;inverts h1].
  -
   forwards*: Merge_Disjoint_arrow_r dis1 dis2.
  -
    inverts mg; auto.
  -
    forwards h1: appDist_lc pat.
    forwards*: Merge_Disjoint_all_r dis1 dis2.
  -
    forwards*: Merge_Disjoint_rcd_r dis1 dis2.
Qed.



Lemma Disjoint_appDist: forall D A1 B1 A2 B2, 
 WFEnv D ->
 appDist A1 A2 ->
 appDist B1 B2 ->
 disjoint D A1 B1 ->
 disjoint D A2 B2.
Proof.
  introv wfe pa1 pa2 dis. gen D B1 B2.
  inductions pa1;intros; try solve[inverts* pa2];
  try solve[inverts pa2].
  -
    inductions pa2; auto.
    forwards lc1: appDist_lc pa2_1.
    forwards lc2: appDist_lc pa2_2.
    inverts lc1 as lc11 lc12. 
    inverts lc2 as lc21 lc22.
    assert(disjoint D (t_arrow A1 A2) A0) as h1.
    assert(spl (t_and A0 A3) A0 A3); auto.
    assert(disjoint D (t_arrow A1 A2) A3) as h2.
    assert(spl (t_and A0 A3) A0 A3); auto.
    forwards* h5: IHpa2_1.
    forwards* h6: IHpa2_2.
    forwards* h7: Merge_Disjoint_arrow h5 h6.
  -
    inductions pa2; auto.
    forwards lc1: appDist_lc pa2_1.
    forwards lc2: appDist_lc pa2_2.
    inverts lc1 as lc11 lc12. 
    inverts lc2 as lc21 lc22.
    forwards h1: disjoint_andr_inv dis; auto.
    forwards* h2: IHpa2_1.
    forwards* h3: IHpa2_2.
    forwards: Merge_Disjoint_ref_l H0 h2 h3; auto.
  -
    inductions pa2; auto.
    forwards lc1: appDist_lc pa2_1.
    forwards lc2: appDist_lc pa2_2.
    inverts lc1 as lc11 lc12. 
    inverts lc2 as lc21 lc22.
    assert(disjoint D (t_forall A1 A2) A0) as h1.
    assert(spl (t_and A0 A3) A0 A3); auto.
    assert(disjoint D (t_forall A1 A2) A3) as h2.
    assert(spl (t_and A0 A3) A0 A3); auto.
    forwards* h5: IHpa2_1.
    forwards* h6: IHpa2_2.
    forwards* h7: Merge_Disjoint_all h5 h6.
  -
    inductions pa2; auto.
    forwards lc1: appDist_lc pa2_1.
    forwards lc2: appDist_lc pa2_2.
    inverts lc1 as lc11 lc12. 
    inverts lc2 as lc21 lc22.
    assert(disjoint D (t_rcd i5 A) A1) as h1.
    assert(spl (t_and A1 A2) A1 A2); auto.
    assert(disjoint D (t_rcd i5 A) A2) as h2.
    assert(spl (t_and A1 A2) A1 A2); auto.
    forwards* h5: IHpa2_1.
    forwards* h6: IHpa2_2.
    forwards* h7: Merge_Disjoint_rcd h5 h6.
  -
    forwards lc1: appDist_lc pa1_1.
    forwards lc2: appDist_lc pa1_2.
    inverts lc1 as lc11 lc12. 
    inverts lc2 as lc21 lc22.
    assert(spl (t_and A1 A2) A1 A2) as h5; auto.
    forwards h6: disjoint_andl_inv h5 dis.
    inverts h6 as h1 h2.
    forwards* h3: IHpa1_1 h1.
    forwards* h4: IHpa1_2 h2.
    forwards*: Merge_Disjoint H h3 h4.
Qed.





Lemma WFTyp_WFEnv: forall D A, 
 WFTyp D A ->
 WFEnv D.
Proof.
 introv wf.
 inductions wf;eauto.
 pick fresh x.
 forwards* h1: H1.
 inverts* h1.
Qed.



Lemma TWell_WFEnv: forall D A, 
 TWell D A ->
 WFEnv D.
Proof.
 introv wf.
 inductions wf;eauto.
Qed.



Lemma WFTyp_TWell: forall D A, 
 WFTyp D A ->
 TWell D A.
Proof.
 introv wf.
 inductions wf;eauto.
Qed.

(* #[export] *) 
Hint Resolve WFTyp_WFEnv TWell_WFEnv WFTyp_TWell: core.





Lemma Well_appDist: forall D A B, WFTyp D A -> appDist A B -> WFTyp D B.
Proof.
  intros. induction H0;auto.
  - (* Merge *)
    inversion H;subst.
    forwards* h2:IHappDist1. 
    forwards* h3:IHappDist2. 
    inverts* H0.
    +
      inverts h2.
      inverts h3.
      forwards*: WFTyp_WFEnv H.
      forwards* h1: Disjoint_appDist  H0_ H0_0.
    +
      inverts h2.
      inverts h3.
      forwards*: WFTyp_WFEnv H.
      forwards* h1: Disjoint_appDist  H0_ H0_0.
      apply w_forall with (union (union (union (union L L0) (dom D)) [[A0]]) [[B0]]);intros; auto.
      forwards h4: H11 X; auto.
      forwards h5: H13 X; auto.
      forwards h6: disjoint_forall_inv h1; auto.
      rewrite_env(nil ++ (X, TyDis A0) :: D) in h4.
      rewrite_env(nil ++ (X, TyDis B0) :: D) in h5.
      assert(algo_sub (t_and A0 B0) A0) as h9.
      auto.
      assert(algo_sub (t_and A0 B0) B0) as h10.
      auto.
      forwards h7: Well_bind_weakening h4 h9;auto.
      forwards h8: Well_bind_weakening h5 h10;auto.
      unfold open_typ_wrt_typ in *; simpl in *; auto.
      +
      inverts h2.
      inverts h3.
      forwards*: WFTyp_WFEnv H.
      forwards* h1: Disjoint_appDist  H0_ H0_0.
Qed.



Lemma topLike_disjoint_weakening: forall x A J,
   x `notin` [[A]] ->
  lc_typ J ->
  topLike (A -^ x) ->
  topLike (A ^-^ J).
Proof.
  introv nin lc0 tl.
  lets tl': tl.
  inductions tl; eauto.
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ; simpl; auto.
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in *. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    forwards*: IHtl1 A1.
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in *. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    forwards* h1: topLike_lc tl'.
    inverts h1.
    (* lc begin *)
    assert(lc_typ ((open_typ_wrt_typ_rec 0 J A1))).
    assert( open_typ_wrt_typ_rec 0 J A1 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A1)).
    assert([x0 ~~> J] (A1 -^ x0)  = [x0 ~~> J] (A1) ^-^  [x0 ~~> J] (t_tvar_f x0)).
    apply typsubst_typ_open_typ_wrt_typ_rec;auto.
    unfold open_typ_wrt_typ in H0.
    rewrite H0.
    assert([x0 ~~> J] A1 = A1).
    apply typsubst_typ_fresh_eq. auto.
    rewrite H3.
    assert([x0 ~~> J] (t_tvar_f x0) = J).
    simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H6. auto.
    rewrite H0.
    apply  typsubst_typ_lc_typ; auto.
    (* lc end *)
    forwards*: IHtl.
  (* -
    destruct A;inversion x. unfold open_typ_wrt_typ in *. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    forwards*: IHtl. *)
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in *. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ. simpl  in *.
    unfold open_typ_wrt_typ in tl'; simpl in *.
    forwards* h1: topLike_lc tl'.
    inverts tl'.
      apply TL_all with (union (union L (singleton x0)) L0); intros;auto.
      (* lc begin *)
      unfold open_typ_wrt_typ in h1; simpl in h1.
      inverts h1 as h1 h2.
      assert( open_typ_wrt_typ_rec 0 J A1 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A1)) as hh0.
      assert([x0 ~~> J] (A1 -^ x0)  = [x0 ~~> J] (A1) ^-^  [x0 ~~> J] (t_tvar_f x0)) as hh1.
      apply typsubst_typ_open_typ_wrt_typ_rec;auto.
      unfold open_typ_wrt_typ in hh1.
      rewrite hh1.
      assert([x0 ~~> J] A1 = A1) as hh2.
      apply typsubst_typ_fresh_eq. auto.
      rewrite hh2.
      assert([x0 ~~> J] (t_tvar_f x0) = J) as hh3.
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. 
      rewrite hh3. auto.
      rewrite hh0.
      apply  typsubst_typ_lc_typ; auto.
      (* lc end *)
      assert(open_typ_wrt_typ_rec 1 J A2 -^ X = (A2 -^ X) ^-^ J). apply open_comm_2; auto.
      rewrite H5.
      forwards* h2: H7 X; auto.
      apply H1 with X x0; auto.
      assert(AtomSetImpl.Subset (typefv_typ (A2 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ A2)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[A2]])). auto. auto.
      rewrite H4.
      apply open_comm. auto.
      unfold open_typ_wrt_typ in *; simpl in *.
      rewrite <- open_comm. auto.
      auto.
  -
     destruct A;inversion x. unfold open_typ_wrt_typ in *. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    forwards*: IHtl.
  - (* ref *)
    destruct A;inversion x. unfold open_typ_wrt_typ in *. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    forwards*: IHtl.
Qed.


Lemma lc_typ_disjoint_weakening: forall x A J,
  x `notin` [[A]] ->
  lc_typ J ->
  lc_typ (A -^ x) ->
  lc_typ (A ^-^ J).
Proof.
  intros.
  assert( open_typ_wrt_typ_rec 0 J A = [x ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x) A)) as hh0.
      assert([x ~~> J] (A -^ x)  = [x ~~> J] (A) ^-^  [x ~~> J] (t_tvar_f x)) as hh1.
      apply typsubst_typ_open_typ_wrt_typ_rec;auto.
      unfold open_typ_wrt_typ in hh1.
      rewrite hh1.
      assert([x ~~> J] A = A) as hh2.
      apply typsubst_typ_fresh_eq. auto.
      rewrite hh2.
      assert([x ~~> J] (t_tvar_f x) = J) as hh3.
      simpl. unfold "==". destruct (EqDec_eq_of_X x x). auto. contradiction. 
      rewrite hh3. auto.
      unfold open_typ_wrt_typ.
      rewrite hh0.
      apply  typsubst_typ_lc_typ; auto.
Qed.


Lemma algo_sub_disjoint_weakening: forall x A B J,
  x `notin` union [[A]] [[B]] ->
  lc_typ J ->
  algo_sub (A -^ x) (B -^ x)->
  algo_sub (A ^-^ J) (B ^-^ J).
Proof.
  intros. dependent induction H1; intros; subst.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ; simpl; auto.
  -
    (* forwards: topLike_disjoint_weakening H0 H2; auto. *)
     (* lc begin *)
     assert(lc_typ ((open_typ_wrt_typ_rec 0 J A))) as hhh0.
     assert( open_typ_wrt_typ_rec 0 J A = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A)) as hh0.
      assert([x0 ~~> J] (A -^ x0)  = [x0 ~~> J] (A) ^-^  [x0 ~~> J] (t_tvar_f x0)) as hh1.
      apply typsubst_typ_open_typ_wrt_typ_rec;auto.
      unfold open_typ_wrt_typ in hh1.
      rewrite hh1.
      assert([x0 ~~> J] A = A) as hh2.
      apply typsubst_typ_fresh_eq. auto.
      rewrite hh2.
      assert([x0 ~~> J] (t_tvar_f x0) = J) as hh3.
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. 
      rewrite hh3. auto.
      rewrite hh0.
      apply  typsubst_typ_lc_typ; auto.

      assert( open_typ_wrt_typ_rec 0 J B = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B)) as hh0.
      assert([x0 ~~> J] (B -^ x0)  = [x0 ~~> J] (B) ^-^  [x0 ~~> J] (t_tvar_f x0)) as hh1.
      apply typsubst_typ_open_typ_wrt_typ_rec;auto.
      unfold open_typ_wrt_typ in hh1.
      rewrite hh1.
      assert([x0 ~~> J] B = B) as hh2.
      apply typsubst_typ_fresh_eq. auto.
      rewrite hh2.
      assert([x0 ~~> J] (t_tvar_f x0) = J) as hh3.
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. 
      rewrite hh3. auto.
      unfold open_typ_wrt_typ in *.
      rewrites hh0.
      rewrite <- x.
      simpl.
      auto.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    inverts x1. inverts x.
    forwards: IHalgo_sub1 B A; auto.
    forwards: IHalgo_sub2 A B; auto.
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       subst. unfold open_typ_wrt_typ. simpl.
        assert(algo_sub  (A1 ^-^ J) (B ^-^ J)). simpl in H.
       apply IHalgo_sub with x0; auto. 
       unfold open_typ_wrt_typ in *; simpl in *; auto.
       (* lc begin *)
     assert(lc_typ ((open_typ_wrt_typ_rec 0 J A2))) as hhh0.
     assert( open_typ_wrt_typ_rec 0 J A2 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A2)) as hh0.
      assert([x0 ~~> J] (A2 -^ x0)  = [x0 ~~> J] (A2) ^-^  [x0 ~~> J] (t_tvar_f x0)) as hh1.
      apply typsubst_typ_open_typ_wrt_typ_rec;auto.
      unfold open_typ_wrt_typ in hh1.
      rewrite hh1.
      assert([x0 ~~> J] A2 = A2) as hh2.
      apply typsubst_typ_fresh_eq. auto.
      rewrite hh2.
      assert([x0 ~~> J] (t_tvar_f x0) = J) as hh3.
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. 
      rewrite hh3. auto.
      rewrite hh0.
      apply  typsubst_typ_lc_typ; auto.
    (* lc end *)
    auto.
  -
     destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
       subst. unfold open_typ_wrt_typ. simpl.
        assert(algo_sub  (A2 ^-^ J) (B ^-^ J)). simpl in H.
       apply IHalgo_sub with x0; auto. 
       unfold open_typ_wrt_typ in *; simpl in *; auto.
       unfold open_typ_wrt_typ in H1. simpl in H1. 
          (* lc begin *)
     assert(lc_typ ((open_typ_wrt_typ_rec 0 J A1))) as hhh0.
     assert( open_typ_wrt_typ_rec 0 J A1 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A1)) as hh0.
      assert([x0 ~~> J] (A1 -^ x0)  = [x0 ~~> J] (A1) ^-^  [x0 ~~> J] (t_tvar_f x0)) as hh1.
      apply typsubst_typ_open_typ_wrt_typ_rec;auto.
      unfold open_typ_wrt_typ in hh1.
      rewrite hh1.
      assert([x0 ~~> J] A1 = A1) as hh2.
      apply typsubst_typ_fresh_eq. auto.
      rewrite hh2.
      assert([x0 ~~> J] (t_tvar_f x0) = J) as hh3.
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. 
      rewrite hh3. auto.
      rewrite hh0.
      apply  typsubst_typ_lc_typ; auto.
    (* lc end *)
    auto.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. unfold open_typ_wrt_typ in *. simpl. simpl in *.
    assert(algo_sub (A2 ^-^ J) (B2 ^-^ J)).
    apply IHalgo_sub2 with x0; auto. 
    assert(algo_sub  (B1 ^-^ J) (A1 ^-^ J)).
    apply IHalgo_sub1 with x0; auto.
    unfold open_typ_wrt_typ in *. simpl. simpl in *; auto.
  -
    forwards h1: open_spl_all H1. 
    lets(D1&D2&h2): h1.
    assert(spl (B -^ x) (D1 -^ x) (D2 -^ x)) as h3. auto.
    forwards h4:split_unique h3 H1. destruct h4;subst.
    pick fresh Z. assert(spl (B -^ Z) (D1 -^ Z) (D2 -^ Z)). auto.
    assert(x `notin` [[(B -^ Z)]]). assert(x<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
    apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(x `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards: split_fv H3 H2. destruct H4.
    assert(algo_sub (A ^-^ J) (D1 ^-^ J)).
    apply IHalgo_sub1 with x; auto.
    assert(spl (B ^-^ J) (D1 ^-^ J) (D2 ^-^ J)) as h5. auto.
    forwards*: spl_lc h5.
    assert(AtomSetImpl.Subset (typefv_typ D1) (typefv_typ (D1 -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual; auto. auto. 
    assert(algo_sub (A ^-^ J) (D2 ^-^ J)).
    apply IHalgo_sub2 with x; auto.
    assert(spl (B ^-^ J) (D1 ^-^ J) (D2 ^-^ J)) as h5. auto.
    forwards*: spl_lc h5.
    assert(AtomSetImpl.Subset (typefv_typ D2) (typefv_typ (D2 -^ Z))).
    apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto.
    eauto.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    simpl in H. subst. unfold open_typ_wrt_typ. simpl.
    apply sub_forall with (union L (singleton x0));
    intros; auto.
    assert(open_typ_wrt_typ_rec 1 J A4 -^ X = (A4 -^ X) ^-^ J). apply open_comm_2; auto. 
    assert(open_typ_wrt_typ_rec 1 J B4 -^ X = (B4 -^ X) ^-^ J). apply open_comm_2; auto. 
    rewrite H6. rewrite H7.
    simpl. assert( open_typ_wrt_typ_rec 0 J B3 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3)).
    assert([x0 ~~> J] (B3 -^ x0)  = [x0 ~~> J] (B3) ^-^  [x0 ~~> J] (t_tvar_f x0)).
    apply typsubst_typ_open_typ_wrt_typ_rec; auto.  
    unfold open_typ_wrt_typ in H8.
    rewrite H8.
    assert([x0 ~~> J] B3 = B3).
    apply typsubst_typ_fresh_eq. auto.
    rewrite H9.
    assert([x0 ~~> J] (t_tvar_f x0) = J).
    simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H10. auto.
    apply H2 with X x0;
    auto.
    assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ A4)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[A4]])). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ B4)).
    apply typefv_typ_open_typ_wrt_typ_upper.
    assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[B4]])); auto. 
    apply open_comm; auto. apply open_comm; auto.
    apply IHalgo_sub with x0; auto.
  -
  destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x;subst.
 destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1;subst.
 unfold open_typ_wrt_typ. simpl; auto.
 inversion x1. subst. simpl in H.
 assert(X<>X). auto. contradiction.
 inversion x. subst.
 destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
  destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1;subst.
 simpl in H.
 assert(x0<>x0). auto. contradiction. inversion x1. subst.
 assert(x0<>X). simpl in H. auto. 
 unfold open_typ_wrt_typ. simpl. eauto.
 -
   destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
    inverts x1. inverts x.
    forwards: IHalgo_sub B A; auto.
    forwards: IHalgo_sub B A; auto.
    inverts* H6.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ in *; simpl in *;auto.
Qed.



Lemma disjoint_weakening : forall A B D E F,
    disjoint (F ++ D) A B ->
    disjoint (F ++ E ++ D) A B.
Proof.
  intros. dependent induction H;auto.
  - assert(binds X (TyDis A) (F ++ E ++ D)). auto.
    eauto.
  -  assert(binds X (TyDis A) (F ++ E ++ D)). auto.
    eauto.
  - apply D_forall with (union L (dom (F ++ E ++ D))); intros;auto.
      rewrite_env(((X,  TyDis (t_and A1 A2)) :: F) ++ E ++ D).
    apply H0; auto. 
Qed.


Lemma disjoint_disjoint_weakening : forall x I J D A B F,
    x `notin` (union (union [[A]] [[B]]) (typefv_typ_range D)) ->
    disjoint (F ++ (x ~ TyDis I) ++ D) (A -^ x) (B -^ x)->
    disjoint D I J ->
    lc_typ J ->
    WFEnv (F ++ (x ~ TyDis I) ++ D)  ->
    disjoint (subst_env J x F ++ D) (A ^-^ J) (B ^-^ J).
Proof.
  intros. dependent induction H0.
  - 
    assert(disjoint_axiom (A ^-^ J) (B ^-^ J)).
    clear H1 H.
    dependent induction H0.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst.  auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.   
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto. 
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst.  auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst.  auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
  destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
        destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
      unfold open_typ_wrt_typ. simpl. subst. 
      auto.
      destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
      unfold open_typ_wrt_typ. simpl. subst. 
      auto.
      destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
      destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
      unfold open_typ_wrt_typ. simpl. subst. 
      auto.
      destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
      destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
      unfold open_typ_wrt_typ. simpl. subst. auto. 
      destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl. subst. 
    auto.
    auto.
  -
    forwards: topLike_lc H0.
    assert(lc_typ (A ^-^ J)).
    eauto with lngen.
    forwards:topLike_disjoint_weakening H2 H0; auto. 
  -
    forwards: topLike_lc H0.
    assert(lc_typ (B ^-^ J)).
    eauto with lngen.
    forwards:topLike_disjoint_weakening H2 H0; auto. 
  -
    forwards(?&?&?):open_spl_all H0.
    assert(spl (A -^ x) (x0 -^ x) (x1 -^ x)). auto.
    forwards h1:split_unique H0 H5; auto. destruct h1;subst.
    pick fresh Z. assert(spl (A -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(x `notin` [[(A -^ Z)]]). assert(x<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (A -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ A)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(x `notin` (Metatheory.union [[t_tvar_f Z]] [[A]])). auto. auto.
    forwards(?&?): split_fv H7 H6.
    assert(disjoint (subst_env J x F ++ D) (x0 ^-^ J) (B ^-^ J)).
    apply IHdisjoint1 with I; auto.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto. auto.
    assert(disjoint (subst_env J x F ++ D) (x1 ^-^ J) (B ^-^ J)).
    apply IHdisjoint2 with I;auto.
    assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto. auto. 
    assert(spl (A ^-^ J) (x0 ^-^ J) (x1 ^-^ J)). apply H4.
    auto.  eauto.
  -
    forwards(?&?&?):open_spl_all H0.
    assert(spl (B -^ x) (x0 -^ x) (x1 -^ x)). auto.
    forwards:split_unique H0 H4; auto. destruct H6;subst.
    pick fresh Z. assert(spl (B -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(x `notin` [[(B -^ Z)]]). assert(x<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(x `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards(?&?): split_fv H7 H6.
    assert(disjoint (subst_env J x F ++ D) (A ^-^ J) (x0 ^-^ J)).
    apply IHdisjoint1 with I; auto.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto. auto.
    assert(disjoint (subst_env J x F ++ D) (A ^-^ J) (x1 ^-^ J)).
    apply IHdisjoint2 with I; auto.
    assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto. auto. auto. auto. auto. auto.
    assert(spl (B ^-^ J) (x0 ^-^ J) (x1 ^-^ J)). 
    apply H4; auto. 
    eauto.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
    destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    unfold open_typ_wrt_typ. simpl.
    subst.
    simpl in H.
    assert(disjoint (subst_env J x0 F ++ D) (open_typ_wrt_typ_rec 0 J A4) (open_typ_wrt_typ_rec 0 J B4)).
    forwards*: IHdisjoint B4 A4.
    simpl in *; eauto.
    auto.
  -
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. subst.
     unfold open_typ_wrt_typ. simpl.
      assert(A0 = I). 
      assert(binds x0 (TyDis I) (F ++ x0 ~ TyDis I ++ D)) as h1; auto.
      forwards* h2 : binds_unique H1 h1. 
      inverts h2; auto.
      subst.
     assert(close_typ_wrt_typ_rec 0 x0 I -^ x0 = I). apply open_typ_wrt_typ_close_typ_wrt_typ.
     assert(algo_sub (close_typ_wrt_typ_rec 0 x0 I -^ x0) (B -^ x0)). rewrite H5. auto.
     forwards: algo_sub_disjoint_weakening H3 H7; auto.
     forwards* h2: algo_sub_lc H0. 
     assert(x0#D).
     forwards* h1: WFEnv_uniq H4.
     clear H1 H x H2 H0 H4 H5 H6 H7 H8. induction F.
      inversion h1;subst;auto.
      destruct a. inversion h1;subst. auto.
      assert(close_typ_wrt_typ_rec 0 x0 I = I).
     apply close_typ_wrt_typ_lc_typ;  auto.
     forwards h3: wfenv_app_r H4.
     inverts* h3.
     assert(open_typ_wrt_typ I J = I). apply open_typ_wrt_typ_lc_typ. auto.
     apply disjoint_covariance with I.
     rewrite_env(nil ++ subst_env J x0 F ++ D). apply disjoint_weakening; auto.
       simpl. 
       apply disjoint_symm; auto.
       rewrite H10 in *; auto.
       rewrite H11 in *.
       auto.
     inversion x. subst.
       unfold open_typ_wrt_typ. simpl.
     simpl in H. assert(x0<>X0). auto.
     assert(close_typ_wrt_typ_rec 0 x0 A0 -^ x0 = A0). apply open_typ_wrt_typ_close_typ_wrt_typ.
     rewrite <- H6 in H0.
     forwards h5: algo_sub_lc H0.
     inverts h5 as h5 h6.
     forwards: algo_sub_disjoint_weakening H3 H0; auto.
     assert([x0 ~~> J] (A0) = (close_typ_wrt_typ_rec 0 x0 A0 ^-^ J)).
     apply typsubst_typ_spec. rewrite <- H8 in H7.
     forwards*: TCW_binds_3 J H1.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. subst.
     unfold open_typ_wrt_typ. simpl.
      assert(A0 = I). 
      assert(binds x0 (TyDis I) (F ++ x0 ~ TyDis I ++ D)) as h1; auto.
      forwards* h2 : binds_unique H1 h1. 
      inverts h2; auto.
      subst.
     assert(close_typ_wrt_typ_rec 0 x0 I -^ x0 = I). apply open_typ_wrt_typ_close_typ_wrt_typ.
     assert(algo_sub (close_typ_wrt_typ_rec 0 x0 I -^ x0) (A -^ x0)). rewrite H5. auto.
     forwards: algo_sub_disjoint_weakening H3 H7. auto.
     forwards* h2: algo_sub_lc H0. 
     assert(x0#D). 
     forwards* h1: WFEnv_uniq H4.
     clear H1 H x H2 H0 H4 H5 H6 H7 H8. induction F.
      inversion h1;subst;auto.
      destruct a. inversion h1;subst. auto.
      assert(close_typ_wrt_typ_rec 0 x0 I = I).
     apply close_typ_wrt_typ_lc_typ. auto. 
     forwards h3: wfenv_app_r H4.
     inverts* h3.
     assert(open_typ_wrt_typ I J = I). apply open_typ_wrt_typ_lc_typ. auto.
     apply disjoint_symm.
     apply disjoint_covariance with I.
     rewrite_env(nil ++ subst_env J x0 F ++ D). apply disjoint_weakening; auto.
       apply disjoint_symm; auto.
       rewrite H10 in *; auto.
       rewrite H11 in *.
       auto.
     inversion x. subst.
       unfold open_typ_wrt_typ. simpl.
     simpl in H. assert(x0<>X0). auto.
     assert(close_typ_wrt_typ_rec 0 x0 A0 -^ x0 = A0). apply open_typ_wrt_typ_close_typ_wrt_typ.
     rewrite <- H6 in H0.
     forwards h5: algo_sub_lc H0.
     inverts h5 as h5 h6.
     forwards: algo_sub_disjoint_weakening H3 H0; auto.
     assert([x0 ~~> J] (A0) = (close_typ_wrt_typ_rec 0 x0 A0 ^-^ J)).
     apply typsubst_typ_spec. rewrite <- H8 in H7.
     forwards*: TCW_binds_3 J H1.
  -
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    simpl in H. subst.
    unfold open_typ_wrt_typ. simpl.
    apply D_forall with (union L
    (union (singleton x0)
       (union [[J]]
          (union [[I]]
             (union [[B3]]
                (union [[A3]]
                   (union [[B4]]
                      (union [[A4]]
                         (union (dom F)
                            (union (dom D)
                               (union 
                                  (typefv_typ_range F)
                                  (typefv_typ_range D)))))))))))).
    intros.
    assert(open_typ_wrt_typ_rec 1 J A4 -^ X = (A4 -^ X) ^-^ J). apply open_comm_2. auto.  auto.
    assert(open_typ_wrt_typ_rec 1 J B4 -^ X = (B4 -^ X) ^-^ J). apply open_comm_2. auto.  auto.
    rewrite H7. rewrite H8.
    assert((X, TyDis (t_and (open_typ_wrt_typ_rec 0 J A3) (open_typ_wrt_typ_rec 0 J B3))) :: subst_env J x0 F =
          subst_env J x0 ((X, TyDis (t_and (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A3)
       (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3))) :: F)).
      simpl. assert( open_typ_wrt_typ_rec 0 J B3 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) B3)).
      assert([x0 ~~> J] (B3 -^ x0)  = [x0 ~~> J] (B3) ^-^  [x0 ~~> J] (t_tvar_f x0)).
      apply typsubst_typ_open_typ_wrt_typ_rec.  auto.
      unfold open_typ_wrt_typ in H9.
      rewrite H9.
      assert([x0 ~~> J] B3 = B3).
      apply typsubst_typ_fresh_eq. auto.
      rewrite H10.
      assert([x0 ~~> J] (t_tvar_f x0) = J).
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H11. auto.
      assert( open_typ_wrt_typ_rec 0 J A3 = [x0 ~~> J] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A3)).
      assert([x0 ~~> J] (A3 -^ x0)  = [x0 ~~> J] (A3) ^-^  [x0 ~~> J] (t_tvar_f x0)).
      apply typsubst_typ_open_typ_wrt_typ_rec. auto.
      unfold open_typ_wrt_typ in H10.
      rewrite H10.
      assert([x0 ~~> J] A3 = A3).
      apply typsubst_typ_fresh_eq. auto.
      rewrite H11.
      assert([x0 ~~> J] (t_tvar_f x0) = J).
      simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite H12. auto.
      rewrite H9. rewrite H10. auto.
      rewrite_env(((X, TyDis (t_and (open_typ_wrt_typ_rec 0 J A3) (open_typ_wrt_typ_rec 0 J B3))) :: subst_env J x0 F) ++ D).
      rewrite H9. apply H0 with X I. auto.
      assert(AtomSetImpl.Subset (typefv_typ (A4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ A4)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[A4]])). eauto.
      assert(AtomSetImpl.Subset (typefv_typ (B4 -^ X)) (typefv_typ (t_tvar_f X)`union`  typefv_typ B4)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(x0 `notin` (Metatheory.union [[t_tvar_f X]] [[B4]])). auto. 
      assert(x0 `notin` (union [[A4 -^ X]] [[B4 -^ X]])) as hh1.
      auto. auto.
      auto.
      apply open_comm. auto. apply open_comm. auto. auto.
      auto.
      simpl.
      apply WFPushV; simpl ;auto.
      simpl_env.
      assert(AtomSetImpl.Subset (typefv_typ (A3 -^ x0)) (typefv_typ (t_tvar_f x0)`union`  typefv_typ A3)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(X `notin` (Metatheory.union [[t_tvar_f x0]] [[A3]])). eauto.
      assert(AtomSetImpl.Subset (typefv_typ (B3 -^ x0)) (typefv_typ (t_tvar_f x0)`union`  typefv_typ B3)).
      apply typefv_typ_open_typ_wrt_typ_upper.
      assert(X `notin` (Metatheory.union [[t_tvar_f x0]] [[B3]])). auto. 
      assert(X `notin` (union [[A3 -^ x0]] [[B3 -^ x0]])) as hh1.
      auto. auto.
      inverts H1 as h1 h2.
      forwards* h3: lc_typ_disjoint_weakening H4 h1.
      forwards* h5: lc_typ_disjoint_weakening H4 h2.
  - 
    destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. simpl in H.
    assert(disjoint (subst_env J x0 F ++ D) (open_typ_wrt_typ_rec 0 J A) (open_typ_wrt_typ_rec 0 J B)).
    forwards*: IHdisjoint.
    unfold open_typ_wrt_typ. simpl. auto.
  - (* ref *)
     destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    destruct A;inversion x1. unfold open_typ_wrt_typ in x1. simpl in x1.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x1. inversion x1. inversion x1.
    subst. simpl in H.
    assert(disjoint (subst_env J x0 F ++ D) (open_typ_wrt_typ_rec 0 J A) (open_typ_wrt_typ_rec 0 J B)).
    forwards*: IHdisjoint.
    unfold open_typ_wrt_typ. simpl. auto.
Qed.


Lemma disjoint_subst: forall E F S U Z B A,
  Z `notin` (typefv_typ_range F) ->
  WFEnv (E ++ Z ~ TyDis S ++ F) ->
  disjoint (E ++ [(Z, TyDis S)] ++ F) B A->
  disjoint F U S ->
  lc_typ U ->
  disjoint (subst_env U Z E ++ F) [Z ~~> U] (B) [Z ~~> U] (A).
Proof.
  intros.
  assert(close_typ_wrt_typ_rec 0 Z A -^ Z = A). apply open_typ_wrt_typ_close_typ_wrt_typ.
  assert(close_typ_wrt_typ_rec 0 Z B -^ Z = B). apply open_typ_wrt_typ_close_typ_wrt_typ.
    rewrite <- H4 in H1.
    rewrite <- H5 in H1.
  apply disjoint_symm in H2.  
  forwards: disjoint_disjoint_weakening H1 H2; auto.
  assert(typsubst_typ U Z B = open_typ_wrt_typ (close_typ_wrt_typ Z B) U).
    apply typsubst_typ_spec.
  assert(typsubst_typ U Z A = open_typ_wrt_typ (close_typ_wrt_typ Z A) U).
    apply typsubst_typ_spec.
  rewrite H7. rewrite H8. auto.
Qed. 









