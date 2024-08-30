Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import syntax_ott
                rules_inf
                Infrastructure
                Wellformedness
                SubtypingInversion
                Value
                Disjointness
               KeyProperties
               Deterministic.

(* 
Lemma subsub2sub: forall A B, subsub A B -> algo_sub A B/\algo_sub B A.
Proof with eauto.
  intros. inductions H;eauto; try solve[destruct IHsubsub; auto].
  - (* and and*)
    destruct IHsubsub1. destruct IHsubsub2.
    forwards: algo_sub_lc H2.
    forwards: algo_sub_lc H4.
    assert(spl (t_and A1 A2) A1 A2). auto.
    split. apply S_and with B1 B2...
    apply S_and with A1 A2...
    apply sub_transitivity with B1.
    apply spl_sub_l with B2... auto.
    apply sub_transitivity with B2.
    apply spl_sub_r with B1... auto.
Qed.



Lemma appDist_arr_subsub: forall A1 A2 C C',
    appDist C (t_arrow A1 A2) -> subsub C' C
    -> exists A2', appDist C' (t_arrow A1 A2') /\ subsub A2' A2.
Proof.
  introv Harr Hsub. gen A1 A2.
  induction Hsub; intros; try solve[inverts Harr].
  - 
    forwards* h1: appDist_lc Harr.
  -  forwards h1: appDist_lc Harr.
    inverts Harr.
    + 
      inverts H.
      forwards ( ?&?&?): IHHsub1; auto.
      forwards ( ?&?&?): IHHsub2; auto.
      forwards h2: appDist_lc H.
      forwards h3: appDist_lc H1.
      assert(Merge (t_arrow A0 x) (t_arrow A0 x0) (t_arrow A0 (t_and x x0))) as h5; auto.
      exists (t_and x x0). splits.
      eauto.
      eauto.
    + inverts H.
      inverts H0.
      forwards ( ?&?&?): IHHsub1 H1; auto.
      forwards ( ?&?&?): IHHsub2 H2; auto.
      forwards h2: appDist_lc H.
      forwards h3: appDist_lc H3.
      assert(Merge (t_arrow A0 x) (t_arrow A0 x0) (t_arrow A0 (t_and x x0))) as h5; auto.
      exists (t_and x x0). splits.
      eauto.
      eauto.
Qed.



Lemma subsub_lc: forall A B,
 subsub A B -> lc_typ A /\ lc_typ B.
Proof.
 introv sub.
 inductions sub; eauto.
Qed.



Lemma appDist_ref_subsub: forall A A1 B,
    appDist A (t_ref A1) -> subsub B A
    -> exists B1, appDist B (t_ref B1) /\ subsub B1 A1.
Proof.
  introv Harr Hsub. gen A1.
  induction Hsub; intros;
  try solve[inverts Harr].
  - 
    forwards*: appDist_lc Harr.
  - 
    forwards*: appDist_lc Harr.
    inverts H; try solve[inverts Harr as h1;inverts h1].
  -
    forwards*: subsub_lc Hsub.
    inverts* Harr.
Qed. 



Lemma appDist_rcd_subsub: forall A1 A2 C C',
    appDist C (t_rcd A1 A2) -> subsub C' C
    -> exists A2', appDist C' (t_rcd A1 A2') /\ subsub A2' A2.
Proof.
  introv Harr Hsub. gen A1 A2.
  induction Hsub; intros; try solve[inverts Harr].
  - 
    forwards* h1: appDist_lc Harr.
  -  forwards h1: appDist_lc Harr.
    inverts Harr.
    + 
      inverts H.
      forwards ( ?&?&?): IHHsub1; auto.
      forwards ( ?&?&?): IHHsub2; auto.
      forwards h2: appDist_lc H.
      forwards h3: appDist_lc H1.
      assert(Merge (t_rcd A0 x) (t_rcd A0 x0) (t_rcd A0 (t_and x x0))) as h5; auto.
      exists (t_and x x0). splits.
      eauto.
      eauto.
    + inverts H.
      inverts H0.
      forwards ( ?&?&?): IHHsub1 H1; auto.
      forwards ( ?&?&?): IHHsub2 H2; auto.
      forwards h2: appDist_lc H.
      forwards h3: appDist_lc H3.
      assert(Merge (t_rcd A0 x) (t_rcd A0 x0) (t_rcd A0 (t_and x x0))) as h5; auto.
      exists (t_and x x0). splits.
      eauto.
      eauto.
  -
    forwards*: subsub_lc Hsub.
    inverts* Harr.
Qed.




Lemma subsub_subst:forall X Y (A B C:typ),
X `notin`  (Metatheory.union [[A]] [[B]])
-> subsub  (A -^ X) (B -^ X)
-> subsub  (A -^ Y) (B -^ Y).
Proof.
  intros. dependent induction H0.
  - (* refl *)
    forwards: open_typ_wrt_typ_rec_inj_mutual x. auto. auto. subst.
    forwards*: lc_typ_rename H0.
  - (* spl *)
    destruct A;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s. inversion x. inversion x. inversion x.
    simpl in H. unfold open_typ_wrt_typ. simpl.
      forwards: open_spl H0. destruct H1. destruct H1.
    assert(spl (B -^ X) (x0 -^ X) (x1 -^ X)).
    auto. forwards*(?&?): split_unique H0 H4. subst.
    pick fresh Z. assert(spl (B -^ Z) (x0 -^ Z) (x1 -^ Z)). auto.
      assert(X `notin` [[(B -^ Z)]]). assert(X<>Z). auto.
    assert(AtomSetImpl.Subset (typefv_typ (B -^ Z)) (typefv_typ (t_tvar_f Z) `union` typefv_typ B)).
      apply typefv_typ_open_typ_wrt_typ_rec_upper_mutual.
    assert(X `notin` (Metatheory.union [[t_tvar_f Z]] [[B]])). auto. auto.
    forwards: split_fv H3 H2. destruct H5.
    assert(subsub (A3 -^ Y) (x0 -^ Y)). 
    forwards h1: IHsubsub1 x0 A3 X; auto.
    assert(AtomSetImpl.Subset (typefv_typ x0) (typefv_typ (x0 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto.
    assert(subsub 
              (A4 -^ Y) (x1 -^ Y)). 
   forwards h2: IHsubsub2 x1 A4 X; auto.
    assert(AtomSetImpl.Subset (typefv_typ x1) (typefv_typ (x1 -^ Z))).
      apply typefv_typ_open_typ_wrt_typ_rec_lower_mutual. auto.
    eauto.
  -
     destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s; inversion x0. inversion x0.
      destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s; inversion x. inversion x.  
    simpl in H. 
    rewrite H2 in *.
    rewrite H3 in *.
    unfold open_typ_wrt_typ in *. simpl in *.
    eauto.
  -
    destruct A;inversion x0. unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct(lt_eq_lt_dec n 0). destruct s; inversion x0. inversion x0.
      destruct B;inversion x. unfold open_typ_wrt_typ in x. simpl in x.
      destruct(lt_eq_lt_dec n 0). destruct s; inversion x. inversion x.  
    simpl in H. 
    rewrite H2 in *.
    rewrite H3 in *.
    unfold open_typ_wrt_typ in *. simpl in *.
    substs*.
Qed.


Lemma subsub_simpl_subst:forall X Y (A B:typ) ,
X `notin`  (Metatheory.union [[A]] [[B]])
-> subsub  (A -^ X) (B -^ X)
-> subsub  (A -^ Y) (B -^ Y).
Proof.
  intros.
  apply subsub_subst with X Y A B in H0. auto. auto. auto.
Qed.



Lemma appDist_forall_subsub: forall A1 A2 C C',
    appDist C (t_forall A1 A2) -> subsub  C' C
    -> exists A1' A2', appDist C' (t_forall A1' A2')
      /\ (forall Y, subsub (A2' -^ Y) (A2 -^ Y))
      /\algo_sub A1 A1'.
Proof.
  intros. gen A1 A2. inductions H0;intros; 
  try solve[inverts H].
  -
    forwards* h1: appDist_lc H0.
  -
    inversion H0;subst.
    +
    inversion H;subst.
    forwards (?&?&?&?&?): IHsubsub1; intuition eauto.
    forwards (?&?&?&?&?): IHsubsub2; intuition eauto.
    forwards h1: appDist_lc H1.
    forwards h2: appDist_lc H6.
    exists (t_and x x1) (t_and x0 x2). split. 
    eauto. split.
    pick fresh X.
    assert(spl (A3 -^ X) (C1 -^ X) (C2 -^ X)). auto.
    assert(subsub  (x0 -^ X) (C1 -^ X)). auto.
    assert(subsub  (x2 -^ X) (C2 -^ X)). auto.
    assert(subsub  (t_and x0 x2 -^ X) (A3 -^ X)).
    unfold open_typ_wrt_typ. simpl. eauto.
    intros. apply subsub_simpl_subst with X. auto. auto. auto. 
    (* auto. eauto. *)
    +
    inversion H;subst.
    inversion H1;subst.
    forwards (?&?&?&?&?): IHsubsub1; intuition eauto.
    forwards (?&?&?&?&?): IHsubsub2; intuition eauto.
    forwards h1: appDist_lc H4.
    forwards h2: appDist_lc H11.
    exists (t_and x x1) (t_and x0 x2). split; eauto. 
    split; eauto.
    pick fresh X.
    assert(spl (t_and A5 B5 -^ X) (A5 -^ X) (B5 -^ X)). eauto.
    assert(subsub  (x0 -^ X) (A5 -^ X)). auto.
    assert(subsub (x2 -^ X) (B5 -^ X)). auto.
    assert(subsub  (t_and x0 x2 -^ X) (t_and A5 B5 -^ X)).
    unfold open_typ_wrt_typ. simpl.
    unfold open_typ_wrt_typ in H16. simpl in H16.
    eauto.
    intros.
    apply subsub_simpl_subst with X. auto. auto. 
Qed.



Lemma appDist_forall_subsub_disjoint: forall A1 A2 C C',
    appDist C (t_forall A1 A2) -> subsub C' C
    -> exists A1' A2', appDist C' (t_forall A1' A2')
      /\ (forall T, lc_typ  T -> subsub (A2' ^-^ T) (A2 ^-^ T))
      /\ algo_sub A1 A1'.
Proof with intuition eauto.
  intros. gen A1 A2. induction H0;intros; try solve[inverts H].
  - (* refl *)
    forwards h1: appDist_lc H0.
    inverts h1 as h11 h12.
    inverts h12 as h121 h122.
    exists A1 A2.
    split. auto.
    split;auto. intros.
    pick fresh x0.
    assert(lc_typ (A2 ^-^ T)) as h2.
    assert( open_typ_wrt_typ_rec 0 T A2 = [x0 ~~> T] (open_typ_wrt_typ_rec 0 (t_tvar_f x0) A2)) as h1.
    assert([x0 ~~> T] (A2 -^ x0)  = [x0 ~~> T] (A2) ^-^  [x0 ~~> T] (t_tvar_f x0)) as h2.
    apply typsubst_typ_open_typ_wrt_typ_rec;auto.
    unfold open_typ_wrt_typ in h2.
    rewrite h2.
    assert([x0 ~~> T] A2 = A2) as h3.
    apply typsubst_typ_fresh_eq. auto.
    rewrite h3.
    assert([x0 ~~> T] (t_tvar_f x0) = T) as h8.
    simpl.
    simpl. unfold "==". destruct (EqDec_eq_of_X x0 x0). auto. contradiction. rewrite h8. auto.
    unfold open_typ_wrt_typ.
    rewrite h1.
    apply  typsubst_typ_lc_typ; auto.
    forwards*: h122 x0.
    eauto. 
  - (*and forall*)
    inversion H0;subst.
    +
    inversion H;subst.
    forwards (?&?&h1&h2&h3): IHsubsub1...
    forwards (?&?&h4&h5&h6): IHsubsub2...
    forwards h7: appDist_lc h1.
    forwards h8: appDist_lc h4.
    exists (t_and x x1) (t_and x0 x2). split. eauto. split.
    intros.
    assert(forall Y, lc_typ Y -> spl (A3 ^-^ Y) (C1 ^-^ Y) (C2 ^-^ Y)).
    apply open_spl_2 with L. auto.
    unfold open_typ_wrt_typ. simpl.
    assert(subsub  (x0 ^-^ T) (C1 ^-^ T)). auto.
    assert(subsub (x2 ^-^ T) (C2 ^-^ T)). auto.
    assert(spl (A3 ^-^ T) (C1 ^-^ T) (C2 ^-^ T)). apply H2; auto.
    eauto.
    inverts h7 as h71 h72.
    inverts h72 as h721 h722.
    inverts h8 as h81 h82.
    inverts h82 as h821 h822.
    eauto.
    +
    inversion H;subst.
    inversion H1;subst.
    forwards (?&?&h1&h2&h3): IHsubsub1...
    forwards (?&?&h4&h5&h6): IHsubsub2...
    forwards h7: appDist_lc h1.
    forwards h8: appDist_lc h4.
    exists (t_and x x1) (t_and x0 x2). split. eauto. split.
    intros.
    assert(spl (t_and A4 B0) A4 B0). eauto.
    assert(subsub (x0 ^-^ T) (A5 ^-^ T)). auto.
    assert(subsub (x2 ^-^ T) (B5 ^-^ T)). auto.
    unfold open_typ_wrt_typ in *. simpl.
    forwards:subsub_lc H10.
    forwards:subsub_lc H11.
    eauto.
    eauto.
Qed.



Lemma subsub_spl:forall A B C D,
  subsub A B ->spl A C D->
exists G H, spl B G H/\subsub C G/\subsub D H.
Proof.
  intros. gen C D.
    induction H;intros. exists*.
    inversion H2;subst. exists*.
    inverts* H0.
    inverts H0 as h1.
    forwards* h2: IHsubsub h1.
Qed.



Lemma spl_uniq: forall A t1 t2 t3 t4,
 spl A t1 t2 ->
 spl A t3 t4 ->
 t1 = t3 /\ t2 = t4.
Proof.
  introv sp1 sp2.
  gen t3 t4.
  inductions sp1; intros; inductions sp2; eauto.
  -
  forwards* h1: IHsp1 sp2.
  lets(t1&t2): h1. substs*.
  -
    pick fresh y.
    forwards* h1: H2 y.
    forwards* h2: H1 h1.
    inverts h2 as h2 h3.
    forwards* h4:  open_typ_wrt_typ_inj h2.
    simpl in *; eauto.
    forwards* h5:  open_typ_wrt_typ_inj h3.
    simpl in *; eauto.
    eauto.
    substs*.
  -
  forwards* h1: IHsp1 sp2.
  lets(t1&t2): h1. substs*.
Qed.



Lemma subsub_trans : forall A B C,
    subsub A B -> subsub B C -> subsub A C.
Proof with auto.
  introv s1 s2.
  indTypSize (size_typ B).
  inverts keep s2...
(*   
    + (* top *)
      inverts s1... *)
    + (* spl *)
      inverts keep s1;auto.
(*       
      * (* top *)
        apply subsub2sub in s2. destruct s2.
        apply toplike_sub in H3... *)
      * (* spl *)
        forwards(?&?&?&?&?): subsub_spl s2 H2.
        forwards(?&?): split_decrease_size H5.
        assert(subsub A0 x). applys IH. apply H3. elia. auto.
        assert(subsub A3 x0). applys IH. apply H4. elia. auto.
        apply IS_and with x x0...
    + inverts keep s1;auto.
(*     
      *
      apply subsub2sub in s2. destruct s2.
      apply toplike_sub in H1... *)
      *
      inverts* H0.
      *
      forwards* h2: IH A1 A0 B0. elia.
    + 
      inverts keep s1;auto.
      *
        inverts s1.
        inverts s2.
        --
        forwards* h0: spl_uniq H0 H5.
        --
        forwards h0: spl_uniq H0 H5.
        inverts h0 as h01 h02.
        forwards* h1: subsub_spl (t_rcd i5 A0) (t_rcd i5 B0) H0.
        lets(t1&t2&h3&h4&h5): h1.
        forwards* h6: IH H6 h4.
        simpl in *.
        elia.
        forwards* h7: IH H8 h5.
        simpl in *.
        elia.
      *
      forwards* h2: IH A1 A0 B0. elia.  
Qed. *)
