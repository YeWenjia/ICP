(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Metalib.Metatheory.

(** syntax *)
Definition i : Set := nat.
Definition label : Set := nat.
Definition typevar : Set := var.

Inductive typ : Set :=  (*r types *)
 | t_tvar_b (_:nat) (*r type variable *)
 | t_tvar_f (X:typevar) (*r type variable *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_and (A:typ) (B:typ) (*r intersection *)
 | t_ref (A:typ) (*r reference *)
 | t_forall (A:typ) (B:typ) (*r universal type *)
 | t_rcd (l: nat) (A:typ)
 | t_unit.

(** This uses the locally nameless representation for terms and cofinite quantification in typing judgements. *)
Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_loc (o:nat) (*r binding *)
 | e_top (*r top *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (e:exp)  (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_merge (e1:exp) (e2:exp) (*r merge *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_ref (e:exp)
 | e_deref (e:exp)
 | e_ass (e1:exp) (e2:exp)
 | e_tabs  (e:exp)  (*r tabstractions *)
 | e_tapp (e:exp) (A:typ) (*r tapplications *)
 | e_rcd (l:nat) (e:exp)
 | e_proj (e:exp) (i:nat)
 | e_unit
 (* Please note that e_loct is a placeholder in function TLVal for uniform top-like reference values. *)
 | e_loct.


Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.



 Inductive TyEnv : Set :=  
 | TyDis : typ -> TyEnv
 | TermV : typ -> TyEnv.



Definition sto : Set := list exp.
Definition phi : Set := list typ.

(* note that if location must exist, we restrict in typing rule that any location should be 
within the store *)
Definition store_Tlookup (n:nat) (ST: phi) :=
  nth n ST t_top.

Definition store_lookup (n:nat) (st:sto) :=
  nth n st (e_top).

Definition ctx : Set := list ( atom * TyEnv ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)

Fixpoint open_typ_wrt_typ_rec (k:nat) (A5:typ) (A_6:typ) {struct A_6}: typ :=
  match A_6 with
  | (t_tvar_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_tvar_b nat
        | inleft (right _) => A5
        | inright _ => t_tvar_b (nat - 1)
      end
  | (t_tvar_f X) => t_tvar_f X
  | t_int => t_int 
  | t_top => t_top 
  | (t_arrow A B) => t_arrow (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec k A5 B)
  | (t_and A B) => t_and (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec k A5 B)
  | (t_ref A) => t_ref (open_typ_wrt_typ_rec k A5 A)
  | (t_forall A B) => t_forall (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec (S k) A5 B)
  | (t_rcd i5 A) => t_rcd i5 (open_typ_wrt_typ_rec k A5 A)
  | t_unit => t_unit
end.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | (e_loc o5) => e_loc o5
  | e_top => e_top
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_tabs e) => e_tabs (open_exp_wrt_exp_rec k e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | (e_ref e) => e_ref (open_exp_wrt_exp_rec k e_5 e)
  | (e_deref e) => e_deref (open_exp_wrt_exp_rec k e_5 e)
  | (e_ass e1 e2) => e_ass (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_tapp e A) => e_tapp (open_exp_wrt_exp_rec k e_5 e) A
  | (e_rcd i5 e) => e_rcd i5 (open_exp_wrt_exp_rec k e_5 e)
  | (e_proj e i5) => e_proj (open_exp_wrt_exp_rec k e_5 e) i5
  | e_unit => e_unit
  | (e_loct) => e_loct
end.



Fixpoint open_exp_wrt_typ_rec (k:nat) (A5:typ) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_loc o5) => e_loc o5 
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_typ_rec k A5 e) 
  | (e_tabs e) => e_tabs (open_exp_wrt_typ_rec (S k) A5 e) 
  | (e_app e1 e2) => e_app (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_typ_rec k A5 e) (open_typ_wrt_typ_rec k A5 A)
  | (e_ref e) => e_ref (open_exp_wrt_typ_rec k A5 e)
  | (e_deref e) => e_deref (open_exp_wrt_typ_rec k A5 e)
  | (e_ass e1 e2) => e_ass (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_tapp e A) => e_tapp (open_exp_wrt_typ_rec k A5 e) (open_typ_wrt_typ_rec k A5 A)
  | (e_rcd i5 e) => e_rcd i5 (open_exp_wrt_typ_rec k A5 e)
  | (e_proj e i5) => e_proj (open_exp_wrt_typ_rec k A5 e) i5 
  | e_unit => e_unit
  | e_loct => e_loct
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.


Definition open_exp_wrt_typ A5 e_5 := open_exp_wrt_typ_rec 0 e_5 A5.

Definition open_typ_wrt_typ A5 A_6 := open_typ_wrt_typ_rec 0 A_6 A5.


(** terms are locally-closed pre-terms *)
(** definitions *)


Inductive lc_typ : typ -> Prop :=    (* defn lc_typ *)
 | lc_t_tvar_f : forall (X:typevar),
     (lc_typ (t_tvar_f X))
 | lc_t_int : 
     (lc_typ t_int)
 | lc_t_top : 
     (lc_typ t_top)
 | lc_t_arrow : forall (A B:typ),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_typ (t_arrow A B))
 | lc_t_and : forall (A B:typ),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_typ (t_and A B))
 | lc_t_ref : forall (A:typ),
     (lc_typ A) ->
     (lc_typ (t_ref A))
 | lc_t_forall : forall (A B:typ),
     (lc_typ A) ->
      ( forall X , lc_typ  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     (lc_typ (t_forall A B))
 | lc_t_rcd : forall i5 (A:typ),
     (lc_typ A) ->
     (lc_typ (t_rcd i5 A))
 | lc_t_unit : 
     (lc_typ t_unit).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_loc : forall o5,
     (lc_exp (e_loc o5))
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_top : 
     (lc_exp (e_top))
 | lc_e_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_tabs : forall (e:exp),
      ( forall X , lc_exp  ( open_exp_wrt_typ e (t_tvar_f X) )  )  ->
     (lc_exp (e_tabs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_merge : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_merge e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_exp (e_anno e A))
 | lc_e_ref : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_ref e))
 | lc_e_deref : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_deref e))
 | lc_e_ass : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_ass e1 e2))
 | lc_e_tapp : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_exp (e_tapp e A))
 | lc_e_rcd : forall i5 (e:exp),
     (lc_exp e) ->
     (lc_exp (e_rcd i5 e))
 | lc_e_proj : forall i5 (e:exp),
     (lc_exp e) ->
     (lc_exp (e_proj e i5))
 | lc_e_unit : 
     (lc_exp (e_unit))
 | lc_e_loct : 
     (lc_exp (e_loct)).

Fixpoint typefv_typ (A5:typ) : vars :=
  match A5 with
  | (t_tvar_b nat) => {}
  | (t_tvar_f X) => {{X}}
  | t_int => {}
  | t_top => {}
  | (t_arrow A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_and A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_ref A) => (typefv_typ A)
  | (t_forall A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_rcd i5 A) => (typefv_typ A)
  | t_unit => {}
end.


(** free variables *)
Fixpoint typefv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {}
  | (e_loc o5) => {}
  | e_top  => {}
  | (e_lit i5) => {}
  | (e_abs e) => (typefv_exp e) 
  | (e_tabs e) => (typefv_exp e) 
  | (e_app e1 e2) => (typefv_exp e1) \u (typefv_exp e2)
  | (e_merge e1 e2) => (typefv_exp e1) \u (typefv_exp e2)
  | (e_anno e A) => (typefv_exp e) \u (typefv_typ A)
  | (e_ref e) => (typefv_exp e)
  | (e_deref e) => (typefv_exp e)
  | (e_ass e1 e2) => (typefv_exp e1) \u (typefv_exp e2)
  | (e_tapp e A) => (typefv_exp e) \u (typefv_typ A)
  | (e_rcd i5 e) => (typefv_exp e)
  | (e_proj e i5) => (typefv_exp e)
  | e_unit  => {}
  | e_loct  => {}
end.


Fixpoint termfv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_loc o5) => {}
  | e_top => {}
  | (e_lit i5) => {}
  | (e_abs e) => (termfv_exp e)
  | (e_tabs e) => (termfv_exp e)
  | (e_app e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_merge e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_anno e A) => (termfv_exp e)
  | (e_ref e) => (termfv_exp e)
  | (e_deref e) => (termfv_exp e)
  | (e_ass e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_tapp e A) => (termfv_exp e)
  | (e_rcd i5 e) => (termfv_exp e)
  | (e_proj e i5) => (termfv_exp e)
  | e_unit  => {}
  | e_loct  => {}
end.

(** substitutions *)

Fixpoint typsubst_typ (A5:typ) (X5:typevar) (A_6:typ) {struct A_6} : typ :=
  match A_6 with
  | (t_tvar_b nat) => t_tvar_b nat
  | (t_tvar_f X) => (if eq_var X X5 then A5 else (t_tvar_f X))
  | t_int => t_int 
  | t_top => t_top 
  | (t_arrow A B) => t_arrow (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_and A B) => t_and (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_ref A) => t_ref (typsubst_typ A5 X5 A)
  | (t_forall A B) => t_forall (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_rcd i5 A) => t_rcd i5 (typsubst_typ A5 X5 A)
  | t_unit  => t_unit
end.

Fixpoint typsubst_exp (A5:typ) (X5:typevar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_loc o5) => e_loc o5
  | e_top => e_top
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (typsubst_exp A5 X5 e) 
  | (e_tabs e) => e_tabs (typsubst_exp A5 X5 e) 
  | (e_app e1 e2) => e_app (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_merge e1 e2) => e_merge (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_anno e A) => e_anno (typsubst_exp A5 X5 e) (typsubst_typ A5 X5 A)
  | (e_ref e) => e_ref (typsubst_exp A5 X5 e)
  | (e_deref e) => e_deref (typsubst_exp A5 X5 e)
  | (e_ass e1 e2) => e_ass (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_tapp e A) => e_tapp (typsubst_exp A5 X5 e) (typsubst_typ A5 X5 A)
  | (e_rcd i5 e) => e_rcd i5 (typsubst_exp A5 X5 e) 
  | (e_proj e i5) => e_proj (typsubst_exp A5 X5 e) i5
  | e_unit  => e_unit
  | e_loct  => e_loct
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_loc o5) => e_loc o5
  | e_top  => e_top 
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_tabs e) => e_tabs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_merge e1 e2) => e_merge (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_ref e) => e_ref (subst_exp e_5 x5 e)
  | (e_deref e) => e_deref (subst_exp e_5 x5 e)
  | (e_ass e1 e2) => e_ass (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_tapp e A) => e_tapp (subst_exp e_5 x5 e) A
  | (e_rcd i5 e) => e_rcd i5 (subst_exp e_5 x5 e)
  | (e_proj e i5) => e_proj (subst_exp e_5 x5 e) i5
  | e_unit  => e_unit 
  | e_loct  => e_loct 
end.
 

(** definitions *)



Fixpoint principle_type (e : exp) : typ :=
    match e with 
    | e_top  => t_top 
    | (e_lit i) => t_int 
    | (e_merge v1 v2) => t_and (principle_type v1) (principle_type v2)
    | (e_anno e A) => A
    | (e_rcd l v) => t_rcd l (principle_type v)
    | e_unit  => t_unit 
    | _ => t_top
    end.


Inductive fvalue : exp -> Prop :=    (* defn value *)
 | fvalue_abs : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs e) ->
     lc_typ (t_arrow A B) ->
    fvalue  (e_anno (e_abs e) (t_arrow A B)) 
 | fvalue_f : forall f A B,
     fvalue f ->
     lc_typ (t_arrow A B) ->
     fvalue (e_anno f (t_arrow A B))
.


(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_top : 
     value (e_top)
 | value_unit : 
     value (e_unit)
 | value_lit : forall (i5:i),
     value (e_lit i5)
 | value_f : forall f,
     fvalue f ->
     value  f
 | value_merge : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     value (e_merge v1 v2)
 | value_loc : forall (o:nat) A,
     lc_typ A ->
     value (e_anno (e_loc o) (t_ref A))
 | value_tabs : forall (e:exp) A (B:typ),
     lc_exp (e_tabs e) ->
     lc_typ (t_forall A B) ->
     value  (e_anno (e_tabs e) (t_forall A B) ) 
 | value_rcd : forall i5 v,
     value v ->
     value (e_rcd i5 v)
 | value_loct : forall A,
     lc_typ A ->
     value (e_anno (e_loct) (t_ref A))
.

(* defns TopLikeType *)
Inductive topLike : typ -> Prop :=    (* defn topLike *)
 | TL_top : 
     topLike t_top
 | TL_and : forall (A B:typ),
     topLike A ->
     topLike B ->
     topLike (t_and A B)
 | TL_arr : forall (A B:typ),
     lc_typ A ->
     topLike B ->
     topLike (t_arrow A B)
 | TL_all : forall L A B,
      lc_typ A ->
     ( forall X , X \notin  L  -> topLike  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
    topLike (t_forall A B)
  | TL_rcd : forall i5 (A:typ),
     topLike A ->
     topLike (t_rcd i5 A)
  | TL_ref : forall (A:typ),
     topLike A ->
     topLike (t_ref  A)
.

(* defns SplitType *)
Inductive spl : typ -> typ -> typ -> Prop :=    (* defn spl *)
 | Sp_and : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     spl (t_and A B) A B
 | Sp_arrow : forall (A B C D:typ),
     lc_typ A ->
     spl B C D ->
     spl (t_arrow A B) (t_arrow A C) (t_arrow A D)
  | Sp_forall : forall (L:vars) (A B C1 C2:typ),
      lc_typ A ->
      ( forall X , X \notin  L  -> spl  ( open_typ_wrt_typ B (t_tvar_f X) )   ( open_typ_wrt_typ C1 (t_tvar_f X) )   ( open_typ_wrt_typ C2 (t_tvar_f X) )  )  ->
     spl (t_forall A B) (t_forall A C1) (t_forall A C2)
  | Sp_rcd : forall l (B C1 C2:typ),
     spl B C1 C2 ->
     spl (t_rcd l B) (t_rcd l C1) (t_rcd l C2)
.

(* defns OrdinaryType *)
Inductive ord : typ -> Prop :=    (* defn ord *)
| O_var : forall (X:typevar),
     ord (t_tvar_f X)
 | O_top : 
     ord t_top
 | O_int : 
     ord t_int
 | O_arrow : forall (A B:typ),
     lc_typ A ->
     ord B ->
     ord (t_arrow A B)
 | O_ref : forall (A:typ),
     lc_typ A ->
     ord (t_ref A)
 | O_forall : forall (L:vars) (A B:typ),
     lc_typ A ->
      ( forall X , X \notin  L  -> ord  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     ord (t_forall A B)
 | O_rcd : forall i5 (B:typ),
     ord B ->
     ord (t_rcd i5 B)
 | O_unit : 
     ord t_unit.

(* defns Subtyping *)

(* defns AlgorithmicSubtyping *)
Inductive algo_sub : typ -> typ -> Prop :=    (* defn algo_sub *)
 | S_int : 
     algo_sub t_int t_int
 | S_top : forall (A:typ),
     lc_typ A ->
     algo_sub A t_top
 | S_ref : forall (A B:typ),
     algo_sub A B ->
     algo_sub B A ->
     algo_sub (t_ref A) (t_ref B)
 | S_andl : forall (A B C:typ),
     lc_typ B ->
     ord C ->
     algo_sub A C ->
     algo_sub (t_and A B) C
 | S_andr : forall (A B C:typ),
     lc_typ A ->
     ord C ->
     algo_sub B C ->
     algo_sub (t_and A B) C
 | S_arr : forall (A C B D:typ),
     ord D ->
     algo_sub B A ->
     algo_sub C D ->
     algo_sub (t_arrow A C) (t_arrow B D)
 | S_and : forall (A D B C:typ),
     spl D B C ->
     algo_sub A B ->
     algo_sub A C ->
     algo_sub A D
 | S_forall : forall (L:vars) (A1 A2 B1 B2:typ),
      ( forall X , X \notin  L  -> ord  ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     algo_sub B1 A1 ->
      ( forall X , X \notin  L  -> algo_sub ( open_typ_wrt_typ A2 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     algo_sub (t_forall A1 A2) (t_forall B1 B2)
 | S_var : forall X,
     algo_sub (t_tvar_f X) (t_tvar_f X)
 | S_rcd : forall  (l:label) (A B:typ),
     ord B ->
     algo_sub A B ->
     algo_sub (t_rcd l A) (t_rcd l B)
 | S_unit : 
     algo_sub t_unit t_unit.


(* defns DisjointnessAxiom *)
Inductive disjoint_axiom : typ -> typ -> Prop :=    (* defn disjoint_axiom *)
 | Dax_intArr : forall (A1 A2:typ),
     disjoint_axiom t_int (t_arrow A1 A2)
 | Dax_intForall : forall (A B:typ),
     disjoint_axiom t_int (t_forall A B)
 | Dax_arrForall : forall (A1 A2 A B:typ),
     disjoint_axiom (t_arrow A1 A2) (t_forall A B)
 | Dax_arrInt : forall (A1 A2:typ),
     disjoint_axiom (t_arrow A1 A2) t_int
 | Dax_forallInt : forall (A B:typ),
     disjoint_axiom (t_forall A B) t_int
 | Dax_forallArr : forall (A B A1 A2:typ),
     disjoint_axiom (t_forall A B) (t_arrow A1 A2)
 | Dax_refall : forall (A A1 A2:typ),
     disjoint_axiom (t_ref A) (t_forall A1 A2)
 | Dax_Allref : forall (A1 A2 A:typ), 
     disjoint_axiom (t_forall A1 A2) (t_ref A)
 | Dax_refInt : forall (A:typ),
     disjoint_axiom (t_ref A) t_int
 | Dax_Intref : forall (A:typ),
     disjoint_axiom t_int (t_ref A)
 | Dax_refarr : forall (A A1 A2:typ),
     disjoint_axiom (t_ref A) (t_arrow A1 A2)
 | Dax_Arrref : forall (A1 A2 A:typ),
     disjoint_axiom (t_arrow A1 A2) (t_ref A)
 | Dax_rcd : forall (A2 B2:typ) i5 i6,
     i5 <> i6 ->
     disjoint_axiom (t_rcd i5 A2) (t_rcd i6 B2)
 | Dax_arrRcd : forall (A1 A2:typ) (l:label) (A:typ),
    disjoint_axiom (t_arrow A1 A2) (t_rcd l A)
 | Dax_rcdArr : forall (A1 A2:typ) (l:label) (A:typ),
    disjoint_axiom (t_rcd l A) (t_arrow A1 A2)
 | Dax_rcdInt : forall (l:label) (A:typ),
     disjoint_axiom (t_rcd l A) t_int
 | Dax_intRcd : forall (l:label) (A:typ),
     disjoint_axiom t_int (t_rcd l A) 
 | Dax_refRcd : forall l (A A2:typ),
     disjoint_axiom (t_ref A) (t_rcd l A2)
 | Dax_rcdref : forall l (A1 A:typ),
     disjoint_axiom (t_rcd l A1) (t_ref A)
 | Dax_allRcd : forall (A1 A2:typ) (l:label) (A:typ),
    disjoint_axiom (t_forall A1 A2) (t_rcd l A)
 | Dax_rcdAll : forall (A1 A2:typ) (l:label) (A:typ),
    disjoint_axiom (t_rcd l A) (t_forall A1 A2)
 | Dax_unitInt : 
    disjoint_axiom t_unit t_int
 | Dax_Intunit : 
    disjoint_axiom t_int t_unit
 | Dax_arrunit : forall (A1 A2:typ),
     disjoint_axiom (t_arrow A1 A2) t_unit
 | Dax_unitarr : forall (A1 A2:typ),
     disjoint_axiom t_unit (t_arrow A1 A2) 
 | Dax_unitForall : forall (A B:typ),
     disjoint_axiom (t_forall A B) t_unit
 | Dax_Forallunit : forall (A B:typ),
     disjoint_axiom t_unit (t_forall A B) 
 | Dax_rcdunit : forall (l:label) (A:typ),
    disjoint_axiom (t_rcd l A) t_unit
 | Dax_unitrcd : forall (l:label) (A:typ),
    disjoint_axiom t_unit (t_rcd l A) 
 | Dax_unitref : forall (A:typ),
    disjoint_axiom t_unit (t_ref A)
 | Dax_refunit : forall (A:typ),
    disjoint_axiom (t_ref A) t_unit
.



(* defns Disjoint *)
Inductive disjoint : ctx -> typ -> typ -> Prop :=    
 | D_axiom : forall G A B,
    disjoint_axiom A B ->
    disjoint G A B 
 | D_topL : forall (A:typ) B G,
     topLike B ->
     disjoint G B A
 | D_topR : forall (A:typ) B G,
     topLike B ->
     disjoint G A B
 | D_andL : forall A (A1 A2 B:typ) G,
     spl A A1 A2 ->
     disjoint G A1 B ->
     disjoint G A2 B ->
     disjoint G A B
 | D_andR : forall (A B1 B2:typ) G B,
     spl B B1 B2 ->
     disjoint G A B1 ->
     disjoint G A B2 ->
     disjoint G A B
 | D_ArrArr : forall (A1 A2 B1 B2:typ) G,
     disjoint G A2 B2 ->
     disjoint G (t_arrow A1 A2) (t_arrow B1 B2)
 | D_varL : forall (A:typ) G B X,
     binds  X (TyDis A) G  ->
     algo_sub A B ->
     disjoint G (t_tvar_f X) B
 | D_varR : forall (A:typ) G B X,
     binds  X (TyDis A) G  ->
     algo_sub A B ->
     disjoint G B (t_tvar_f X)
 | D_forall : forall (G : ctx) (A1 A2 B1 B2: typ) (L:vars),
    ( forall X , X \notin  L  -> 
    disjoint  (cons ( X , TyDis (t_and A1 A2) )  G )  ( open_typ_wrt_typ B1 (t_tvar_f X) ) ( open_typ_wrt_typ B2 (t_tvar_f X) ) ) ->
    lc_typ (t_and A1 A2) ->
    disjoint G (t_forall A1 B1) (t_forall A2 B2) 
 | D_rcdeq : forall G (A2 B2:typ) i5 ,
    disjoint G A2 B2 ->
    disjoint G (t_rcd i5 A2) (t_rcd i5 B2)
 | D_ref : forall G (A2 B2:typ) ,
    disjoint G A2 B2 ->
    disjoint G (t_ref A2) (t_ref B2)
.



Inductive WFEnv : ctx -> Prop :=    
 | WFNil : 
     WFEnv nil
 | WFPushV : forall G x A,
     WFEnv G ->
     x `notin` union (dom G) (typefv_typ A)  ->
     WFEnv (cons ( x , (TyDis A) )  G )
 | WFPushT : forall G x A,
     WFEnv G ->
     x `notin` (dom G)   ->
     WFEnv (cons ( x , (TermV A))  G) .


Inductive TWell : ctx -> typ -> Prop :=    
 | TWell_top : forall G,
     WFEnv G ->
     TWell G t_top
 | TWell_int : forall G,
     WFEnv G ->
     TWell G t_int
 | TWell_unit : forall G,
     WFEnv G ->
     TWell G t_unit
 | TWell_arrow : forall (A B:typ) G,
     TWell G A ->
     TWell G B ->
     TWell G (t_arrow A B)
 | TWell_ref : forall (A:typ) G,
     TWell G A ->
     TWell G (t_ref A)
 | TWell_and : forall (A:typ) B G,
     TWell G A ->
     TWell G B ->
     TWell G (t_and A B)
 | TWell_tvar : forall X G A,
     WFEnv G ->
     binds X (TyDis A) G ->
     TWell G (t_tvar_f X)
 | TWell_forall : forall (A:typ) B G L,
     TWell G A ->
     ( forall X , X \notin  L  -> 
     TWell  (cons ( X , TyDis A )  G )  ( open_typ_wrt_typ B (t_tvar_f X) ) ) ->
     TWell G (t_forall A B)
 | TWell_rcd : forall i5 (A:typ) G,
     TWell G A ->
     TWell G (t_rcd i5 A).


Inductive WFTyp : ctx -> typ -> Prop :=    
 | w_top : forall G,
     WFEnv G ->
     WFTyp G t_top
 | w_int : forall G,
     WFEnv G ->
     WFTyp G t_int
 | w_unit : forall G,
     WFEnv G ->
     WFTyp G t_unit
 | w_arrow : forall (A B:typ) G,
     WFTyp G A ->
     WFTyp G B ->
     WFTyp G (t_arrow A B)
 | w_ref : forall (A:typ) G,
     WFTyp G A ->
     WFTyp G (t_ref A)
 | w_and : forall (A:typ) B G,
     WFTyp G A ->
     WFTyp G B ->
     disjoint G A B ->
     WFTyp G (t_and A B)
 | w_tvar : forall X G A,
     WFEnv G ->
     binds X (TyDis A) G ->
     WFTyp G (t_tvar_f X)
 | w_forall : forall (A:typ) B G L,
     TWell G A ->
     ( forall X , X \notin  L  -> 
     WFTyp  (cons ( X , (TyDis A) )  G )  ( open_typ_wrt_typ B (t_tvar_f X) ) ) ->
     WFTyp G (t_forall A B)
 | w_rcd : forall (A:typ) G i5,
     WFTyp G A ->
     WFTyp G (t_rcd i5 A)
.



Inductive ctx_item : Type :=
  | appCtxL : exp -> ctx_item
  | appCtxR : exp -> ctx_item
  | mergeCtxL : exp -> ctx_item
  | mergeCtxR : exp -> ctx_item
  | refCtx :  ctx_item
  | getCtx : ctx_item
  | setCtxL : exp -> ctx_item 
  | setCtxR : exp -> ctx_item 
  | annoCtx : typ -> ctx_item 
  | tappCtx : typ -> ctx_item
  | rcdCtx : nat -> ctx_item 
  | projCtx : nat -> ctx_item 
.

Inductive WFTypformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    lc_exp e ->
                    WFTypformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    value v ->
                    WFTypformed (appCtxR v)
     | wf_mergeCtxL : forall (e : exp),
                    lc_exp e ->
                    WFTypformed (mergeCtxL e)
     | wf_mergeCtxR : forall (v : exp),
                    value v ->
                    WFTypformed (mergeCtxR v)
     | wf_setCtxL : forall e,
                    lc_exp e ->
                    WFTypformed (setCtxL e)
     | wf_setCtxR : forall e,
                    value e ->
                    WFTypformed (setCtxR e)
     | wf_refCtx : 
                    WFTypformed refCtx
     | wf_getCtx : 
                    WFTypformed getCtx
     | wf_annoCtx : forall A,
                    WFTypformed (annoCtx A) 
     | wf_tappCtx : forall A,
                    WFTypformed (tappCtx A) 
     | wf_rcdCtx : forall i5,
                    WFTypformed (rcdCtx i5) 
     | wf_projCtx : forall i5,
                    WFTypformed (projCtx i5) 
.


Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | mergeCtxL e2 => e_merge e e2
     | mergeCtxR v1 => e_merge v1 e
     | setCtxL e2 => e_ass e e2
     | setCtxR v1 => e_ass v1 e
     | refCtx => e_ref e
     | getCtx => e_deref e
     | annoCtx A => e_anno e A 
     | tappCtx A => e_tapp e A 
     | rcdCtx i5 => e_rcd i5 e 
     | projCtx i5 => e_proj e i5 
     end.


Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Definition conf := (exp * sto)%type.


Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok nil
  | sto_ok_push : forall mu t,
      sto_ok mu -> value t -> 
      sto_ok (t :: mu).

Inductive phi_ok : ctx -> phi -> Prop :=
  | phi_ok_empty : forall G,
     phi_ok G nil
  | phi_ok_push : forall mu G t,
      phi_ok G mu -> WFTyp G t -> 
      phi_ok G (t :: mu).



(* defns IsomorphicSubtyping *)
Inductive subsub : typ -> typ -> Prop :=    (* defn subsub *)
 | IS_refl : forall (A:typ),
     lc_typ A ->
     subsub A A
 | IS_and : forall (A1 A2 B B1 B2:typ),
     spl B B1 B2 ->
     subsub A1 B1 ->
     subsub A2 B2 ->
     subsub (t_and A1 A2) B
 | IS_ref : forall A B, 
     subsub A B ->
     subsub (t_ref A) (t_ref B)
 | IS_rcd : forall i5 A B, 
     subsub A B ->
     subsub (t_rcd i5 A) (t_rcd i5 B). 


Fixpoint TLVal (A : typ) : exp :=
    match A with 
    | t_top => e_top 
    | (t_arrow A1 A2) =>  (e_anno (e_abs (TLVal A2)) (t_arrow A1 A2))
    | (t_forall A1 B1) => (e_anno (e_tabs (TLVal B1)) (t_forall A1 B1))
    | (t_rcd i5 A1) => (e_rcd i5 (TLVal A1))
    | t_ref A1 => (e_anno (e_loct) (t_ref A1)) 
    | t_and A1 A2 => (e_merge (TLVal A1) (TLVal A2)) 
    | _ => e_top
    end.

Inductive Cast : exp -> typ -> exp -> Prop :=    (* defn Cast *)
 | cast_top : forall (v:exp) A,
     lc_exp v ->
     ord A ->
     topLike A ->
     algo_sub (principle_type v) A ->
     Cast (v) A (TLVal A)
 | cast_i : forall (i5:i) ,
     Cast ((e_lit i5)) t_int ((e_lit i5))
 | cast_unit : 
     Cast ((e_unit)) t_unit ((e_unit))
 | cast_lam : forall (A1:typ) f (B1 A2 B2:typ),
     fvalue f ->
     not (topLike (t_arrow A2 B2))  ->
     ord (t_arrow A2 B2) ->
     principle_type f = (t_arrow A1 B1) ->
     algo_sub (t_arrow A1 B1) (t_arrow A2 B2) ->
     Cast f (t_arrow A2 B2) (e_anno f (t_arrow A2 B2))
 | cast_ref : forall (o:nat) (A:typ) B,
    not(topLike (t_ref B)) ->
    algo_sub (t_ref A) (t_ref B) ->
    Cast ((e_anno (e_loc o) (t_ref A))) (t_ref B) ((e_anno (e_loc o) (t_ref B)))
 | cast_tabs : forall e (A1:typ) B1 A2 B2,
    not (topLike (t_forall A2 B2) )  ->
    ord (t_forall A2 B2) ->
    algo_sub (t_forall A1 B1) (t_forall A2 B2) ->
    Cast (e_anno (e_tabs e) (t_forall A1 B1)) (t_forall A2 B2) (e_anno (e_tabs e) (t_forall A2 B2))
 | cast_rcd : forall l v B v',
    ord (t_rcd l B) ->
    Cast v B v' ->
    Cast ((e_rcd l v)) (t_rcd l B) ((e_rcd l v'))
 | cast_mergel : forall (v1 v2:exp) (A:typ) (v1':exp),
     lc_exp v2 ->
     ord A ->
     Cast (v1) A (v1') ->
     Cast ((e_merge v1 v2)) A (v1')
 | cast_merger : forall (v1 v2:exp) (A:typ) (v2':exp),
     lc_exp v1 ->
     ord A ->
     Cast (v2) A (v2') ->
     Cast (e_merge v1 v2) A (v2')
 | cast_and : forall (v:exp) (A:typ) (v1 v2:exp) (B C:typ),
     spl A B C ->
     Cast (v) B (v1) ->
     Cast (v) C (v2) ->
     Cast (v) A ((e_merge v1 v2)).


(* defns MergeTwoApplicativeTypes *)
Inductive Merge : typ -> typ -> typ -> Prop :=    (* defn Merge *)
 | M_arrow : forall (A B1 B2:typ),
     lc_typ A ->
     lc_typ B1 ->
     lc_typ B2 ->
     Merge (t_arrow A B1) (t_arrow A B2) (t_arrow A (t_and B1 B2))
 | M_forall : forall (A1 A2 B1 B2:typ),
     lc_typ (t_forall A1 A2) ->
     lc_typ (t_forall B1 B2) ->
     lc_typ A1 ->
     lc_typ B1 ->
     Merge (t_forall A1 A2) (t_forall B1 B2) (t_forall (t_and A1 B1)  (t_and A2 B2) )
 | M_rcd : forall i5 (B1 B2:typ),
     lc_typ B1 ->
     lc_typ B2 ->
     Merge (t_rcd i5 B1) (t_rcd i5 B2) (t_rcd i5 (t_and B1 B2))
.



Inductive appDist : typ -> typ -> Prop :=    
 | AD_arr : forall A1 A2,
     lc_typ (t_arrow A1 A2) ->
     appDist (t_arrow A1 A2) (t_arrow A1 A2)
 | AD_ref : forall A,
     lc_typ (t_ref A) ->
     appDist (t_ref A) (t_ref A)
 | AD_forall : forall A1 A2,
     lc_typ (t_forall A1 A2) ->
     appDist (t_forall A1 A2) (t_forall A1 A2)
 | AD_rcd : forall i5 A,
     lc_typ (t_rcd i5 A) ->
     appDist (t_rcd i5 A) (t_rcd i5 A)
 | AD_and : forall B A1 A2 B1 B2,
     Merge B1 B2 B ->
     appDist A1 B1 ->
     appDist A2 B2 ->
     appDist (t_and A1 A2) B.


Inductive arg : Set :=
  | arg_exp (e : exp) : arg
  | arg_typ (t : typ) : arg
  | arg_la (l:nat) : arg.


Inductive papp :  exp -> arg -> sto -> exp -> sto -> Prop :=    (* defn papp *)
 | pap_beta : forall (A:typ) (e:exp) B (v:exp) (v':exp) mu,
     lc_exp (e_abs e) ->
     value v ->
     Cast (v) A v' ->
     papp (e_anno (e_abs e) (t_arrow A B)) (arg_exp v) mu (e_anno (open_exp_wrt_exp e v') B) mu
 | pap_app : forall f v A B mu,
     fvalue f ->
     value v ->
     papp (e_anno f (t_arrow A B)) (arg_exp v) mu (e_anno (e_app f (e_anno v A)) B) mu
 | pap_tapp : forall (A:typ) (e:exp) B C mu,
     lc_exp (e_tabs e) ->
     papp (e_anno (e_tabs e) (t_forall A B)) (arg_typ C) mu (e_anno (open_exp_wrt_typ e C) (open_typ_wrt_typ B C)) mu
 | pap_ass : forall (mu:sto) (o:nat) (v v':exp) A,
     value v ->
     Cast (v) (principle_type (store_lookup o mu)) (v') ->
     papp (e_anno (e_loc o) A) (arg_exp v) mu  (e_unit) (replace o v' mu)
 | pap_asst : forall (mu:sto) (v:exp) A,
     value v ->
     papp (e_anno (e_loct) A) (arg_exp v) mu  (e_unit)  mu
 | pap_proj : forall v l mu,
     value v ->
     papp (e_rcd l v) (arg_la l) mu v mu
 | pap_merge : forall (v1 v2:exp) arg5 e3 e4 mu,
     value v1 ->
     value v2 -> 
     papp v1 arg5 mu (e3) mu ->
     papp v2 arg5 mu (e4) mu ->
     papp (e_merge v1 v2) arg5 mu ((e_merge e3 e4)) mu
.



Inductive step : conf  -> conf  -> Prop :=    (* defn step *)
  | step_eval : forall mu mu' F e1 e2,
     WFTypformed F ->
     step (e1, mu) (e2, mu') ->
     step ((fill F e1), mu) (((fill F e2)), mu')
 | Step_beta : forall (mu:sto)  (e:exp)  (v1 v2:exp),
     sto_ok mu ->
     value v1 ->
     value v2 ->
     papp v1 (arg_exp v2) mu e mu ->
     step ((e_app  v1 v2), mu) (e, mu)
 | Step_annov : forall (mu:sto) (v:exp) (A:typ) (v':exp),
     sto_ok mu ->
     value v ->
     Cast (v) A (v') ->
     not (value (e_anno v A)) ->
     step ((e_anno v A), mu) (v', mu)
 | Step_deref : forall (mu:sto) (o:nat) (A:typ),
     sto_ok mu ->
     step ((e_deref (e_anno (e_loc o) (t_ref A)) ), mu) ((e_anno (store_lookup o mu) A), mu)
 | Step_dereft : forall (mu:sto) (A:typ),
     sto_ok mu ->
     step ((e_deref (e_anno (e_loct) (t_ref A)) ), mu) ((TLVal A), mu)
 | Step_ref : forall (mu:sto) (v:exp),
     sto_ok mu ->
     value v ->
     step ((e_ref v), mu)  ((e_anno (e_loc (length mu)) (t_ref (principle_type v))), mu ++ v::nil)
 | Step_tapp : forall (mu:sto)  (e:exp) v1 A,
     sto_ok mu ->
     value v1 ->
     lc_typ A ->
     papp v1 (arg_typ A) mu e mu ->
     step ((e_tapp v1 A), mu) (e, mu)
 | Step_ass : forall (mu:sto) v1 v2 e mu',
     sto_ok mu ->
     value v1 ->
     value v2 ->
     papp v1 (arg_exp v2) mu e mu' ->
     step ((e_ass v1 v2), mu)  (e, mu')
 | Step_pproj : forall (v:exp) i5 (e:exp) mu,
     value v ->
     papp v (arg_la i5) mu e mu ->
     step ((e_proj v i5), mu) (e, mu)
.


Definition disjointSpec A B :=
  forall C, algo_sub A C -> algo_sub B C -> topLike C.
  


Inductive prevalue : exp -> Prop :=    (* defn prevalue *)
 | PV_val : forall (v:exp),
     value v ->
     prevalue v
 | PV_anno : forall (e:exp) (A:typ),
     lc_exp e ->
     prevalue (e_anno e A)
 | PV_merge : forall (u1 u2:exp),
     prevalue u1 ->
     prevalue u2 ->
     prevalue (e_merge u1 u2).

(* defns Typing *)
Inductive Typing : phi -> ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_top : forall (L:phi) (G:ctx),
      WFEnv G ->
     Typing L G (e_top) Inf t_top
 | Typ_lit : forall (L:phi) (G:ctx) (i5:i),
      WFEnv G ->
     Typing L G (e_lit i5) Inf t_int
 | Typ_var : forall (L:phi) (G:ctx) (x:var) (A:typ),
      WFEnv G ->
      binds  x (TermV A) G  ->
      WFTyp G A ->
     Typing L G (e_var_f x) Inf A
 | Typ_abs : forall (LL : vars)  L (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  LL  -> Typing L  (cons ( x , (TermV A) )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     WFTyp G A -> 
     Typing L G (e_anno (e_abs e) (t_arrow A B)) Inf (t_arrow A B)
 | Typ_app : forall (L:phi) (G:ctx) (e1 e2:exp) (A:typ) A1 A2,
     Typing L G e1 Inf A ->
     Typing L G e2 Chk A1 ->
     appDist A (t_arrow A1 A2) ->
     Typing L G (e_app e1 e2) Inf A2
 | Typ_merge : forall (L:phi) (G:ctx) (e1 e2:exp) (A B:typ),
     Typing L G e1 Inf A ->
     Typing L G e2 Inf B ->
     disjoint G A B ->
     Typing L G (e_merge e1 e2) Inf (t_and A B)
 | Typ_anno : forall (L:phi) (G:ctx) (e:exp) (A:typ),
     Typing L G e Chk A ->
     Typing L G (e_anno e A) Inf A
 | Typ_sub : forall (L:phi) (G:ctx) (e:exp) (B A:typ),
     Typing L G e Inf A ->
     algo_sub A B ->
     WFTyp G B ->
     Typing L G e Chk B
 | Typ_loc : forall (L:phi) (G:ctx) (o:nat) A,
      WFEnv G ->
     WFTyp G A ->
     o < length L ->
     algo_sub (t_ref  (store_Tlookup o L)) (t_ref A) ->
     Typing L G (e_anno (e_loc o) (t_ref A) ) Inf (t_ref A) 
 | Typ_ass : forall (L:phi) (G:ctx) (e1 e2:exp) (A:typ),
     Typing L G e1 Inf (t_ref A) ->
     Typing L G e2 Chk A ->
     Typing L G (e_ass e1 e2) Inf t_unit
 | Typ_deref : forall (L:phi) (G:ctx) (e:exp) (A:typ),
     Typing L G e Inf (t_ref A) ->
     Typing L G (e_deref e) Inf A
 | Typ_ref : forall (L:phi) (G:ctx) (e:exp) (A:typ),
     Typing L G e Inf A ->
     Typing L G (e_ref e) Inf (t_ref A)
 | Typ_tabs : forall LL L (G:ctx) (A:typ) (e:exp) B,
      ( forall X , X \notin  LL  -> Typing L  (cons ( X , (TyDis A) )  G )   ( open_exp_wrt_typ e (t_tvar_f X) )  Chk ( open_typ_wrt_typ B (t_tvar_f X) ) )  ->
     TWell G A -> 
     Typing L G (e_anno (e_tabs e) (t_forall A B)) Inf (t_forall A B)
 | Typ_tapp : forall (L:phi) (G:ctx) e (A:typ) A1 A2 B,
     Typing L G e Inf A ->
     appDist A (t_forall A1 A2) ->
     WFTyp G B -> 
     disjoint G B A1 ->
     Typing L G (e_tapp e B) Inf (open_typ_wrt_typ A2 B)
 | Typ_rcd : forall (L:phi) (G:ctx) (e:exp) (A:typ) i5,
     Typing L G e Inf A ->
     Typing L G (e_rcd i5 e) Inf (t_rcd i5 A)
 | Typ_proj : forall (L:phi) (G:ctx) (e:exp) (A:typ) i5 B,
     Typing L G e Inf A ->
     appDist A (t_rcd i5 B) ->
     Typing L G (e_proj e i5) Inf B
 | Typ_unit : forall (L:phi) (G:ctx),
      WFEnv G ->
     Typing L G (e_unit) Inf t_unit
 | Typ_loct : forall (L:phi) (G:ctx) A,
     WFEnv G ->
    WFTyp G A ->
    topLike (t_ref A) ->
    Typing L G (e_anno (e_loct) (t_ref A) ) Inf (t_ref A) 
.

Definition sto_typing P mu :=
     sto_ok mu /\ 
     length P = length mu /\
     (forall l, l < length mu -> 
      exists A, Typing P nil (store_lookup l mu) Inf A /\ subsub A (store_Tlookup l P)).


Notation "P |== mu" := (sto_typing P mu) (at level 68).


Inductive extends : phi -> phi -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil  
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).

(** infrastructure *)

(* (* #[export] *)  *)
Hint Constructors fvalue Merge TWell WFEnv disjoint_axiom lc_typ extends WFTyp subsub prevalue WFTypformed algo_sub appDist papp sto_ok phi_ok value topLike spl ord disjoint Cast step Typing lc_exp : core.


