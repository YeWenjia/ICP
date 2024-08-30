(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Metalib.Metatheory.

(** syntax *)
Definition i : Set := nat.
Definition label : Set := nat.
Definition termvar : Set := var.

Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top *)
 | t_arrow (A:typ) (B:typ) (*r function type *)
 | t_and (A:typ) (B:typ) (*r intersection type *)
 | t_unit : typ (*r  *)
 | t_ref (A:typ) (*r function type *)
 | t_pos : typ (*r int *)
.

(** This uses the locally nameless representation for terms and cofinite quantification in typing judgements. *)
Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variable *)
 | e_var_f (x:termvar) (*r variable *)
 | e_top : exp (*r top *)
 | e_lit (i5:i) (*r lit *)
 | e_unit : exp (*r  *)
 | e_abs (e:exp) (A:typ) (*r abstraction *)
 | e_app (e1:exp) (e2:exp) (*r application *)
 | e_ref (e:exp) (*r  *)
 | e_loc (o:i) (*r  *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_get (e:exp) (*r  *)
 | e_set (e1:exp) (e2:exp) (*r set *)
 (* | e_val (e1:exp) (A:typ) *)
 .


Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.



 (* Inductive TyEnv : Set :=  
 | TyDis : typ -> TyEnv
 | TermV : typ -> TyEnv. *)



Definition sto : Set := list exp.
Definition phi : Set := list typ.

(* note that if location must exist, we restrict in typing rule that any location should be 
within the store *)
Definition store_Tlookup (n:nat) (ST: phi) :=
  nth n ST t_top.

Definition store_lookup (n:nat) (st:sto) :=
  nth n st (e_top).

Definition ctx : Set := list ( atom * typ ).


(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | e_unit => e_unit 
  | (e_abs e t) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e) t
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_ref e) => e_ref (open_exp_wrt_exp_rec k e_5 e)
  | (e_loc o) => e_loc o
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | (e_get e) => e_get (open_exp_wrt_exp_rec k e_5 e)
  | (e_set e1 e2) => e_set (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  (* | (e_val e t) => e_val (open_exp_wrt_exp_rec k e_5 e) t *)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:termvar),
     (lc_exp (e_var_f x))
 | lc_e_top : 
     (lc_exp e_top)
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_unit : 
     (lc_exp e_unit)
 | lc_e_abs : forall (e:exp) t,
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e t))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_ref : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_ref e))
 | lc_e_loc : forall (o:i),
     (lc_exp (e_loc o))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_get : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_get e))
 | lc_e_set : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_set e1 e2))
 (* | lc_e_val : forall (e:exp) t,
     (lc_exp e) ->
     (lc_exp (e_val e t)) *)
.

(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | e_top => {}
  | (e_lit i5) => {}
  | e_unit => {}
  | (e_abs e t) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_ref e) => (fv_exp e)
  | (e_loc o) => {}
  | (e_anno e A) => (fv_exp e)
  | (e_get e) => (fv_exp e)
  | (e_set e1 e2) => (fv_exp e1) \u (fv_exp e2)
  (* | (e_val e t) => (fv_exp e) *)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:termvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | e_unit => e_unit 
  | (e_abs e t) => e_abs (subst_exp e_5 x5 e) t
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_ref e) => e_ref (subst_exp e_5 x5 e)
  | (e_loc o) => e_loc o
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_get e) => e_get (subst_exp e_5 x5 e)
  | (e_set e1 e2) => e_set (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  (* | (e_val e t) => e_val (subst_exp e_5 x5 e) t *)
end.


(** definitions *)


Inductive tymu : exp -> sto -> typ -> Prop :=   
 | ty_top : forall mu, 
     tymu e_top mu t_top
 | ty_i : forall mu, 
     tymu (e_lit 0) mu t_int
 | ty_lit : forall i mu, 
     i > 0 ->
     tymu (e_lit i) mu t_pos 
 | ty_unit:forall mu, 
   tymu e_unit mu t_unit  
 | ty_loc:forall mu t p o,
   (e_anno p t) = store_lookup o mu ->  
   tymu (e_loc o) mu (t_ref t)  
.


Inductive pvalue : exp -> Prop :=    (* defn value *)
 | pvalue_abs : forall (A:typ) (e:exp) (B:typ) t,
     lc_exp (e_abs e t) ->
    pvalue (e_abs e t)
 | pvalue_top : 
     pvalue e_top
 | pvalue_unit : 
     pvalue e_unit
 | pvalue_lit : forall i, 
     pvalue (e_lit i)
 | pvalue_loc : forall i,
     pvalue (e_loc i)
.


Inductive ppvalue : exp -> Prop :=    (* defn value *)
 | ppvalue_top : 
     ppvalue e_top
 | ppvalue_unit : 
     ppvalue e_unit
 | ppvalue_lit : forall i, 
     ppvalue (e_lit i)
 | ppvalue_loc: forall o,
    ppvalue (e_loc o)
.


Inductive nvalue : exp -> Prop :=   
 | nvalue_abs : forall  (e:exp) t,
     lc_exp (e_abs e t) ->
    nvalue  (e_abs e t) 
 | nvalue_top : 
     nvalue e_top
 | nvalue_unit : 
     nvalue e_unit
 | nvalue_lit : forall i, 
     nvalue (e_lit i)
 | nvalue_loc : forall i,
     nvalue (e_loc i)
.



Inductive value : exp -> Prop :=    (* defn value *)
 | value_anno : forall p A,
     pvalue p ->
     value (e_anno p A)
 | value_abs : forall e A,
     lc_exp (e_abs e A) ->
     value (e_abs e A)
.


(* defns SplitType *)
Inductive spl : typ -> typ -> typ -> Prop :=    (* defn spl *)
 | Sp_and : forall (A B:typ),
     spl (t_and A B) A B
 | Sp_arrow : forall (A B C D:typ),
     spl B C D ->
     spl (t_arrow A B) (t_arrow A C) (t_arrow A D)
.

(* defns OrdinaryType *)
Inductive ord : typ -> Prop :=    (* defn ord *)
 | O_top : 
     ord t_top
 | O_int : 
     ord t_int
 | O_arrow : forall (A B:typ),
     ord B ->
     ord (t_arrow A B)
 | O_ref : forall (A:typ),
     ord (t_ref A)
 | O_unit : 
     ord t_unit
 | O_pos : 
     ord t_pos.

(* defns Subtyping *)

(* defns AlgorithmicSubtyping *)
Inductive algo_sub : typ -> typ -> Prop :=    (* defn algo_sub *)
 | S_int : 
     algo_sub t_int t_int
 | S_top : forall (A:typ),
     algo_sub A t_top
 | S_ref : forall (A B:typ),
     algo_sub A B ->
     algo_sub B A ->
     algo_sub (t_ref A) (t_ref B)
 | S_andl : forall (A B C:typ),
     ord C ->
     algo_sub A C ->
     algo_sub (t_and A B) C
 | S_andr : forall (A B C:typ),
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
 | S_unit : 
     algo_sub t_unit t_unit
 | S_pos : 
     algo_sub t_pos t_pos
 | S_posi : 
     algo_sub t_pos t_int
.




Inductive ctx_item : Type :=
  | appCtxL : exp -> ctx_item
  | appCtxR : exp -> ctx_item
  (* | mergeCtxL : exp -> ctx_item
  | mergeCtxR : exp -> ctx_item *)
  | refCtx :  ctx_item
  | getCtx : ctx_item
  | setCtxL : exp -> ctx_item 
  | setCtxR : exp -> ctx_item 
  (* | annoCtx : typ -> ctx_item  *)
  (* | tappCtx : typ -> ctx_item
  | rcdCtx : nat -> ctx_item 
  | projCtx : nat -> ctx_item  *)
.


Inductive nctx_item : Type :=
  | nappCtxL : exp -> nctx_item
  | nappCtxR : exp -> nctx_item
  | nrefCtx :  nctx_item
  | ngetCtx : nctx_item
  | nsetCtxL : exp -> nctx_item 
  | nsetCtxR : exp -> nctx_item 
.


Inductive Wformed : nctx_item -> Prop :=
     | nwf_appCtxL : forall (e : exp),
                    lc_exp e ->
                    Wformed (nappCtxL e)
     | nwf_appCtxR : forall (v : exp),
                    nvalue v ->
                    Wformed (nappCtxR v)
     | nwf_setCtxL : forall e,
                    lc_exp e ->
                    Wformed (nsetCtxL e)
     | nwf_setCtxR : forall e,
                    nvalue e ->
                    Wformed (nsetCtxR e)
     | nwf_refCtx : 
                    Wformed nrefCtx
     | nwf_getCtx : 
                    Wformed ngetCtx
.



Inductive WFTypformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    lc_exp e ->
                    WFTypformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    value v ->
                    WFTypformed (appCtxR v)
     (* | wf_mergeCtxL : forall (e : exp),
                    lc_exp e ->
                    WFTypformed (mergeCtxL e)
     | wf_mergeCtxR : forall (v : exp),
                    value v ->
                    WFTypformed (mergeCtxR v) *)
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
     (* | wf_annoCtx : forall A,
                    WFTypformed (annoCtx A)  *)
     (* | wf_tappCtx : forall A,
                    WFTypformed (tappCtx A) 
     | wf_rcdCtx : forall i5,
                    WFTypformed (rcdCtx i5) 
     | wf_projCtx : forall i5,
                    WFTypformed (projCtx i5)  *)
.



Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     (* | mergeCtxL e2 => e_merge e e2
     | mergeCtxR v1 => e_merge v1 e *)
     | setCtxL e2 => e_set e e2
     | setCtxR v1 => e_set v1 e
     | refCtx => e_ref e
     | getCtx => e_get e
     (* | annoCtx A => e_anno e A  *)
     (* | tappCtx A => e_tapp e A 
     | rcdCtx i5 => e_rcd i5 e 
     | projCtx i5 => e_proj e i5  *)
     end.

Definition nfill (E : nctx_item) (e : exp) : exp :=
     match E with
     | nappCtxL e2 => e_app e e2
     | nappCtxR v1 => e_app v1 e
     | nsetCtxL e2 => e_set e e2
     | nsetCtxR v1 => e_set v1 e
     | nrefCtx => e_ref e
     | ngetCtx => e_get e
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
      phi_ok G mu -> 
      phi_ok G (t :: mu).



Inductive step : conf  -> conf  -> Prop :=    (* defn step *)
  | step_eval : forall mu mu' F e1 e2,
     WFTypformed F ->
     step (e1, mu) (e2, mu') ->
     step ((fill F e1), mu) (((fill F e2)), mu')
 | Step_anno : forall (mu:sto) (A:typ) e e' mu',
     not (pvalue e) ->
     step (e, mu) (e', mu') -> 
     step ((e_anno e A) , mu) ((e_anno e' A), mu')
 | Step_beta : forall (mu:sto)  (e:exp) A1 B1 B2 C p,
     sto_ok mu ->
     pvalue p ->
     step ((e_app (e_anno ((e_abs e A1)) (t_arrow B1 B2)) (e_anno p C)), mu) (e_anno (open_exp_wrt_exp e (e_anno p A1)) B2, mu)
 | Step_app : forall (mu:sto)  (e1:exp) A1 B1 B2 t e2,
     sto_ok mu ->
     lc_exp (e_abs e1 A1) ->
     lc_exp (e_abs e2 t) ->
     step ((e_app (e_anno (e_abs e1 A1) (t_arrow B1 B2)) (e_abs e2 t)), mu) (e_app (e_anno (e_abs e1 A1) (t_arrow B1 B2)) (e_anno (e_abs e2 t) B1), mu)
 | Step_annov : forall (mu:sto) (A:typ) B p,
     sto_ok mu ->
     pvalue p ->
     step ((e_anno (e_anno p A) B), mu) ((e_anno p B), mu)
 | Step_deref : forall (mu:sto) (o:nat) (A:typ),
     sto_ok mu ->
     step ((e_get (e_anno (e_loc o) (t_ref A)) ), mu) ((e_anno (store_lookup o mu) A), mu)
 | Step_ref : forall (mu:sto) (v:exp) t,
     sto_ok mu ->
     value (e_anno v t) ->
     step ((e_ref (e_anno v t)), mu)  ((e_anno (e_loc (length mu)) (t_ref t)), mu ++ (e_anno v t)::nil)
 | Step_ass : forall (mu:sto) o p B A pp t,
     sto_ok mu ->
     pvalue p ->
     (e_anno pp t) = (store_lookup o mu) ->
     step ((e_set (e_anno (e_loc o) (t_ref A)) (e_anno p B)), mu)  (e_unit, replace o (e_anno p t) mu)
 | Step_assa : forall (mu:sto) o p B A,
     sto_ok mu ->
     lc_exp (e_abs p B)  ->
     step ((e_set (e_anno (e_loc o) (t_ref A)) (e_abs p B)), mu)  ((e_set (e_anno (e_loc o) (t_ref A)) (e_anno (e_abs p B) A)), mu)
 | Step_p : forall (mu:sto) p t,
     sto_ok mu ->
     ppvalue p ->
     tymu p mu t ->
     step (p, mu)  ((e_anno p t), mu)
 (* | Step_o : forall (mu:sto) o,
     sto_ok mu ->
     step ((e_loc o), mu)  ((e_anno (e_loc o) (t_ref (principle_type (store_lookup o mu)))), mu) *)
.



Inductive sto_okn : sto -> Prop :=
  | sto_ok_emptyn : sto_okn nil
  | sto_ok_pushn : forall mu t,
      sto_okn mu -> nvalue t -> 
      sto_okn (t :: mu).


Inductive nstep : conf  -> conf  -> Prop :=    (* defn step *)
  | nstep_eval : forall mu mu' F e1 e2,
     Wformed F ->
     nstep (e1, mu) (e2, mu') ->
     nstep ((nfill F e1), mu) (((nfill F e2)), mu')
 | nStep_beta : forall (mu:sto)  (e:exp) v t,
     sto_okn mu ->
     nvalue v ->
     nstep ((e_app (e_abs e t) v), mu) ((open_exp_wrt_exp e v), mu)
 | nStep_deref : forall (mu:sto) (o:nat) (A:typ),
     sto_okn mu ->
     nstep ((e_get (e_loc o)), mu) ((store_lookup o mu), mu)
 | nStep_ref : forall (mu:sto) (v:exp),
     sto_okn mu ->
     nvalue v ->
     nstep ((e_ref v), mu)  ((e_loc (length mu)), mu ++ v::nil)
 | nStep_ass : forall (mu:sto) o v,
     sto_okn mu ->
     nvalue v ->
     nstep ((e_set (e_loc o) v), mu)  (e_unit, replace o v mu)
.


(* defns Typing *)
Inductive Typing : phi -> ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_top : forall (L:phi) (G:ctx),
     uniq G ->
     Typing L G (e_top) Inf t_top
 | Typ_lit : forall (L:phi) (G:ctx) ,
      uniq G ->
     Typing L G (e_lit 0) Inf t_int
 | Typ_litp : forall (L:phi) (G:ctx) (i5:i),
     uniq G ->
     i5 > 0 ->
    Typing L G (e_lit i5) Inf t_pos
 | Typ_var : forall (L:phi) (G:ctx) (x:var) (A:typ),
       uniq G ->
      binds  x A G  ->
     Typing L G (e_var_f x) Inf A
 | Typ_abs : forall (LL : vars)  L (G:ctx) (A1 A2:typ) (e:exp) (B:typ),
      ( forall x , x \notin  LL  -> Typing L  (cons ( x ,  A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
      algo_sub A2 A1 ->
     Typing L G (e_abs e A1) Chk (t_arrow A2 B)
 | Typ_app : forall (L:phi) (G:ctx) (e1 e2:exp) A1 A2,
     Typing L G e1 Inf (t_arrow A1 A2) ->
     Typing L G e2 Chk A1 ->
     Typing L G (e_app e1 e2) Inf A2
 | Typ_anno : forall (L:phi) (G:ctx) (e:exp) (A:typ),
     Typing L G e Chk A ->
     Typing L G (e_anno e A) Inf A
 | Typ_sub : forall (L:phi) (G:ctx) (e:exp) (B A:typ),
     Typing L G e Inf A ->
     algo_sub A B ->
     Typing L G e Chk B
 | Typ_loc : forall (L:phi) (G:ctx) (o:nat),
      uniq G ->
     o < length L ->
     Typing L G (e_loc o) Inf (t_ref  (store_Tlookup o L))
 | Typ_ass : forall (L:phi) (G:ctx) (e1 e2:exp) (A:typ),
     Typing L G e1 Inf (t_ref A) ->
     Typing L G e2 Chk A ->
     Typing L G (e_set e1 e2) Inf t_unit
 | Typ_deref : forall (L:phi) (G:ctx) (e:exp) (A:typ),
     Typing L G e Inf (t_ref A) ->
     Typing L G (e_get e) Inf A
 | Typ_ref : forall (L:phi) (G:ctx) (e:exp) (A:typ),
     Typing L G e Inf A ->
     Typing L G (e_ref e) Inf (t_ref A)
 | Typ_unit : forall (L:phi) (G:ctx),
       uniq G ->
     Typing L G (e_unit) Inf t_unit
 | Typ_intro : forall (L:phi) (G:ctx) e (C A B:typ),
     Typing L G e Chk A ->
     Typing L G e Chk B ->
     spl C A B ->
     Typing L G e Chk C 
  (* this is rule is because top is the super type of everytype, we do not show in the figure and we add a note in the paper.*)
 | Typ_abst : forall (LL : vars)  L (G:ctx) (A:typ) (e:exp),
     ( forall x , x \notin  LL  -> Typing L  (cons ( x ,  A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_top )  ->
    Typing L G (e_abs e A) Chk t_top
.

Definition sto_typing P mu :=
     sto_ok mu /\ 
     length P = length mu /\
     (forall l, l < length mu -> 
     Typing P nil (store_lookup l mu) Inf (store_Tlookup l P)).


Notation "P |== mu" := (sto_typing P mu) (at level 68).


Inductive extends : phi -> phi -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil  
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).



Inductive erase : exp -> exp -> Prop := 
 | ed_x: forall x,
     erase (e_var_f x) (e_var_f x)
 | ed_unit: 
     erase e_unit e_unit
 | ed_top:
     erase e_top e_top
 | ed_lit: forall i5,
     erase (e_lit i5) (e_lit i5)
 | ed_loc: forall i5,
     erase (e_loc i5) (e_loc i5)
 | ed_app: forall e1 e2 e1' e2' ,
     erase e1 e1' ->
     erase e2 e2' ->
     erase  (e_app e1 e2) (e_app e1' e2')
 | ed_abs: forall L e e' t,
     ( forall x , x \notin  L  -> 
     erase (open_exp_wrt_exp e (e_var_f x) ) (open_exp_wrt_exp e' (e_var_f x) ))  ->
     erase (e_abs e t) (e_abs e' t)
| ed_ass: forall e1 e2 e1' e2' ,
     erase e1 e1' ->
     erase e2 e2' ->
     erase  (e_set e1 e2) (e_set e1'  e2')
| ed_get: forall e1 e1' ,
     erase e1 e1' ->
     erase  (e_get e1) (e_get e1')
| ed_ref: forall e1 e1',
     erase e1 e1' ->
     erase  (e_ref e1) (e_ref e1')
| ed_anno: forall e1 e1' t,
     erase e1 e1' ->
     erase  (e_anno e1 t) e1'
(* | ed_val: forall e1 e1' t,
     erase e1 e1' ->
     erase  (e_val e1 t) e1' *)
.



Inductive erasem : sto -> sto -> Prop := 
| edm_top:
   erasem nil nil 
| edm_cons: forall mu1 mu2 t1 t2,
   erase t1 t2 ->
   erasem mu1 mu2 ->
   erasem (t1 :: mu1) (t2 :: mu2)
.



Inductive nsteps : conf  -> conf -> Prop :=
  | nsteps_refl e mu:
    nsteps (e, mu) (e, mu)

  | nsteps_n e mu e' mu' e'' mu'':   
    nstep (e, mu) (e', mu') ->
    nsteps (e', mu') (e'', mu'') ->
    nsteps (e, mu) (e'', mu'').


Inductive steps : conf  -> conf -> Prop :=
  | steps_refl e mu:
    steps (e, mu) (e, mu)

  | steps_n e mu e' mu' e'' mu'':   
    step (e, mu) (e', mu') ->
    steps (e', mu') (e'', mu'') ->
    steps (e, mu) (e'', mu'').


(** infrastructure *)

(* (* #[export] *)  *)
Hint Constructors tymu sto_okn erasem nsteps steps erase nvalue nstep ppvalue extends  pvalue WFTypformed Wformed algo_sub sto_ok phi_ok value spl ord step Typing lc_exp : core.


