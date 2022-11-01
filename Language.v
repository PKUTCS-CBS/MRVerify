(**

This file describes the representation of modelling language.

Author: Bowen Zhang.

Date : 2022.01.06
*)

From SLF (* TLC *) Require Export LibCore.
From SLF (* Sep *) Require Export TLCbuffer Var Fmap.

(* ###################### Syntax ###################### *)

Definition loc : Type := nat.
Definition bloc : Type := nat.
Definition floc : Type := nat.

Definition listint : Type := list int.
Definition listbloc : Type := list bloc.

Definition fnull : floc := 0%nat.
Definition bnull : bloc := 0%nat.

(*-- wordcount kvpair (word, times) --*)
Definition wdpair : Type := int * int.

(*-- indexinvert kvpair (word, location, times) --*)
Definition index : Type := int * bloc.
Definition idcnt : Type := index * int.
Definition blcnt : Type := bloc * int.
Definition env : Type := int * list (bloc * int).

(*---------- the block primitive operations ----------*)
Inductive bval : Type :=
(* basic operations *)
  | bval_create : bval
  | bval_append : bval  
  | bval_get : bval
  | bval_delete : bval
  | bval_bsize : bval
  | bval_truncate : bval
(* mapper in block level *)
  | bval_wdmap : bval
  | bval_locate : bval
  | bval_iimap : bval.

(*---------- the file primitive operations ----------*)
Inductive fval : Type :=
(* basic operations *)
  | fval_create : fval
  | fval_attach : fval
  | fval_fsize : fval
  | fval_get : fval
  | fval_get_nth_blk : fval
  | fval_set_nth_blk : fval
  | fval_delete : fval
  | fval_truncate : fval
  | fval_buffer: fval
  | fval_buffer_list : fval
  | fval_rev_blist : fval
(* reduer in file level *)
  (*- wordcount cmd -*)
  | fval_wdmerge : fval
  | fval_wdshuffle : fval
  | fval_wdreduce : fval
  (*- invertindex cmd -*)
  | fval_iimerge : fval
  | fval_iishuffle : fval
  | fval_iireduce : fval
  | fval_iiorganize : fval.

(*-------- some auxiliary primitive operations (not important) --------*)
Inductive prim : Type :=
  | val_eq : prim        (*a ?= b*)
  | val_add : prim       (*a + b*)
  | val_min : prim       (*a - b*)
  | val_le : prim       (*a <= b*)
  | val_reform : prim      (*trans list to save*)
  | val_list_rev : prim    (*reverse a list*)
  | val_list_hd  : prim    (*extract list for a block*)
  | val_list_len : prim   (*get the length of content*)
  | val_list_tl  : prim    (*after extraction*)
  | val_list_app : prim    (*append a list*)
  | val_list_cut : prim   (*truncate a list*)
  | val_app_wdlist : prim (*append a word list*)
  | val_app_iilist : prim (*append an indexivert list*)
  | val_app_idxlist : prim. (*append an indexivert list*)

(*---------- the val and the term ----------*)
Inductive val : Type :=
  | val_unit : val
  | val_prim : prim -> val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_listint : list int -> val
  | val_listbloc : list bloc -> val
  | val_listenv : (list env) -> val
  | val_floc : floc -> val
  | val_bloc : bloc -> val
  | val_bval : bval -> val
  | val_fval : fval -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
(* values for wordcount *)
  | val_listwdpair : list wdpair -> val
  | val_Listwd : (list (list wdpair)) -> val
(* values for invertindex *)
  | val_listindex : list index -> val
  | val_Listidx : (list (list index)) -> val
  | val_listiipair : list idcnt -> val
  | val_Listii : (list (list idcnt)) -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(* ##################### The Definition of CBS heap ##################### *)
(*------- the entire corresponding state -------*)
Definition stateb : Type := fmap bloc listint.
Definition statef : Type := fmap floc listbloc.
Definition state : Type := statef * stateb.

(*------- the part of corresponding state -------*)
Definition heapb : Type := stateb.
Definition heapf : Type := statef.
Definition heap : Type := state.

Notation "'hb_empty'" := (@Fmap.empty bloc listint)
  (at level 0).
Notation "'hf_empty'" := (@Fmap.empty floc listbloc)
  (at level 0).
Notation "'h_empty'" := (hf_empty,hb_empty)
  (at level 0).
Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).

(*** Implicit Types and coercions (to improve the readability) ***)

Implicit Types bp : bloc.
Implicit Types fp : floc.
Implicit Types ln : list int.
Implicit Types n : int.
Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : bool.
Implicit Types hb : heapb.
Implicit Types sb : stateb.
Implicit Types hf : heapf.
Implicit Types sf : statef.

Coercion val_bool : bool >-> val.
Coercion val_floc : floc >-> val.
Coercion val_bloc : bloc >-> val.
Coercion val_prim : prim >-> val.
Coercion val_int : Z >-> val.
Coercion val_bval : bval >-> val.
Coercion val_fval : fval >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(*** The substitution function ***)
(* -- subst var to val directly -- *)
Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

Definition droplast (n:nat) {A} (l:list A) : list A :=
  let l' := rev l in
  let l'' := drop n l' in
    rev l''.

(**===================== List Function for MapReduce =============================**)

(*--------------------------- Poly ----------------------------------------*)
Definition mapper {A} {B} (l:list A) (v:B) : list (A*B) := 
  List.map (fun (i:A) => (i,v)) l.

Definition app {A} (l1 l2 : list A) :=
  List.fold_right (fun x (acc:list A) => x::acc) l2 l1.

Definition merge {A} (l:list (list A)) := fold_right app nil l.

Fixpoint classify {A} (f:A->A->bool) (l1 l2:list A) : list (list A) :=
  match l1,l2 with
  | nil,_ => nil
  | _,nil => nil
  | x::l1',l2 => (List.filter (f x) l2) :: 
    (classify f l1' l2)
end.

Definition remove {A} (f:A->A->bool) (a:A) (l:list A) : list A := 
  List.filter (f a) l.

Fixpoint remove_duplicates {A} (f:A->A->bool) (l:list A) : list A :=
  match l with
  | nil => nil
  | x::l' => x :: (remove f x (remove_duplicates f l'))
  end.

Definition shuffle {A} (l:list A) (f1 f2:A->A->bool) : list (list A) :=
  let l1 := remove_duplicates f1 l in
    classify f2 l1 l.

Definition init {A} {B} (a:A*B) (b:B) : A*B := ((fst a), b).

Definition exec {A} {B} (f:B->B->B) (a1 a2:A*B) : A*B := 
  ((fst a1), (f (snd a1) (snd a2) )).

Definition combine {A} {B} (a:A*B) (b:B) (f:B->B->B) (l:list (A*B)) : A*B:=
  let p := init a b in
  List.fold_right (exec f) p l.

Definition reducer {A} {B} (a:A*B) (b:B) (f:B->B->B) (L:list (list (A*B))) :list (A*B) :=
  LibList.map (combine a b f) L.

(* =================== For WordCount ==================== *)

Definition wordmapper (lw:list int):= mapper lw 1.

Definition wordmerge (L:list (list wdpair)) := merge L.

Definition eqword (p1 p2: wdpair) := (fst p1) =? (fst p2).

Definition neqword (p1 p2: wdpair) := negb (eqword p1 p2).

Definition wordshuffle (l:list wdpair) := shuffle l neqword eqword.

Definition addint (n1 n2:int) := n1+n2.

Definition wordreducer (L:list (list wdpair)) :=
  let p := (nth_default (0,0) 0 ((nth_default nil 0 L))) in
  reducer p 0 addint L.

Fixpoint filetrans (l:list wdpair) : (list int) :=
  match l with
  | nil => nil
  | (w,n) :: tl => w :: n :: (filetrans tl)
end.

(* =================== For InvertIndex ==================== *)

Definition locate (l : list int) (b: bloc) := List.map (fun (i:int) => (i,b)) l.

Definition iimapper (lw:list index) := mapper lw 1.

Definition iimerge (L:list (list idcnt)) := merge L.

(* Compute iimerge (((((10, 1%nat, 1) :: (8, 1%nat, 1) :: (10, 1%nat, 1) :: nil)
          :: ((10, 2%nat, 1) :: nil) :: nil))). *)

Definition eqindex (p1 p2 : index) := 
  andb ((fst p1) =? (fst p2)) ((snd p1) =? (snd p2)).

Definition eqiikey (p1 p2 : idcnt) := eqindex (fst p1) (fst p2).

Definition neqiikey (p1 p2 : idcnt) := negb (eqiikey p1 p2).

Definition eqid (p1 p2 : idcnt) := (fst (fst p1)) =? (fst (fst p2)).

Definition neqid (p1 p2 : idcnt) := negb (eqid p1 p2).

Definition iishuffle (l:list idcnt) := shuffle l neqiikey eqiikey.

Definition idshuffle (l:list idcnt) := shuffle l neqid eqid.

Definition addidcnt (p1 p2 : idcnt):= ((fst p1), ((snd p1)+(snd p2))).

Definition iireducer (L:list (list idcnt)) :=
  let p := (nth_default (0,0%nat,0) 0 ((nth_default nil 0 L))) in
  reducer p 0 addint L.

Definition appenv (i:idcnt) (e:env) :=
  (fst e, (snd (fst i), (snd i)) :: (snd e)). 

Definition organize (l:list idcnt):=
  let p := (nth_default (0,0%nat,0) 0 l) in
  List.fold_right appenv ((fst (fst p)),nil) l.

(* Compute idshuffle ((10, 1%nat, 2) :: (8, 1%nat, 1) :: (10, 2%nat, 1) :: nil). *)

Definition iiorganize (l:list idcnt) :=
  let L := idshuffle l in
  List.map organize L.

(* ########################### The Evaluation Rules ########################### *)
Open Scope liblist_scope.
Open Scope Z_scope.

Inductive eval : heap -> trm -> heap -> val -> Prop :=
  (*===== eval rules for mapreduce======*)

  (*-- mapper --*)
  (* wordcount *)
  | eval_wdmap : forall sf sb bp,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_wdmap bp) (sf, sb) 
        (val_listwdpair (wordmapper (Fmap.read sb bp)))

  (* invertindex *)
  | eval_locate : forall sf sb bp,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_locate bp) (sf, sb)
        (val_listindex (locate (Fmap.read sb bp) bp))

  | eval_iimap : forall sf sb l,
      eval (sf, sb) (bval_iimap (val_listindex l)) (sf, sb) 
        (val_listiipair (iimapper l))

  | eval_reform : forall s l,
      eval s (val_reform (val_listwdpair l)) s 
        (val_listint (filetrans l))

  (*-- reducer --*)
  (* wordcount *)
  | eval_wdmerge : forall s L,
      eval s (fval_wdmerge (val_Listwd L)) s (val_listwdpair (wordmerge L))

  | eval_wdshuffle : forall s l,
      eval s (fval_wdshuffle (val_listwdpair l)) s (val_Listwd (wordshuffle l))

  | eval_wdreduce : forall s L,
      eval s (fval_wdreduce (val_Listwd L)) s (val_listwdpair (wordreducer L))

  (* invertindex *)
  | eval_iimerge : forall s L,
      eval s (fval_iimerge (val_Listii L)) s (val_listiipair (iimerge L))

  | eval_iishuffle : forall s l,
      eval s (fval_iishuffle (val_listiipair l)) s (val_Listii (iishuffle l))

  | eval_iireduce : forall s L,
      eval s (fval_iireduce (val_Listii L)) s (val_listiipair (iireducer L))

  | eval_iiorganize : forall s l,
      eval s (fval_iiorganize (val_listiipair l)) s (val_listenv (iiorganize l))

  (*-- aux rules for list operation --*)
  | eval_app_wdlist : forall s lw L,
      eval s (val_app_wdlist (val_listwdpair lw) (val_Listwd L)) 
           s (val_Listwd (lw :: L))
  | eval_app_idxlist : forall s l L,
      eval s (val_app_idxlist (val_listindex l) (val_Listidx L)) 
           s (val_Listidx (l :: L))
  | eval_app_iilist : forall s l L,
      eval s (val_app_iilist (val_listiipair l) (val_Listii L)) 
           s (val_Listii (l :: L))

(*__________________previous______________________________*)
  (*------ trm eval to its value ------*)
  | eval_val_refine : forall sf sb v,
      eval (sf, sb) (trm_val v) (sf, sb) v
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)

  (*------   aux prim operation    ------*)
  | eval_add : forall s n1 n2,
      eval s (val_add n1 n2) s (n1 + n2)
  | eval_min : forall s n1 n2,
      eval s (val_min n1 n2) s (n1 - n2)
  | eval_le : forall s n1 n2,
      eval s (val_le n1 n2) s (val_bool (isTrue (n1 <= n2)))
  | eval_eq : forall s n1 n2,
      eval s (val_eq n1 n2) s (val_bool (n1 =? n2))
  | eval_list_rev : forall s l1,
      eval s (val_list_rev (val_listint l1)) s (val_listint (rev l1))
  | eval_list_app : forall s l1 l2,
      eval s (val_list_app (val_listint l1) (val_listint l2)) 
           s (val_listint (l1 ++ l2))

  | eval_list_hd : forall s l1,
      eval s (val_list_hd (val_listint l1)) s (val_listint (LibList.take 2%nat l1))
  | eval_list_tl : forall s l1,
      eval s (val_list_tl (val_listint l1)) s (val_listint (LibList.drop 2%nat l1))
  | eval_list_len : forall s l1,
      eval s (val_list_len (val_listint l1)) s (LibList.length l1)  


  (*--------- block prim operation ---------*)
  | eval_bcreate_list : forall sf sb bp ll,
      ~ Fmap.indom sb bp ->
      eval (sf, sb) (bval_create (val_listint ll))
        (sf, (Fmap.update sb bp ll)) (val_bloc bp)

  | eval_bget : forall sf sb bp,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_get (val_bloc bp)) (sf, sb) (val_listint (Fmap.read sb bp))

  | eval_bdelete : forall sf sb bp,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_delete (val_bloc bp)) (sf, (Fmap.remove sb bp)) val_unit

  | eval_bsize : forall sf sb bp,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_bsize (val_bloc bp))
           (sf, sb) (val_int (List.length (Fmap.read sb bp)))

  | eval_btruncate : forall sf sb bp n,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_truncate (val_bloc bp) n) 
        (sf, (Fmap.update sb bp (droplast (Z.to_nat n) (Fmap.read sb bp) )))  val_unit

  | eval_bappend_list : forall sf sb bp ll,
      Fmap.indom sb bp ->
      eval (sf, sb) (bval_append (val_bloc bp) (val_listint ll)) 
        (sf, (Fmap.update sb bp ((Fmap.read sb bp) ++ ll) ))  val_unit

 (*----------- file prim operation -----------*)
  | eval_fcreate_list : forall sf sb fp bll,
      ~ Fmap.indom sf fp ->
      noduplicates bll ->
      eval (sf, sb) (fval_create (val_listbloc bll))
        ((Fmap.update sf fp bll), sb) (val_floc fp)

  | eval_fget : forall sf sb fp,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_get (val_floc fp)) (sf, sb) (val_listbloc (Fmap.read sf fp))

  | eval_fsize : forall sf sb fp,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_fsize (val_floc fp))
           (sf, sb) (val_int (List.length (Fmap.read sf fp)))

  | eval_fget_nth_blk : forall sf sb fp n,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_get_nth_blk (val_floc fp) n) (sf, sb)
           (val_bloc (nth_default bnull (Z.to_nat n) (Fmap.read sf fp)))

  | eval_fset_nth_blk : forall sf sb fp n bp,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_set_nth_blk (val_floc fp) n (val_bloc bp))
           (Fmap.update sf fp (LibList.update (to_nat n) bp (Fmap.read sf fp)), sb) val_unit
  
  | eval_fattach: forall sf sb fp lb,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_attach (val_floc fp) (val_listbloc lb)) 
       ((Fmap.update sf fp ( (Fmap.read sf fp) ++ lb )), sb) val_unit
  
  | eval_fdelete : forall sf sb fp,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_delete (val_floc fp)) ( (Fmap.remove sf fp), sb) val_unit

  | eval_frev_blist : forall sf sb bl,
      eval (sf, sb) (fval_rev_blist (val_listbloc bl)) (sf, sb) (val_listbloc (LibList.rev bl))
  
  | eval_fbuffer : forall sf sb bp,
      eval (sf, sb) (fval_buffer (val_bloc bp)) (sf, sb) (val_listbloc (bp::nil))

  | eval_fbuffer_list : forall sf sb bp bl,
      eval (sf, sb) (fval_buffer_list (val_bloc bp) (val_listbloc bl)) (sf, sb) (val_listbloc (bp::bl))

  | eval_ftruncate : forall sf sb fp n,
      Fmap.indom sf fp ->
      eval (sf, sb) (fval_truncate (val_floc fp) n) 
        ( (Fmap.update sf fp (droplast (Z.to_nat n) (Fmap.read sf fp) )), sb) val_unit

  (*------------ trm rules ------------*)
   | eval_app_args : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
      (~ trm_is_val t1 \/ ~trm_is_val t2) ->
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v2 ->
      eval s3 (trm_app v1 v2) s4 r ->
      eval s1 (trm_app t1 t2) s4 r
   | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
   | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
   | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
   | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
   | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v.

(*  --------------- some relation about terms --------------- *)
Definition eval_like (t1 t2:trm) : Prop :=
  forall s s' v, eval s t1 s' v -> eval s t2 s' v.

Definition trm_equiv (t1 t2:trm) : Prop :=
  forall s s' v, eval s t1 s' v <-> eval s t2 s' v.

Lemma eval_like_eta_reduction : forall (t:trm) (x:var),
  eval_like t (trm_let x t x).
Proof using.
  introv R. applys eval_let R.
  simpl. rewrite var_eq_spec. case_if. apply eval_val.
Qed.

Lemma eval_like_eta_expansion : forall (t:trm) (x:var),
  eval_like (trm_let x t x) t.
Proof using.
  introv R. inverts R as. introv R1 R2.
  simpl in R2. rewrite var_eq_spec in R2. case_if.
  inverts R2; apply R1.
Qed.

Lemma trm_equiv_eta : forall (t:trm) (x:var),
  trm_equiv t (trm_let x t x).
Proof using.
  intros. intros s s' v. iff M.
  { applys eval_like_eta_reduction M. }
  { applys eval_like_eta_expansion M. }
Qed.

(* ################### evaluation rule in SL style ############################## *)

Lemma eval_wdmap_sep : forall sf sb sb2 bp l,
  sb = Fmap.union (Fmap.single bp l) sb2 ->
  eval (sf, sb) (bval_wdmap (val_bloc bp))
       (sf, sb) (val_listwdpair (wordmapper l)).
Proof.
  introv ->. forwards Dv: Fmap.indom_single bp l.
  applys_eq eval_wdmap 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_locate_sep : forall sf sb sb2 bp l,
  sb = Fmap.union (Fmap.single bp l) sb2 ->
  eval (sf, sb) (bval_locate (val_bloc bp))
       (sf, sb) (val_listindex (locate l bp)).
Proof.
  introv ->. forwards Dv: Fmap.indom_single bp l.
  applys_eq eval_locate 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

(*_________________previous__________________*)

(*--- block prim operations ---*)
Lemma eval_bcreate_sep : forall sf sb1 sb2 l bp,
  sb2 = Fmap.single bp l ->
  Fmap.disjoint sb2 sb1 ->
  eval (sf, sb1) (bval_create (val_listint l))
       (sf, (Fmap.union sb2 sb1)) (val_bloc bp).
Proof.
  introv -> M. forwards Db: Fmap.indom_single bp l.
  rewrite <- Fmap.update_eq_union_single.
  apply~ eval_bcreate_list.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both M N. }
Qed.

Lemma eval_bget_sep : forall sf sb sb2 bp l,
  sb = Fmap.union (Fmap.single bp l) sb2 ->
  eval (sf, sb) (bval_get (val_bloc bp))
       (sf, sb) (val_listint l).
Proof.
  introv ->. forwards Dv: Fmap.indom_single bp l.
  applys_eq eval_bget 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_bsize_sep : forall sf sb sb2 bp l,
  sb = Fmap.union (Fmap.single bp l) sb2 ->
  eval (sf, sb) (bval_bsize (val_bloc bp))
       (sf, sb) (List.length l).
Proof.
  introv ->. forwards Dv: Fmap.indom_single bp l.
  applys_eq eval_bsize 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_bdelete_sep : forall sf sb1 sb2 bp l,
  sb1 = Fmap.union (Fmap.single bp l) sb2 ->
  Fmap.disjoint (Fmap.single bp l) sb2 ->
  eval (sf, sb1) (bval_delete (val_bloc bp))
       (sf, sb2) val_unit.
Proof.
  introv -> D. forwards Db: Fmap.indom_single bp l.
  applys_eq eval_bdelete 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.remove_union_single_l.
    intros D1. applys~ Fmap.disjoint_inv_not_indom_both D D1. }
Qed.

Lemma eval_btruncate_sep : forall sf sb1 sb2 sb bp l1 n,
  sb1 = Fmap.union (Fmap.single bp l1) sb ->
  sb2 = Fmap.union (Fmap.single bp (droplast (Z.to_nat n) l1)) sb ->
  Fmap.disjoint (Fmap.single bp l1) sb ->
  eval (sf, sb1) (bval_truncate (val_bloc bp) n)
       (sf, sb2) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single bp l1.
  applys_eq eval_btruncate 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single.  }
Qed.

Lemma eval_bappend_sep : forall sf sb1 sb2 sb bp l1 l2,
  sb1 = Fmap.union (Fmap.single bp l1) sb ->
  sb2 = Fmap.union (Fmap.single bp (l1++l2)) sb ->
  Fmap.disjoint (Fmap.single bp l1) sb ->
  eval (sf, sb1) (bval_append (val_bloc bp) (val_listint l2))
       (sf, sb2) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single bp l1.
  applys_eq eval_bappend_list 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

(*--- file prim operations ---*)

Lemma eval_fcreate_sep : forall sf1 sb sf2 bll fp,
  sf2 = Fmap.single fp bll ->
  Fmap.disjoint sf2 sf1 ->
  noduplicates bll ->
  eval (sf1, sb) (fval_create (val_listbloc bll))
       ((Fmap.union sf2 sf1), sb) (val_floc fp).
Proof.
  introv -> D. forwards Db: Fmap.indom_single fp bll.
  rewrite <- Fmap.update_eq_union_single.
  apply eval_fcreate_list.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed. 

Lemma eval_fsize_sep : forall sf sb sf2 fp l,
  sf = Fmap.union (Fmap.single fp l) sf2 ->
  eval (sf, sb) (fval_fsize (val_floc fp))
       (sf, sb) (List.length l).
Proof.
  introv ->. forwards Dv: Fmap.indom_single fp l.
  applys_eq eval_fsize 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fget_sep : forall sf sb sf2 bll fp,
  sf = Fmap.union (Fmap.single fp bll) sf2 ->
  eval (sf, sb) (fval_get (val_floc fp))
       (sf, sb) (val_listbloc bll).
Proof.
  introv ->. forwards Df: Fmap.indom_single fp bll.
  applys_eq eval_fget 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fget_nth_blk_sep : forall sf sb sf2 bll fp n,
  sf = Fmap.union (Fmap.single fp bll) sf2 ->
  eval (sf, sb) (fval_get_nth_blk (val_floc fp) n)
       (sf, sb) (val_bloc (nth_default bnull (Z.to_nat n) bll)).
Proof.
  introv ->. forwards Df: Fmap.indom_single fp bll.
  applys_eq eval_fget_nth_blk 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fset_nth_blk_sep : forall sf sb sf1 sf2 bll fp n bp,
  sf1 = Fmap.union (Fmap.single fp bll) sf ->
  sf2 = Fmap.union (Fmap.single fp (LibList.update (to_nat n) bp bll)) sf ->
  Fmap.disjoint (Fmap.single fp bll) sf ->
  eval (sf1, sb) (fval_set_nth_blk (val_floc fp) n (val_bloc bp))
       (sf2, sb) (val_unit).
Proof.
  introv -> -> D. forwards Df: Fmap.indom_single fp bll.
  applys_eq eval_fset_nth_blk 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single.
    rewrite~ Fmap.read_union_l. 
    rewrite~ Fmap.read_single. }
Qed.

Lemma eval_fdelete_sep : forall sf1 sb sf2 bll fp,
  sf1 = Fmap.union (Fmap.single fp bll) sf2 ->
  Fmap.disjoint (Fmap.single fp bll) sf2 ->
  eval (sf1, sb) (fval_delete (val_floc fp))
       (sf2, sb) val_unit.
Proof.
  introv -> D. forwards Df: Fmap.indom_single fp bll.
  applys_eq eval_fdelete 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.remove_union_single_l. intros D1.
    applys~  Fmap.disjoint_inv_not_indom_both D D1. }
Qed.

Lemma eval_fattach_sep : forall sf sf1 sf2 sb fp bl1 bl2,
  sf1 = Fmap.union (Fmap.single fp bl1) sf ->
  sf2 = Fmap.union (Fmap.single fp (bl1++bl2)) sf ->
  Fmap.disjoint (Fmap.single fp bl1) sf ->
  eval (sf1, sb) (fval_attach (val_floc fp) (val_listbloc bl2))
       (sf2, sb) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single fp bl1.
  applys_eq eval_fattach 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

Lemma eval_ftruncate_sep : forall sf sf1 sf2 sb fp bl n,
  sf1 = Fmap.union (Fmap.single fp bl) sf ->
  sf2 = Fmap.union (Fmap.single fp (droplast (Z.to_nat n) bl)) sf ->
  Fmap.disjoint (Fmap.single fp bl) sf ->
  eval (sf1, sb) (fval_truncate (val_floc fp) n)
       (sf2, sb) val_unit.
Proof.
  introv -> -> D. forwards Db: Fmap.indom_single fp bl.
  applys_eq eval_ftruncate 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite Fmap.read_union_l, Fmap.read_single; auto.
    rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.



(*==============================================================*)
(* ############ Notations of the language (to improve the readability) #################### *)
Module NotationForTrm.

(* ====== Notation for mapreduce ====== *)

(* -- mapper -- *)
Notation "'wdmap bp" :=
  (bval_wdmap bp)
  (at level 67) : trm_scope.

Notation "'iimap bp" :=
  (bval_iimap bp)
  (at level 67) : trm_scope.

Notation "'locate b" :=
  (bval_locate b)
  (at level 67) : trm_scope.

(* -- reducer -- *)
Notation "'wdmerge l" :=
  (fval_wdmerge l)
  (at level 67) : trm_scope.

Notation "'wdshuffle l" :=
  (fval_wdshuffle l)
  (at level 67) : trm_scope.

Notation "'wdreduce l" :=
  (fval_wdreduce l)
  (at level 67) : trm_scope.

Notation "'iimerge l" :=
  (fval_iimerge l)
  (at level 67) : trm_scope.

Notation "'iishuffle l" :=
  (fval_iishuffle l)
  (at level 67) : trm_scope.

Notation "'iireduce l" :=
  (fval_iireduce l)
  (at level 67) : trm_scope.

Notation "'iiorgan l" :=
  (fval_iiorganize l)
  (at level 67) : trm_scope.

(*-- some aux list operations --*)
Notation "l 'w:: L" :=
  (val_app_wdlist l L)
  (at level 67, format " l ''w::' L") : trm_scope.

Notation "l 'i:: L" :=
  (val_app_idxlist l L)
  (at level 67, format " l ''i::' L") : trm_scope.

Notation "l 'ii:: L" :=
  (val_app_iilist l L)
  (at level 67, format " l ''ii::' L") : trm_scope.

(*_________________previous______________________*)
(** ** Notation for terms *)
Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x at level 0, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "t1 '';' t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity,
   format "'[v' '[' t1 ']'  '';'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x1 ':=' t" :=
  (val_fix f x1 t)
  (at level 69, f, x1 at level 0, format "'Fix'  f  x1  ':='  t") : val_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f,x1, x2 at level 0, format "'Fix'  f x1 x2 ':=' t") : val_scope.

Notation "'Fix' f x1 x2 x3 ':=' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f,x1, x2, x3 at level 0, format "'Fix'  f x1 x2 x3 ':=' t") : val_scope.

Notation "'Fix_' f x1 ':=' t" :=
  (trm_fix f x1 t)
  (at level 69, f, x1 at level 0, format "'Fix_'  f  x1  ':='  t") : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 at level 0, format "'Fun'  x1  ':='  t") : val_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (val_fun x1 (trm_fun x2 t))
  (at level 69, x1, x2 at level 0, format "'Fun' x1 x2 ':=' t") : val_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1, x2, x3 at level 0, format "'Fun' x1 x2 x3 ':=' t") : val_scope.

Notation "'Fun_' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0, format "'Fun_'  x1  ':='  t") : trm_scope.

Notation "'Fun_' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1, x2 at level 0, format "'Fun_' x1 x2 ':=' t") : trm_scope.

Notation "'Fun_' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1, x2, x3 at level 0, format "'Fun_' x1 x2 x3 ':=' t") : trm_scope.

(* ----------Notations of file prim---------------- *)
Notation "'fcreate ll" :=
  (fval_create ll)
  (at level 67) : trm_scope.

Notation "'frev bl" :=
  (fval_rev_blist bl)
  (at level 67) : trm_scope.

Notation "'fbuffer p" :=
  (fval_buffer p)
  (at level 67) : trm_scope.

Notation "'fatt bp l" :=
  (fval_attach bp l)
  (at level 67,bp at level 0,format "''fatt' bp l").

Notation "'set_nth_blk fp n 'As bp" :=
  (fval_set_nth_blk fp n bp)
  (at level 67, fp,bp at level 0,format "''set_nth_blk' fp n ''As' bp") : trm_scope.

Notation "'fsize p" :=
  (fval_fsize p)
  (at level 67) : trm_scope.

Notation "'fdelete fp" :=
  (fval_delete fp)
  (at level 67) : trm_scope.

Notation "'ftrun fp n" :=
  (fval_truncate fp n)
  (at level 67,fp at level 0,format "''ftrun' fp n") : trm_scope.

Notation "'nth_blk fp n" :=
  (fval_get_nth_blk fp n)
  (at level 67, fp at level 0,format "''nth_blk' fp n") : trm_scope.

Notation "bp 'b+ bl" :=
  (fval_buffer_list bp bl)
  (at level 67) : trm_scope.

(* ----------Notations of block prim---------------- *)
Notation "'bcreate ll" :=
  (bval_create ll)
  (at level 67) : trm_scope.

Notation "'bapp bp l" :=
  (bval_append bp l)
  (at level 67,bp at level 0,format "''bapp' bp l") : trm_scope.

Notation "'bsize p" :=
  (bval_bsize p)
  (at level 67) : trm_scope.

Notation "'bget bp" :=
  (bval_get bp)
  (at level 67) : trm_scope.

Notation "'bsize bp" :=
  (bval_bsize bp)
  (at level 67) : trm_scope.

Notation "'bdelete bp" :=
  (bval_delete bp)
  (at level 67) : trm_scope.

Notation "'btrun bp n" :=
  (bval_truncate bp n)
  (at level 67, bp at level 0,format "''btrun' bp n") : trm_scope.

(* ----------Notations of aux prim---------------- *)
Notation "n1 '= n2" :=
  (val_eq n1 n2)
  (at level 67) : trm_scope.

Notation "n1 '+ n2" :=
  (val_add n1 n2)
  (at level 67) : trm_scope.

Notation "n1 '- n2" :=
  (val_min n1 n2)
  (at level 67) : trm_scope.

Notation "n1 '<= n2" :=
  (val_le n1 n2)
  (at level 67) : trm_scope.

Notation "l1 '++ l2" :=
  (val_list_app l1 l2)
  (at level 67) : trm_scope.

Notation "'rev l1" :=
  (val_list_rev l1)
  (at level 67) : trm_scope.

Notation "'hd l1" :=
  (val_list_hd l1)
  (at level 67) : trm_scope.

Notation "'tl l1" :=
  (val_list_tl l1)
  (at level 67) : trm_scope.

Notation "'len l1" :=
  (val_list_len l1)
  (at level 67) : trm_scope.

Notation "'reform l" :=
  (val_reform l)
  (at level 67) : trm_scope.

Notation "'()" := val_unit : trm_scope.

End NotationForTrm.