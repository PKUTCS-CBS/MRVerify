(**

== Representation and verification of InvertIndex ==

This file verifies another MR application.

Author: Bowen Zhang.

Date : 2022.11.1
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export Rules AuxLmm.


(* !! Need to read the Language.v firstly !! *)
Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.


(*----------------------------- InvertIndex --------------------------------------*)
Definition IIMapper := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (val_Listii nil)
    Else
      Let 'bk := 'nth_blk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      Let 'l := 'locate 'bk in
      Let 'ln := 'iimap 'l in
      Let 'ln1 := 'F 'f 'i1 in
      'ln 'ii:: 'ln1.

Lemma triple_IIMapper: forall Hf Hb (f:floc) (n1 n2:int) (b1 b2:bloc) (L:(list (list idcnt))),
  n1 =? n2 = false /\ b1 =? b2 = false ->
  Hf = ( f ~f~> (b1::b2::nil) ) ->
  Hb = ( (b1 ~b~> (n1::n2::n1::nil)) \b* (b2 ~b~> (n1::nil)) ) ->
  L =  ( ((n1,b1,1)::(n2,b1,1)::(n1,b1,1)::nil) :: ((n1,b2,1)::nil) :: nil ) ->
triple (IIMapper f 0)
    (\R[Hf,Hb])
    (fun r => \[r= val_Listii L] \* \R[Hf,Hb]).
Proof.
  fix_locate.
  rewrite hstar_sep, hfstar_hempty_l. apply himpl_refl.
  rew_read. ext.
  applys triple_let triple_iimap. ext.

  applys triple_let.
  fix_locate.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm. apply himpl_refl.
  rew_read. ext.
  applys triple_let triple_iimap. ext.

  applys triple_let.
  exp_fix.
  applys triple_val'. ext.
  apply triple_app_iilist. ext.
  applys triple_conseq triple_app_iilist.
  apply himpl_refl.
  intros r. rew_list. 
  rewrite hbstar_comm. apply himpl_refl.
Qed.


Definition IIShuffle :=
  Fun 'f :=
    Let 'L := IIMapper 'f 0 in
    Let 'l := 'iimerge 'L in
      'iishuffle 'l.

Lemma triple_IIShuffle: forall Hf Hb (f:floc) (n1 n2:int) (b1 b2:bloc) (L:(list (list idcnt))),
  n1 =? n2 = false /\ b1 =? b2 = false ->
  Hf = ( f ~f~> (b1::b2::nil) ) ->
  Hb = ( (b1 ~b~> (n1::n2::n1::nil)) \b* (b2 ~b~> (n1::nil)) ) ->
  L =  ( ( ((n1,b1),1)::((n1,b1),1)::nil ) :: 
         ( ((n2,b1),1)::nil) :: 
         ( ((n1,b2),1)::nil) :: nil ) ->
triple (IIShuffle f)
    (\R[Hf,Hb])
    (fun r => \[r= val_Listii L] \* \R[Hf,Hb]).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_let.
  applys triple_conseq_frame.
  applys* triple_IIMapper.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r.
  applys himpl_refl.
  simpl. intros r. ext.
  applys triple_let.
  applys triple_conseq_frame triple_iimerge.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'. applys himpl_refl.
  simpl. intros r. unfold iimerge,merge. ext.
  applys triple_conseq_frame triple_iishuffle.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  apply iishuffle_diff in H.
  rewrite <- H. applys himpl_refl.
Qed.

Definition IIReducer :=
  Fun 'f :=
    Let 'L := IIShuffle 'f in
    Let 'l := 'iireduce 'L in
      'iiorgan 'l.

Lemma triple_IIReducer: forall Hf Hb (f:floc) (n1 n2:int) (b1 b2:bloc) (l: list env),
  n1 =? n2 = false /\ b1 =? b2 = false ->
  Hf = ( (f ~f~> (b1::b2::nil)) ) ->
  Hb = ( (b1 ~b~> (n1::n2::n1::nil)) \b* (b2 ~b~> (n1::nil)) ) ->
  l =  ( (n1,((b1,2)::(b2,1)::nil)) :: (n2,((b1,1)::nil)) :: nil ) ->
triple (IIReducer f)
    (\R[Hf,Hb])
    (fun r => \[r= val_listenv l] \* \R[Hf,Hb]).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_let.
  applys triple_conseq_frame.
  applys* triple_IIShuffle.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r.
  applys himpl_refl.
  simpl. intros r. ext.
  applys triple_let.
  applys triple_conseq_frame triple_iireduce.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'. applys himpl_refl.
  simpl. intros r. ext.
  applys triple_conseq_frame triple_iiorganize.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  apply iiorgan_diff in H.
  rewrite <- H. applys himpl_refl.
Qed.
 

