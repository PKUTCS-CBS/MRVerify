(**

== Representation and verification of WordCount ==

WordCount is a standard MapReduce application.
It counts each word's frequency in a CBS file.

This file shows how we represent the actual application, 
and how we specify and verify the behavior of programs.

Advice: readers need to read Language.v first.

Author: Bowen Zhang.

Date : 2022.11.1
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export Rules AuxLmm.
(*------------------------------------------------------------------------*)

Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.

(* ########################### WordCount ########################### *)

(*  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose a HDFS state before WordCount:

--f
  | bk1 [n1;n2]
  | bk2 [n3;n1]
  | bk3 [n2]

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The state after WordCount:

--f
  | bk1 [n1;n2]
  | bk2 [n3;n1]
  | bk3 [n2]

--f2
  | bk4 [n1;2]
  | bk5 [n2;2]
  | bk6 [n3;1]
*)

(* 
------- Representation and Specification ----------

Definition WordCount := 
  Fun 'f :=
    Let 'L1 := Mapper 'f 0 in
    Let 'L2 := Shuffle 'L1 in
    Let 'l := Reducer 'L2 in
    Create_File 'l.


Lemma triple_WordCount: forall Hf Hb (f:floc) (n1 n2 n3 :int) (p1 p2 p3:bloc),
  diff_each_3 n1 n2 n3 ->
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n1::nil)) \b* (p3 ~b~> (n2::nil)) ) ->
  triple (WordCount f)
    (\R[Hf,Hb])
    (fun r => \exists f1 b4 b5 b6,( \[r= (val_floc f1)] \* 
        (\R[(f1 ~f~> (b4::b5::b6::nil) \f* Hf),
        Hb \b* (b4 ~b~> (n1::2::nil)) \b* (b5 ~b~> (n2::2::nil))
        \b* (b6 ~b~> (n3::1::nil))] ))).

*)

(*============= Mapper ================*)
Definition Mapper := 
  Fix 'F 'f 'i :=
    Let 'n := 'fsize 'f in
    Let 'be := ('i '= 'n) in
    If_ 'be
    Then (val_Listwd nil)
    Else
      Let 'bk := 'nth_blk 'f 'i in
      Let 'i1 := 'i '+ 1 in
      Let 'ln := 'wdmap 'bk in
      Let 'ln1 := 'F 'f 'i1 in
      'ln 'w:: 'ln1.

(* specification of mapper *)
Lemma triple_Mapper: forall Hf Hb (f:floc) (n1 n2 n3:int) (p1 p2 p3:bloc) (L:(list (list wdpair))),
  diff_each_3 n1 n2 n3 ->
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n1::nil)) \b* (p3 ~b~> (n2::nil)) ) ->
  L = ( ((n1,1)::(n2,1)::nil) :: ((n3,1)::(n1,1)::nil) :: ((n2,1)::nil) :: nil ) ->
  triple (Mapper f 0)
    (\R[Hf,Hb])
    (fun r => \[r= val_Listwd L] \* \R[Hf,Hb]).
Proof.
  fix_map.
  rewrite hstar_sep, hfstar_hempty_l. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  fix_map.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm,hbstar_assoc. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  fix_map.
  rewrite hstar_sep, hfstar_hempty_l,hbstar_comm,hbstar_assoc. apply himpl_refl.
  rew_read. ext.

  applys triple_let.
  exp_fix.
  applys triple_val'. ext.
  applys triple_app_wdlist. ext.
  applys triple_app_wdlist. ext.
  applys triple_conseq triple_app_wdlist.
  apply himpl_refl.
  intros r. rew_list. 
  rewrite hbstar_comm,hbstar_assoc. apply himpl_refl.
Qed.

(*============= Shuffle ================*)
Definition Shuffle :=
 Fun 'L :=
    Let 'l := 'wdmerge 'L in
      'wdshuffle 'l.

Lemma triple_Shuffle: forall Hf Hb (n1 n2 n3 : int) (L1 L2: (list (list wdpair))),
  diff_each_3 n1 n2 n3 ->
  L1 = ( ((n1,1)::(n2,1)::nil) :: ((n3,1)::(n1,1)::nil) :: ((n2,1)::nil) :: nil ) ->
  L2 = ( ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: ((n3,1)::nil) ::nil ) ->
  triple (Shuffle (val_Listwd L1))
    (\R[Hf,Hb])
    (fun r => \[r= val_Listwd L2] \* \R[Hf,Hb]).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_let.
  applys triple_conseq_frame triple_wdmerge.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  unfold wordmerge,merge. simpl. applys himpl_refl.
  ext.
  applys triple_conseq_frame triple_wdshuffle.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  apply shuffle_diff in H.
  rewrite <- H.
  applys himpl_refl.
Qed.

(*============= Reducer ================*)
Definition Reducer :=
  Fun 'L :=  'wdreduce 'L.

Lemma triple_Reducer: forall Hf Hb (n1 n2 n3 : int) (lwd:list wdpair) (L : (list (list wdpair))),
  diff_each_3 n1 n2 n3 ->
  L = ( ((n1,1)::(n1,1)::nil) :: ((n2,1)::(n2,1)::nil) :: ((n3,1)::nil) ::nil ) ->
  lwd = ((n1,2)::(n2,2)::(n3,1)::nil ) ->
  triple (Reducer (val_Listwd L))
    (\R[Hf,Hb])
    (fun r => \[r= val_listwdpair lwd] \* \R[Hf,Hb]).
Proof.
  intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_conseq_frame triple_wdreduce.
  rewrite hstar_hempty_r'. applys himpl_refl.
  intros r. rewrite hstar_hempty_r'.
  applys himpl_refl.
Qed.


(*============= Create files ================*)
Definition Create_Blks_buffer : val :=
  Fix 'F 'l 'lb:=
    Let 'm := 'len 'l in
    Let 'be := ('m '<= 2) in
    If_ 'be
    Then 
      Let 'bk := 'bcreate 'l in
        'bk 'b+ 'lb
    Else
      Let 'l1 := 'hd 'l in
      Let 'l2 := 'tl 'l in
      Let 'bk1 := 'bcreate 'l1 in
      Let 'lb1 := 'bk1 'b+ 'lb in
        'F 'l2 'lb1.

Lemma triple_Create_Blks_buffer : forall Hf (n1 n2 n3 n4 n5 n6:int),
  triple (Create_Blks_buffer (val_listint (n1::n2::n3::n4::n5::n6::nil)) (val_listbloc nil))
    (\R[Hf, \b[] ])
     (fun r => \exists b1 b2 b3,( \[r=(val_listbloc (b3::b2::b1::nil))] \* 
               (\R[Hf, (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil) \b* (b3 ~b~> (n5::n6::nil)))]))).
Proof.
  intros. applys* triple_app_fix2. simpl.
  applys triple_let triple_list_len.
  ext. applys triple_let triple_le. ext.
  applys triple_if. case_if*. destruct C. auto.
  applys triple_let triple_list_hd. ext.
  applys triple_let triple_list_tl. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bcreate.
  rewrite hstar_sep. rewrite hfstar_hempty_r, hbstar_hempty_l.
  apply himpl_refl. intros r. simpl.
  apply himpl_refl. intros r. simpl.
  rewrite hstar_hexists.
  applys triple_hexists. intros b1.
  rewrite hstar_hempty_r. ext.
  applys triple_let triple_fbuffer_list.
  intros. simpl. ext.

  applys* triple_app_fix2. simpl.
  applys triple_let triple_list_len.
  ext. applys triple_let triple_le. ext.
  applys triple_if. case_if*.
  applys triple_let triple_list_hd. ext.
  applys triple_let triple_list_tl. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bcreate.
  rewrite hstar_sep. rewrite hfstar_hempty_r, hbstar_hempty_l.
  apply himpl_refl. intros r. simpl.
  apply himpl_refl. intros r. simpl.
  rewrite hstar_hexists.
  applys triple_hexists. intros b2.
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_r. ext.
  applys triple_let triple_fbuffer_list.
  intros. simpl. ext.

  applys* triple_app_fix2. simpl.
  applys triple_let triple_list_len.
  ext. applys triple_let triple_le. ext.
  applys triple_if. case_if*.
  applys triple_let.
  applys triple_conseq_frame triple_bcreate.
  rewrite hstar_sep. rewrite hfstar_hempty_r, hbstar_hempty_l.
  apply himpl_refl. intros r. simpl.
  apply himpl_refl. intros r. simpl.
  rewrite hstar_hexists.
  applys triple_hexists. intros b3.
  rewrite hstar_assoc, hstar_sep, hfstar_hempty_r. ext.
  applys triple_conseq_frame triple_fbuffer_list.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros r. simpl. rewrite hstar_hempty_r.
  rewrite hbstar_comm3. intros h H.
  rewrite hstar_hpure_iff in H.
  destruct H as (H1&H2).
  exists b1 b2 b3.
  applys hstar_hpure_iff. splits~.
  destruct C1. rew_list. discriminate.
Qed.

Definition Create_File : val :=
  Fun 'l:=
    Let 'l1 := 'reform 'l in
    Let 'lb1 := Create_Blks_buffer 'l1 (val_listbloc nil) in
    Let 'lb := 'frev 'lb1 in
      'fcreate 'lb.

Lemma triple_Create_File : forall (w1 w2 w3 n1 n2 n3:int),
  triple (Create_File (val_listwdpair ((w1,n1)::(w2,n2)::(w3,n3)::nil)) )
    (\R[\f[], \b[] ])
     (fun r => \exists f b1 b2 b3,( \[r= (val_floc f)] \* 
               (\R[(f ~f~> (b1::b2::b3::nil)), (b1 ~b~> (w1::n1::nil)) \b* (b2 ~b~> (w2::n2::nil) \b* (b3 ~b~> (w3::n3::nil)))]))).
Proof.
  intros. applys* triple_app_fun. simpl.
  applys triple_let triple_MRlist_reform.
  ext.
  applys triple_let triple_Create_Blks_buffer.
  intros v. ext. intros b1. ext. intros b2. ext. intros b3. ext.
  applys triple_let.
  applys triple_conseq_frame triple_frev_blist.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros r. rewrite hstar_assoc, hstar_hempty_l. apply himpl_refl.
  ext.
  applys triple_conseq_frame triple_fcreate.
  rewrite hstar_hempty_r'.
  apply himpl_noduplicate3.
  intros v. rewrite hstar_hempty_r'.
  apply himpl_hexists_l. intros f.
  intros h M. exists~ f b1 b2 b3.
Qed.



(* $$$$$$$$$$$$$==================$$$$$$$$$$$$$$$$$$$$$ *)


Definition WordCount := 
  Fun 'f :=
    Let 'L1 := Mapper 'f 0 in
    Let 'L2 := Shuffle 'L1 in
    Let 'l := Reducer 'L2 in
    Create_File 'l.

Lemma triple_WordCount: forall Hf Hb (f:floc) (n1 n2 n3 :int) (p1 p2 p3:bloc),
  diff_each_3 n1 n2 n3 ->
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n1::nil)) \b* (p3 ~b~> (n2::nil)) ) ->
  triple (WordCount f)
    (\R[Hf,Hb])
    (fun r => \exists f1 b4 b5 b6,( \[r= (val_floc f1)] \* 
        (\R[(f1 ~f~> (b4::b5::b6::nil) \f* Hf),
        Hb \b* (b4 ~b~> (n1::2::nil)) \b* (b5 ~b~> (n2::2::nil))
        \b* (b6 ~b~> (n3::1::nil))] ))).
Proof.
    intros. subst.
  applys* triple_app_fun. simpl.
  applys triple_let.
  applys* triple_Mapper.
  simpl. intros r. ext.
  applys triple_let. applys* triple_Shuffle H.
  ext.
  applys triple_let. applys* triple_Reducer.
  ext.
  applys triple_conseq_frame triple_Create_File.
  rewrite hstar_hempty_l'. apply himpl_refl.
  intros r. rewrite hstar_hexists.
  apply himpl_hexists_l. intros f1.
  rewrite hstar_hexists.
  apply himpl_hexists_l. intros b4.
  rewrite hstar_hexists.
  apply himpl_hexists_l. intros b5.
  rewrite hstar_hexists.
  apply himpl_hexists_l. intros b6.
  rewrite hstar_assoc.
  intros h M.
  rewrite hstar_hpure_iff in M.
  destruct M as (M1&M2).
  rewrite hstar_sep in M2.
  exists f1 b4 b5 b6.
  rewrite hstar_hpure_iff.
  splits*. rewrite~ hbstar_comm.
Qed.
 
