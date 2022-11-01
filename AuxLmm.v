From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export Rules.


(*------------------------------------------------------------------------*)

(* ================================================================= *)
(** Some ltac to simplify the verification *)

(*--- to extract the existential quantifier ---*)
Ltac extexists :=
  intros; simpl; 
  try apply triple_hfexists;
  try apply triple_hfexists';
  try apply triple_hbexists;
  try apply triple_hbexists';
  try apply triple_hexists.

(*--- to extract the pure fact ---*)
Ltac extpure :=
  intros; simpl; 
  try apply triple_hfpure;
  try apply triple_hbpure; 
  try apply triple_hpure;
  simpls;
  intros ->.

(* - combine the extraction - *)
Ltac ext :=
  try extpure; try extexists.

(*--------- Some scripts for CBS-heap entailments --------------*)
Ltac inner_femp :=
 try intros r;
 try rewrite hstar_sep;
 try rewrite hfstar_hempty_l;
 try rewrite hfstar_hempty_r;
 apply himpl_refl.

Ltac inner_bemp :=
 try intros r;
 try rewrite hstar_sep;
 try rewrite hbstar_hempty_l;
 try rewrite hbstar_hempty_r;
 apply himpl_refl.

Ltac outer_emp :=
 try intros r;
 try rewrite hstar_hempty_l';
 try rewrite hstar_hempty_r';
 apply himpl_refl.

Ltac rew_read:=
  intros v;
  rewrite hstar_assoc,hstar_sep,hfstar_hempty_l;
  apply himpl_refl;
  ext.

(*--------- Some scripts for recursive programs --------------*)
Lemma nth_listbloc_1 : forall p1 p2 p3,
(nth_default bnull (to_nat 1) (p1 :: p2 :: p3 :: nil)) = p2.
Proof.
  intros. rewrite to_nat_1,nth_default_succ,nth_default_zero. auto.
Qed.

Lemma nth_listbloc_1' : forall p1 p2,
(nth_default bnull (to_nat 1) (p1 :: p2 :: nil)) = p2.
Proof.
  intros. rewrite to_nat_1,nth_default_succ,nth_default_zero. auto.
Qed.

Lemma nth_listbloc_2 : forall p1 p2 p3,
(nth_default bnull (to_nat (1 + 1)) (p1 :: p2 :: p3 :: nil)) = p3.
Proof.
  intros. rewrite to_nat_plus; try math.
  rewrite to_nat_1. do 2 rewrite nth_default_succ. rewrite~ nth_default_zero.
Qed.

(*----- expand the recursive program  -------*)
Ltac exp_fix :=
  intros; subst; applys* triple_app_fix2; simpl;
  applys triple_let triple_fsize; ext;
  applys triple_let triple_eq; ext;
  applys triple_if; case_if*.

(*----- verify rec body until to the target block -------*)
Ltac fix_body := 
  applys triple_let triple_fget_nth_blk; ext;
  applys triple_let triple_add; ext;
  try rewrite nth_default_zero;
  try rewrite nth_listbloc_1;
  try rewrite nth_listbloc_1';
  try rewrite nth_listbloc_2.

(* ------ for read file example --------- *)
Ltac fix_read :=
  exp_fix; fix_body;
  applys triple_let;
  try applys triple_conseq_frame triple_bget.

(* ------ for map file example --------- *)
Ltac fix_map :=
  exp_fix; fix_body;
  applys triple_let;
  try applys triple_conseq_frame triple_wdmap.

Ltac fix_locate :=
  exp_fix; fix_body;
  applys triple_let;
  try applys triple_conseq_frame triple_locate.

(* ------ for remove file example --------- *)
Ltac fix_rem :=
  exp_fix; fix_body;
  applys triple_seq;
  try applys triple_conseq_frame triple_bdelete.

(* ################################## *)
Lemma eqword_refl : forall n1,
  eqword (n1,1) (n1,1) = true.
Proof. intros. unfold eqword. simpl. apply~ Z.eqb_eq. Qed.

Lemma neqword_refl : forall n1,
  neqword (n1,1) (n1,1) = false.
Proof. intros. unfold neqword. rewrite~ eqword_refl. Qed.

Lemma eqword_diff : forall n1 n2,
  n1 =? n2 = false ->
  eqword (n1,1) (n2,1) = false.
Proof. intros. unfold eqword. simpls~. Qed.

Lemma neqword_diff : forall n1 n2,
  n1 =? n2 = false ->
  neqword (n1,1) (n2,1) = true.
Proof. intros. unfold neqword. rewrite~ eqword_diff. Qed.

Lemma eqb_comm : forall n1 n2,
  (n1 =? n2) = (n2 =? n1).
Proof.
  intros. destruct (n1 =? n2) eqn:H.
  apply Z.eqb_eq in H. rewrite H.
  symmetry. apply~ Z.eqb_eq.
  symmetry. apply Bool.not_true_is_false.
  intro N.  apply Z.eqb_eq in N.
  rewrite N in H. lets : Z.eqb_eq n1 n1.
  assert (H1: n1 = n1). auto.
  apply H0 in H1. rewrite H in H1. discriminate.
Qed.

Lemma eqword_diff_2 : forall n1 n2,
  n1 =? n2 = false ->
  eqword (n2,1) (n1,1) = false.
Proof. intros. unfold eqword. simpls. rewrite~ eqb_comm. Qed.

Lemma neqword_diff_2 : forall n1 n2,
  n1 =? n2 = false ->
  neqword (n2,1) (n1,1) = true.
Proof. intros. unfold neqword. rewrite~ eqword_diff_2. Qed.

Hint Resolve eqword_refl neqword_refl eqword_diff_2 neqword_diff_2
             eqb_comm neqword_diff.

Definition diff_each_3 (n1 n2 n3:int) : Prop :=
  n1 =? n2 = false /\ n1 =? n3 = false /\ n2 =? n3 = false.

Lemma diff_3_bool : forall n1 n2 n3,
   diff_each_3 n1 n2 n3 ->
   eqword (n1,1) (n1,1) = true
/\ eqword (n2,1) (n2,1) = true
/\ eqword (n3,1) (n3,1) = true
/\ neqword (n1,1) (n2,1) = true
/\ neqword (n1,1) (n3,1) = true
/\ neqword (n2,1) (n3,1) = true
/\ neqword (n2,1) (n1,1) = true
/\ neqword (n3,1) (n1,1) = true
/\ neqword (n3,1) (n2,1) = true
/\ eqword (n1,1) (n2,1) = false
/\ eqword (n1,1) (n3,1) = false
/\ eqword (n2,1) (n3,1) = false
/\ eqword (n2,1) (n1,1) = false
/\ eqword (n3,1) (n1,1) = false
/\ eqword (n3,1) (n2,1) = false
/\ neqword (n1,1) (n1,1) = false
/\ neqword (n2,1) (n2,1) = false
/\ neqword (n3,1) (n3,1) = false.
Proof. introv. intros (H1&H2&H3). splits*. Qed.
 
Lemma shuffle_diff : forall (n1 n2 n3:int),
  diff_each_3 n1 n2 n3 ->
  wordshuffle ((n1,1)::(n2,1)::(n3,1)::(n1,1)::(n2,1)::nil) =
  (((n1,1)::(n1,1):: nil) :: ((n2,1)::(n2,1)::nil) ::((n3,1)::nil) ::nil).
Proof.
  intros.
  apply diff_3_bool in H 
  as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10
    &H11&H12&H13&H14&H15&H16&H17&H18).
  unfold wordshuffle, shuffle, remove_duplicates.
  repeat case_if. simpl.
  repeat case_if. simpl.
  repeat case_if. simpl.
  repeat case_if. auto.
Qed.

(* $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ *)
Lemma eqiikey_refl : forall n b,
  eqiikey (n,b,1) (n,b,1) = true.
Proof. intros. unfold eqiikey, eqindex. simpl.
  apply Bool.andb_true_iff. splits*;
  apply~ Z.eqb_eq.
Qed.

Lemma neqiikey_refl : forall n b,
  neqiikey (n,b,1) (n,b,1) = false.
Proof. intros. unfold neqiikey. rewrite~ eqiikey_refl. Qed.

Lemma eqiikey_diff_n : forall n1 n2 b1 b2,
  n1 =? n2 = false ->
  eqiikey (n1,b1,1) (n2,b2,1) = false.
Proof. 
  intros. unfold eqiikey,eqindex. simpl.
  apply Bool.andb_false_iff. left~.
Qed.

Lemma eqiikey_diff_b : forall n1 n2 (b1 b2:nat),
  b1 =? b2 = false ->
  eqiikey (n1,b1,1) (n2,b2,1) = false.
Proof. 
  intros. unfold eqiikey,eqindex. simpl.
  apply Bool.andb_false_iff. right~.
Qed.

Lemma neqiikey_diff_n : forall n1 n2 b1 b2,
  n1 =? n2 = false ->
  neqiikey (n1,b1,1) (n2,b2,1) = true.
Proof. intros. unfold neqiikey. rewrite~ eqiikey_diff_n. Qed.

Lemma neqiikey_diff_b : forall n1 n2 (b1 b2:nat),
  b1 =? b2 = false ->
  neqiikey (n1,b1,1) (n2,b2,1) = true.
Proof. intros. unfold neqiikey. rewrite~ eqiikey_diff_b. Qed.

Lemma eqindex_comm : forall n1 n2 b1 b2,
  eqindex (n1,b1) (n2,b2) = eqindex (n2,b2) (n1,b1).
Proof.
  intros. destruct (eqindex (n1,b1) (n2,b2)) eqn:H.
  unfolds eqindex. simpls.
  apply Bool.andb_true_iff in H as (H1&H2).
  symmetry. apply Bool.andb_true_iff.
  split; rewrite~ eqb_comm.
  unfolds eqindex. simpls.
  apply Bool.andb_false_iff in H.
  destruct H; symmetry; apply Bool.andb_false_iff.
  left. rewrite~ eqb_comm.
  right. rewrite~ eqb_comm.
Qed.

Lemma eqiikey_diff_2_n : forall n1 n2 b1 b2,
  n1 =? n2 = false ->
  eqiikey (n2,b1,1) (n1,b2,1) = false.
Proof.
  intros. unfold eqiikey. simpl.
  rewrite eqindex_comm. unfold eqindex. simpls.
  apply Bool.andb_false_iff. left~.
Qed.

Lemma eqiikey_diff_2_b : forall n1 n2 (b1 b2:bloc),
  b1 =? b2 = false ->
  eqiikey (n1,b2,1) (n2,b1,1) = false.
Proof.
  intros. unfold eqiikey. simpl.
  rewrite eqindex_comm. unfold eqindex. simpls.
  apply Bool.andb_false_iff. right~.
Qed.

Lemma neqiikey_diff_2_n : forall n1 n2 b1 b2,
  n1 =? n2 = false ->
  neqiikey (n2,b1,1) (n1,b2,1) = true.
Proof. intros. unfold neqiikey. rewrite~ eqiikey_diff_2_n. Qed.

Lemma neqiikey_diff_2_b : forall n1 n2 (b1 b2:bloc),
  b1 =? b2 = false ->
  neqiikey (n1,b2,1) (n2,b1,1) = true.
Proof. intros. unfold neqiikey. rewrite~ eqiikey_diff_2_b. Qed.

Hint Resolve eqiikey_refl neqiikey_refl 
eqiikey_diff_n eqiikey_diff_b neqiikey_diff_n
neqiikey_diff_b eqiikey_diff_2_n eqiikey_diff_2_b
neqiikey_diff_2_n neqiikey_diff_2_b.

Lemma diff_each_index: forall (n1 n2:int) (b1 b2:bloc),
  n1 =? n2 = false /\ b1 =? b2 = false ->
  eqiikey (n1,b1,1) (n1,b1,1) = true
/\ eqiikey (n1,b2,1) (n1,b2,1) = true
/\ eqiikey (n2,b1,1) (n2,b1,1) = true
/\ neqiikey (n1,b1,1) (n1,b2,1) = true
/\ neqiikey (n1,b1,1) (n2,b1,1) = true
/\ neqiikey (n1,b2,1) (n2,b1,1) = true
/\ neqiikey (n1,b2,1) (n1,b1,1) = true
/\ neqiikey (n2,b1,1) (n1,b1,1) = true
/\ neqiikey (n2,b1,1) (n1,b2,1) = true
/\ eqiikey (n1,b1,1) (n1,b2,1) = false
/\ eqiikey (n1,b1,1) (n2,b1,1) = false
/\ eqiikey (n1,b2,1) (n2,b1,1) = false
/\ eqiikey (n1,b2,1) (n1,b1,1) = false
/\ eqiikey (n2,b1,1) (n1,b1,1) = false
/\ eqiikey (n2,b1,1) (n1,b2,1) = false
/\ neqiikey (n1,b1,1) (n1,b1,1) = false
/\ neqiikey (n1,b2,1) (n1,b2,1) = false
/\ neqiikey (n2,b1,1) (n2,b1,1) = false.
Proof. introv. intros (H1&H2). splits*. Qed.


Lemma iishuffle_diff : forall (n1 n2:int) (b1 b2:bloc),
  n1 =? n2 = false /\ b1 =? b2 = false ->
(iishuffle ((n1, b1, 1) :: (n2, b1, 1)::
            (n1, b1, 1):: (n1, b2, 1) :: nil)) =
( ((n1, b1, 1) :: (n1, b1, 1) :: nil)::
  ((n2, b1, 1) :: nil)::
  ((n1, b2, 1) :: nil):: nil).
Proof.
  intros.
  apply diff_each_index in H as
  (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10
    &H11&H12&H13&H14&H15&H16&H17&H18).
  unfold iishuffle,shuffle,remove_duplicates.
  simpl. repeat case_if.
  simpl. repeat case_if.
  simpl. repeat case_if.
  simpl. repeat case_if. auto.
Qed.

(* $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ *)
Lemma eqid_refl : forall (n c1 c2:int) (b1 b2:bloc),
  eqid (n,b1,c1) (n,b2,c2) = true.
Proof. intros. unfold eqid. simpl. apply~ Z.eqb_eq. Qed.

Lemma neqid_refl : forall (n c1 c2:int) (b1 b2:bloc),
  neqid (n,b1,c1) (n,b2,c2) = false.
Proof. intros. unfold neqid. rewrite~ eqid_refl. Qed.

Lemma eqid_diff : forall (n1 n2 c1 c2:int) (b1 b2:bloc),
  n1 =? n2 = false ->
  eqid (n1,b1,c1) (n2,b2,c2) = false.
Proof. intros. unfold eqid. simpls~. Qed.

Lemma neqid_diff : forall (n1 n2 c1 c2:int) (b1 b2:bloc),
  n1 =? n2 = false ->
  neqid (n1,b1,c1) (n2,b2,c2) = true.
Proof. intros. unfold neqid. rewrite~ eqid_diff. Qed.

Lemma eqid_diff_2 : forall (n1 n2 c1 c2:int) (b1 b2:bloc),
  n1 =? n2 = false ->
  eqid (n2,b1,c1) (n1,b2,c2) = false.
Proof. intros. unfold eqid. simpls. rewrite~ eqb_comm. Qed.

Lemma neqid_diff_2 : forall (n1 n2 c1 c2:int) (b1 b2:bloc),
  n1 =? n2 = false ->
  neqid (n2,b1,c1) (n1,b2,c2) = true.
Proof. intros. unfold neqid. rewrite~ eqid_diff_2. Qed.

Hint Resolve eqid_refl neqid_refl eqid_diff_2 neqid_diff_2
             eqb_comm neqid_diff.

Lemma diff_ind : forall (n1 n2:int) (b1 b2:bloc),
  n1 =? n2 = false /\ b1 =? b2 = false ->
   eqid (n1,b1,2) (n1,b1,2) = true
/\ eqid (n1,b1,2) (n2,b1,1) = false
/\ eqid (n1,b1,2) (n1,b2,1) = true
/\ eqid (n2,b1,1) (n2,b1,1) = true
/\ eqid (n2,b1,1) (n1,b1,2) = false
/\ eqid (n2,b1,1) (n1,b2,1) = false
/\ eqid (n1,b2,1) (n2,b1,1) = false
/\ eqid (n1,b2,1) (n1,b1,2) = true
/\ eqid (n1,b2,1) (n1,b2,1) = true
/\ neqid (n1,b1,2) (n1,b1,2) = false
/\ neqid (n1,b1,2) (n2,b1,1) = true
/\ neqid (n1,b1,2) (n1,b2,1) = false
/\ neqid (n2,b1,1) (n2,b1,1) = false
/\ neqid (n2,b1,1) (n1,b1,2) = true
/\ neqid (n2,b1,1) (n1,b2,1) = true
/\ neqid (n1,b2,1) (n2,b1,1) = true
/\ neqid (n1,b2,1) (n1,b1,2) = false
/\ neqid (n1,b2,1) (n1,b2,1) = false.
Proof. intros. splits*. Qed.

Lemma iiorgan_diff : forall (n1 n2:int) (b1 b2:bloc),
  n1 =? n2 = false /\ b1 =? b2 = false ->
iiorganize ((n1, b1, 2) :: (n2, b1, 1) :: (n1, b2, 1) :: nil) = 
  ((n1, (b1, 2) :: (b2, 1) :: nil) :: (n2, (b1, 1) :: nil) :: nil).
Proof.
  intros. unfold iiorganize, idshuffle.
  unfold shuffle, remove_duplicates.
  apply diff_ind in H as
  (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10
    &H11&H12&H13&H14&H15&H16&H17&H18).
  simpl. repeat case_if.
  simpl. repeat case_if.
  simpl. repeat case_if. auto.
Qed.
