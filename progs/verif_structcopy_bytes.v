Require Import VST.floyd.proofauto.
Require Import VST.floyd.data_at_memvals.
Require Import VST.floyd.copy_alignment.
Require Import VST.veric.memvals_at.
Require Import VST.veric.res_predicates.
Require Import VST.veric.align_mem.

Local Open Scope Z_scope.
Local Open Scope logic.

Definition raw_pair_id: ident := 101%positive.
Definition overaligned_char_id: ident := 102%positive.
Definition empty_aligned_member_id: ident := 103%positive.
Definition empty_struct_id: ident := 104%positive.
Definition copy_empty_id: ident := 105%positive.
Definition destination_id: ident := 106%positive.
Definition source_id: ident := 107%positive.
Definition first_id: ident := 1%positive.
Definition second_id: ident := 2%positive.

Definition byte_test_composites: list composite_definition :=
  [Composite raw_pair_id Struct
    [Member_plain first_id tuint; Member_plain second_id tuint] noattr;
   Composite overaligned_char_id Struct [Member_plain first_id tuchar]
    {| attr_volatile := false; attr_alignas := Some 3%N |};
   Composite empty_aligned_member_id Struct
    [Member_plain first_id tuchar;
     Member_plain second_id (tarray tuint 0)] noattr;
   Composite empty_struct_id Struct [] noattr].

Definition f_copy_empty := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params :=
    [(destination_id, tptr (Tstruct empty_struct_id noattr));
     (source_id, tptr (Tstruct empty_struct_id noattr))];
  fn_vars := [];
  fn_temps := [];
  fn_body := Sassign
    (Ederef (Etempvar destination_id (tptr (Tstruct empty_struct_id noattr)))
      (Tstruct empty_struct_id noattr))
    (Ederef (Etempvar source_id (tptr (Tstruct empty_struct_id noattr)))
      (Tstruct empty_struct_id noattr))
|}.

Definition byte_test_program: Clight.program :=
  Clightdefs.mkprogram byte_test_composites
    [(copy_empty_id, Gfun (Ctypes.Internal f_copy_empty))]
    [copy_empty_id] copy_empty_id Logic.I.

#[local] Instance ByteTestSpecs: compspecs.
Proof. make_compspecs byte_test_program. Defined.

Definition raw_pair_type := Tstruct raw_pair_id noattr.
Definition overaligned_char_type := Tstruct overaligned_char_id noattr.
Definition empty_aligned_member_type :=
  Tstruct empty_aligned_member_id noattr.
Definition empty_struct_type := Tstruct empty_struct_id noattr.

Lemma test_shares_are_distinct_and_readable:
  readable_share Ews /\ readable_share Ers /\ Ews <> Ers.
Proof.
  split; [apply writable_readable, writable_Ews |].
  split; [apply readable_Ers |]. intro SAME.
  assert (RETAINER: Share.glb extern_retainer Share.Rsh = Share.bot).
  {
    unfold extern_retainer. rewrite <- (glb_split_x Share.Lsh) at 1.
    rewrite (Share.glb_commute Share.Lsh (fst (Share.split Share.Lsh))),
      Share.glb_assoc, glb_Lsh_Rsh, Share.glb_bot. reflexivity.
  }
  pose proof (f_equal (fun sh => Share.glb Share.Rsh sh) SAME) as READ_PART.
  unfold Ews, Ers in READ_PART. rewrite !Share.distrib1 in READ_PART.
  rewrite (Share.glb_commute Share.Rsh extern_retainer), RETAINER,
    Share.glb_idem, glb_split_x in READ_PART.
  rewrite (Share.lub_commute Share.bot Share.Rsh),
    (Share.lub_commute Share.bot (fst (Share.split Share.Rsh))),
    !Share.lub_bot in READ_PART.
  destruct (Share.split Share.Rsh) as [left_share right_share] eqn:SPLIT.
  simpl in READ_PART.
  apply (nonemp_split_neq1 Share.Rsh left_share right_share
    Rsh_nonidentity SPLIT).
  symmetry; exact READ_PART.
Qed.

Lemma raw_pair_nonzero_compatible: forall b,
  field_compatible raw_pair_type [] (Vptr b (Ptrofs.repr 16)) /\
  field_compatible raw_pair_type [] (Vptr b (Ptrofs.repr 40)).
Proof.
  intro b. split; apply malloc_compatible_field_compatible;
    try reflexivity; unfold malloc_compatible.
  all: rewrite Ptrofs.unsigned_repr by rep_lia; split;
    [apply Z.mod_divide; computable | computable].
Qed.

Lemma arbitrary_bytes_reconstruct_two_shares: forall bytes b1 b2,
  Zlength bytes = sizeof raw_pair_type ->
  memvals_at_ptr Ews bytes (Vptr b1 (Ptrofs.repr 16)) *
  memvals_at_ptr Ers bytes (Vptr b2 (Ptrofs.repr 40)) |--
  data_at Ews raw_pair_type (default_val raw_pair_type)
    (Vptr b1 (Ptrofs.repr 16)) *
  data_at Ers raw_pair_type (default_val raw_pair_type)
    (Vptr b2 (Ptrofs.repr 40)).
Proof.
  intros bytes b1 b2 LENGTH. apply sepcon_derives.
  - rewrite data_at_memvals_eq by
      (auto using writable_readable, writable_Ews; vm_compute; auto).
    apply andp_right.
    + apply prop_right. apply raw_pair_nonzero_compatible.
    + apply exp_right with (x := bytes). apply andp_right.
      * apply prop_right. apply data_at_memvals_default;
          auto; vm_compute; auto.
      * apply derives_refl.
  - rewrite data_at_memvals_eq by
      (auto using readable_Ers; vm_compute; auto).
    apply andp_right.
    + apply prop_right. apply raw_pair_nonzero_compatible.
    + apply exp_right with (x := bytes). apply andp_right.
      * apply prop_right. apply data_at_memvals_default;
          auto; vm_compute; auto.
      * apply derives_refl.
Qed.

Definition fragment_and_undef_bytes (payload: block): list memval :=
  [Fragment (Vptr payload (Ptrofs.repr 3)) Q64 0;
   Undef;
   Byte (Byte.repr 255);
   Fragment (Vptr payload (Ptrofs.repr 3)) Q32 1;
   Undef; Byte Byte.zero; Undef; Undef].

Lemma fragments_and_undef_reconstruct_two_shares: forall payload b1 b2,
  memvals_at_ptr Ews (fragment_and_undef_bytes payload)
    (Vptr b1 (Ptrofs.repr 16)) *
  memvals_at_ptr Ers (fragment_and_undef_bytes payload)
    (Vptr b2 (Ptrofs.repr 40)) |--
  (data_at Ews raw_pair_type (default_val raw_pair_type)
     (Vptr b1 (Ptrofs.repr 16)) *
   data_at Ers raw_pair_type (default_val raw_pair_type)
     (Vptr b2 (Ptrofs.repr 40))) &&
  (memvals_at_ptr Ews (fragment_and_undef_bytes payload)
     (Vptr b1 (Ptrofs.repr 16)) *
   memvals_at_ptr Ers (fragment_and_undef_bytes payload)
     (Vptr b2 (Ptrofs.repr 40))).
Proof.
  intros. apply andp_right.
  - apply arbitrary_bytes_reconstruct_two_shares. reflexivity.
  - apply derives_refl.
Qed.

Lemma empty_array_bridge_nonzero: forall sh b,
  readable_share sh ->
  data_at_ sh (tarray tuint 0) (Vptr b (Ptrofs.repr 24)) =
  memvals_at_ptr sh [] (Vptr b (Ptrofs.repr 24)).
Proof.
  intros sh b READABLE. rewrite data_at__memvals_eq by auto.
  rewrite prop_true_andp.
  2: {
    apply malloc_compatible_field_compatible; try reflexivity.
    unfold malloc_compatible. rewrite Ptrofs.unsigned_repr by rep_lia.
    split; [apply Z.mod_divide; computable |].
    change (24 < Ptrofs.modulus). computable.
  }
  apply pred_ext.
  - apply exp_left; intro bytes. Intros.
    assert (bytes = []) by (apply Zlength_nil_inv; exact H).
    subst bytes. cancel.
  - apply exp_right with (x := @nil memval).
    rewrite prop_true_andp by reflexivity. apply derives_refl.
Qed.

Lemma scalar_leaf_recovers_pair_alignment: forall p,
  field_compatible raw_pair_type [StructField second_id] p ->
  copy_aligned raw_pair_type p.
Proof.
  intros p COMPATIBLE.
  eapply field_compatible_copy_aligned with
    (gfs := [StructField second_id]) (ch := Mint32);
    [exact COMPATIBLE | reflexivity | apply Z.divide_refl |
      apply Z.divide_refl].
Qed.

Lemma overaligned_char_alignment_limit: forall b,
  field_compatible overaligned_char_type [] (Vptr b (Ptrofs.repr 1)) /\
  ~ copy_aligned overaligned_char_type (Vptr b (Ptrofs.repr 1)).
Proof.
  intro b. split.
  - unfold field_compatible. split; [exact I |].
    split; [reflexivity |]. split.
    + change (Ptrofs.unsigned (Ptrofs.repr 1) + 8 < Ptrofs.modulus).
      rewrite Ptrofs.unsigned_repr by rep_lia. computable.
    + split; [|exact I].
      change (align_compatible_rec cenv_cs overaligned_char_type
        (Ptrofs.unsigned (Ptrofs.repr 1))).
      rewrite Ptrofs.unsigned_repr by rep_lia.
      apply natural_aligned_sound with (na := 1); reflexivity.
  - unfold copy_aligned. rewrite Ptrofs.unsigned_repr by rep_lia.
    intro ALIGN. specialize (ALIGN ltac:(computable)).
    change (8 | 1) in ALIGN. destruct ALIGN as [multiple ALIGN]. lia.
Qed.

Lemma empty_array_member_alignment_limit: forall b,
  field_compatible empty_aligned_member_type [] (Vptr b (Ptrofs.repr 1)) /\
  ~ copy_aligned empty_aligned_member_type (Vptr b (Ptrofs.repr 1)).
Proof.
  intro b. split.
  - unfold field_compatible. split; [exact I |].
    split; [reflexivity |]. split.
    + change (Ptrofs.unsigned (Ptrofs.repr 1) + 4 < Ptrofs.modulus).
      rewrite Ptrofs.unsigned_repr by rep_lia. computable.
    + split; [|exact I].
      change (align_compatible_rec cenv_cs empty_aligned_member_type
        (Ptrofs.unsigned (Ptrofs.repr 1))).
      rewrite Ptrofs.unsigned_repr by rep_lia.
      eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity |].
      intros i0 t0 z0 Htype Hoff. cbn in Htype, Hoff.
      destruct (ident_eq i0 first_id) as [FIRST | FIRST].
      * inv Htype. inv Hoff.
        apply align_compatible_rec_by_value with (ch := Mint8unsigned);
          [reflexivity | exists 1; reflexivity].
      * destruct (ident_eq i0 second_id); [|discriminate].
        inv Htype. inv Hoff. apply align_compatible_rec_Tarray.
        intros index BOUNDS. lia.
  - unfold copy_aligned. rewrite Ptrofs.unsigned_repr by rep_lia.
    intro ALIGN. specialize (ALIGN ltac:(computable)).
    change (4 | 1) in ALIGN. destruct ALIGN as [multiple ALIGN]. lia.
Qed.

Definition copy_empty_spec :=
  DECLARE copy_empty_id
  WITH destination: val, source: val
  PRE [tptr empty_struct_type, tptr empty_struct_type]
    PROP () PARAMS (destination; source)
    SEP (data_at_ Ews empty_struct_type destination;
         data_at Ers empty_struct_type (default_val empty_struct_type) source)
  POST [tvoid]
    PROP () RETURN ()
    SEP (data_at Ews empty_struct_type (default_val empty_struct_type)
           destination;
         data_at Ers empty_struct_type (default_val empty_struct_type) source).

Definition ByteVprog: varspecs := [].
Definition ByteGprog: funspecs := [copy_empty_spec].

Lemma empty_struct_has_zero_size: sizeof empty_struct_type = 0.
Proof. reflexivity. Qed.

Lemma empty_struct_copy_aligned: forall p,
  isptr p -> copy_aligned empty_struct_type p.
Proof.
  intros p POINTER. destruct p; try contradiction POINTER.
  unfold copy_aligned. intro POSITIVE.
  change (0 > 0) in POSITIVE. lia.
Qed.

Lemma body_copy_empty:
  semax_body ByteVprog ByteGprog f_copy_empty copy_empty_spec.
Proof.
  start_function. forward.
  all: try solve [apply empty_struct_copy_aligned;
    eapply field_compatible_isptr; eassumption].
  entailer!.
Qed.
