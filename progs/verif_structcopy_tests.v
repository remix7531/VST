Require Import VST.floyd.proofauto.
Require Import VST.progs.structcopy_tests.
Require Import VST.floyd.data_at_memvals.
Require Import VST.veric.semax_copy.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tpair := Tstruct _pair noattr.
Definition tnested := Tstruct _nested noattr.
Definition tarray_member := Tstruct _array_member noattr.
Definition tpair_array := Tstruct _pair_array noattr.
Definition tpointer_member := Tstruct _pointer_member noattr.
Definition tpadded := Tstruct _padded noattr.

Ltac struct_copy_predicate_head predicate :=
  lazymatch predicate with
  | ?function _ => struct_copy_predicate_head function
  | _ => predicate
  end.

Ltac check_struct_copy_predicate_heads actual expected :=
  lazymatch actual with
  | nil => lazymatch expected with nil => idtac end
  | ?actual_predicate :: ?actual_tail =>
      lazymatch expected with
      | ?expected_predicate :: ?expected_tail =>
          let actual_head := struct_copy_predicate_head actual_predicate in
          let expected_head := struct_copy_predicate_head expected_predicate in
          constr_eq actual_head expected_head;
          check_struct_copy_predicate_heads actual_tail expected_tail
      end
  end.

Ltac check_struct_copy_spatial_order expected :=
  rewrite ?copy_rules.copy_reptype_refl,
    ?copy_rules.copy_reptype_struct, ?copy_rules.copy_reptype_union;
  lazymatch goal with
  | |- ENTAIL _, ?pre |-- _ =>
      lazymatch pre with
      | context [SEPx ?actual] =>
          check_struct_copy_predicate_heads actual expected;
          unify actual expected
      end
  end.

Definition copy_pointer_spec :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, v: reptype tpair, sh1: share, sh2: share
 PRE [tptr tpair, tptr tpair]
   PROP (writable_share sh1; readable_share sh2)
   PARAMS (destination; source)
   SEP (data_at_ sh1 tpair destination; data_at sh2 tpair v source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at sh1 tpair v destination; data_at sh2 tpair v source).

Definition copy_local_spec :=
 DECLARE _copy_local
 WITH source: val, i: Z, j: Z
 PRE [tptr tpair]
   PROP () PARAMS (source)
   SEP (data_at Ews tpair (Vint (Int.repr i), Vint (Int.repr j)) source)
 POST [tuint]
   PROP () RETURN (Vint (Int.repr (i + j)))
   SEP (data_at Ews tpair (Vint (Int.repr i), Vint (Int.repr j)) source).

Definition copy_nested_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val,
      v1: reptype tpair, v2: reptype tpair,
      w1: reptype tpair, w2: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (data_at Ews tnested (v1, v2) destination;
        data_at Ers tnested (w1, w2) source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tnested (w2, v2) destination;
        data_at Ers tnested (w1, w2) source).

Definition copy_array_member_spec :=
 DECLARE _copy_array_member
 WITH destination: val, source: val, first: val, second: val
 PRE [tptr tarray_member, tptr tarray_member]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tarray_member destination;
        data_at Ers tarray_member [first; second] source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tarray_member [first; second] destination;
        data_at Ers tarray_member [first; second] source).

Definition copy_pointer_member_spec :=
 DECLARE _copy_pointer_member
 WITH destination: val, source: val, pointer: val, value: val
 PRE [tptr tpointer_member, tptr tpointer_member]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tpointer_member destination;
        data_at Ers tpointer_member (pointer, value) source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpointer_member (pointer, value) destination;
        data_at Ers tpointer_member (pointer, value) source).

Definition copy_padding_spec :=
 DECLARE _copy_padding
 WITH destination: val, source: val, tag: Z, value: Z
 PRE [tptr tpadded, tptr tpadded]
   PROP (0 <= tag <= Byte.max_unsigned) PARAMS (destination; source)
   SEP (data_at_ Ews tpadded destination;
        data_at Ers tpadded (Vint (Int.repr tag), Vint (Int.repr value)) source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpadded (Vint (Int.repr tag), Vint (Int.repr value)) destination;
        data_at Ers tpadded (Vint (Int.repr tag), Vint (Int.repr value)) source).

Definition copy_partial_spec :=
 DECLARE _copy_partial
 WITH destination: val, source: val, first: Z
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tpair destination;
        data_at Ers tpair (Vint (Int.repr first), Vundef) source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair (Vint (Int.repr first), Vundef) destination;
        data_at Ers tpair (Vint (Int.repr first), Vundef) source).

Definition copy_self_spec :=
 DECLARE _copy_self
 WITH object: val, v: reptype tpair
 PRE [tptr tpair]
   PROP () PARAMS (object)
   SEP (data_at Ews tpair v object)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair v object).

Definition copy_proved_alias_spec :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, v: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP (destination = source) PARAMS (destination; source)
   SEP (data_at Ews tpair v source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair v source).

Definition copy_fields_spec :=
 DECLARE _copy_fields
 WITH object: val, first: reptype tpair, second: reptype tpair
 PRE [tptr tnested]
   PROP () PARAMS (object)
   SEP (data_at Ews tnested (first, second) object)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tnested (second, second) object).

Definition copy_field_self_spec :=
 DECLARE _copy_field_self
 WITH object: val, first: reptype tpair, second: reptype tpair
 PRE [tptr tnested]
   PROP () PARAMS (object)
   SEP (data_at Ews tnested (first, second) object)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tnested (first, second) object).

Definition copy_nested_uninitialized_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, first: reptype tpair, second: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tnested destination;
        data_at Ers tnested (first, second) source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tnested (second, default_val tpair) destination;
        data_at Ers tnested (first, second) source).

Definition copy_array_fields_spec :=
 DECLARE _copy_array_fields
 WITH destination: val, source: val,
      v1: reptype tpair, v2: reptype tpair,
      w1: reptype tpair, w2: reptype tpair
 PRE [tptr tpair_array, tptr tpair_array]
   PROP () PARAMS (destination; source)
   SEP (data_at Ews tpair_array [v1; v2] destination;
        data_at Ers tpair_array [w1; w2] source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair_array [w2; v2] destination;
        data_at Ers tpair_array [w1; w2] source).

Definition copy_qualified_spec :=
 DECLARE _copy_qualified
 WITH destination: val, source: val, v: reptype tpair
 PRE [tptr tpair, tptr (tvolatile tpair)]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tpair destination; data_at Ers tpair v source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair v destination; data_at Ers tpair v source).

Definition Gprog : funspecs := ltac:(with_library prog
  [copy_pointer_spec; copy_local_spec; copy_nested_spec;
   copy_array_member_spec; copy_pointer_member_spec; copy_padding_spec;
   copy_partial_spec; copy_self_spec; copy_fields_spec; copy_field_self_spec;
   copy_array_fields_spec; copy_qualified_spec]).

Lemma body_copy_pointer: semax_body Vprog Gprog f_copy_pointer copy_pointer_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_local: semax_body Vprog Gprog f_copy_local copy_local_spec.
Proof. start_function. forward. forward. forward. forward. entailer!. Qed.

Lemma body_copy_nested: semax_body Vprog Gprog f_copy_nested copy_nested_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_array_member: semax_body Vprog Gprog f_copy_array_member copy_array_member_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_pointer_member: semax_body Vprog Gprog f_copy_pointer_member copy_pointer_member_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_padding: semax_body Vprog Gprog f_copy_padding copy_padding_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_partial: semax_body Vprog Gprog f_copy_partial copy_partial_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_self: semax_body Vprog Gprog f_copy_self copy_self_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_proved_alias:
  semax_body Vprog Gprog f_copy_pointer copy_proved_alias_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_fields: semax_body Vprog Gprog f_copy_fields copy_fields_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_field_self:
  semax_body Vprog Gprog f_copy_field_self copy_field_self_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_nested_uninitialized:
  semax_body Vprog Gprog f_copy_nested copy_nested_uninitialized_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_array_fields:
  semax_body Vprog Gprog f_copy_array_fields copy_array_fields_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_qualified:
  semax_body Vprog Gprog f_copy_qualified copy_qualified_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma copy_partial_overlap_rejected: forall block,
  ~ copy_compatible 8 (Vptr block (Ptrofs.repr 0))
      (Vptr block (Ptrofs.repr 4)).
Proof.
  intros block. unfold copy_compatible.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  lia.
Qed.

Goal True.
  Fail check_no_bitfields' 1%positive
    (Member_bitfield 2%positive I32 Unsigned noattr 1 false :: nil).
  exact I.
Qed.

Lemma copy_hidden_load_rejected:
  check_norm_stmt
    (Sassign
      (Ederef (Etempvar _destination (tptr tpair)) tpair)
      (Ederef
        (Efield (Ederef (Etempvar _source (tptr tpointer_member)) tpointer_member)
          _pointer (tptr tpair)) tpair)) <> DE_OK.
Proof. discriminate. Qed.

Lemma copy_different_qualifiers_normalized:
  check_norm_stmt
    (Sassign
      (Ederef (Etempvar _destination (tptr tpair)) tpair)
      (Ederef (Etempvar _source (tptr (tvolatile tpair)))
        (tvolatile tpair))) = DE_OK.
Proof. reflexivity. Qed.

Lemma copy_different_structs_rejected:
  copy_type_compatible tpair tnested = false.
Proof. reflexivity. Qed.

Definition copy_unknown_alias_spec :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, v: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at Ews tpair v source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair v destination).

Goal semax_body Vprog Gprog f_copy_pointer copy_unknown_alias_spec.
Proof. start_function. Fail forward. Abort.

Definition copy_source_candidates_spec (first_share second_share: share) :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tpair destination;
        data_at first_share tpair value source;
        data_at second_share tpair value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair value destination;
        data_at first_share tpair value source;
        data_at second_share tpair value source).

Lemma body_copy_source_unreadable_first:
  semax_body Vprog Gprog f_copy_pointer
    (copy_source_candidates_spec Share.Lsh Share.Rsh).
Proof.
  start_function.
  pose proof (writable0_readable writable0_Rsh).
  forward. entailer!.
Qed.

Lemma body_copy_source_readable_first:
  semax_body Vprog Gprog f_copy_pointer
    (copy_source_candidates_spec Share.Rsh Share.Lsh).
Proof.
  start_function.
  pose proof (writable0_readable writable0_Rsh).
  forward. entailer!.
Qed.

Lemma body_copy_source_unproved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_pointer
    (copy_source_candidates_spec unproved_share Ers).
Proof. intros. start_function. forward. entailer!. Qed.

Lemma body_copy_source_proved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_pointer
    (copy_source_candidates_spec Ers unproved_share).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_destination_candidates_spec (first_share second_share: share) :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at_ first_share tpair destination;
        data_at_ second_share tpair destination;
        data_at Ers tpair value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at_ first_share tpair destination;
        data_at second_share tpair value destination;
        data_at Ers tpair value source).

Lemma body_copy_destination_unwritable_first:
  semax_body Vprog Gprog f_copy_pointer
    (copy_destination_candidates_spec (Share.comp Ews) Ews).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_destination_unproved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_pointer
    (copy_destination_candidates_spec unproved_share Ews).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_destination_proved_first_spec (unproved_share: share) :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tpair destination;
        data_at_ unproved_share tpair destination;
        data_at Ers tpair value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair value destination;
        data_at_ unproved_share tpair destination;
        data_at Ers tpair value source).

Lemma body_copy_destination_proved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_pointer
    (copy_destination_proved_first_spec unproved_share).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_self_candidates_spec (first_share second_share: share) :=
 DECLARE _copy_self
 WITH object: val, value: reptype tpair
 PRE [tptr tpair]
   PROP () PARAMS (object)
   SEP (data_at first_share tpair value object;
        data_at second_share tpair value object)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at first_share tpair value object;
        data_at second_share tpair value object).

Lemma body_copy_self_writable_candidate:
  semax_body Vprog Gprog f_copy_self
    (copy_self_candidates_spec (Share.comp Ews) Ews).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_self_writable_first:
  semax_body Vprog Gprog f_copy_self
    (copy_self_candidates_spec Ews (Share.comp Ews)).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_self_unproved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_self
    (copy_self_candidates_spec unproved_share Ews).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_unproved_permissions_spec (destination_share source_share: share) :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at_ destination_share tpair destination;
        data_at source_share tpair value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at destination_share tpair value destination;
        data_at source_share tpair value source).

Goal forall unproved_share,
  semax_body Vprog Gprog f_copy_pointer
    (copy_unproved_permissions_spec Ews unproved_share).
Proof. intros. start_function. Fail forward. Abort.

Goal forall unproved_share,
  semax_body Vprog Gprog f_copy_pointer
    (copy_unproved_permissions_spec unproved_share Ers).
Proof. intros. start_function. Fail forward. Abort.

Definition copy_uninitialized_source_spec :=
 DECLARE _copy_pointer
 WITH destination: val, source: val
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ers tpair source;
        data_at_ Ews tpair destination)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at_ Ers tpair source;
        data_at Ews tpair (default_val tpair) destination).

Lemma body_copy_uninitialized_source:
  semax_body Vprog Gprog f_copy_pointer copy_uninitialized_source_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at_ Ers tpair source;
     data_at Ews tpair (default_val tpair) destination].
  entailer!.
Qed.

Definition f_copy_pair_attributes (destination_attributes source_attributes: attr) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := [(_destination, tptr (Tstruct _pair destination_attributes));
                (_source, tptr (Tstruct _pair source_attributes))];
  fn_vars := nil;
  fn_temps := nil;
  fn_body := Sassign
    (Ederef (Etempvar _destination (tptr (Tstruct _pair destination_attributes)))
      (Tstruct _pair destination_attributes))
    (Ederef (Etempvar _source (tptr (Tstruct _pair source_attributes)))
      (Tstruct _pair source_attributes))
|}.

Definition copy_pair_attributes_spec
    (destination_attributes source_attributes
      destination_owned_attributes source_owned_attributes: attr) :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr (Tstruct _pair destination_attributes),
      tptr (Tstruct _pair source_attributes)]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews (Tstruct _pair destination_owned_attributes) destination;
        data_at Ers (Tstruct _pair source_owned_attributes) value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews (Tstruct _pair destination_owned_attributes) value destination;
        data_at Ers (Tstruct _pair source_owned_attributes) value source).

Definition volatile_pair_attributes := attr_of_type (tvolatile tpair).
Definition aligned_pair_attributes :=
  {| attr_volatile := false; attr_alignas := Some 4%N |}.

Lemma copy_misaligned_pair_rejected: forall block,
  ~ copy_aligned tpair (Vptr block (Ptrofs.repr 2)).
Proof.
  intros block Haligned.
  unfold copy_aligned in Haligned.
  change (8 > 0 -> (4 | Ptrofs.unsigned (Ptrofs.repr 2))) in Haligned.
  specialize (Haligned ltac:(lia)).
  rewrite Ptrofs.unsigned_repr in Haligned by rep_lia.
  destruct Haligned as [multiple Haligned]. lia.
Qed.

Lemma body_copy_alignas_ownership:
  semax_body Vprog Gprog f_copy_pointer
    (copy_pair_attributes_spec noattr noattr
      aligned_pair_attributes aligned_pair_attributes).
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at Ews (Tstruct _pair aligned_pair_attributes) value destination;
     data_at Ers (Tstruct _pair aligned_pair_attributes) value source].
  entailer!.
Qed.

Lemma body_copy_qualified_source_ownership:
  semax_body Vprog Gprog f_copy_qualified
    (copy_pair_attributes_spec noattr volatile_pair_attributes
      noattr volatile_pair_attributes).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_qualified_destination_ownership:
  semax_body Vprog Gprog f_copy_pointer
    (copy_pair_attributes_spec noattr noattr volatile_pair_attributes noattr).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_both_qualified_ownership:
  semax_body Vprog Gprog f_copy_pointer
    (copy_pair_attributes_spec noattr noattr
      volatile_pair_attributes volatile_pair_attributes).
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at Ews (Tstruct _pair volatile_pair_attributes) value destination;
     data_at Ers (Tstruct _pair volatile_pair_attributes) value source].
  entailer!.
Qed.

Lemma body_copy_qualified_destination_expression:
  semax_body Vprog Gprog (f_copy_pair_attributes volatile_pair_attributes noattr)
    (copy_pair_attributes_spec volatile_pair_attributes noattr
      volatile_pair_attributes noattr).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_both_qualified_expressions:
  semax_body Vprog Gprog
    (f_copy_pair_attributes volatile_pair_attributes volatile_pair_attributes)
    (copy_pair_attributes_spec volatile_pair_attributes volatile_pair_attributes
      volatile_pair_attributes volatile_pair_attributes).
Proof. start_function. forward. entailer!. Qed.

Definition copy_qualified_empty_fields_spec
    (destination_attributes source_attributes: attr) :=
 DECLARE _copy_pointer
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tpair, tptr tpair]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews (Tstruct _pair destination_attributes) [] destination;
        field_at Ers (Tstruct _pair source_attributes) [] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews (Tstruct _pair destination_attributes) [] value destination;
        field_at Ers (Tstruct _pair source_attributes) [] value source).

Lemma body_copy_qualified_empty_source_field:
  semax_body Vprog Gprog f_copy_pointer
    (copy_qualified_empty_fields_spec noattr volatile_pair_attributes).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_qualified_empty_destination_field:
  semax_body Vprog Gprog f_copy_pointer
    (copy_qualified_empty_fields_spec volatile_pair_attributes noattr).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_both_qualified_empty_fields:
  semax_body Vprog Gprog f_copy_pointer
    (copy_qualified_empty_fields_spec volatile_pair_attributes volatile_pair_attributes).
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [field_at Ews (Tstruct _pair volatile_pair_attributes) [] value destination;
     field_at Ers (Tstruct _pair volatile_pair_attributes) [] value source].
  entailer!.
Qed.

Lemma body_copy_alignas_empty_fields:
  semax_body Vprog Gprog f_copy_pointer
    (copy_qualified_empty_fields_spec aligned_pair_attributes aligned_pair_attributes).
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_qualified_root_spec
    (destination_attributes source_attributes: attr) :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews (Tstruct _nested destination_attributes)
          [StructField _first] destination;
        field_at Ers (Tstruct _nested source_attributes)
          [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews (Tstruct _nested destination_attributes)
          [StructField _first] value destination;
        field_at Ers (Tstruct _nested source_attributes)
          [StructField _second] value source).

Lemma body_copy_native_qualified_source_root:
  semax_body Vprog Gprog f_copy_nested
    (copy_native_qualified_root_spec noattr volatile_pair_attributes).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_native_qualified_destination_root:
  semax_body Vprog Gprog f_copy_nested
    (copy_native_qualified_root_spec volatile_pair_attributes noattr).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_native_both_qualified_roots:
  semax_body Vprog Gprog f_copy_nested
    (copy_native_qualified_root_spec volatile_pair_attributes volatile_pair_attributes).
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_fields_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, old: reptype tpair,
      value: reptype tpair, sibling: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at Ews tnested [StructField _second] sibling destination;
        field_at Ers tnested [StructField _second] value source;
        field_at Ews tnested [StructField _first] old destination)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _second] sibling destination;
        field_at Ers tnested [StructField _second] value source;
        field_at Ews tnested [StructField _first] value destination).

Lemma body_copy_native_fields:
  semax_body Vprog Gprog f_copy_nested copy_native_fields_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [field_at Ews tnested [StructField _second] sibling destination;
     field_at Ers tnested [StructField _second] value source;
     field_at Ews tnested [StructField _first] value destination].
  entailer!.
Qed.

Definition copy_native_uninitialized_field_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews tnested [StructField _first] destination;
        field_at Ers tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _first] value destination;
        field_at Ers tnested [StructField _second] value source).

Lemma body_copy_native_uninitialized_field:
  semax_body Vprog Gprog f_copy_nested copy_native_uninitialized_field_spec.
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_uninitialized_source_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews tnested [StructField _first] destination;
        field_at_ Ers tnested [StructField _second] source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _first] (default_val tpair) destination;
        field_at_ Ers tnested [StructField _second] source).

Lemma body_copy_native_uninitialized_source:
  semax_body Vprog Gprog f_copy_nested copy_native_uninitialized_source_spec.
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_source_candidates_spec (first_share second_share: share) :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews tnested [StructField _first] destination;
        field_at first_share tnested [StructField _second] value source;
        field_at second_share tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _first] value destination;
        field_at first_share tnested [StructField _second] value source;
        field_at second_share tnested [StructField _second] value source).

Lemma body_copy_native_source_unreadable_first:
  semax_body Vprog Gprog f_copy_nested
    (copy_native_source_candidates_spec Share.Lsh Share.Rsh).
Proof.
  start_function. pose proof (writable0_readable writable0_Rsh).
  forward. entailer!.
Qed.

Lemma body_copy_native_source_readable_first:
  semax_body Vprog Gprog f_copy_nested
    (copy_native_source_candidates_spec Share.Rsh Share.Lsh).
Proof.
  start_function. pose proof (writable0_readable writable0_Rsh).
  forward. entailer!.
Qed.

Lemma body_copy_native_source_unproved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_nested
    (copy_native_source_candidates_spec unproved_share Ers).
Proof. intros. start_function. forward. entailer!. Qed.

Lemma body_copy_native_source_proved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_nested
    (copy_native_source_candidates_spec Ers unproved_share).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_native_destination_candidates_spec
    (first_share second_share: share) :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ first_share tnested [StructField _first] destination;
        field_at_ second_share tnested [StructField _first] destination;
        field_at Ers tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at_ first_share tnested [StructField _first] destination;
        field_at second_share tnested [StructField _first] value destination;
        field_at Ers tnested [StructField _second] value source).

Lemma body_copy_native_destination_unwritable_first:
  semax_body Vprog Gprog f_copy_nested
    (copy_native_destination_candidates_spec (Share.comp Ews) Ews).
Proof. start_function. forward. entailer!. Qed.

Lemma body_copy_native_destination_unproved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_nested
    (copy_native_destination_candidates_spec unproved_share Ews).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_native_destination_proved_first_spec (unproved_share: share) :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews tnested [StructField _first] destination;
        field_at_ unproved_share tnested [StructField _first] destination;
        field_at Ers tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _first] value destination;
        field_at_ unproved_share tnested [StructField _first] destination;
        field_at Ers tnested [StructField _second] value source).

Lemma body_copy_native_destination_proved_first: forall unproved_share,
  semax_body Vprog Gprog f_copy_nested
    (copy_native_destination_proved_first_spec unproved_share).
Proof. intros. start_function. forward. entailer!. Qed.

Definition copy_native_unproved_permissions_spec
    (destination_share source_share: share) :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ destination_share tnested [StructField _first] destination;
        field_at source_share tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at destination_share tnested [StructField _first] value destination;
        field_at source_share tnested [StructField _second] value source).

Goal forall unproved_share,
  semax_body Vprog Gprog f_copy_nested
    (copy_native_unproved_permissions_spec Ews unproved_share).
Proof. intros. start_function. Fail forward. Abort.

Goal forall unproved_share,
  semax_body Vprog Gprog f_copy_nested
    (copy_native_unproved_permissions_spec unproved_share Ers).
Proof. intros. start_function. Fail forward. Abort.

Definition copy_native_field_from_whole_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, first: reptype tpair, second: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (data_at Ers tnested (first, second) source;
        field_at_ Ews tnested [StructField _first] destination)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ers tnested (first, second) source;
        field_at Ews tnested [StructField _first] second destination).

Lemma body_copy_native_field_from_whole:
  semax_body Vprog Gprog f_copy_nested copy_native_field_from_whole_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at Ers tnested (first, second) source;
     field_at Ews tnested [StructField _first] second destination].
  entailer!.
Qed.

Definition copy_native_field_from_uninitialized_whole_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ers tnested source;
        field_at_ Ews tnested [StructField _first] destination)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at_ Ers tnested source;
        field_at Ews tnested [StructField _first] (default_val tpair) destination).

Lemma body_copy_native_field_from_uninitialized_whole:
  semax_body Vprog Gprog f_copy_nested copy_native_field_from_uninitialized_whole_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at_ Ers tnested source;
     field_at Ews tnested [StructField _first] (default_val tpair) destination].
  entailer!.
Qed.

Definition copy_native_whole_from_field_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tnested destination;
        field_at Ers tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tnested (value, default_val tpair) destination;
        field_at Ers tnested [StructField _second] value source).

Lemma body_copy_native_whole_from_field:
  semax_body Vprog Gprog f_copy_nested copy_native_whole_from_field_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at Ews tnested (value, default_val tpair) destination;
     field_at Ers tnested [StructField _second] value source].
  entailer!.
Qed.

Definition copy_native_field_from_leaf_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews tnested [StructField _first] destination;
        data_at Ers tpair value
          (field_address tnested [StructField _second] source))
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _first] value destination;
        data_at Ers tpair value
          (field_address tnested [StructField _second] source)).

Lemma body_copy_native_field_from_leaf:
  semax_body Vprog Gprog f_copy_nested copy_native_field_from_leaf_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [field_at Ews tnested [StructField _first] value destination;
     data_at Ers tpair value (field_address tnested [StructField _second] source)].
  entailer!.
Qed.

Definition copy_native_leaf_from_field_spec :=
 DECLARE _copy_nested
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tnested, tptr tnested]
   PROP () PARAMS (destination; source)
   SEP (data_at_ Ews tpair (field_address tnested [StructField _first] destination);
        field_at Ers tnested [StructField _second] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair value
          (field_address tnested [StructField _first] destination);
        field_at Ers tnested [StructField _second] value source).

Lemma body_copy_native_leaf_from_field:
  semax_body Vprog Gprog f_copy_nested copy_native_leaf_from_field_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at Ews tpair value (field_address tnested [StructField _first] destination);
     field_at Ers tnested [StructField _second] value source].
  entailer!.
Qed.

Definition copy_native_siblings_spec :=
 DECLARE _copy_fields
 WITH object: val, first: reptype tpair, second: reptype tpair
 PRE [tptr tnested]
   PROP () PARAMS (object)
   SEP (field_at Ers tnested [StructField _second] second object;
        field_at Ews tnested [StructField _first] first object)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ers tnested [StructField _second] second object;
        field_at Ews tnested [StructField _first] second object).

Lemma body_copy_native_siblings:
  semax_body Vprog Gprog f_copy_fields copy_native_siblings_spec.
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_field_self_spec :=
 DECLARE _copy_field_self
 WITH object: val, value: reptype tpair
 PRE [tptr tnested]
   PROP () PARAMS (object)
   SEP (field_at Ews tnested [StructField _first] value object)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tnested [StructField _first] value object).

Lemma body_copy_native_field_self:
  semax_body Vprog Gprog f_copy_field_self copy_native_field_self_spec.
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_leaf_self_spec :=
 DECLARE _copy_field_self
 WITH object: val, value: reptype tpair
 PRE [tptr tnested]
   PROP () PARAMS (object)
   SEP (data_at Ews tpair value (field_address tnested [StructField _first] object))
 POST [tvoid]
   PROP () RETURN ()
   SEP (data_at Ews tpair value (field_address tnested [StructField _first] object)).

Lemma body_copy_native_leaf_self:
  semax_body Vprog Gprog f_copy_field_self copy_native_leaf_self_spec.
Proof.
  start_function. forward.
  check_struct_copy_spatial_order
    [data_at Ews tpair value (field_address tnested [StructField _first] object)].
  entailer!.
Qed.

Definition copy_owned_array_fields_spec :=
 DECLARE _copy_array_fields
 WITH destination: val, source: val, first: reptype tpair, second: reptype tpair,
      source_first: reptype tpair, source_second: reptype tpair
 PRE [tptr tpair_array, tptr tpair_array]
   PROP () PARAMS (destination; source)
   SEP (field_at Ers tpair_array [StructField _values]
          [source_first; source_second] source;
        field_at Ews tpair_array [StructField _values] [first; second] destination)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ers tpair_array [StructField _values]
          [source_first; source_second] source;
        field_at Ews tpair_array [StructField _values]
          [source_second; second] destination).

Lemma body_copy_owned_array_fields:
  semax_body Vprog Gprog f_copy_array_fields copy_owned_array_fields_spec.
Proof. start_function. forward. entailer!. Qed.

Definition copy_native_array_elements_spec :=
 DECLARE _copy_array_fields
 WITH destination: val, source: val, value: reptype tpair
 PRE [tptr tpair_array, tptr tpair_array]
   PROP () PARAMS (destination; source)
   SEP (field_at_ Ews tpair_array [ArraySubsc 0; StructField _values] destination;
        field_at Ers tpair_array [ArraySubsc 1; StructField _values] value source)
 POST [tvoid]
   PROP () RETURN ()
   SEP (field_at Ews tpair_array [ArraySubsc 0; StructField _values] value destination;
        field_at Ers tpair_array [ArraySubsc 1; StructField _values] value source).

Lemma body_copy_native_array_elements:
  semax_body Vprog Gprog f_copy_array_fields copy_native_array_elements_spec.
Proof. start_function. forward. entailer!. Qed.
