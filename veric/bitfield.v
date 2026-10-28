(** * Bitfield descriptors and storage carriers. *)

Require Export VST.veric.expr.
Require Import VST.veric.base VST.veric.compspecs compcert.cfrontend.Ctypes.

Import compcert.lib.Maps.

(** [bitfield_field] relates a struct or union member to its byte
    offset and CompCert descriptor. Other root types are excluded.
    A [Bits] descriptor records the declared integer size, signedness,
    bit position and width. This predicate checks layout lookup only,
    the store rules separately require valid bounds and ownership. *)
Definition bitfield_field (ce: composite_env) (root_type: type) (field: ident)
    (delta: Z) (descriptor: bitfield): Prop :=
  match root_type with
  | Tstruct id _ => exists co,
      ce ! id = Some co /\
      field_offset ce field (co_members co) = Errors.OK (delta, descriptor)
  | Tunion id _ => exists co,
      ce ! id = Some co /\
      union_field_offset ce field (co_members co) = Errors.OK (delta, descriptor)
  | _ => False
  end.

(** A root with a field descriptor has aggregate access mode. *)
Lemma bitfield_field_by_copy: forall ce t field delta descriptor,
  bitfield_field ce t field delta descriptor -> access_mode t = By_copy.
Proof. intros ce t. destruct t; simpl; intros; try contradiction; reflexivity. Qed.

(** Extending a consistent composite environment preserves the member
    descriptor and byte offset. *)
Lemma bitfield_field_cenv_sub: forall {CS: compspecs} ce t field delta descriptor,
  cenv_sub cenv_cs ce ->
  bitfield_field cenv_cs t field delta descriptor ->
  bitfield_field ce t field delta descriptor.
Proof.
  intros CS ce t field delta descriptor SUB FIELD.
  assert (EXTENDS: forall id co, cenv_cs ! id = Some co -> ce ! id = Some co).
  { intros id co LOOKUP. specialize (SUB id). hnf in SUB.
    rewrite LOOKUP in SUB. exact SUB. }
  destruct t; simpl in FIELD |- *; try contradiction.
  - destruct FIELD as [co [LOOKUP OFFSET]]. exists co. split.
    + apply EXTENDS; auto.
    + rewrite (Ctypes.field_offset_stable cenv_cs ce); auto.
      eapply co_consistent_complete. apply (cenv_consistent i); auto.
  - destruct FIELD as [co [LOOKUP OFFSET]]. exists co. split.
    + apply EXTENDS; auto.
    + rewrite (Ctypes.union_field_offset_stable cenv_cs ce); auto.
      eapply co_consistent_complete. apply (cenv_consistent i); auto.
Qed.

(** [bitfield_carrier_type] represents the whole storage unit as a
    nonvolatile unsigned integer. Boolean fields use an unsigned byte,
    not a boolean value. Ownership of this type covers the carrier,
    including the bits outside the selected field. *)
Definition bitfield_carrier_type (sz: intsize): type :=
  Tint (match sz with IBool => I8 | _ => sz end) Unsigned noattr.

(** Carrier loads and stores use the CompCert carrier memory chunk. *)
Lemma bitfield_carrier_access_mode: forall sz,
  access_mode (bitfield_carrier_type sz) = By_value (Cop.chunk_for_carrier sz).
Proof. destruct sz; reflexivity. Qed.

(** The carrier representation always uses ordinary memory access. *)
Lemma bitfield_carrier_nonvolatile: forall sz,
  type_is_volatile (bitfield_carrier_type sz) = false.
Proof. destruct sz; reflexivity. Qed.

(** Loading the carrier chunk normalizes an integer to a value accepted
    by the unsigned carrier type. *)
Lemma bitfield_carrier_load_result_type: forall sz n,
  tc_val (bitfield_carrier_type sz) (Val.load_result (Cop.chunk_for_carrier sz) (Vint n)).
Proof.
  intros sz n. destruct sz; simpl; auto.
  - pose proof (Int.zero_ext_range 8 n ltac:(compute; split; congruence)) as RANGE.
    change (Int.unsigned (Int.zero_ext 8 n) <= 255).
    change (0 <= Int.unsigned (Int.zero_ext 8 n) < 256) in RANGE. lia.
  - pose proof (Int.zero_ext_range 16 n ltac:(compute; split; congruence)) as RANGE.
    change (Int.unsigned (Int.zero_ext 16 n) <= 65535).
    change (0 <= Int.unsigned (Int.zero_ext 16 n) < 65536) in RANGE. lia.
  - pose proof (Int.zero_ext_range 8 n ltac:(compute; split; congruence)) as RANGE.
    change (Int.unsigned (Int.zero_ext 8 n) <= 255).
    change (0 <= Int.unsigned (Int.zero_ext 8 n) < 256) in RANGE. lia.
Qed.
