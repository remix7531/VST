(** * Deriving aggregate copy alignment from compatible scalar leaves. *)
Require Import VST.floyd.base2.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.veric.align_mem.
Require Import VST.veric.copy.

Local Open Scope Z_scope.

(** Recover base copy alignment from an aligned scalar at a known offset.
    The block copy alignment must divide both its chunk alignment and the
    offset, so scalar alignment alone is insufficient. *)
Lemma copy_aligned_from_scalar_offset:
  forall {cs: compspecs} t leaf ch b ofs offset,
  access_mode leaf = By_value ch ->
  align_compatible_rec cenv_cs leaf (Ptrofs.unsigned ofs + offset) ->
  (alignof_blockcopy cenv_cs t | align_chunk ch) ->
  (alignof_blockcopy cenv_cs t | offset) ->
  copy_aligned t (Vptr b ofs).
Proof.
  intros cs t leaf ch b ofs offset MODE ALIGN CHUNK OFFSET.
  unfold copy_aligned. intros SIZE.
  pose proof (align_compatible_rec_by_value_inv cenv_cs leaf ch
    (Ptrofs.unsigned ofs + offset) MODE ALIGN) as SUM.
  destruct CHUNK as [multiple CHUNK]. destruct SUM as [count SUM].
  destruct OFFSET as [other OFFSET].
  exists (count * multiple - other). nia.
Qed.

(** Prove copy alignment through a compatible scalar field. Require a
    [By_value] leaf and divisibility of its chunk alignment and field
    offset by the enclosing block copy alignment. *)
Lemma field_compatible_copy_aligned:
  forall {cs: compspecs} t gfs p ch,
  field_compatible t gfs p ->
  access_mode (nested_field_type t gfs) = By_value ch ->
  (alignof_blockcopy cenv_cs t | align_chunk ch) ->
  (alignof_blockcopy cenv_cs t | nested_field_offset t gfs) ->
  copy_aligned t p.
Proof.
  intros cs t gfs p ch COMPATIBLE MODE CHUNK OFFSET.
  destruct COMPATIBLE as [PTR [COMPLETE [SIZE [ALIGN LEGAL]]]].
  destruct p as [| | | | | b ofs]; try contradiction PTR.
  pose proof (align_compatible_nested_field t gfs (Vptr b ofs)
    LEGAL SIZE ALIGN COMPLETE) as LEAFALIGN.
  change (align_compatible_rec cenv_cs (nested_field_type t gfs)
    (Ptrofs.unsigned
      (Ptrofs.add ofs (Ptrofs.repr (nested_field_offset t gfs)))))
    in LEAFALIGN.
  pose proof (nested_field_offset_in_range t gfs LEGAL COMPLETE) as RANGE.
  pose proof (sizeof_pos (nested_field_type t gfs)) as LEAFSIZE.
  pose proof (Ptrofs.unsigned_range ofs) as POINTER.
  change (Ptrofs.unsigned ofs + sizeof t < Ptrofs.modulus) in SIZE.
  rewrite Ptrofs.add_unsigned in LEAFALIGN.
  rewrite (Ptrofs.unsigned_repr (nested_field_offset t gfs)) in LEAFALIGN
    by (unfold Ptrofs.max_unsigned; lia).
  rewrite Ptrofs.unsigned_repr in LEAFALIGN
    by (unfold Ptrofs.max_unsigned; lia).
  eapply copy_aligned_from_scalar_offset; eauto.
Qed.
