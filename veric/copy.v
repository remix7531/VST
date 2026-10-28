Require Export VST.veric.expr.
Require Import VST.veric.base VST.veric.compspecs compcert.cfrontend.Ctypes.
Require Import VST.veric.change_compspecs.

Import compcert.lib.Maps.

(** Clight aggregate assignment requires the same struct or union tag
    on both sides. Attributes do not change that identity. This test
    deliberately excludes arrays and scalar casts. Completeness, size,
    alignment and ownership remain separate premises of the copy rules. *)
Definition copy_type_compatible (destination source: type): bool :=
  match destination, source with
  | Tstruct destination_id _, Tstruct source_id _
  | Tunion destination_id _, Tunion source_id _ =>
      if ident_eq destination_id source_id then true else false
  | _, _ => false
  end.

Lemma copy_type_compatible_source: forall destination source,
  copy_type_compatible destination source = true ->
  access_mode source = By_copy.
Proof.
  intros destination source Hcompatible.
  destruct destination; destruct source; simpl in Hcompatible;
    try discriminate; reflexivity.
Qed.

Lemma copy_type_compatible_refl: forall t,
  access_mode t = By_copy -> copy_type_compatible t t = true.
Proof.
  intros t Hcopy.
  destruct t; simpl in Hcopy; try discriminate; simpl.
  - destruct i, s; discriminate.
  - destruct f; discriminate.
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_true by reflexivity. reflexivity.
Qed.

(** Block-copy alignment is required only for positive-size objects.
    The pointer must still be a [Vptr] when the size is zero. This is
    Clight block-copy alignment, which can differ from scalar chunk
    alignment and is not a claim that any bytes are owned at [p]. *)
Definition copy_aligned {CS: compspecs} (t: type) (p: val) : Prop :=
  match p with
  | Vptr _ ofs =>
      (sizeof t > 0)%Z -> Z.divide (Ctypes.alignof_blockcopy cenv_cs t) (Ptrofs.unsigned ofs)
  | _ => False
  end.

Lemma cenv_sub_alignof_blockcopy {ce ce'} (SUB: cenv_sub ce' ce):
  forall t, complete_type ce' t = true ->
    alignof_blockcopy ce t = alignof_blockcopy ce' t.
Proof.
  induction t; simpl; intros; auto.
  all: specialize (SUB i); destruct (ce' ! i); try congruence;
    rewrite SUB; auto.
Qed.
