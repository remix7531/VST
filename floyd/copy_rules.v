(** * Typed aggregate assignment rules.

    These rules transfer the full object representation through the byte
    copy rules, then recover typed ownership. Padding bytes remain part
    of the copied representation. *)
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_memvals.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.entailer.
Require Import VST.veric.memvals_at.
Require Import VST.veric.copy_lemmas.
Require Import VST.veric.align_mem.

Import LiftNotation.
Local Open Scope logic.

Section typed_copy.
Context {cs: compspecs} {Espec: OracleKind}.

Lemma copy_nested_field_rec: forall destination source path,
  copy_type_compatible destination source = true ->
  path <> nil ->
  nested_field_rec destination path = nested_field_rec source path.
Proof.
  intros destination source path Hcompatible.
  induction path as [|field path IH]; [contradiction |].
  intros Hpath.
  destruct path as [|next path].
  - destruct destination; destruct source; simpl in Hcompatible; try discriminate.
    all: destruct (ident_eq i i0); try discriminate; subst i0;
      destruct field; reflexivity.
  - assert (Hstep: forall tail,
      nested_field_rec destination tail = nested_field_rec source tail ->
      nested_field_rec destination (field :: tail) = nested_field_rec source (field :: tail)).
    { intros tail Htail. simpl nested_field_rec. rewrite Htail. reflexivity. }
    apply Hstep, IH. discriminate.
Qed.

Lemma copy_nested_field_type: forall destination source path,
  copy_type_compatible destination source = true ->
  path <> nil ->
  nested_field_type destination path = nested_field_type source path.
Proof.
  intros destination source path Hcompatible Hpath.
  unfold nested_field_type.
  rewrite (copy_nested_field_rec _ _ _ Hcompatible Hpath).
  reflexivity.
Qed.

Lemma copy_nested_field_type_compatible: forall destination source path,
  copy_type_compatible destination source = true ->
  access_mode (nested_field_type destination path) = By_copy ->
  copy_type_compatible (nested_field_type destination path)
    (nested_field_type source path) = true.
Proof.
  intros destination source path Hcompatible Hmode.
  destruct path as [|field path]; [exact Hcompatible |].
  rewrite (copy_nested_field_type _ _ (field :: path) Hcompatible ltac:(discriminate)).
  apply copy_type_compatible_refl.
  rewrite <- (copy_nested_field_type _ _ (field :: path) Hcompatible ltac:(discriminate)).
  exact Hmode.
Qed.

Lemma copy_nested_field_offset: forall destination source path,
  copy_type_compatible destination source = true ->
  nested_field_offset destination path = nested_field_offset source path.
Proof.
  intros destination source path Hcompatible.
  destruct path as [|field path]; [reflexivity |].
  unfold nested_field_offset.
  rewrite (copy_nested_field_rec _ _ (field :: path) Hcompatible ltac:(discriminate)).
  reflexivity.
Qed.

Lemma copy_legal_nested_field: forall destination source path,
  copy_type_compatible destination source = true ->
  legal_nested_field destination path = legal_nested_field source path.
Proof.
  intros destination source path Hcompatible.
  induction path as [|field path IH]; [reflexivity |].
  simpl legal_nested_field. rewrite IH.
  destruct path as [|next path].
  - destruct destination; destruct source; simpl in Hcompatible; try discriminate.
    all: destruct (ident_eq i i0); try discriminate; subst i0;
      destruct field; reflexivity.
  - rewrite (copy_nested_field_rec _ _ (next :: path) Hcompatible ltac:(discriminate)).
    reflexivity.
Qed.

Lemma copy_align_compatible: forall destination source p,
  copy_type_compatible destination source = true ->
  align_compatible destination p = align_compatible source p.
Proof.
  intros destination source p Hcompatible.
  unfold align_compatible.
  destruct p as [|integer|long_integer|float_value|single_value|block offset]; try reflexivity.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    apply prop_ext; split; intros H; inversion H; subst;
    try discriminate;
    first [eapply align_compatible_rec_Tstruct | eapply align_compatible_rec_Tunion]; eauto.
Qed.

Lemma copy_field_compatible: forall destination source path p,
  copy_type_compatible destination source = true ->
  field_compatible destination path p = field_compatible source path p.
Proof.
  intros destination source path p Hcompatible.
  unfold field_compatible.
  rewrite (copy_legal_nested_field _ _ _ Hcompatible),
    (copy_align_compatible _ _ _ Hcompatible).
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0; reflexivity.
Qed.

Lemma copy_field_address: forall destination source path p,
  copy_type_compatible destination source = true ->
  field_compatible destination path p ->
  field_compatible source path p ->
  field_address destination path p = field_address source path p.
Proof.
  intros destination source path p Hcompatible Hdestination Hsource.
  unfold field_address.
  rewrite !if_true by assumption.
  rewrite (copy_nested_field_offset _ _ _ Hcompatible).
  reflexivity.
Qed.

Lemma copy_reptype_eq: forall destination source,
  copy_type_compatible destination source = true ->
  reptype source = reptype destination.
Proof.
  intros destination source Hcompatible.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    rewrite !reptype_eq; reflexivity.
Defined.

Definition copy_reptype destination source
  (Hcompatible: copy_type_compatible destination source = true)
  (v: reptype source): reptype destination :=
  eq_rect _ (fun T: Type => T) v _ (copy_reptype_eq destination source Hcompatible).

Lemma copy_reptype_JMeq: forall destination source Hcompatible v,
  JMeq (copy_reptype destination source Hcompatible v) v.
Proof.
  intros destination source Hcompatible v.
  unfold copy_reptype.
  apply (@eq_rect_JMeq Type (reptype source) (reptype destination)
    (fun T: Type => T) v (copy_reptype_eq destination source Hcompatible)).
Qed.

Lemma copy_reptype_refl: forall t Hcompatible (v: reptype t),
  copy_reptype t t Hcompatible v = v.
Proof.
  intros. apply JMeq_eq, copy_reptype_JMeq.
Qed.

Lemma copy_reptype_struct: forall id destination_attr source_attr Hcompatible
  (v: reptype (Tstruct id source_attr)),
  copy_reptype (Tstruct id destination_attr) (Tstruct id source_attr) Hcompatible v =
  @fold_reptype cs (Tstruct id destination_attr) (unfold_reptype v).
Proof.
  intros. apply JMeq_eq.
  eapply JMeq_trans; [apply copy_reptype_JMeq |].
  apply JMeq_sym.
  eapply JMeq_trans.
  - exact (@fold_reptype_JMeq cs (Tstruct id destination_attr) (unfold_reptype v)).
  - exact (@unfold_reptype_JMeq cs (Tstruct id source_attr) v).
Qed.

Lemma copy_reptype_union: forall id destination_attr source_attr Hcompatible
  (v: reptype (Tunion id source_attr)),
  copy_reptype (Tunion id destination_attr) (Tunion id source_attr) Hcompatible v =
  @fold_reptype cs (Tunion id destination_attr) (unfold_reptype v).
Proof.
  intros. apply JMeq_eq.
  eapply JMeq_trans; [apply copy_reptype_JMeq |].
  apply JMeq_sym.
  eapply JMeq_trans.
  - exact (@fold_reptype_JMeq cs (Tunion id destination_attr) (unfold_reptype v)).
  - exact (@unfold_reptype_JMeq cs (Tunion id source_attr) v).
Qed.

Lemma copy_unfold_reptype_struct: forall id destination_attr source_attr
  (destination_value: reptype (Tstruct id destination_attr))
  (source_value: reptype (Tstruct id source_attr)),
  JMeq destination_value source_value ->
  unfold_reptype destination_value = unfold_reptype source_value.
Proof.
  intros id destination_attr source_attr destination_value source_value Hvalue.
  apply JMeq_eq.
  eapply JMeq_trans.
  - exact (@unfold_reptype_JMeq cs (Tstruct id destination_attr) destination_value).
  - eapply JMeq_trans; [exact Hvalue |].
    apply JMeq_sym.
    exact (@unfold_reptype_JMeq cs (Tstruct id source_attr) source_value).
Qed.

Lemma copy_unfold_reptype_union: forall id destination_attr source_attr
  (destination_value: reptype (Tunion id destination_attr))
  (source_value: reptype (Tunion id source_attr)),
  JMeq destination_value source_value ->
  unfold_reptype destination_value = unfold_reptype source_value.
Proof.
  intros id destination_attr source_attr destination_value source_value Hvalue.
  apply JMeq_eq.
  eapply JMeq_trans.
  - exact (@unfold_reptype_JMeq cs (Tunion id destination_attr) destination_value).
  - eapply JMeq_trans; [exact Hvalue |].
    apply JMeq_sym.
    exact (@unfold_reptype_JMeq cs (Tunion id source_attr) source_value).
Qed.

Lemma copy_data_at_memvals: forall destination source
  (destination_value: reptype destination) (source_value: reptype source) bytes,
  copy_type_compatible destination source = true ->
  JMeq destination_value source_value ->
  data_at_memvals destination destination_value bytes =
  data_at_memvals source source_value bytes.
Proof.
  intros destination source destination_value source_value bytes Hcompatible Hvalue.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    unfold data_at_memvals;
    rewrite (value_fits_eq _ destination_value), (value_fits_eq _ source_value),
      (value_memvals_rec_eq _ destination_value bytes),
      (value_memvals_rec_eq _ source_value bytes);
    first [rewrite (copy_unfold_reptype_struct _ _ _ _ _ Hvalue)
          |rewrite (copy_unfold_reptype_union _ _ _ _ _ Hvalue)];
    reflexivity.
Qed.

(** Ownership conversion preserves the value and the receiving type's
    compatibility facts. Copy alignment remains a separate obligation. *)
Lemma copy_data_at: forall sh destination source
  (destination_value: reptype destination) (source_value: reptype source) p,
  copy_type_compatible destination source = true ->
  JMeq destination_value source_value ->
  field_compatible destination nil p ->
  data_at sh source source_value p |-- data_at sh destination destination_value p.
Proof.
  intros sh destination source destination_value source_value p Hcompatible Hvalue Hfield.
  unfold data_at, field_at. simpl nested_field_type. simpl nested_field_offset.
  unfold at_offset.
  apply andp_right; [apply prop_right; exact Hfield |].
  apply andp_left2.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    rewrite (data_at_rec_eq _ _ destination_value), (data_at_rec_eq _ _ source_value);
    first [rewrite (copy_unfold_reptype_struct _ _ _ _ _ Hvalue)
          |rewrite (copy_unfold_reptype_union _ _ _ _ _ Hvalue)];
    apply derives_refl.
Qed.

Lemma copy_default_val_JMeq: forall destination source,
  copy_type_compatible destination source = true ->
  JMeq (default_val destination) (default_val source).
Proof.
  intros destination source Hcompatible.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    rewrite !default_val_eq;
    eapply JMeq_trans; [apply fold_reptype_JMeq |];
    apply JMeq_sym;
    first [apply (@fold_reptype_JMeq cs (Tstruct i a0))
          |apply (@fold_reptype_JMeq cs (Tunion i a0))].
Qed.

Lemma copy_data_at_: forall sh destination source p,
  copy_type_compatible destination source = true ->
  field_compatible destination nil p ->
  data_at_ sh source p |-- data_at_ sh destination p.
Proof.
  intros sh destination source p Hcompatible Hfield.
  rewrite !data_at__eq.
  apply copy_data_at; auto using copy_default_val_JMeq.
Qed.

(** Copy a complete compatible [By_copy] object into writable ownership
    from readable source ownership. Separation supplies disjoint regions,
    both addresses must satisfy [copy_aligned], and [P] is preserved.
    The proof exposes byte witnesses, applies the copy rule, then rebuilds
    both typed predicates using the source representation witness. *)
Lemma semax_data_at_copy:
  forall Delta e1 e2 sh1 sh2 (v: reptype (typeof e1)) P,
  copy_type_compatible (typeof e1) (typeof e2) = true -> access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  semax Delta
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
      ((`(data_at_ sh1 (typeof e1)) (eval_lvalue e1) *
        `(data_at sh2 (typeof e1) v) (eval_lvalue e2)) * P)))
    (Sassign e1 e2)
    (normal_ret_assert
      ((`(data_at sh1 (typeof e1) v) (eval_lvalue e1) *
        `(data_at sh2 (typeof e1) v) (eval_lvalue e2)) * P)).
Proof.
  intros Delta e1 e2 sh1 sh2 v P Htype Hmode Hcomplete Hwrite Hread.
  (* ===== Expose representations and retain compatibility ===== *)

  eapply semax_pre with
    (|> (EX old: list memval, EX bytes: list memval,
      !! (Zlength old = sizeof (typeof e1) /\
          data_at_memvals (typeof e1) v bytes) &&
      (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
        local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
        local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
        ((`(memvals_at_ptr sh1 old) (eval_lvalue e1) *
          `(memvals_at_ptr sh2 bytes) (eval_lvalue e2)) *
          (local (`(field_compatible (typeof e1) nil) (eval_lvalue e1)) &&
           local (`(field_compatible (typeof e1) nil) (eval_lvalue e2)) && P))))).
  { intro rho.
    cbn.
    apply andp_left2.
    apply later_derives.
    unfold local, lift1.
    unfold_lift.
    cbn.
    rewrite data_at__memvals_eq by auto using writable_readable.
    rewrite data_at_memvals_eq by auto.
    normalize.
    Exists x bytes.
    entailer!. }
  rewrite (later_exp' _ nil).
  apply semax_extract_exists.
  intro old.
  rewrite (later_exp' _ nil).
  apply semax_extract_exists.
  intro bytes.
  rewrite later_andp.
  apply semax_extract_later_prop.
  intros [Hold Hbytes].

  (* ===== Recover typed ownership after copying bytes ===== *)

  eapply semax_post' with
    (R' :=
      (`(memvals_at_ptr sh1 bytes) (eval_lvalue e1) *
       `(memvals_at_ptr sh2 bytes) (eval_lvalue e2)) *
      (local (`(field_compatible (typeof e1) nil) (eval_lvalue e1)) &&
       local (`(field_compatible (typeof e1) nil) (eval_lvalue e2)) && P)).
  - (* The same representation witnesses both resulting typed values. *)
    intro rho.
    unfold local, lift1.
    unfold_lift.
    cbn.
    rewrite !data_at_memvals_eq by auto using writable_readable.
    normalize.
    Exists bytes bytes.
    entailer!.
  - eapply semax_copy; eauto.
    destruct Hbytes as [_ [Hlength _]].
    exact Hlength.
Qed.

(** Preserve one writable typed object when both lvalues denote the same
    address. Address equality replaces separate source ownership.
    The proof exposes one representation, applies the self-copy rule,
    and restores that representation with its compatibility facts. *)
Lemma semax_data_at_selfcopy:
  forall Delta e1 e2 sh (v: reptype (typeof e1)) P,
  copy_type_compatible (typeof e1) (typeof e2) = true -> access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh ->
  semax Delta
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      (`(data_at sh (typeof e1) v) (eval_lvalue e1) * P)))
    (Sassign e1 e2)
    (normal_ret_assert (`(data_at sh (typeof e1) v) (eval_lvalue e1) * P)).
Proof.
  intros Delta e1 e2 sh v P Htype Hmode Hcomplete Hwrite.
  (* ===== Expose one representation at the shared address ===== *)

  eapply semax_pre with
    (|> (EX bytes: list memval,
      !! data_at_memvals (typeof e1) v bytes &&
      (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
        local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
        local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
        (`(memvals_at_ptr sh bytes) (eval_lvalue e1) *
          (local (`(field_compatible (typeof e1) nil) (eval_lvalue e1)) && P))))).
  { intro rho.
    unfold_lift.
    cbn.
    apply andp_left2.
    apply later_derives.
    unfold local, lift1.
    unfold_lift.
    rewrite data_at_memvals_eq by auto using writable_readable.
    normalize.
    Exists bytes.
    entailer!. }
  rewrite (later_exp' _ nil).
  apply semax_extract_exists.
  intro bytes.
  rewrite later_andp.
  apply semax_extract_later_prop.
  intro Hbytes.

  (* ===== Restore the unchanged typed object ===== *)

  eapply semax_post' with
    (R' := `(memvals_at_ptr sh bytes) (eval_lvalue e1) *
      (local (`(field_compatible (typeof e1) nil) (eval_lvalue e1)) && P)).
  - (* Self-copy preserves the original representation witness. *)
    intro rho.
    unfold local, lift1.
    unfold_lift.
    cbn.
    rewrite data_at_memvals_eq by auto using writable_readable.
    normalize.
    Exists bytes.
    entailer!.
  - eapply semax_selfcopy; eauto.
    destruct Hbytes as [_ [Hlength _]].
    exact Hlength.
Qed.

(** The expression types govern the assignment checks. The ownership
    types retain their own attributes and address compatibility facts. *)
Lemma semax_data_at_copy_qualified:
  forall Delta e1 e2 sh1 sh2 destination source
    (Hstored: copy_type_compatible destination source = true)
    (v: reptype source) P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  copy_type_compatible (typeof e1) destination = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  semax Delta
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
      ((`(data_at_ sh1 destination) (eval_lvalue e1) *
        `(data_at sh2 source v) (eval_lvalue e2)) * P)))
    (Sassign e1 e2)
    (normal_ret_assert
      ((`(data_at sh1 destination (copy_reptype destination source Hstored v)) (eval_lvalue e1) *
        `(data_at sh2 source v) (eval_lvalue e2)) * P)).
Proof.
  intros Delta e1 e2 sh1 sh2 destination source Hstored v P
    Htype Hdestination Hmode Hcomplete Hwrite Hread.
  pose proof (copy_type_compatible_sizeof _ _ Hdestination) as Hdestination_size.
  pose proof (copy_type_compatible_sizeof _ _ Hstored) as Hsource_size.
  eapply semax_pre with
    (|> (EX old: list memval, EX bytes: list memval,
      !! (Zlength old = sizeof destination /\ data_at_memvals source v bytes) &&
      (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
        local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
        local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
        ((`(memvals_at_ptr sh1 old) (eval_lvalue e1) *
          `(memvals_at_ptr sh2 bytes) (eval_lvalue e2)) *
          (local (`(field_compatible destination nil) (eval_lvalue e1)) &&
           local (`(field_compatible source nil) (eval_lvalue e2)) && P))))).
  { intro rho. cbn. apply andp_left2. apply later_derives.
    unfold local, lift1. unfold_lift. cbn.
    rewrite data_at__memvals_eq by auto using writable_readable.
    rewrite data_at_memvals_eq by auto.
    normalize. Exists x bytes. entailer!. }
  rewrite (later_exp' _ nil). apply semax_extract_exists. intro old.
  rewrite (later_exp' _ nil). apply semax_extract_exists. intro bytes.
  rewrite later_andp. apply semax_extract_later_prop. intros [Hold Hbytes].
  assert (Hdestination_bytes:
    data_at_memvals destination (copy_reptype destination source Hstored v) bytes).
  { rewrite (copy_data_at_memvals _ _ _ _ _ Hstored (copy_reptype_JMeq _ _ _ _)).
    exact Hbytes. }
  eapply semax_post' with
    (R' :=
      (`(memvals_at_ptr sh1 bytes) (eval_lvalue e1) *
       `(memvals_at_ptr sh2 bytes) (eval_lvalue e2)) *
      (local (`(field_compatible destination nil) (eval_lvalue e1)) &&
       local (`(field_compatible source nil) (eval_lvalue e2)) && P)).
  - intro rho. unfold local, lift1. unfold_lift. cbn.
    rewrite !data_at_memvals_eq by auto using writable_readable.
    normalize. Exists bytes bytes. entailer!.
  - eapply semax_copy; eauto.
    + change (Zlength old = sizeof (typeof e1)).
      change (sizeof (typeof e1) = sizeof destination) in Hdestination_size.
      rewrite Hdestination_size. exact Hold.
    + destruct Hbytes as [_ [Hlength _]].
      change (sizeof (typeof e1) = sizeof destination) in Hdestination_size.
      change (sizeof destination = sizeof source) in Hsource_size.
      rewrite Hdestination_size, Hsource_size. exact Hlength.
Qed.

Lemma semax_data_at_selfcopy_qualified:
  forall Delta e1 e2 sh owned (v: reptype owned) P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  copy_type_compatible (typeof e1) owned = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh ->
  semax Delta
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      (`(data_at sh owned v) (eval_lvalue e1) * P)))
    (Sassign e1 e2)
    (normal_ret_assert (`(data_at sh owned v) (eval_lvalue e1) * P)).
Proof.
  intros Delta e1 e2 sh owned v P Htype Howned Hmode Hcomplete Hwrite.
  pose proof (copy_type_compatible_sizeof _ _ Howned) as Howned_size.
  eapply semax_pre with
    (|> (EX bytes: list memval,
      !! data_at_memvals owned v bytes &&
      (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
        local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
        local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
        (`(memvals_at_ptr sh bytes) (eval_lvalue e1) *
          (local (`(field_compatible owned nil) (eval_lvalue e1)) && P))))).
  { intro rho. unfold_lift. cbn. apply andp_left2. apply later_derives.
    unfold local, lift1. unfold_lift.
    rewrite data_at_memvals_eq by auto using writable_readable.
    normalize. Exists bytes. entailer!. }
  rewrite (later_exp' _ nil). apply semax_extract_exists. intro bytes.
  rewrite later_andp. apply semax_extract_later_prop. intro Hbytes.
  eapply semax_post' with
    (R' := `(memvals_at_ptr sh bytes) (eval_lvalue e1) *
      (local (`(field_compatible owned nil) (eval_lvalue e1)) && P)).
  - intro rho. unfold local, lift1. unfold_lift. cbn.
    rewrite data_at_memvals_eq by auto using writable_readable.
    normalize. Exists bytes. entailer!.
  - eapply semax_selfcopy; eauto.
    destruct Hbytes as [_ [Hlength _]].
    change (sizeof (typeof e1) = sizeof owned) in Howned_size.
    rewrite Howned_size. exact Hlength.
Qed.

End typed_copy.

#[export] Hint Rewrite @copy_reptype_refl @copy_reptype_struct @copy_reptype_union : norm.
