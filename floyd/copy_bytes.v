(** * Aggregate assignment with explicit byte ownership.

    Byte ownership records the entire representation, including padding.
    These rules do not require a typed value decoding those bytes. *)
From Ltac2 Require Import Ltac2.
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.veric.memvals_at.
Require Import VST.veric.copy_lemmas.
Require Import VST.floyd.copy_forward.
Require Import VST.floyd.copy_discovery.

Import LiftNotation.
Import compcert.lib.Maps.
Local Open Scope logic.
Set Default Proof Mode "Classic".

Section CopyBytes.
Context {cs: compspecs} {Espec: OracleKind}.

(** Own exactly [sizeof t] memory values at [p]. The length is part of
    the predicate, and readability or writability is required separately
    by each assignment rule. *)
Definition copy_bytes_at (sh: share) (t: type) (bytes: list memval)
    (p: val): mpred :=
  !! (Zlength bytes = sizeof t) && memvals_at_ptr sh bytes p.

Lemma copy_bytes_at_type: forall sh destination source bytes p,
  copy_type_compatible destination source = true ->
  copy_bytes_at sh destination bytes p = copy_bytes_at sh source bytes p.
Proof.
  intros sh destination source bytes p Hcompatible.
  unfold copy_bytes_at, expr.sizeof.
  rewrite (copy_type_compatible_sizeof destination source Hcompatible).
  reflexivity.
Qed.

Lemma copy_bytes_at_length: forall sh t bytes p,
  copy_bytes_at sh t bytes p |-- !! (Zlength bytes = sizeof t).
Proof. intros. unfold copy_bytes_at. apply andp_left1, derives_refl. Qed.

Lemma copy_bytes_at_isptr: forall sh t bytes p,
  copy_bytes_at sh t bytes p |-- !! isptr p.
Proof.
  intros. unfold copy_bytes_at. apply andp_left2.
  rewrite derives_eq. intros phi H.
  apply memvals_at_ptr_isptr in H. exact H.
Qed.

(** Copy a complete compatible aggregate from readable source ownership
    into a separated writable destination, preserving [P]. Both lvalues
    must be aligned. Expose the stored lengths, apply [semax_copy], then
    restore the length assertions for both resulting byte predicates. *)
Lemma semax_copy_bytes:
  forall Delta e1 e2 sh1 sh2 old bytes P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  semax Delta
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
      ((`(copy_bytes_at sh1 (typeof e1) old) (eval_lvalue e1) *
        `(copy_bytes_at sh2 (typeof e1) bytes) (eval_lvalue e2)) * P)))
    (Sassign e1 e2)
    (normal_ret_assert
      ((`(copy_bytes_at sh1 (typeof e1) bytes) (eval_lvalue e1) *
        `(copy_bytes_at sh2 (typeof e1) bytes) (eval_lvalue e2)) * P)).
Proof.
  intros Delta e1 e2 sh1 sh2 old bytes P Htype Hmode Hcomplete Hwrite Hread.
  eapply semax_pre with
    (|> (!! (Zlength old = sizeof (typeof e1) /\
              Zlength bytes = sizeof (typeof e1)) &&
      (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
       local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
       local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
       ((`(memvals_at_ptr sh1 old) (eval_lvalue e1) *
         `(memvals_at_ptr sh2 bytes) (eval_lvalue e2)) * P)))).
  - (* Ownership supplies both representation lengths. *)
    intro rho.
    cbn.
    apply andp_left2.
    apply later_derives.
    unfold copy_bytes_at, local, lift1.
    unfold_lift.
    entailer!.
  - (* Both resulting regions have the source length and bytes. *)
    rewrite later_andp.
    apply semax_extract_later_prop.
    intros [Hold Hbytes].
    eapply semax_post' with
      (R' :=
        (`(memvals_at_ptr sh1 bytes) (eval_lvalue e1) *
         `(memvals_at_ptr sh2 bytes) (eval_lvalue e2)) * P).
    + intro rho.
      unfold copy_bytes_at, local, lift1.
      unfold_lift.
      cbn.
      entailer!.
    + apply semax_copy; eauto.
Qed.

(** Preserve one writable byte region when both lvalues have equal
    addresses. Only that shared address needs alignment. Expose its
    length, apply [semax_selfcopy], and restore the same byte predicate. *)
Lemma semax_selfcopy_bytes:
  forall Delta e1 e2 sh bytes P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true -> writable_share sh ->
  semax Delta
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      (`(copy_bytes_at sh (typeof e1) bytes) (eval_lvalue e1) * P)))
    (Sassign e1 e2)
    (normal_ret_assert
      (`(copy_bytes_at sh (typeof e1) bytes) (eval_lvalue e1) * P)).
Proof.
  intros Delta e1 e2 sh bytes P Htype Hmode Hcomplete Hwrite.
  eapply semax_pre with
    (|> (!! (Zlength bytes = sizeof (typeof e1)) &&
      (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
       local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
       local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
       (`(memvals_at_ptr sh bytes) (eval_lvalue e1) * P)))).
  - (* A single ownership predicate supplies the shared byte region. *)
    intro rho.
    cbn.
    apply andp_left2.
    apply later_derives.
    unfold copy_bytes_at, local, lift1.
    unfold_lift.
    entailer!.
  - (* The shared representation and its length remain unchanged. *)
    rewrite later_andp.
    apply semax_extract_later_prop.
    intro Hbytes.
    eapply semax_post' with
      (R' := `(memvals_at_ptr sh bytes) (eval_lvalue e1) * P).
    + intro rho.
      unfold copy_bytes_at, local, lift1.
      unfold_lift.
      cbn.
      entailer!.
    + apply semax_selfcopy; eauto.
Qed.

(** Expose separated byte regions and a wand from their copied state to
    [Q]. Lvalue checks and alignment are supplied independently. Apply
    the byte rule with the reconstruction wand as frame, then consume it. *)
Lemma semax_copy_bytes_ram:
  forall Delta e1 e2 sh1 sh2 old bytes P Q,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e2))) ->
  (local (tc_environ Delta) && P |--
    (`(copy_bytes_at sh1 (typeof e1) old) (eval_lvalue e1) *
     `(copy_bytes_at sh2 (typeof e1) bytes) (eval_lvalue e2)) *
    ((`(copy_bytes_at sh1 (typeof e1) bytes) (eval_lvalue e1) *
      `(copy_bytes_at sh2 (typeof e1) bytes) (eval_lvalue e2)) -* Q)) ->
  semax Delta (|> P) (Sassign e1 e2) (normal_ret_assert Q).
Proof.
  intros Delta e1 e2 sh1 sh2 old bytes P Q Htype Hmode Hcomplete Hwrite Hread Hcheck Hram.
  eapply semax_pre with
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
      ((`(copy_bytes_at sh1 (typeof e1) old) (eval_lvalue e1) *
        `(copy_bytes_at sh2 (typeof e1) bytes) (eval_lvalue e2)) *
       ((`(copy_bytes_at sh1 (typeof e1) bytes) (eval_lvalue e1) *
         `(copy_bytes_at sh2 (typeof e1) bytes) (eval_lvalue e2)) -* Q)))).
  - (* Separate the checked copy footprint from its reconstruction. *)
    apply later_ENTAIL.
    apply andp_right; assumption.
  - (* Copy the footprint and recover the caller postcondition. *)
    eapply semax_post'.
    + apply andp_left2.
      apply modus_ponens_wand.
    + eapply semax_copy_bytes; eauto.
Qed.

(** Expose one writable byte region at provably equal lvalue addresses.
    The supplied wand restores [Q] from the unchanged region. Apply the
    self-copy rule with this wand as frame, then consume it. *)
Lemma semax_selfcopy_bytes_ram:
  forall Delta e1 e2 sh bytes P Q,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true -> writable_share sh ->
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
    local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e1))) ->
  (local (tc_environ Delta) && P |--
    `(copy_bytes_at sh (typeof e1) bytes) (eval_lvalue e1) *
    (`(copy_bytes_at sh (typeof e1) bytes) (eval_lvalue e1) -* Q)) ->
  semax Delta (|> P) (Sassign e1 e2) (normal_ret_assert Q).
Proof.
  intros Delta e1 e2 sh bytes P Q Htype Hmode Hcomplete Hwrite Hcheck Hram.
  eapply semax_pre with
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      (`(copy_bytes_at sh (typeof e1) bytes) (eval_lvalue e1) *
       (`(copy_bytes_at sh (typeof e1) bytes) (eval_lvalue e1) -* Q)))).
  - (* Equality permits one checked region and one reconstruction wand. *)
    apply later_ENTAIL.
    apply andp_right; assumption.
  - (* Preserve the region and recover the caller postcondition. *)
    eapply semax_post'.
    + apply andp_left2.
      apply modus_ponens_wand.
    + eapply semax_selfcopy_bytes; eauto.
Qed.

End CopyBytes.

#[export] Hint Resolve copy_bytes_at_length copy_bytes_at_isptr : saturate_local.

Module CopyBytesForward.

Ltac2 Type candidate := {
  index : constr;
  share : constr;
  bytes : constr;
  permission : constr;
  stored_type : constr;
  compatible : constr
}.

(** Search byte predicates in spatial list order, matching object type
    and pointer by unification. Select a region only after proving its
    required permission. Alignment remains a separate obligation. *)
Ltac2 rec find_candidate (permission : constr) (predicates : constr) (object_type : constr)
    (pointer : constr) (index : constr) : candidate :=
  lazy_match! predicates with
  | @nil _ => copy_missing_region permission object_type pointer
  | @cons _ ?predicate ?tail =>
      Control.plus
        (fun () =>
          lazy_match! predicate with
          | @copy_bytes_at _ ?share ?stored_type ?bytes ?stored_pointer =>
              let compatible := copy_prove_type object_type stored_type in
              Std.unify stored_pointer pointer;
              let proof := copy_prove_permission permission share in
              { index := index; share := share; bytes := bytes; permission := proof;
                stored_type := stored_type; compatible := compatible }
          | _ => Control.zero Match_failure
          end)
        (fun _ => find_candidate permission tail object_type pointer constr:(S $index))
  end.

Ltac2 find_bytes (permission : constr) (assignment : CopyForward.assignment) (pointer : constr) : candidate :=
  let spatial := assignment.(CopyForward.spatial) in
  let object_type := assignment.(CopyForward.object_type) in
  Control.once (fun () => find_candidate permission spatial object_type pointer constr:(O)).

Ltac2 prove_alignment (address : constr) :=
  rewrite (add_andp _ _ $address);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  ltac1:(entailer!).

Ltac2 prove_selfcopy_checks (addresses : CopyForward.addresses) :=
  apply andp_right;
  Control.dispatch
    [ (fun () =>
        apply andp_right;
        Control.dispatch
          [ CopyForward.prove_lvalue_types;
            (fun () => CopyForward.prove_same_address addresses) ]);
      (fun () => prove_alignment (addresses.(CopyForward.destination_address))) ].

Ltac2 prove_copy_checks (addresses : CopyForward.addresses) :=
  apply andp_right;
  Control.dispatch
    [ (fun () =>
        apply andp_right;
        Control.dispatch
          [ CopyForward.prove_lvalue_types;
            (fun () => prove_alignment (addresses.(CopyForward.destination_address))) ]);
      (fun () => prove_alignment (addresses.(CopyForward.source_address))) ].

Ltac2 prove_selfcopy_ramification (assignment : CopyForward.assignment)
    (addresses : CopyForward.addresses) (candidate : candidate) :=
  let index := candidate.(index) in
  let spatial := assignment.(CopyForward.spatial) in
  let remainder := eval cbn [replace_nth] in (replace_nth $index $spatial emp) in
  let frame_name := Fresh.in_goal @COPY_FRAME in
  Std.pose (Some frame_name) constr:(fold_right_sepcon $remainder);
  let address := addresses.(CopyForward.destination_address) in
  let object_type := assignment.(CopyForward.object_type) in
  let stored_type := candidate.(stored_type) in
  let compatible := candidate.(compatible) in
  rewrite (add_andp _ _ $address);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  let frame := Control.hyp frame_name in
  eapply RAMIF_PLAIN.solve with (F := $frame);
  Control.enter (fun () =>
    ltac1:(frame_name |- unfold frame_name) (Ltac1.of_ident frame_name);
    unfold fold_right_sepcon;
    repeat (progress (rewrite <- (copy_bytes_at_type _ $object_type $stored_type _ _ $compatible)));
    ltac1:(entailer!)).

Ltac2 prove_copy_ramification (assignment : CopyForward.assignment)
    (addresses : CopyForward.addresses) (destination : candidate) (source : candidate) :=
  let destination_index := destination.(index) in
  let source_index := source.(index) in
  let spatial := assignment.(CopyForward.spatial) in
  let remainder := eval cbn [replace_nth] in
    (replace_nth $source_index (replace_nth $destination_index $spatial emp) emp) in
  let frame_name := Fresh.in_goal @COPY_FRAME in
  Std.pose (Some frame_name) constr:(fold_right_sepcon $remainder);
  let destination_address := addresses.(CopyForward.destination_address) in
  let source_address := addresses.(CopyForward.source_address) in
  let object_type := assignment.(CopyForward.object_type) in
  let destination_type := destination.(stored_type) in
  let source_type := source.(stored_type) in
  let destination_compatible := destination.(compatible) in
  let source_compatible := source.(compatible) in
  rewrite (add_andp _ _ $destination_address), (add_andp _ _ $source_address);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  let frame := Control.hyp frame_name in
  eapply RAMIF_PLAIN.solve with (F := $frame);
  Control.enter (fun () =>
    ltac1:(frame_name |- unfold frame_name) (Ltac1.of_ident frame_name);
    unfold fold_right_sepcon;
    repeat (progress (rewrite <- (copy_bytes_at_type _ $object_type $destination_type _ _ $destination_compatible)));
    repeat (progress (rewrite <- (copy_bytes_at_type _ $object_type $source_type _ _ $source_compatible)));
    ltac1:(entailer!)).

Ltac2 selfcopy (assignment : CopyForward.assignment) (addresses : CopyForward.addresses) :=
  let destination_pointer := addresses.(CopyForward.destination_pointer) in
  let source_pointer := addresses.(CopyForward.source_pointer) in
  let _ := CopyForward.prove_fact @COPY_SAME_ADDRESS
    constr:($destination_pointer = $source_pointer)
    (fun () => ltac1:(congruence)) in
  let candidate := find_bytes constr:(writable_share) assignment source_pointer in
  let share := candidate.(share) in
  let bytes := candidate.(bytes) in
  let permission := candidate.(permission) in
  let props := assignment.(CopyForward.props) in
  let locals := assignment.(CopyForward.locals) in
  let spatial := assignment.(CopyForward.spatial) in
  let post := constr:(PROPx $props (LOCALx $locals (SEPx $spatial))) in
  eapply semax_selfcopy_bytes_ram with (sh := $share) (bytes := $bytes) (Q := $post);
  Control.dispatch
    [ (fun () => reflexivity); (fun () => reflexivity); (fun () => reflexivity);
      (fun () => exact $permission);
      (fun () => prove_selfcopy_checks addresses);
      (fun () => prove_selfcopy_ramification assignment addresses candidate) ].

Ltac2 disjoint_copy (assignment : CopyForward.assignment) (addresses : CopyForward.addresses) :=
  let destination_pointer := addresses.(CopyForward.destination_pointer) in
  let source_pointer := addresses.(CopyForward.source_pointer) in
  let source := find_bytes constr:(readable_share) assignment source_pointer in
  let destination := find_bytes constr:(writable_share) assignment destination_pointer in
  let object_type := destination.(stored_type) in
  let destination_share := destination.(share) in
  let source_share := source.(share) in
  let destination_permission := destination.(permission) in
  let source_permission := source.(permission) in
  let old_bytes := destination.(bytes) in
  let bytes := source.(bytes) in
  let index := destination.(index) in
  let spatial := assignment.(CopyForward.spatial) in
  let updated := constr:(replace_nth $index $spatial
    (copy_bytes_at $destination_share $object_type $bytes $destination_pointer)) in
  let props := assignment.(CopyForward.props) in
  let locals := assignment.(CopyForward.locals) in
  let post := constr:(PROPx $props (LOCALx $locals (SEPx $updated))) in
  eapply semax_copy_bytes_ram with (sh1 := $destination_share) (sh2 := $source_share)
    (old := $old_bytes) (bytes := $bytes) (Q := $post);
  Control.dispatch
    [ (fun () => reflexivity); (fun () => reflexivity); (fun () => reflexivity);
      (fun () => exact $destination_permission); (fun () => exact $source_permission);
      (fun () => prove_copy_checks addresses);
      (fun () => prove_copy_ramification assignment addresses destination source) ].

(** Forward a canonical aggregate assignment using [copy_bytes_at]
    entries. Try equal addresses with one writable region first, then
    separated readable source and writable destination regions. Match
    ownership by object type and evaluated pointer, replace destination
    bytes, and frame remaining entries. Missing ownership or unproved
    type, completeness, share, or alignment checks prevent completion. *)
Ltac2 run () :=
  Control.enter (fun () =>
    let assignment := CopyForward.read_assignment () in
    let addresses := CopyForward.evaluate_addresses assignment in
    Control.plus
      (fun () => selfcopy assignment addresses)
      (fun _ => disjoint_copy assignment addresses)).

End CopyBytesForward.
