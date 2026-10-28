(** * Typed ownership and native aggregate copy automation.

    Ramification exposes the copied objects and retains a wand that
    reconstructs the caller postcondition. The native entry point handles
    whole objects with canonical [PROP], [LOCAL], and [SEP] ownership. *)
From Ltac2 Require Import Ltac2.
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.copy_rules.
Require Import VST.floyd.copy_discovery.
Require Import VST.floyd.data_at_memvals.
Require Import VST.floyd.field_at.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.copy_alignment.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.sc_set_load_store.

Import LiftNotation.
Import compcert.lib.Maps.
Local Open Scope logic.
Set Default Proof Mode "Classic".

Section ForwardCopy.
Context {cs: compspecs} {Espec: OracleKind}.

(** Copy between separated typed objects, using writable destination
    and readable source ownership. The first entailment supplies lvalue
    checks and alignment, the second supplies objects and a reconstruction
    wand. Apply the typed rule with that wand as frame, then eliminate it. *)
Lemma semax_copy_ram:
  forall Delta e1 e2 sh1 sh2 (v: reptype (typeof e1)) P Q,
  copy_type_compatible (typeof e1) (typeof e2) = true -> access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e2))) ->
  (local (tc_environ Delta) && P |--
    (`(data_at_ sh1 (typeof e1)) (eval_lvalue e1) *
     `(data_at sh2 (typeof e1) v) (eval_lvalue e2)) *
    ((`(data_at sh1 (typeof e1) v) (eval_lvalue e1) *
      `(data_at sh2 (typeof e1) v) (eval_lvalue e2)) -* Q)) ->
  semax Delta (|> P) (Sassign e1 e2) (normal_ret_assert Q).
Proof.
  intros Delta e1 e2 sh1 sh2 v P Q Htype Hmode Hcomplete Hwrite Hread Hcheck Hramify.
  eapply semax_pre with
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
      ((`(data_at_ sh1 (typeof e1)) (eval_lvalue e1) *
        `(data_at sh2 (typeof e1) v) (eval_lvalue e2)) *
       ((`(data_at sh1 (typeof e1) v) (eval_lvalue e1) *
         `(data_at sh2 (typeof e1) v) (eval_lvalue e2)) -* Q)))).
  - (* Expose the checked regions and retain their reconstruction wand. *)
    apply later_ENTAIL.
    apply andp_right; assumption.
  - (* Copy the regions, then reconstruct the caller postcondition. *)
    eapply semax_post'.
    + apply andp_left2.
      apply modus_ponens_wand.
    + eapply semax_data_at_copy; eauto.
Qed.

(** Copy at equal addresses using a single writable object. The checks
    require address equality and destination alignment, and the wand
    restores [Q] from unchanged ownership. Apply the self-copy rule with
    the wand as frame, then eliminate it. *)
Lemma semax_selfcopy_ram:
  forall Delta e1 e2 sh (v: reptype (typeof e1)) P Q,
  copy_type_compatible (typeof e1) (typeof e2) = true -> access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh ->
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
    local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e1))) ->
  (local (tc_environ Delta) && P |--
    `(data_at sh (typeof e1) v) (eval_lvalue e1) *
    (`(data_at sh (typeof e1) v) (eval_lvalue e1) -* Q)) ->
  semax Delta (|> P) (Sassign e1 e2) (normal_ret_assert Q).
Proof.
  intros Delta e1 e2 sh v P Q Htype Hmode Hcomplete Hwrite Hcheck Hramify.
  eapply semax_pre with
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      (`(data_at sh (typeof e1) v) (eval_lvalue e1) *
       (`(data_at sh (typeof e1) v) (eval_lvalue e1) -* Q)))).
  - (* One checked region suffices when both addresses are equal. *)
    apply later_ENTAIL.
    apply andp_right; assumption.
  - (* Preserve the object and discharge the reconstruction wand. *)
    eapply semax_post'.
    + apply andp_left2.
      apply modus_ponens_wand.
    + eapply semax_data_at_selfcopy; eauto.
Qed.

Lemma semax_copy_qualified_ram:
  forall Delta e1 e2 sh1 sh2 destination source
    (Hstored: copy_type_compatible destination source = true)
    (v: reptype source) P Q,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  copy_type_compatible (typeof e1) destination = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e2))) ->
  (local (tc_environ Delta) && P |--
    (`(data_at_ sh1 destination) (eval_lvalue e1) *
     `(data_at sh2 source v) (eval_lvalue e2)) *
    ((`(data_at sh1 destination (copy_reptype destination source Hstored v))
        (eval_lvalue e1) *
      `(data_at sh2 source v) (eval_lvalue e2)) -* Q)) ->
  semax Delta (|> P) (Sassign e1 e2) (normal_ret_assert Q).
Proof.
  intros Delta e1 e2 sh1 sh2 destination source Hstored v P Q
    Htype Hdestination Hmode Hcomplete Hwrite Hread Hcheck Hramify.
  eapply semax_pre with
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e2)) &&
      ((`(data_at_ sh1 destination) (eval_lvalue e1) *
        `(data_at sh2 source v) (eval_lvalue e2)) *
       ((`(data_at sh1 destination (copy_reptype destination source Hstored v))
           (eval_lvalue e1) *
         `(data_at sh2 source v) (eval_lvalue e2)) -* Q)))).
  - apply later_ENTAIL. apply andp_right; assumption.
  - eapply semax_post'.
    + apply andp_left2. apply modus_ponens_wand.
    + eapply semax_data_at_copy_qualified; eauto.
Qed.

Lemma semax_selfcopy_qualified_ram:
  forall Delta e1 e2 sh owned (v: reptype owned) P Q,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  copy_type_compatible (typeof e1) owned = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh ->
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
    local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
    local (`(copy_aligned (typeof e1)) (eval_lvalue e1))) ->
  (local (tc_environ Delta) && P |--
    `(data_at sh owned v) (eval_lvalue e1) *
    (`(data_at sh owned v) (eval_lvalue e1) -* Q)) ->
  semax Delta (|> P) (Sassign e1 e2) (normal_ret_assert Q).
Proof.
  intros Delta e1 e2 sh owned v P Q
    Htype Howned Hmode Hcomplete Hwrite Hcheck Hramify.
  eapply semax_pre with
    (|> (tc_lvalue Delta e1 && tc_lvalue Delta e2 &&
      local (`eq (eval_lvalue e1) (eval_lvalue e2)) &&
      local (`(copy_aligned (typeof e1)) (eval_lvalue e1)) &&
      (`(data_at sh owned v) (eval_lvalue e1) *
       (`(data_at sh owned v) (eval_lvalue e1) -* Q)))).
  - apply later_ENTAIL. apply andp_right; assumption.
  - eapply semax_post'.
    + apply andp_left2. apply modus_ponens_wand.
    + eapply semax_data_at_selfcopy_qualified; eauto.
Qed.

End ForwardCopy.

Lemma copy_alignment_lvalue: forall {cs: compspecs} Delta P e t p,
  (local (tc_environ Delta) && P |-- local (`(eq p) (eval_lvalue e))) ->
  copy_aligned t p ->
  local (tc_environ Delta) && P |--
    local (`(copy_aligned t) (eval_lvalue e)).
Proof.
  intros cs Delta P e t p Haddress Haligned.
  eapply derives_trans; [exact Haddress |].
  intro rho. unfold local, lift1. unfold_lift.
  apply prop_derives. intros H. rewrite <- H. exact Haligned.
Qed.

Module CopyForward.

(** Canonical assignment data shared by the whole object, byte, and field
    entry points. The spatial list retains caller order. *)
Ltac2 Type assignment := {
  specs : constr;
  delta : constr;
  props : constr;
  locals : constr;
  spatial : constr;
  destination_expr : constr;
  source_expr : constr;
  object_type : constr
}.

(** Evaluated pointers with entailments connecting them to both lvalues.
    Equality of these pointers still needs a separate proof for self-copy. *)
Ltac2 Type addresses := {
  destination_pointer : constr;
  source_pointer : constr;
  destination_address : constr;
  source_address : constr
}.

Ltac2 Type local_environment := {
  temporaries : constr;
  variables : constr;
  globals : constr;
  tree_equality : constr
}.

Ltac2 reject (message : string) :=
  Control.zero (Tactic_failure (Some (Message.of_string message))).

(** Read a single assignment with a later canonical precondition.
    Reject goals outside that shape before attempting ownership search. *)
Ltac2 read_assignment () : assignment :=
  lazy_match! goal with
  | [ |- @semax ?cs _ ?delta
      (|> (PROPx ?props (LOCALx ?locals (SEPx ?spatial))))
      (Sassign ?destination ?source) _ ] =>
      let object_type := eval hnf in (typeof $destination) in
      { specs := cs; delta := delta; props := props; locals := locals;
        spatial := spatial; destination_expr := destination;
        source_expr := source; object_type := object_type }
  | [ |- _ ] => reject "Aggregate copy requires a canonical assignment"
  end.

Ltac2 prove_fact (name : ident) (proposition : constr) (proof : unit -> unit) : constr :=
  let name := Fresh.in_goal name in
  Std.assert (Std.AssertType
    (Some (Std.IntroNaming (Std.IntroIdentifier name))) proposition (Some proof));
  Control.hyp name.

Ltac2 prove_local_environment (assignment : assignment) : local_environment :=
  let locals := assignment.(locals) in
  let temps := open_constr:(_ : PTree.t val) in
  let variables := open_constr:(_ : PTree.t (type * val)) in
  let globals := open_constr:(_ : option globals) in
  let local_tree := prove_fact @COPY_LOCALS
    constr:(local2ptree $locals = ($temps, $variables, nil, $globals))
    (fun () => ltac1:(prove_local2ptree)) in
  { temporaries := temps; variables := variables; globals := globals;
    tree_equality := local_tree }.

Ltac2 prove_local_tree (assignment : assignment) : constr :=
  let environment := prove_local_environment assignment in
  environment.(tree_equality).

(** Evaluate both lvalues through the canonical local environment and
    certify the resulting pointers. Unsupported expressions or missing
    local bindings fail through the lvalue evaluator. *)
Ltac2 evaluate_addresses (assignment : assignment) : addresses :=
  let delta := assignment.(delta) in
  let props := assignment.(props) in
  let locals := assignment.(locals) in
  let spatial := assignment.(spatial) in
  let destination := assignment.(destination_expr) in
  let source := assignment.(source_expr) in
  let environment := prove_local_environment assignment in
  let temps := environment.(temporaries) in
  let variables := environment.(variables) in
  let globals := environment.(globals) in
  let local_tree := environment.(tree_equality) in
  let destination_pointer := open_constr:(_ : val) in
  let source_pointer := open_constr:(_ : val) in
  let destination_value := prove_fact @COPY_DESTINATION
    constr:(msubst_eval_lvalue $delta $temps $variables $globals $destination =
      Some $destination_pointer)
    (fun () => ltac1:(solve_msubst_eval_lvalue)) in
  let source_value := prove_fact @COPY_SOURCE
    constr:(msubst_eval_lvalue $delta $temps $variables $globals $source = Some $source_pointer)
    (fun () => ltac1:(solve_msubst_eval_lvalue)) in
  let pre := constr:(PROPx $props (LOCALx $locals (SEPx $spatial))) in
  let destination_address := prove_fact @COPY_DESTINATION_ADDRESS
    constr:(local (tc_environ $delta) && $pre |--
      local (`(eq $destination_pointer) (eval_lvalue $destination)))
    (fun () =>
      erewrite (local2ptree_soundness $props $locals $spatial) by exact $local_tree;
      apply msubst_eval_lvalue_eq;
      exact $destination_value) in
  let source_address := prove_fact @COPY_SOURCE_ADDRESS
    constr:(local (tc_environ $delta) && $pre |--
      local (`(eq $source_pointer) (eval_lvalue $source)))
    (fun () =>
      erewrite (local2ptree_soundness $props $locals $spatial) by exact $local_tree;
      apply msubst_eval_lvalue_eq;
      exact $source_value) in
  { destination_pointer := destination_pointer; source_pointer := source_pointer;
    destination_address := destination_address; source_address := source_address }.

Ltac2 divide () :=
  lazy_match! goal with
  | [ |- Z.divide ?alignment ?offset ] =>
      let quotient := eval vm_compute in (Z.div $offset $alignment) in
      exists $quotient;
      vm_compute;
      reflexivity
  | [ |- _ ] => reject "Aggregate copy alignment requires a divisibility goal"
  end.

Ltac2 rec scalar_path (cs : constr) (object_type : constr) (path : constr)
    (continuation : constr -> constr -> unit) :=
  let mode := eval hnf in (access_mode $object_type) in
  lazy_match! mode with
  | By_value ?chunk => continuation path chunk
  | _ =>
      let object_type := eval hnf in $object_type in
      lazy_match! object_type with
      | Tarray ?element _ _ =>
          scalar_path cs element constr:(ArraySubsc 0 :: $path) continuation
      | Tstruct ?id _ =>
          let members := eval hnf in (co_members (@get_co $cs $id)) in
          scalar_members cs members path false continuation
      | Tunion ?id _ =>
          let members := eval hnf in (co_members (@get_co $cs $id)) in
          scalar_members cs members path true continuation
      | _ => reject "Aggregate copy cannot find a scalar alignment leaf"
      end
  end
with scalar_members (cs : constr) (members : constr) (path : constr)
    (is_union : bool) (continuation : constr -> constr -> unit) :=
  lazy_match! members with
  | @cons _ ?member ?tail =>
      Control.plus
        (fun () =>
          let field := eval cbn in (name_member $member) in
          let field_type := eval cbn in (type_member $member) in
          let path := if is_union then constr:(UnionField $field :: $path)
            else constr:(StructField $field :: $path) in
          scalar_path cs field_type path continuation)
        (fun _ => scalar_members cs tail path is_union continuation)
  | @nil _ => reject "Aggregate copy cannot prove alignment from its scalar leaves"
  end.

Ltac2 hypothesis_name (proof : constr) : ident :=
  match Constr.Unsafe.kind proof with
  | Constr.Unsafe.Var name => name
  | _ => reject "Aggregate copy expected a compatibility hypothesis"
  end.

Ltac2 prove_leaf_alignment (compatible : constr) (path : constr) (chunk : constr) :=
  let compatible_name := hypothesis_name compatible in
  eapply field_compatible_copy_aligned with (gfs := $path) (ch := $chunk);
  Control.dispatch
    [ (fun () =>
        unfold field_compatible in $compatible_name |- *;
        ltac1:(intuition);
        Control.enter (fun () =>
          Control.plus
            (fun () => solve [repeat constructor; simpl; auto; ltac1:(lia)])
            (fun _ => ())));
      (fun () => reflexivity);
      (fun () => divide ());
      (fun () => divide ()) ].

(** Try to derive block copy alignment from a compatible scalar leaf.
    Arrays use index zero and composites search their members. A leaf
    must satisfy the chunk and offset divisibility obligations. Unsolved
    alignment remains an obligation for the caller. *)
Ltac2 solve_alignment (compatible : constr) :=
  Control.enter (fun () =>
    Control.plus
      (fun () =>
        solve [lazy_match! goal with
        | [ |- @copy_aligned ?cs ?object_type _ ] =>
            let compatible :=
              lazy_match! Constr.type compatible with
              | @field_compatible _ ?owned_type ?path ?pointer =>
                  Control.plus
                    (fun () => Std.unify object_type owned_type; compatible)
                    (fun _ =>
                      let type_compatible := copy_prove_type object_type owned_type in
                      prove_fact @COPY_ALIGNMENT_COMPATIBLE
                        constr:(@field_compatible $cs $object_type $path $pointer)
                        (fun () =>
                          rewrite (@copy_field_compatible $cs $object_type $owned_type
                            $path $pointer $type_compatible);
                          exact $compatible))
              end in
            scalar_path cs object_type constr:(@nil gfield)
              (fun path chunk => prove_leaf_alignment compatible path chunk)
        end])
      (fun _ => ())).

Ltac2 find_whole (permission : constr) (assignment : assignment) (pointer : constr) : copy_candidate :=
  let spatial := assignment.(spatial) in
  let object_type := assignment.(object_type) in
  Control.once (fun () => copy_find_candidate permission spatial object_type pointer constr:(O)).

Ltac2 extract_compatibility (object_type : constr) (pointer : constr) : constr :=
  let name := Fresh.in_goal @COPY_COMPATIBLE in
  let proposition := constr:(field_compatible $object_type nil $pointer) in
  ltac1:(proposition name |- assert_PROP proposition as name by entailer!)
    (Ltac1.of_constr proposition) (Ltac1.of_ident name);
  Control.hyp name.

Ltac2 prove_lvalue_types () :=
  apply andp_right;
  Control.enter (fun () => ltac1:(entailer!)).

Ltac2 prove_alignment (address : constr) (compatible : constr) (same : constr option) :=
  eapply copy_alignment_lvalue;
  Control.dispatch
    [ (fun () => exact $address);
      (fun () =>
        match same with
        | Some equality => Control.plus (fun () => rewrite $equality) (fun _ => ())
        | None => ()
        end;
        solve_alignment compatible) ].

Ltac2 prove_same_address (addresses : addresses) :=
  let destination_address := addresses.(destination_address) in
  let source_address := addresses.(source_address) in
  rewrite (add_andp _ _ $destination_address), (add_andp _ _ $source_address);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  ltac1:(entailer!).

Ltac2 prove_selfcopy_checks (addresses : addresses) (compatible : constr) (same : constr) :=
  apply andp_right;
  Control.dispatch
    [ (fun () =>
        apply andp_right;
        Control.dispatch [prove_lvalue_types; (fun () => prove_same_address addresses)]);
      (fun () => prove_alignment (addresses.(destination_address)) compatible (Some same)) ].

Ltac2 prove_copy_checks (addresses : addresses)
    (destination_compatible : constr) (source_compatible : constr) :=
  apply andp_right;
  Control.dispatch
    [ (fun () =>
        apply andp_right;
        Control.dispatch
          [ prove_lvalue_types;
            (fun () => prove_alignment (addresses.(destination_address)) destination_compatible None) ]);
      (fun () => prove_alignment (addresses.(source_address)) source_compatible None) ].

Ltac2 prove_selfcopy_ramification (assignment : assignment) (addresses : addresses)
    (candidate : copy_candidate) :=
  let index := candidate.(copy_candidate_index) in
  let spatial := assignment.(spatial) in
  let remainder := eval cbn [replace_nth] in (replace_nth $index $spatial emp) in
  (* Normalization substitutes pointers, so the frame must follow those substitutions. *)
  let frame_name := Fresh.in_goal @COPY_FRAME in
  Std.pose (Some frame_name) constr:(fold_right_sepcon $remainder);
  let address := addresses.(destination_address) in
  rewrite (add_andp _ _ $address);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  let frame := Control.hyp frame_name in
  eapply RAMIF_PLAIN.solve with (F := $frame);
  Control.enter (fun () =>
    ltac1:(frame_name |- unfold frame_name) (Ltac1.of_ident frame_name);
    cbn [fold_right_sepcon]; ltac1:(entailer!)).

Ltac2 prove_copy_ramification (assignment : assignment) (addresses : addresses)
    (destination : copy_candidate) (source : copy_candidate) :=
  let specs := assignment.(specs) in
  let destination_type := destination.(copy_candidate_type) in
  let source_type := source.(copy_candidate_type) in
  let compatible := copy_prove_type destination_type source_type in
  let value := source.(copy_candidate_value) in
  Control.plus
    (fun () =>
      let equality := constr:(JMeq_eq
        (@copy_reptype_JMeq $specs $destination_type $source_type $compatible $value)) in
      rewrite $equality)
    (fun _ => ());
  let destination_index := destination.(copy_candidate_index) in
  let source_index := source.(copy_candidate_index) in
  let spatial := assignment.(spatial) in
  let remainder := eval cbn [replace_nth] in
    (replace_nth $source_index (replace_nth $destination_index $spatial emp) emp) in
  let frame_name := Fresh.in_goal @COPY_FRAME in
  Std.pose (Some frame_name) constr:(fold_right_sepcon $remainder);
  let destination_address := addresses.(destination_address) in
  let source_address := addresses.(source_address) in
  rewrite (add_andp _ _ $destination_address), (add_andp _ _ $source_address);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  let frame := Control.hyp frame_name in
  eapply RAMIF_PLAIN.solve with (F := $frame);
  Control.enter (fun () =>
    ltac1:(frame_name |- unfold frame_name) (Ltac1.of_ident frame_name);
    cbn [fold_right_sepcon]; ltac1:(entailer!)).

Ltac2 selfcopy (assignment : assignment) (addresses : addresses) :=
  let destination_pointer := addresses.(destination_pointer) in
  let source_pointer := addresses.(source_pointer) in
  let same := prove_fact @COPY_SAME_ADDRESS
    constr:($destination_pointer = $source_pointer)
    (fun () => ltac1:(congruence)) in
  let candidate := find_whole constr:(writable_share) assignment source_pointer in
  let object_type := candidate.(copy_candidate_type) in
  let compatible := extract_compatibility object_type source_pointer in
  let share := candidate.(copy_candidate_share) in
  let value := candidate.(copy_candidate_value) in
  let permission := candidate.(copy_candidate_permission) in
  let compatible_type := candidate.(copy_candidate_compatible) in
  let props := assignment.(props) in
  let locals := assignment.(locals) in
  let spatial := assignment.(spatial) in
  let post := constr:(PROPx $props (LOCALx $locals (SEPx $spatial))) in
  eapply semax_selfcopy_qualified_ram with (sh := $share) (owned := $object_type)
    (v := $value) (Q := $post);
  Control.dispatch
    [ (fun () => reflexivity); (fun () => exact $compatible_type);
      (fun () => reflexivity); (fun () => reflexivity);
      (fun () => exact $permission);
      (fun () => prove_selfcopy_checks addresses compatible same);
      (fun () => prove_selfcopy_ramification assignment addresses candidate) ].

Ltac2 disjoint_copy (assignment : assignment) (addresses : addresses) :=
  let specs := assignment.(specs) in
  let destination_pointer := addresses.(destination_pointer) in
  let source_pointer := addresses.(source_pointer) in
  let source := find_whole constr:(readable_share) assignment source_pointer in
  let destination := find_whole constr:(writable_share) assignment destination_pointer in
  let destination_type := destination.(copy_candidate_type) in
  let source_type := source.(copy_candidate_type) in
  let stored_compatible := copy_prove_type destination_type source_type in
  let destination_compatible := extract_compatibility destination_type destination_pointer in
  let source_compatible := extract_compatibility source_type source_pointer in
  let destination_share := destination.(copy_candidate_share) in
  let source_share := source.(copy_candidate_share) in
  let destination_permission := destination.(copy_candidate_permission) in
  let source_permission := source.(copy_candidate_permission) in
  let destination_compatible_type := destination.(copy_candidate_compatible) in
  let value := source.(copy_candidate_value) in
  let copied_value := Control.plus
    (fun () => constr:($value : @reptype $specs $destination_type))
    (fun _ => constr:(@copy_reptype $specs $destination_type $source_type $stored_compatible $value)) in
  let index := destination.(copy_candidate_index) in
  let spatial := assignment.(spatial) in
  let updated := constr:(replace_nth $index $spatial
    (@data_at $specs $destination_share $destination_type $copied_value $destination_pointer)) in
  let props := assignment.(props) in
  let locals := assignment.(locals) in
  let post := constr:(PROPx $props (LOCALx $locals (SEPx $updated))) in
  eapply semax_copy_qualified_ram with (sh1 := $destination_share) (sh2 := $source_share)
    (destination := $destination_type) (source := $source_type)
    (Hstored := $stored_compatible) (v := $value) (Q := $post);
  Control.dispatch
    [ (fun () => reflexivity); (fun () => exact $destination_compatible_type);
      (fun () => reflexivity); (fun () => reflexivity);
      (fun () => exact $destination_permission); (fun () => exact $source_permission);
      (fun () => prove_copy_checks addresses destination_compatible source_compatible);
      (fun () => prove_copy_ramification assignment addresses destination source) ].

(** Forward one whole object aggregate assignment. Try equal addresses
    with one writable predicate first, then separated source and
    destination predicates with readable and writable shares respectively.
    Discover [data_at] or [data_at_] by type and evaluated pointer, update
    the destination entry, and frame the other [SEP] entries. Type,
    completeness and alignment remain separate obligations. Candidates
    are selected only after their required permissions are proved. *)
Ltac2 run () :=
  Control.enter (fun () =>
    let assignment := read_assignment () in
    let addresses := evaluate_addresses assignment in
    Control.plus
      (fun () => selfcopy assignment addresses)
      (fun _ => disjoint_copy assignment addresses)).

End CopyForward.
