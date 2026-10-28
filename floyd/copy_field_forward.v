(** * Native automation for aggregate assignment through field paths.

    Discover enclosing typed ownership, project the source value, and
    rebuild the enclosing destination with its selected field updated.
    Unselected ownership is retained through ramification. *)
From Ltac2 Require Import Ltac2.
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.floyd.copy_forward.
Require Import VST.floyd.copy_rules.
Require Import VST.floyd.copy_discovery.
Require Import VST.floyd.copy_address.
Require Import VST.floyd.copy_field_ramify.
Require Import VST.floyd.copy_array_ramify.
Require Import VST.floyd.unfold_data_at.
Require Import VST.floyd.replace_refill_reptype_lemmas.

Import LiftNotation.
Local Open Scope logic.
Set Default Proof Mode "Classic".

Lemma copy_field_eq_rect_r_eq:
  forall (U: Type) (p: U) Q x h,
  @eq_rect_r U p Q x p h = x.
Proof.
  intros. unfold eq_rect_r. symmetry. apply eq_rect_eq.
Qed.

(** An enclosing type, selected path, and root pointer with a certificate
    of the expression type, evaluated field address, and lvalue checks. *)
Ltac2 Type copy_field_address := {
  copy_field_root_type : constr;
  copy_field_path : constr;
  copy_field_owned_path : constr;
  copy_field_relative_path : constr;
  copy_field_pointer : constr;
  copy_field_certificate : constr
}.

(** Original ownership and its value within the selected owned ancestor.
    Reconstruction retains the original predicate form. *)
Ltac2 Type copy_field_candidate := {
  copy_field_candidate_index : constr;
  copy_field_candidate_share : constr;
  copy_field_candidate_value : constr;
  copy_field_candidate_predicate : constr;
  copy_field_candidate_type : constr;
  copy_field_candidate_permission : constr
}.

Ltac2 copy_field_prove_compatibility () :=
  ltac1:(entailer!);
  repeat (rewrite field_compatible_cons);
  repeat (first [assumption | split]);
  try (vm_compute; auto);
  try (ltac1:(lia)).

(** Directly owned leaves may be rooted at an already computed field
    address. Their enclosing expression need not share the owned root. *)
Ltac2 copy_field_direct_normalize_addresses () :=
  repeat (
    match! goal with
    | [ |- context[field_address ?root ?path ?pointer] ] =>
        let compatible := CopyForward.prove_fact @COPY_FIELD_CURRENT_COMPATIBLE
          constr:(field_compatible $root $path $pointer)
          (fun () => assumption) in
        progress (rewrite (field_compatible_field_address $root $path $pointer $compatible))
    end);
  repeat (
    match! goal with
    | [ compatible : field_compatible _ _ (field_address ?root ?path ?pointer) |- _ ] =>
        let compatible := Control.hyp compatible in
        let name := Fresh.in_goal @COPY_FIELD_PARENT_COMPATIBLE in
        Std.pose (Some name) constr:(copy_field_address_parent_compatible _ _ _ _ _ $compatible);
        let parent := Control.hyp name in
        rewrite (field_compatible_field_address $root $path $pointer $parent) in *
    end);
  repeat (
    match! goal with
    | [ |- context[field_address ?root ?path ?pointer] ] =>
        let compatible := CopyForward.prove_fact @COPY_FIELD_CURRENT_COMPATIBLE
          constr:(field_compatible $root $path $pointer)
          (fun () => assumption) in
        progress (rewrite (field_compatible_field_address $root $path $pointer $compatible))
    end);
  ltac1:(autorewrite with norm in *);
  repeat (
    match! goal with
    | [ |- context surrounding [@nested_field_offset ?cs ?root ?path] ] =>
        let offset := eval vm_compute in (@nested_field_offset $cs $root $path) in
        let changed := Pattern.instantiate surrounding offset in
        progress (change $changed)
    end).

Ltac2 copy_field_direct_finish () :=
  copy_field_direct_normalize_addresses ();
  first
  [ ltac1:(congruence)
  | match! goal with
    | [ compatible : field_compatible _ _ ?pointer |- isptr ?requested_pointer ] =>
        Std.unify pointer requested_pointer;
        let compatible := Control.hyp compatible in
        exact (proj1 $compatible)
    end ].

Ltac2 copy_field_direct_address (locals : constr) (expression : constr) :=
  lazy_match! Constr.type locals with
  | local2ptree _ = (?temps, ?variables, nil, ?globals) =>
      lazy_match! goal with
      | [ |- ENTAIL ?delta, PROPx ?pure (LOCALx ?localdefs (SEPx ?spatial)) |-- _ ] =>
          let evaluated := open_constr:(_ : val) in
          let evaluation := CopyForward.prove_fact @COPY_FIELD_DIRECT_EVAL
            constr:(msubst_eval_lvalue $delta $temps $variables $globals $expression =
              Some $evaluated)
            (fun () => ltac1:(solve_msubst_eval_lvalue)) in
          let pre := constr:(PROPx $pure (LOCALx $localdefs (SEPx $spatial))) in
          let address := CopyForward.prove_fact @COPY_FIELD_DIRECT_ADDRESS
            constr:(local (tc_environ $delta) && $pre |--
              local (lift1 (eq $evaluated) (eval_lvalue $expression)))
            (fun () =>
              erewrite (local2ptree_soundness $pure $localdefs $spatial) by exact $locals;
              apply msubst_eval_lvalue_eq; exact $evaluation) in
          apply andp_right >
          [ apply prop_right; reflexivity
          | apply andp_right >
            [ rewrite (add_andp _ _ $address);
              ltac1:(go_lowerx); ltac1:(normalize); ltac1:(entailer!);
              Control.enter copy_field_direct_finish
            | ltac1:(entailer!);
              Control.enter copy_field_direct_finish ] ]
      end
  end.

(** Check one original spatial entry before selecting it. The address
    certificate keeps both the owned ancestor and the relative copy path. *)
Ltac2 copy_field_address_candidate (locals : constr) (permission : constr)
    (expression : constr) (predicate : constr) (index : constr)
    : copy_field_address * copy_field_candidate :=
  lazy_match! goal with
  | [ |- semax ?delta (|> (PROPx ?pure (LOCALx ?localdefs (SEPx ?spatial)))) _ _ ] =>
      let (cs, share, root, owned, value, pointer) :=
        lazy_match! predicate with
        | @data_at ?cs ?share ?root ?value ?pointer =>
            (cs, share, root, constr:(@nil gfield), value, pointer)
        | @data_at_ ?cs ?share ?root ?pointer =>
            (cs, share, root, constr:(@nil gfield),
              constr:(@default_val $cs $root), pointer)
        | @field_at ?cs ?share ?root ?owned ?value ?pointer =>
            (cs, share, root, owned, value, pointer)
        | @field_at_ ?cs ?share ?root ?owned ?pointer =>
            (cs, share, root, owned,
              constr:(@default_val $cs (@nested_field_type $cs $root $owned)), pointer)
        | _ => Control.zero Match_failure
        end in
      let permission := copy_prove_permission permission share in
      let path := open_constr:(_ : list gfield) in
      let relative := open_constr:(_ : list gfield) in
      let certificate := Fresh.in_goal @COPY_FIELD_ADDRESS in
      assert ($certificate :
        ENTAIL $delta, PROPx $pure (LOCALx $localdefs (SEPx $spatial)) |--
        !! (copy_type_compatible (typeof $expression)
          (nested_field_type $root $path) = true) &&
        (local (lift1 (eq (field_address $root $path $pointer))
          (eval_lvalue $expression)) && tc_lvalue $delta $expression))
        by (Control.once (fun () => Control.plus (fun () =>
          let address_root := open_constr:(_ : type) in
          eapply copy_lvalue_field_address_qualified with
            (n := $index) (sh := $share) (t_root := $root)
            (address_root := $address_root)
            (gfs0 := $owned) (gfs1 := $relative) (v := $value)
            (Rn := $predicate) >
          [ exact $locals
          | reflexivity
          | reflexivity
          | ltac1:(solve_msubst_eval_LR)
          | ltac1:(solve_msubst_efield_denote)
          | econstructor
          | ltac1:(solve_field_address_gen)
          | first [left; reflexivity | right; reflexivity]
          | reflexivity
          | apply derives_refl
          | lazy_match! goal with
            | [ |- ?full = _ ++ _ ] =>
                ltac1:(full |- prove_gfs_suffix full) (Ltac1.of_constr full)
            end
          | ltac1:(solve_legal_nested_field_in_entailment)
          | ltac1:(entailer_for_load_tac) ])
          (fun _ =>
            Std.unify path owned;
            Std.unify relative constr:(@nil gfield);
            copy_field_direct_address locals expression)));
      let root := eval hnf in $root in
      ({ copy_field_root_type := root;
        copy_field_path := path;
        copy_field_owned_path := owned;
        copy_field_relative_path := relative;
        copy_field_pointer := pointer;
        copy_field_certificate := Control.hyp certificate },
      { copy_field_candidate_index := index;
        copy_field_candidate_share := share;
        copy_field_candidate_value := value;
        copy_field_candidate_predicate := predicate;
        copy_field_candidate_type := constr:(@nested_field_type $cs $root $owned);
        copy_field_candidate_permission := permission })
  end.

(** Scan the caller list directly. Failed permissions, address checks or
    ancestor suffixes backtrack to the next original spatial entry. *)
Ltac2 rec copy_field_address_get_run (locals : constr) (permission : constr)
    (expression : constr) (spatial : constr) (index : constr)
    : copy_field_address * copy_field_candidate :=
  lazy_match! spatial with
  | @nil _ =>
      let message := Message.concat
        (Message.of_string "Aggregate field copy cannot prove ")
        (Message.concat (Message.of_constr permission)
          (Message.concat (Message.of_string " for ownership of lvalue ")
            (Message.of_constr expression))) in
      Control.zero (Tactic_failure (Some message))
  | @cons _ ?predicate ?tail =>
      Control.plus
        (fun () => copy_field_address_candidate locals permission expression predicate index)
        (fun _ => copy_field_address_get_run locals permission expression tail constr:(S $index))
  end.

Ltac2 copy_field_unfold_root (cs : constr) (share : constr)
    (root : constr) (pointer : constr) :=
  match! goal with
  | [ |- context [@data_at ?actual_cs ?actual_share ?stored ?value ?actual_pointer] ] =>
      Std.unify actual_cs cs;
      Std.unify actual_share share;
      Std.unify actual_pointer pointer;
      Std.unify stored root;
      let predicate := constr:(@data_at $cs $share $stored $value $pointer) in
      ltac1:(predicate |- unfold_data_at predicate) (Ltac1.of_constr predicate)
  | [ |- context [@data_at_ ?actual_cs ?actual_share ?stored ?actual_pointer] ] =>
      Std.unify actual_cs cs;
      Std.unify actual_share share;
      Std.unify actual_pointer pointer;
      Std.unify stored root;
      let predicate := constr:(@data_at_ $cs $share $stored $pointer) in
      ltac1:(predicate |- unfold_data_at predicate) (Ltac1.of_constr predicate)
  end.

Ltac2 copy_field_unfold_parent (cs : constr) (share : constr) (root : constr)
    (parent : constr) (pointer : constr) :=
  match! goal with
  | [ |- context [@field_at ?actual_cs ?actual_share ?stored ?actual ?value ?actual_pointer] ] =>
      Std.unify actual_cs cs;
      Std.unify actual_share share;
      Std.unify actual_pointer pointer;
      Std.unify stored root;
      Std.unify actual parent;
      let predicate := constr:(@field_at $cs $share $stored $actual $value $pointer) in
      ltac1:(predicate |- unfold_field_at predicate) (Ltac1.of_constr predicate)
  | [ |- context [@field_at_ ?actual_cs ?actual_share ?stored ?actual ?actual_pointer] ] =>
      Std.unify actual_cs cs;
      Std.unify actual_share share;
      Std.unify actual_pointer pointer;
      Std.unify stored root;
      Std.unify actual parent;
      let predicate := constr:(@field_at_ $cs $share $stored $actual $pointer) in
      ltac1:(predicate |- unfold_field_at predicate) (Ltac1.of_constr predicate)
  end.

Ltac2 copy_field_unfold_ancestor (cs : constr) (share : constr) (root : constr)
    (parent : constr) (pointer : constr) :=
  first
  [ copy_field_unfold_array_ancestor_run cs share root parent pointer
  | lazy_match! parent with
    | @nil _ => copy_field_unfold_root cs share root pointer
    | _ => copy_field_unfold_parent cs share root parent pointer
    end
  | () ].

Ltac2 rec copy_field_descend_ancestors (cs : constr) (share : constr)
    (root : constr) (remaining : constr) (parent : constr) (pointer : constr) :=
  lazy_match! remaining with
  | @nil _ => ()
  | @cons _ ?field ?tail =>
      copy_field_unfold_ancestor cs share root parent pointer;
      copy_field_descend_ancestors cs share root tail
        constr:($field :: $parent) pointer
  end.

(** Expose ancestors from the owned region to its selected field. Arrays use finite list
    decomposition, structures expose separate fields, and unions expose
    the member selected by their current representation. *)
Ltac2 copy_field_unfold_ancestors_run (cs : constr) (share : constr)
    (root : constr) (path : constr) (owned : constr) (pointer : constr) :=
  let reversed := eval cbv [rev app] in (rev $path) in
  copy_field_descend_ancestors cs share root reversed owned pointer.

Ltac2 copy_field_restore_addresses_run () :=
  repeat (
    match! goal with
    | [ equation : field_address _ _ _ = _ |- _ ] =>
        let equation := Control.hyp equation in
        progress (rewrite <- $equation)
    end).

Module CopyFieldValues.

Ltac2 reduce_casts (equation : ident) :=
  rewrite ?copy_field_eq_rect_r_eq, <- ?eq_rect_eq in $equation.

Ltac2 unfold_values (equation : ident) :=
  repeat (lazy_match! Constr.type (Control.hyp equation) with
  | context [@unfold_reptype ?cs ?t ?value] =>
      rewrite (JMeq_eq (@unfold_reptype_JMeq $cs $t $value)) in $equation
  end).

Ltac2 fold_values (equation : ident) :=
  repeat (lazy_match! Constr.type (Control.hyp equation) with
  | context [@fold_reptype ?cs ?t ?value] =>
      rewrite (JMeq_eq (@fold_reptype_JMeq $cs $t $value)) in $equation
  end).

(* Reduce the remembered expression separately from the result evar.
   Rewriting that evar can create a fresh cast evar at every step. *)
Ltac2 reduce_update () :=
  lazy_match! goal with
  | [ |- ?lhs = _ ] =>
      let computed := Fresh.in_goal @COPY_COMPUTED_VALUE in
      let equation := Fresh.in_goal @COPY_COMPUTED_EQUATION in
      remember $lhs as $computed eqn:$equation;
      rewrite ?copy_reptype_refl, ?copy_reptype_struct, ?copy_reptype_union in $equation;
      cbn [upd_reptype] in $equation;
      reduce_casts equation;
      unfold upd_gfield_reptype in $equation;
      unfold_values equation;
      reduce_casts equation;
      fold_values equation;
      cbn -[data_at field_address nested_field_type] in $equation;
      reduce_casts equation;
      subst $computed
  end.

Ltac2 simplify_updates () :=
  repeat (lazy_match! goal with
  | [ |- context [@upd_reptype ?cs ?t ?path ?old ?replacement] ] =>
      let update := constr:(@upd_reptype $cs $t $path $old $replacement) in
      let value_type := constr:(@reptype $cs $t) in
      let normalized := open_constr:(_ : $value_type) in
      let equation_name := Fresh.in_goal @COPY_UPDATED_VALUE_EQUATION in
      assert ($update = $normalized) as $equation_name by
        (reduce_update (); reflexivity);
      let equation := Control.hyp equation_name in
      rewrite $equation;
      clear $equation_name
  end).

Ltac2 simplify_projection (projection : ident) :=
  unfold eq_pose in $projection;
  unfold field_type_name_member in $projection;
  rewrite <- ?eq_rect_eq in $projection;
  repeat (lazy_match! Constr.type (Control.hyp projection) with
  | context [@proj_struct ?field ?members ?family ?value ?default] =>
      let result := Fresh.in_goal @COPY_PROJECTED_VALUE in
      let equation := Fresh.in_goal @COPY_PROJECTION_EQUATION in
      let projected := constr:(@proj_struct $field $members $family $value $default) in
      remember $projected as $result eqn:$equation;
      let computed_members := eval vm_compute in $members in
      let computed_default := eval vm_compute in $default in
      let result_value := Control.hyp result in
      let computed := constr:(@proj_struct $field $computed_members $family
        $value $computed_default) in
      change ($result_value = $computed) in $equation;
      ltac1:(equation |- cbv_proj_struct equation) (Ltac1.of_ident equation);
      subst $result
  | context surrounding [@proj_union ?field ?members ?family ?value ?default] =>
      let projected := constr:(@proj_union $field $members $family $value $default) in
      let computed := eval vm_compute in $projected in
      let changed := Pattern.instantiate surrounding computed in
      progress (change $changed in $projection)
  end).

End CopyFieldValues.

Module CopyFieldForward.

Ltac2 Type region := {
  address : copy_field_address;
  ownership : copy_field_candidate;
  compatible : constr
}.

Ltac2 Type operation := {
  assignment : CopyForward.assignment;
  destination : region;
  source : region;
  projection : constr;
  copied_value : constr;
  replacement : constr;
  stored_compatible : constr
}.

Ltac2 prove_compatibility () :=
  copy_field_prove_compatibility ().

Ltac2 extract_compatibility (cs : constr) (address : copy_field_address) :=
  let root := address.(copy_field_root_type) in
  let path := address.(copy_field_path) in
  let pointer := address.(copy_field_pointer) in
  let name := Fresh.in_goal @COPY_FIELD_COMPATIBLE in
  let proposition := constr:(@field_compatible $cs $root $path $pointer) in
  eapply (assert_later_PROP' $proposition);
  (* The later precondition must be fixed before proving compatibility. *)
  Control.dispatch
    [ (fun () => ());
      (fun () => ltac1:(hoist_later_left); apply derives_refl);
      (fun () => ()) ];
  Control.dispatch [prove_compatibility; (fun () => intro $name)];
  Control.hyp name.

Ltac2 discover_region (assignment : CopyForward.assignment) (locals : constr)
    (permission : constr) (expression : constr) : region :=
  let (address, candidate) := Control.once (fun () =>
    copy_field_address_get_run locals permission expression
      (assignment.(CopyForward.spatial)) constr:(O)) in
  { address := address; ownership := candidate;
    compatible := extract_compatibility (assignment.(CopyForward.specs)) address }.

Ltac2 project_source (cs : constr) (source : region) : constr * constr :=
  let address := source.(address) in
  let root := source.(ownership).(copy_field_candidate_type) in
  let path := address.(copy_field_relative_path) in
  let value := source.(ownership).(copy_field_candidate_value) in
  let name := Fresh.in_goal @COPY_PROJECT in
  ltac1:(cs root path value name |- pose_proj_reptype cs root path value name)
    (Ltac1.of_constr cs) (Ltac1.of_constr root) (Ltac1.of_constr path)
    (Ltac1.of_constr value) (Ltac1.of_ident name);
  CopyFieldValues.simplify_projection name;
  let projection := Control.hyp name in
  lazy_match! Constr.type projection with
  | _ = ?value => (projection, value)
  end.

Ltac2 current_post (assignment : CopyForward.assignment) (spatial : constr) :=
  let props := assignment.(CopyForward.props) in
  let locals := assignment.(CopyForward.locals) in
  constr:(PROPx $props (LOCALx $locals (SEPx $spatial))).

Ltac2 updated_value (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  let destination := operation.(destination) in
  let root := destination.(ownership).(copy_field_candidate_type) in
  let path := destination.(address).(copy_field_relative_path) in
  let old := destination.(ownership).(copy_field_candidate_value) in
  let value := operation.(replacement) in
  constr:(@upd_reptype $cs $root $path $old $value).

Ltac2 enclosing_predicate (cs : constr) (region : region) (value : constr) :=
  let share := region.(ownership).(copy_field_candidate_share) in
  let root := region.(address).(copy_field_root_type) in
  let owned := region.(address).(copy_field_owned_path) in
  let pointer := region.(address).(copy_field_pointer) in
  let original := region.(ownership).(copy_field_candidate_predicate) in
  lazy_match! original with
  | @data_at _ _ _ _ _ => constr:(@data_at $cs $share $root $value $pointer)
  | @data_at_ _ _ _ _ => constr:(@data_at $cs $share $root $value $pointer)
  | _ => constr:(@field_at $cs $share $root $owned $value $pointer)
  end.

Ltac2 updated_post (operation : operation) :=
  let assignment := operation.(assignment) in
  let destination := operation.(destination) in
  let cs := assignment.(CopyForward.specs) in
  let index := destination.(ownership).(copy_field_candidate_index) in
  let predicate := enclosing_predicate cs destination (updated_value operation) in
  let spatial := assignment.(CopyForward.spatial) in
  current_post assignment constr:(replace_nth $index $spatial $predicate).

Ltac2 select_address_fact (address : copy_field_address) :=
  let certificate := address.(copy_field_certificate) in
  eapply derives_trans >
  [ exact $certificate
  | intro rho; cbn; ltac1:(solve_andp) ].

Ltac2 prove_lvalue_types (operation : operation) :=
  apply andp_right >
  [ select_address_fact (operation.(destination).(address))
  | select_address_fact (operation.(source).(address)) ].

Ltac2 prove_alignment (region : region) :=
  let compatible := region.(compatible) in
  eapply copy_alignment_lvalue >
  [ select_address_fact (region.(address))
  | rewrite field_compatible_field_address by exact $compatible;
    let child := Fresh.in_goal @COPY_CHILD_COMPATIBLE in
    Std.pose (Some child) constr:(field_compatible_nested_field _ _ _ $compatible);
    CopyForward.solve_alignment (Control.hyp child) ].

Ltac2 lower_addresses (operation : operation) :=
  let destination := operation.(destination).(address).(copy_field_certificate) in
  let source := operation.(source).(address).(copy_field_certificate) in
  rewrite (add_andp _ _ $destination), (add_andp _ _ $source);
  ltac1:(go_lowerx);
  ltac1:(normalize);
  copy_field_restore_addresses_run ().

Ltac2 prove_same_address (operation : operation) :=
  lower_addresses operation;
  ltac1:(entailer!).

Ltac2 prove_selfcopy_checks (operation : operation) :=
  apply andp_right >
  [ apply andp_right >
    [ prove_lvalue_types operation
    | prove_same_address operation ]
  | prove_alignment (operation.(destination)) ].

Ltac2 prove_copy_checks (operation : operation) :=
  apply andp_right >
  [ apply andp_right >
    [ prove_lvalue_types operation
    | prove_alignment (operation.(destination)) ]
  | prove_alignment (operation.(source)) ].

Ltac2 unfold_region (cs : constr) (region : region) :=
  let share := region.(ownership).(copy_field_candidate_share) in
  let address := region.(address) in
  copy_field_unfold_ancestors_run cs share (address.(copy_field_root_type))
    (address.(copy_field_relative_path)) (address.(copy_field_owned_path))
    (address.(copy_field_pointer)).

Ltac2 cancel_fields () :=
  rewrite ?field_at__data_at_, ?field_at_data_at;
  Control.plus
    (fun () => solve [ltac1:(cancel)])
    (fun _ => copy_field_direct_normalize_addresses (); solve [ltac1:(cancel)]).

(** Empty owned paths retain the original pointer when descendants are
    rerooted through [field_address]. *)
Ltac2 copy_field_canonicalize_whole () :=
  repeat (
    match! goal with
    | [ |- context surrounding [@field_at ?cs ?share ?root nil ?value ?pointer] ] =>
        let changed := Pattern.instantiate surrounding
          constr:(@data_at $cs $share $root $value $pointer) in
        progress (change $changed)
    | [ |- context surrounding [@field_at_ ?cs ?share ?root nil ?pointer] ] =>
        let changed := Pattern.instantiate surrounding
          constr:(@data_at_ $cs $share $root $pointer) in
        progress (change $changed)
    end).

(* The existing cancellation tactic recognizes a named frame definition. *)
Ltac2 make_frame () :=
  let name := Fresh.in_goal @COPY_FRAME in
  let value := open_constr:(_ : list mpred) in
  Std.pose (Some name) value;
  (name, Control.hyp name).

Ltac2 selfcopy_frame (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  lower_addresses operation;
  let (frame_name, frame) := make_frame () in
  eapply RAMIF_PLAIN.solve with (F := fold_right_sepcon $frame) >
  [ apply andp_left1;
    unfold_region cs (operation.(source));
    cbn [fold_right_sepcon]; cancel_fields ()
  | subst $frame_name;
    unfold_region cs (operation.(source));
    cbn [fold_right_sepcon]; cancel_fields () ].

Ltac2 unfold_both_regions (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  unfold_region cs (operation.(destination));
  unfold_region cs (operation.(source));
  cancel_fields ().

Ltac2 same_enclosing_frame (operation : operation) :=
  let (frame_name, frame) := make_frame () in
  eapply RAMIF_PLAIN.solve with (F := fold_right_sepcon $frame) >
  [ apply andp_left1; unfold_both_regions operation
  | subst $frame_name;
    CopyFieldValues.simplify_updates (); unfold_both_regions operation ].

Ltac2 source_update_identity (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  let source := operation.(source) in
  let root := source.(ownership).(copy_field_candidate_type) in
  let path := source.(address).(copy_field_relative_path) in
  let value := source.(ownership).(copy_field_candidate_value) in
  let projection := operation.(projection) in
  CopyForward.prove_fact @COPY_SOURCE_UNCHANGED
    constr:(@upd_reptype $cs $root $path $value
      (@proj_reptype $cs $root $path $value) = $value)
    (fun () =>
      rewrite $projection;
      CopyFieldValues.reduce_update ();
      reflexivity).

Ltac2 enclosing_pair_frame () :=
  let (frame_name, frame) := make_frame () in
  eapply RAMIF_PLAIN.solve with (F := fold_right_sepcon $frame) >
  [ apply andp_left1; rewrite ?field_at__data_at_, ?field_at_data_at; solve [ltac1:(cancel)]
  | subst $frame_name;
    CopyFieldValues.simplify_updates ();
    cbn [fold_right_sepcon]; rewrite ?field_at__data_at_, ?field_at_data_at;
    solve [ltac1:(cancel)] ].

Ltac2 distinct_fields_frame (operation : operation) (unchanged : constr) :=
  let destination := operation.(destination) in
  let source := operation.(source) in
  let cs := operation.(assignment).(CopyForward.specs) in
  let destination_root := destination.(address).(copy_field_root_type) in
  let destination_owned := destination.(address).(copy_field_owned_path) in
  let destination_path := destination.(address).(copy_field_relative_path) in
  let destination_pointer := destination.(address).(copy_field_pointer) in
  let source_root := source.(address).(copy_field_root_type) in
  let source_owned := source.(address).(copy_field_owned_path) in
  let source_path := source.(address).(copy_field_relative_path) in
  let source_pointer := source.(address).(copy_field_pointer) in
  let destination_compatible := destination.(compatible) in
  let source_compatible := source.(compatible) in
  let projection := operation.(projection) in
  let destination_address := constr:(@field_address_app $cs $destination_root
    $destination_owned $destination_path $destination_pointer) in
  let source_address := constr:(@field_address_app $cs $source_root
    $source_owned $source_path $source_pointer) in
  eapply derives_trans >
  [ eapply (@separate_field_regions_ramify_replacement $cs)
      with (root1 := $destination_root) (owned1 := $destination_owned)
        (path1 := $destination_path) (p1 := $destination_pointer)
        (root2 := $source_root) (owned2 := $source_owned)
        (path2 := $source_path) (p2 := $source_pointer) >
    [ exact $destination_compatible
    | exact $source_compatible
    | exact $unchanged ]
  | copy_field_canonicalize_whole ();
    rewrite ?field_at_data_at;
    rewrite <- ?($destination_address), <- ?($source_address);
    rewrite $projection;
    apply sepcon_derives >
    [ apply sepcon_derives > [apply data_at_data_at_ | apply derives_refl]
    | apply derives_refl ] ].

Ltac2 distinct_enclosing_frame (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  let destination := operation.(destination) in
  let source := operation.(source) in
  let destination_old := destination.(ownership).(copy_field_candidate_value) in
  let source_old := source.(ownership).(copy_field_candidate_value) in
  let destination_before := enclosing_predicate cs destination destination_old in
  let destination_after := enclosing_predicate cs destination (updated_value operation) in
  let source_predicate := enclosing_predicate cs source source_old in
  let unchanged := source_update_identity operation in
  eapply RAMIF_PLAIN.trans with
    (m := $destination_before * $source_predicate)
    (m' := $destination_after * $source_predicate) >
  [ enclosing_pair_frame () | distinct_fields_frame operation unchanged ].

Ltac2 disjoint_frame (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  let destination := operation.(destination) in
  let source := operation.(source) in
  let destination_root := destination.(ownership).(copy_field_candidate_type) in
  let destination_path := destination.(address).(copy_field_relative_path) in
  let source_root := source.(ownership).(copy_field_candidate_type) in
  let source_path := source.(address).(copy_field_relative_path) in
  let compatible := operation.(stored_compatible) in
  let value := operation.(copied_value) in
  Control.plus
    (fun () =>
      let equality := constr:(JMeq_eq (@copy_reptype_JMeq $cs
        (@nested_field_type $cs $destination_root $destination_path)
        (@nested_field_type $cs $source_root $source_path) $compatible $value)) in
      rewrite $equality)
    (fun _ => ());
  CopyFieldValues.simplify_updates ();
  lower_addresses operation;
  let source_index := operation.(source).(ownership).(copy_field_candidate_index) in
  let destination_index := operation.(destination).(ownership).(copy_field_candidate_index) in
  if Constr.equal source_index destination_index then same_enclosing_frame operation
  else distinct_enclosing_frame operation.

Ltac2 selfcopy (operation : operation) :=
  let cs := operation.(assignment).(CopyForward.specs) in
  let destination := operation.(destination).(address) in
  let source := operation.(source).(address) in
  let destination_root := destination.(copy_field_root_type) in
  let destination_path := destination.(copy_field_path) in
  let destination_pointer := destination.(copy_field_pointer) in
  let source_root := source.(copy_field_root_type) in
  let source_path := source.(copy_field_path) in
  let source_pointer := source.(copy_field_pointer) in
  let _ := CopyForward.prove_fact @COPY_SAME_FIELD
    constr:(@field_address $cs $destination_root $destination_path $destination_pointer =
      @field_address $cs $source_root $source_path $source_pointer)
    (fun () => ltac1:(congruence)) in
  let share := operation.(source).(ownership).(copy_field_candidate_share) in
  let permission := operation.(source).(ownership).(copy_field_candidate_permission) in
  let value := operation.(copied_value) in
  let assignment := operation.(assignment) in
  let post := current_post assignment (assignment.(CopyForward.spatial)) in
  eapply semax_selfcopy_qualified_ram with (sh := $share) (v := $value) (Q := $post) >
  [ reflexivity | reflexivity | reflexivity | reflexivity | exact $permission
  | prove_selfcopy_checks operation | selfcopy_frame operation ].

Ltac2 disjoint_copy (operation : operation) :=
  let destination_share := operation.(destination).(ownership).(copy_field_candidate_share) in
  let source_share := operation.(source).(ownership).(copy_field_candidate_share) in
  let destination_permission := operation.(destination).(ownership).(copy_field_candidate_permission) in
  let source_permission := operation.(source).(ownership).(copy_field_candidate_permission) in
  let value := operation.(copied_value) in
  let compatible := operation.(stored_compatible) in
  let cs := operation.(assignment).(CopyForward.specs) in
  let destination := operation.(destination) in
  let destination_root := destination.(ownership).(copy_field_candidate_type) in
  let destination_path := destination.(address).(copy_field_relative_path) in
  let destination_type := constr:(@nested_field_type $cs $destination_root $destination_path) in
  let post := updated_post operation in
  eapply semax_copy_qualified_ram with (sh1 := $destination_share) (sh2 := $source_share)
    (destination := $destination_type) (Hstored := $compatible) (v := $value) (Q := $post) >
  [ reflexivity | reflexivity | reflexivity | reflexivity
  | exact $destination_permission | exact $source_permission
  | prove_copy_checks operation | disjoint_frame operation ].

Ltac2 prepare_operation (self : bool) : operation :=
  let assignment := CopyForward.read_assignment () in
  let locals := CopyForward.prove_local_tree assignment in
  let destination := discover_region assignment locals constr:(writable_share)
    (assignment.(CopyForward.destination_expr)) in
  let permission := if self then constr:(writable_share) else constr:(readable_share) in
  let source := discover_region assignment locals permission
    (assignment.(CopyForward.source_expr)) in
  let (projection, value) := project_source (assignment.(CopyForward.specs)) source in
  let cs := assignment.(CopyForward.specs) in
  let destination_root := destination.(ownership).(copy_field_candidate_type) in
  let destination_path := destination.(address).(copy_field_relative_path) in
  let source_root := source.(ownership).(copy_field_candidate_type) in
  let source_path := source.(address).(copy_field_relative_path) in
  let destination_type := constr:(@nested_field_type $cs $destination_root $destination_path) in
  let source_type := constr:(@nested_field_type $cs $source_root $source_path) in
  let compatible := copy_prove_type destination_type source_type in
  let replacement := Control.plus
    (fun () => constr:($value : @reptype $cs $destination_type))
    (fun _ => constr:(@copy_reptype $cs $destination_type $source_type $compatible $value)) in
  { assignment := assignment; source := source; destination := destination;
    projection := projection; copied_value := value; replacement := replacement;
    stored_compatible := compatible }.

(** Forward a canonical aggregate assignment through structure, array,
    and selected union paths in original typed whole or field ownership. Try
    equal field addresses with one writable region first. Otherwise
    require separated readable source and writable destination fields,
    including fields within one enclosing object. Reconstruct only the
    destination value and frame the remaining ownership. Reject paths
    whose ownership, selected union representation, array decomposition,
    source restoration identity, or copy checks cannot be proved. *)
Ltac2 run () :=
  Control.enter (fun () =>
    Control.plus
      (fun () => selfcopy (prepare_operation true))
      (fun _ => disjoint_copy (prepare_operation false))).

End CopyFieldForward.
