(** * Ramified bitfield store rules and native Ltac2 automation. *)

From Ltac2 Require Import Ltac2.
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.field_compat.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.floyd.copy_discovery.
Require Import VST.veric.bitfield.

Import LiftNotation.
Import compcert.lib.Maps.
Local Open Scope logic.
Set Default Proof Mode "Classic".

Section BitfieldForward.
Context {cs: compspecs} {Espec: OracleKind}.

(** An initialized carrier [data_at] is its field compatibility fact
    together with whole-carrier [mapsto]. [JMeq] relates the value to
    the dependent representation selected by the carrier size. *)
Lemma bitfield_carrier_data_at: forall sz sh v (rv: reptype (bitfield_carrier_type sz)) p,
  JMeq v rv ->
  data_at sh (bitfield_carrier_type sz) rv p =
    !! field_compatible (bitfield_carrier_type sz) nil p &&
    mapsto sh (bitfield_carrier_type sz) p v.
Proof.
  intros sz sh v rv p VALUE.
  assert (BY_VALUE: type_is_by_value (bitfield_carrier_type sz) = true)
    by (destruct sz; reflexivity).
  apply pred_ext.
  - assert_PROP (field_compatible (bitfield_carrier_type sz) nil p) by entailer!.
    rewrite <- (mapsto_data_at' sh (bitfield_carrier_type sz) v rv p) by
      auto using bitfield_carrier_nonvolatile.
    entailer!.
  - normalize.
    rewrite (mapsto_data_at' sh (bitfield_carrier_type sz) v rv p) by
      auto using bitfield_carrier_nonvolatile.
    apply derives_refl.
Qed.

(** Assign a nonvolatile struct or union bitfield using writable
    [mapsto] ownership of its initialized unsigned carrier. Descriptor
    bounds must fit the field in the carrier. The first entailment
    supplies root typechecking and the cast integer, the second supplies
    the old carrier and a wand from the normalized inserted carrier
    to [Q].

    The proof exposes these two obligations under later, identifies the
    cast result expected by the primitive store rule, then consumes
    the returned carrier with the ramification wand. *)
Lemma semax_store_bitfield_ram:
  forall Delta root field rhs delta sz sg pos width attr sh carrier new_value P Q,
  bitfield_field cenv_cs (typeof root) field delta (Bits sz sg pos width) ->
  0 <= pos -> 0 < width <= bitsize_intsize sz ->
  pos + width <= Cop.bitsize_carrier sz ->
  attr_volatile attr = false -> writable_share sh ->
  let target_type := Tint sz (if zlt width (bitsize_intsize sz) then Signed else sg) attr in
  let inserted := Val.load_result (Cop.chunk_for_carrier sz)
    (Vint (Int.bitfield_insert (Cop.first_bit sz pos width) width carrier new_value)) in
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta root && tc_expr Delta (Ecast rhs target_type) &&
    local (`(eq (Vint new_value)) (eval_expr (Ecast rhs target_type)))) ->
  (local (tc_environ Delta) && P |--
    `(fun p => mapsto sh (bitfield_carrier_type sz) p (Vint carrier))
      (`(offset_val delta) (eval_lvalue root)) *
    (`(fun p => mapsto sh (bitfield_carrier_type sz) p inserted)
      (`(offset_val delta) (eval_lvalue root)) -* Q)) ->
  semax Delta (|> P) (Sassign (Efield root field target_type) rhs)
    (normal_ret_assert Q).
Proof.
  intros Delta root field rhs delta sz sg pos width attr sh carrier new_value P Q
    FIELD POS WIDTH RANGE NONVOL WRITE target_type inserted CHECK RAM.

  (* ===== Setup: retain checks and carrier ramification under later ===== *)

  eapply semax_pre with
    (|> (tc_lvalue Delta root && tc_expr Delta (Ecast rhs target_type) &&
      local (`(eq (Vint new_value)) (eval_expr (Ecast rhs target_type))) &&
      (`(fun p => mapsto sh (bitfield_carrier_type sz) p (Vint carrier))
        (`(offset_val delta) (eval_lvalue root)) *
       (`(fun p => mapsto sh (bitfield_carrier_type sz) p inserted)
         (`(offset_val delta) (eval_lvalue root)) -* Q)))).
  - apply later_ENTAIL.
    apply andp_right; assumption.
  - (* The cast expression denotes the integer for the primitive rule. *)
    eapply semax_pre with
      (|> (tc_lvalue Delta root && tc_expr Delta (Ecast rhs target_type) &&
         local (fun rho => force_val
           (sem_cast (typeof rhs) target_type (eval_expr rhs rho)) = Vint new_value) &&
         ((fun rho => mapsto sh (bitfield_carrier_type sz)
            (offset_val delta (eval_lvalue root rho)) (Vint carrier)) *
          (`(fun p => mapsto sh (bitfield_carrier_type sz) p inserted)
            (`(offset_val delta) (eval_lvalue root)) -* Q)))).
    + intro rho.
      cbn.
      apply andp_left2.
      apply later_derives.
      unfold local, lift1.
      unfold_lift.
      cbn [eval_expr eval_cast force_val1].
      normalize.
      entailer!.
    + (* ===== Closeout: consume the inserted carrier with the wand ===== *)

      eapply semax_post'.
      { intro rho.
        cbn.
        apply andp_left2.
        apply modus_ponens_wand. }
      eapply semax_store_bitfield; eauto.
Qed.

(** The ramified store rule for initialized carrier [data_at]. The two
    [JMeq] premises identify the old and normalized inserted integer
    representations. The same descriptor bounds, nonvolatile target,
    writable share and cast checks as the [mapsto] rule are required.

    The proof exposes field compatibility in the old [data_at], then
    converts the updated [mapsto] back to [data_at] at the same address
    before using the supplied ramification wand. *)
Lemma semax_store_bitfield_data_at_ram:
  forall Delta root field rhs delta sz sg pos width attr sh carrier new_value
    (old_value new_carrier_value: reptype (bitfield_carrier_type sz)) P Q,
  bitfield_field cenv_cs (typeof root) field delta (Bits sz sg pos width) ->
  0 <= pos -> 0 < width <= bitsize_intsize sz ->
  pos + width <= Cop.bitsize_carrier sz ->
  attr_volatile attr = false -> writable_share sh ->
  JMeq (Vint carrier) old_value ->
  JMeq (Val.load_result (Cop.chunk_for_carrier sz)
    (Vint (Int.bitfield_insert (Cop.first_bit sz pos width) width carrier new_value)))
    new_carrier_value ->
  let target_type := Tint sz (if zlt width (bitsize_intsize sz) then Signed else sg) attr in
  (local (tc_environ Delta) && P |--
    tc_lvalue Delta root && tc_expr Delta (Ecast rhs target_type) &&
    local (`(eq (Vint new_value)) (eval_expr (Ecast rhs target_type)))) ->
  (local (tc_environ Delta) && P |--
    `(data_at sh (bitfield_carrier_type sz) old_value)
      (`(offset_val delta) (eval_lvalue root)) *
    (`(data_at sh (bitfield_carrier_type sz) new_carrier_value)
      (`(offset_val delta) (eval_lvalue root)) -* Q)) ->
  semax Delta (|> P) (Sassign (Efield root field target_type) rhs)
    (normal_ret_assert Q).
Proof.
  intros Delta root field rhs delta sz sg pos width attr sh carrier new_value
    old_value new_carrier_value P Q FIELD POS WIDTH RANGE NONVOL WRITE OLD NEW
    target_type CHECK RAM.

  (* ===== Setup: reduce to the rule for whole-carrier mapsto ===== *)

  eapply semax_store_bitfield_ram with
    (carrier := carrier) (new_value := new_value); eauto.
  eapply derives_trans.
  { exact RAM. }
  intro rho.
  unfold local, lift1.
  unfold_lift.
  cbn.
  rewrite (bitfield_carrier_data_at sz sh (Vint carrier) old_value) by auto.
  normalize.

  (* ===== Closeout: recover data_at at the compatible carrier address ===== *)

  rewrite (mapsto_data_at' sh (bitfield_carrier_type sz)
    (Val.load_result (Cop.chunk_for_carrier sz)
      (Vint (Int.bitfield_insert (Cop.first_bit sz pos width) width carrier new_value)))
    new_carrier_value
    (offset_val delta (eval_lvalue root rho))) by
    (auto using bitfield_carrier_nonvolatile; destruct sz; reflexivity).
  apply derives_refl.
Qed.

End BitfieldForward.

Module BitfieldStore.

(** A computed member descriptor records the byte offset and the four
    parameters of the CompCert [Bits] descriptor. *)
Ltac2 Type descriptor := {
  byte_offset : constr;
  carrier_size : constr;
  field_sign : constr;
  bit_position : constr;
  bit_width : constr
}.

(** A selected initialized [data_at] records its position in [SEP], its
    ownership share, proved writability and whole-carrier integer. *)
Ltac2 Type carrier := {
  index : constr;
  share : constr;
  integer : constr;
  permission : constr
}.

(** The canonical assignment view retains the composite specifications,
    typing context, assertion lists and direct field assignment. *)
Ltac2 Type assignment := {
  specs : constr;
  delta : constr;
  props : constr;
  locals : constr;
  spatial : constr;
  root : constr;
  field : constr;
  target_type : constr;
  rhs : constr
}.

(** Symbolic evaluation supplies the root address and cast integer,
    with entailments connecting them to the current assertion. *)
Ltac2 Type symbolic_values := {
  pointer : constr;
  new_integer : constr;
  root_address : constr;
  cast_value : constr
}.

Ltac2 reject (message : string) :=
  Control.zero (Tactic_failure (Some (Message.of_string message))).

Ltac2 read_assignment () : assignment :=
  lazy_match! goal with
  | [ |- @semax ?cs _ ?delta
      (|> (PROPx ?props (LOCALx ?locals (SEPx ?spatial))))
      (Sassign (Efield ?root ?field ?target_type) ?rhs) _ ] =>
      { specs := cs; delta := delta; props := props; locals := locals;
        spatial := spatial; root := root; field := field;
        target_type := target_type; rhs := rhs }
  | [ |- _ ] => reject "Bitfield store requires a canonical field assignment"
  end.

Ltac2 read_descriptor (cs : constr) (root_type : constr) (field : constr) : descriptor :=
  let root_type := eval hnf in $root_type in
  let (id, is_union) :=
    lazy_match! root_type with
    | Tstruct ?id _ => (id, false)
    | Tunion ?id _ => (id, true)
    | _ => reject "Bitfield store requires a struct or union root"
    end in
  let lookup := eval hnf in ((@cenv_cs $cs) ! $id) in
  let composite :=
    lazy_match! lookup with
    | Some ?composite => composite
    | _ => reject "Bitfield store cannot find its composite descriptor"
    end in
  let location :=
    if is_union then
      eval vm_compute in
        (Ctypes.union_field_offset (@cenv_cs $cs) $field (co_members $composite))
    else
      eval vm_compute in
        (Ctypes.field_offset (@cenv_cs $cs) $field (co_members $composite)) in
  lazy_match! location with
  | Errors.OK (?offset, Bits ?sz ?sg ?pos ?width) =>
      { byte_offset := offset; carrier_size := sz; field_sign := sg;
        bit_position := pos; bit_width := width }
  | _ => reject "Bitfield store requires a Bits field descriptor"
  end.

Ltac2 rec find_carrier (predicates : constr) (requested_type : constr)
    (requested_pointer : constr) (index : constr) : carrier :=
  lazy_match! predicates with
  | @nil _ => copy_missing_region constr:(writable_share) requested_type requested_pointer
  | @cons _ ?predicate ?tail =>
      Control.plus
          (fun () =>
            lazy_match! predicate with
            | @data_at _ ?share ?stored_type ?value ?pointer =>
                Std.unify stored_type requested_type;
                Std.unify pointer requested_pointer;
                let permission := copy_prove_permission constr:(writable_share) share in
                lazy_match! value with
                | Vint ?integer =>
                    { index := index; share := share; integer := integer; permission := permission }
                | _ => Control.zero Match_failure
                end
            | _ => Control.zero Match_failure
            end)
          (fun _ => find_carrier tail requested_type requested_pointer constr:(S $index))
  end.

Ltac2 prove_fact (name : ident) (proposition : constr) (proof : unit -> unit) : constr :=
  let name := Fresh.in_goal name in
  Std.assert (Std.AssertType
    (Some (Std.IntroNaming (Std.IntroIdentifier name))) proposition (Some proof));
  Control.hyp name.

Ltac2 evaluate_symbolic_values (assignment : assignment) : symbolic_values :=
  let delta := assignment.(delta) in
  let props := assignment.(props) in
  let locals := assignment.(locals) in
  let spatial := assignment.(spatial) in
  let root := assignment.(root) in
  let rhs := assignment.(rhs) in
  let target_type := assignment.(target_type) in
  let temps := open_constr:(_ : PTree.t val) in
  let variables := open_constr:(_ : PTree.t (type * val)) in
  let globals := open_constr:(_ : option globals) in
  let local_tree := prove_fact @BITFIELD_LOCALS
    constr:(local2ptree $locals = ($temps, $variables, nil, $globals))
    (fun () => ltac1:(prove_local2ptree)) in
  let pointer := open_constr:(_ : val) in
  let value := open_constr:(_ : val) in
  let root_value := prove_fact @BITFIELD_ROOT
    constr:(msubst_eval_lvalue $delta $temps $variables $globals $root = Some $pointer)
    (fun () => ltac1:(solve_msubst_eval_lvalue)) in
  let expression_value := prove_fact @BITFIELD_CAST
    constr:(msubst_eval_expr $delta $temps $variables $globals
      (Ecast $rhs $target_type) = Some $value)
    (fun () => ltac1:(solve_msubst_eval_expr)) in
  let value := eval hnf in $value in
  let new_integer :=
    lazy_match! value with
    | Vint ?integer => integer
    | _ => reject "Bitfield store requires an integer cast result"
    end in
  let pre := constr:(PROPx $props (LOCALx $locals (SEPx $spatial))) in
  let root_address := prove_fact @BITFIELD_ROOT_ADDRESS
    constr:(local (tc_environ $delta) && $pre |--
      local (`(eq $pointer) (eval_lvalue $root)))
    (fun () =>
      erewrite (local2ptree_soundness $props $locals $spatial) by exact $local_tree;
      apply msubst_eval_lvalue_eq;
      exact $root_value) in
  let cast_value := prove_fact @BITFIELD_CAST_VALUE
    constr:(local (tc_environ $delta) && $pre |--
      local (`(eq $value) (eval_expr (Ecast $rhs $target_type))))
    (fun () =>
      erewrite (local2ptree_soundness $props $locals $spatial) by exact $local_tree;
      apply msubst_eval_expr_eq;
      exact $expression_value) in
  { pointer := pointer; new_integer := new_integer;
    root_address := root_address; cast_value := cast_value }.

Ltac2 carrier_pointer (offset : constr) (pointer : constr) : constr :=
  lazy_match! offset with
  | Z0 => pointer
  | _ => constr:(offset_val $offset $pointer)
  end.

Ltac2 apply_store_rule (assignment : assignment) (descriptor : descriptor)
    (carrier : carrier) (values : symbolic_values) (carrier_type : constr)
    (carrier_pointer : constr) :=
  let offset := descriptor.(byte_offset) in
  let sz := descriptor.(carrier_size) in
  let sg := descriptor.(field_sign) in
  let pos := descriptor.(bit_position) in
  let width := descriptor.(bit_width) in
  let target_type := assignment.(target_type) in
  let attr :=
    let target := eval hnf in $target_type in
    lazy_match! target with
    | Tint _ _ ?attr => attr
    | _ => reject "Bitfield store requires an integer target type"
    end in
  let share := carrier.(share) in
  let old_integer := carrier.(integer) in
  let new_integer := values.(new_integer) in
  let index := carrier.(index) in
  let spatial := assignment.(spatial) in
  let updated_value := eval cbv [Cop.chunk_for_carrier Val.load_result] in
    (Val.load_result (Cop.chunk_for_carrier $sz)
      (Vint (Int.bitfield_insert (Cop.first_bit $sz $pos $width)
        $width $old_integer $new_integer))) in
  let updated := constr:(replace_nth $index $spatial
    (data_at $share $carrier_type $updated_value $carrier_pointer)) in
  let props := assignment.(props) in
  let locals := assignment.(locals) in
  let post := constr:(PROPx $props (LOCALx $locals (SEPx $updated))) in
  eapply semax_store_bitfield_data_at_ram with
    (delta := $offset) (sz := $sz) (sg := $sg) (pos := $pos) (width := $width)
    (attr := $attr) (sh := $share) (carrier := $old_integer)
    (new_value := $new_integer) (old_value := Vint $old_integer)
    (new_carrier_value := $updated_value) (Q := $post).

Ltac2 prove_store_premises (assignment : assignment) (carrier : carrier)
    (values : symbolic_values) :=
  let cast_value := values.(cast_value) in
  let root_address := values.(root_address) in
  let index := carrier.(index) in
  let spatial := assignment.(spatial) in
  let permission := carrier.(permission) in
  let bounds := fun () =>
    cbn [bitsize_intsize Cop.bitsize_carrier]; ltac1:(lia) in
  Control.dispatch
    [ (fun () => unfold bitfield_field; eexists; split; reflexivity);
      bounds; bounds; bounds;
      (fun () => reflexivity);
      (fun () => exact $permission);
      (fun () => apply JMeq_refl);
      (fun () => apply JMeq_refl);
      (fun () =>
        apply andp_right;
        Control.dispatch
          [ (fun () => apply andp_right; Control.enter (fun () => ltac1:(entailer!)));
            (fun () => exact $cast_value) ]);
      (fun () =>
        let remainder := eval cbn [replace_nth] in (replace_nth $index $spatial emp) in
        let frame_name := Fresh.in_goal @COPY_FRAME in
        Std.pose (Some frame_name) constr:(fold_right_sepcon $remainder);
        rewrite (add_andp _ _ $root_address);
        ltac1:(go_lowerx);
        ltac1:(normalize);
        let frame := Control.hyp frame_name in
        eapply RAMIF_PLAIN.solve with (F := $frame);
        Control.enter (fun () =>
          ltac1:(frame_name |- unfold frame_name) (Ltac1.of_ident frame_name);
          unfold fold_right_sepcon; ltac1:(entailer!))) ].

(** [BitfieldStore.run] handles a direct field assignment whose later
    precondition has canonical [PROPx], [LOCALx] and [SEPx] form. It
    looks up a struct or union [Bits] descriptor, evaluates the root
    address and cast expression, and replaces the matching initialized
    carrier [data_at] in [SEP] by the normalized inserted integer.

    It rejects other goal shapes, nonaggregate roots, missing composite
    or [Bits] descriptors, noninteger targets or cast results, and a
    missing matching writable carrier with an initialized [Vint].
    Candidates whose writability cannot be proved are skipped in caller
    order. Descriptor bounds, nonvolatile access, typechecking and
    ramification must be discharged by the existing premise solvers.
    A failure leaves the assignment unproved. *)
Ltac2 run () :=
  Control.enter (fun () =>
    let assignment := read_assignment () in
    let root := assignment.(root) in
    let descriptor := read_descriptor (assignment.(specs))
      constr:(typeof $root) (assignment.(field)) in
    let values := evaluate_symbolic_values assignment in
    let sz := descriptor.(carrier_size) in
    let carrier_type := eval cbv [bitfield_carrier_type] in (bitfield_carrier_type $sz) in
    let pointer := carrier_pointer (descriptor.(byte_offset)) (values.(pointer)) in
    let carrier := find_carrier (assignment.(spatial)) carrier_type pointer constr:(O) in
    apply_store_rule assignment descriptor carrier values carrier_type pointer;
    prove_store_premises assignment carrier values).

End BitfieldStore.
