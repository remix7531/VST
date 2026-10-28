Require Import VST.floyd.proofauto.
Require Import VST.floyd.copy_array_ramify.

Definition arraycopy_pair_id: ident := 301%positive.
Definition arraycopy_holder_id: ident := 302%positive.
Definition arraycopy_first_id: ident := 303%positive.
Definition arraycopy_second_id: ident := 304%positive.
Definition arraycopy_values_id: ident := 305%positive.
Definition arraycopy_object_id: ident := 306%positive.
Definition arraycopy_siblings_id: ident := 307%positive.
Definition arraycopy_self_id: ident := 308%positive.

Definition arraycopy_pair_type := Tstruct arraycopy_pair_id noattr.
Definition arraycopy_holder_type := Tstruct arraycopy_holder_id noattr.

Definition arraycopy_element (index: Z): expr :=
  Ederef
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar arraycopy_object_id (tptr arraycopy_holder_type))
          arraycopy_holder_type)
        arraycopy_values_id (tarray arraycopy_pair_type 2))
      (Econst_int (Int.repr index) tint) (tptr arraycopy_pair_type))
    arraycopy_pair_type.

Definition arraycopy_function (destination_index source_index: Z): function := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := [(arraycopy_object_id, tptr arraycopy_holder_type)];
  fn_vars := [];
  fn_temps := [];
  fn_body := Sassign (arraycopy_element destination_index)
    (arraycopy_element source_index)
|}.

Definition f_arraycopy_siblings := arraycopy_function 0 1.
Definition f_arraycopy_self := arraycopy_function 1 1.

Definition arraycopy_composites: list composite_definition :=
  [Composite arraycopy_pair_id Struct
     [Member_plain arraycopy_first_id tuint;
      Member_plain arraycopy_second_id tuint] noattr;
   Composite arraycopy_holder_id Struct
     [Member_plain arraycopy_values_id (tarray arraycopy_pair_type 2)] noattr].

Definition arraycopy_program: Clight.program :=
  Clightdefs.mkprogram arraycopy_composites
    [(arraycopy_siblings_id, Gfun (Ctypes.Internal f_arraycopy_siblings));
     (arraycopy_self_id, Gfun (Ctypes.Internal f_arraycopy_self))]
    [arraycopy_siblings_id; arraycopy_self_id] arraycopy_siblings_id Logic.I.

#[local] Instance ArrayCopySpecs: compspecs.
Proof. make_compspecs arraycopy_program. Defined.

Lemma empty_array_decomposition_endpoint: forall sh p,
  array_at sh (tarray arraycopy_pair_type 0) [] 0 0 [] p |--
  !! (field_compatible0 (tarray arraycopy_pair_type 0) [ArraySubsc 0] p) && emp.
Proof.
  intros sh p.
  ltac2:(Control.enter (fun () =>
    copy_array_unfold_at_run constr:(ArrayCopySpecs) constr:(sh)
      constr:(tarray arraycopy_pair_type 0) constr:(@nil gfield)
      constr:(0) constr:(0) constr:(@nil (reptype arraycopy_pair_type)) constr:(p))).
  apply derives_refl.
Qed.

Lemma symbolic_empty_array_decomposition_endpoint: forall sh p upper,
  upper = 0 ->
  array_at sh (tarray arraycopy_pair_type 0) [] 0 upper [] p |--
  !! (field_compatible0 (tarray arraycopy_pair_type 0) [ArraySubsc 0] p) && emp.
Proof.
  intros sh p upper Hupper.
  ltac2:(Control.enter (fun () =>
    copy_array_unfold_at_run constr:(ArrayCopySpecs) constr:(sh)
      constr:(tarray arraycopy_pair_type 0) constr:(@nil gfield)
      constr:(0) constr:(upper) constr:(@nil (reptype arraycopy_pair_type)) constr:(p))).
  apply derives_refl.
Qed.

Definition arraycopy_siblings_spec :=
  DECLARE arraycopy_siblings_id
  WITH object: val, first: reptype arraycopy_pair_type,
       second: reptype arraycopy_pair_type
  PRE [tptr arraycopy_holder_type]
    PROP () PARAMS (object)
    SEP (data_at Ews arraycopy_holder_type [first; second] object)
  POST [tvoid]
    PROP () RETURN ()
    SEP (data_at Ews arraycopy_holder_type [second; second] object).

Definition arraycopy_self_spec :=
  DECLARE arraycopy_self_id
  WITH object: val, first: reptype arraycopy_pair_type,
       second: reptype arraycopy_pair_type
  PRE [tptr arraycopy_holder_type]
    PROP () PARAMS (object)
    SEP (data_at Ews arraycopy_holder_type [first; second] object)
  POST [tvoid]
    PROP () RETURN ()
    SEP (data_at Ews arraycopy_holder_type [first; second] object).

Definition ArrayCopyVprog: varspecs := [].
Definition ArrayCopyGprog: funspecs :=
  [arraycopy_siblings_spec; arraycopy_self_spec].

Lemma body_arraycopy_siblings:
  semax_body ArrayCopyVprog ArrayCopyGprog f_arraycopy_siblings arraycopy_siblings_spec.
Proof.
  start_function. forward. entailer!.
Qed.

Lemma body_arraycopy_self:
  semax_body ArrayCopyVprog ArrayCopyGprog f_arraycopy_self arraycopy_self_spec.
Proof.
  start_function. forward. entailer!.
Qed.
