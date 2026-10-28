Require Import VST.floyd.proofauto.
Require Import VST.floyd.copy_bytes.

Local Open Scope Z_scope.
Local Open Scope logic.

Definition bitfield_struct_id: ident := 201%positive.
Definition bitfield_union_id: ident := 202%positive.
Definition copy_bitfield_struct_id: ident := 203%positive.
Definition copy_bitfield_union_id: ident := 204%positive.
Definition selfcopy_bitfield_id: ident := 205%positive.
Definition bitfield_destination_id: ident := 206%positive.
Definition bitfield_source_id: ident := 207%positive.
Definition bitfield_first_id: ident := 208%positive.
Definition bitfield_second_id: ident := 209%positive.
Definition nested_bitfield_id: ident := 210%positive.

Definition bitfield_struct_type := Tstruct bitfield_struct_id noattr.
Definition bitfield_union_type := Tunion bitfield_union_id noattr.

Definition bitfield_copy_composites: list composite_definition :=
  [Composite bitfield_struct_id Struct
     [Member_bitfield bitfield_first_id I32 Unsigned noattr 3 false;
      Member_bitfield bitfield_second_id I32 Unsigned noattr 5 false] noattr;
   Composite bitfield_union_id Union
     [Member_bitfield bitfield_first_id I32 Unsigned noattr 3 false;
      Member_bitfield bitfield_second_id I32 Unsigned noattr 5 false] noattr].

Definition bitfield_copy_function (t: type) (self: bool): function := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := [(bitfield_destination_id, tptr t); (bitfield_source_id, tptr t)];
  fn_vars := [];
  fn_temps := [];
  fn_body := Sassign
    (Ederef (Etempvar bitfield_destination_id (tptr t)) t)
    (Ederef (Etempvar (if self then bitfield_destination_id else bitfield_source_id)
      (tptr t)) t)
|}.

Definition f_copy_bitfield_struct := bitfield_copy_function bitfield_struct_type false.
Definition f_copy_bitfield_union := bitfield_copy_function bitfield_union_type false.
Definition f_selfcopy_bitfield := bitfield_copy_function bitfield_struct_type true.

Definition bitfield_copy_program: Clight.program :=
  Clightdefs.mkprogram bitfield_copy_composites
    [(copy_bitfield_struct_id, Gfun (Ctypes.Internal f_copy_bitfield_struct));
     (copy_bitfield_union_id, Gfun (Ctypes.Internal f_copy_bitfield_union));
     (selfcopy_bitfield_id, Gfun (Ctypes.Internal f_selfcopy_bitfield))]
    [copy_bitfield_struct_id; copy_bitfield_union_id; selfcopy_bitfield_id]
    copy_bitfield_struct_id Logic.I.

#[local] Instance BitfieldCopySpecs: compspecs.
Proof. ltac2:(ByteCopyCompspecs.run constr:(bitfield_copy_program)). Defined.

Definition nested_bitfield_program: Clight.program :=
  Clightdefs.mkprogram
    (bitfield_copy_composites ++
     [Composite nested_bitfield_id Struct
       [Member_plain bitfield_first_id bitfield_struct_type] noattr])
    [] [] copy_bitfield_struct_id Logic.I.

Fail Definition nested_bitfield_specs: compspecs :=
  ltac2:(ByteCopyCompspecs.run constr:(nested_bitfield_program)).

Definition bitfield_fragment_bytes (payload: block): list memval :=
  [Fragment (Vptr payload (Ptrofs.repr 3)) Q32 0;
   Undef;
   Fragment (Vptr payload (Ptrofs.repr 3)) Q32 3;
   Undef].

Definition copy_bitfield_struct_spec :=
  DECLARE copy_bitfield_struct_id
  WITH destination: val, source: val, old: list memval, payload: block
  PRE [tptr bitfield_struct_type, tptr bitfield_struct_type]
    PROP (copy_aligned bitfield_struct_type destination;
          copy_aligned bitfield_struct_type source)
    PARAMS (destination; source)
    SEP (copy_bytes_at Ews bitfield_struct_type old destination;
         copy_bytes_at Ers bitfield_struct_type (bitfield_fragment_bytes payload) source)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at Ews bitfield_struct_type (bitfield_fragment_bytes payload) destination;
         copy_bytes_at Ers bitfield_struct_type (bitfield_fragment_bytes payload) source).

Definition copy_bitfield_union_spec :=
  DECLARE copy_bitfield_union_id
  WITH destination: val, source: val, old: list memval, bytes: list memval
  PRE [tptr bitfield_union_type, tptr bitfield_union_type]
    PROP (copy_aligned bitfield_union_type destination;
          copy_aligned bitfield_union_type source)
    PARAMS (destination; source)
    SEP (copy_bytes_at Ews bitfield_union_type old destination;
         copy_bytes_at Ers bitfield_union_type bytes source)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at Ews bitfield_union_type bytes destination;
         copy_bytes_at Ers bitfield_union_type bytes source).

Definition selfcopy_bitfield_spec :=
  DECLARE selfcopy_bitfield_id
  WITH destination: val, unused_source: val, bytes: list memval
  PRE [tptr bitfield_struct_type, tptr bitfield_struct_type]
    PROP (copy_aligned bitfield_struct_type destination)
    PARAMS (destination; unused_source)
    SEP (copy_bytes_at Ews bitfield_struct_type bytes destination)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at Ews bitfield_struct_type bytes destination).

Definition BitfieldVprog: varspecs := [].
Definition BitfieldGprog: funspecs :=
  [copy_bitfield_struct_spec; copy_bitfield_union_spec; selfcopy_bitfield_spec].

Lemma bitfield_layout_sizes:
  sizeof bitfield_struct_type = 4 /\ sizeof bitfield_union_type = 4.
Proof. split; reflexivity. Qed.

Lemma bitfield_fragment_length: forall payload,
  Zlength (bitfield_fragment_bytes payload) = sizeof bitfield_struct_type.
Proof. intros. reflexivity. Qed.

Lemma body_copy_bitfield_struct:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct copy_bitfield_struct_spec.
Proof.
  start_function. forward. entailer!.
Qed.

Lemma body_copy_bitfield_union:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_union copy_bitfield_union_spec.
Proof.
  start_function. forward. entailer!.
Qed.

Lemma body_selfcopy_bitfield:
  semax_body BitfieldVprog BitfieldGprog f_selfcopy_bitfield selfcopy_bitfield_spec.
Proof.
  start_function. forward. entailer!.
Qed.

Definition byte_source_candidates_spec (first_share second_share: share) :=
  DECLARE copy_bitfield_struct_id
  WITH destination: val, source: val, old: list memval, bytes: list memval
  PRE [tptr bitfield_struct_type, tptr bitfield_struct_type]
    PROP (copy_aligned bitfield_struct_type destination;
          copy_aligned bitfield_struct_type source)
    PARAMS (destination; source)
    SEP (copy_bytes_at Ews bitfield_struct_type old destination;
         copy_bytes_at first_share bitfield_struct_type bytes source;
         copy_bytes_at second_share bitfield_struct_type bytes source)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at Ews bitfield_struct_type bytes destination;
         copy_bytes_at first_share bitfield_struct_type bytes source;
         copy_bytes_at second_share bitfield_struct_type bytes source).

Lemma byte_source_skips_unreadable:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_source_candidates_spec Share.Lsh Share.Rsh).
Proof.
  start_function.
  pose proof (writable0_readable writable0_Rsh) as READABLE.
  forward. entailer!.
Qed.

Lemma byte_source_accepts_readable_first:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_source_candidates_spec Share.Rsh Share.Lsh).
Proof.
  start_function.
  pose proof (writable0_readable writable0_Rsh) as READABLE.
  forward. entailer!.
Qed.

Lemma byte_source_skips_unproved: forall sh,
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_source_candidates_spec sh Ers).
Proof. intros. start_function. forward. entailer!. Qed.

Lemma byte_source_preserves_unproved_after_readable: forall sh,
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_source_candidates_spec Ers sh).
Proof. intros. start_function. forward. entailer!. Qed.

Definition byte_destination_candidates_spec
    (first_share second_share: share) (first_writable: bool) :=
  DECLARE copy_bitfield_struct_id
  WITH destination: val, source: val, old: list memval, bytes: list memval
  PRE [tptr bitfield_struct_type, tptr bitfield_struct_type]
    PROP (copy_aligned bitfield_struct_type destination;
          copy_aligned bitfield_struct_type source)
    PARAMS (destination; source)
    SEP (copy_bytes_at first_share bitfield_struct_type old destination;
         copy_bytes_at second_share bitfield_struct_type old destination;
         copy_bytes_at Ers bitfield_struct_type bytes source)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at first_share bitfield_struct_type
           (if first_writable then bytes else old) destination;
         copy_bytes_at second_share bitfield_struct_type
           (if first_writable then old else bytes) destination;
         copy_bytes_at Ers bitfield_struct_type bytes source).

Lemma byte_destination_skips_unwritable:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_destination_candidates_spec (Share.comp Ews) Ews false).
Proof.
  start_function.
  forward. entailer!.
Qed.

Lemma byte_destination_accepts_writable_first:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_destination_candidates_spec Ews (Share.comp Ews) true).
Proof.
  start_function.
  forward. entailer!.
Qed.

Lemma byte_destination_skips_unproved: forall sh,
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_destination_candidates_spec sh Ews false).
Proof. intros. start_function. forward. entailer!. Qed.

Lemma byte_destination_preserves_unproved_after_writable: forall sh,
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_destination_candidates_spec Ews sh true).
Proof. intros. start_function. forward. entailer!. Qed.

Definition byte_self_candidates_spec (first_share second_share: share) :=
  DECLARE selfcopy_bitfield_id
  WITH destination: val, unused_source: val, bytes: list memval
  PRE [tptr bitfield_struct_type, tptr bitfield_struct_type]
    PROP (copy_aligned bitfield_struct_type destination)
    PARAMS (destination; unused_source)
    SEP (copy_bytes_at first_share bitfield_struct_type bytes destination;
         copy_bytes_at second_share bitfield_struct_type bytes destination)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at first_share bitfield_struct_type bytes destination;
         copy_bytes_at second_share bitfield_struct_type bytes destination).

Lemma byte_selfcopy_skips_unwritable:
  semax_body BitfieldVprog BitfieldGprog f_selfcopy_bitfield
    (byte_self_candidates_spec (Share.comp Ews) Ews).
Proof.
  start_function.
  forward. entailer!.
Qed.

Lemma byte_selfcopy_accepts_writable_first:
  semax_body BitfieldVprog BitfieldGprog f_selfcopy_bitfield
    (byte_self_candidates_spec Ews (Share.comp Ews)).
Proof.
  start_function.
  forward. entailer!.
Qed.

Goal forall first_share second_share,
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_source_candidates_spec first_share second_share).
Proof. intros. start_function. Fail forward. Abort.

Goal forall first_share second_share,
  semax_body BitfieldVprog BitfieldGprog f_selfcopy_bitfield
    (byte_self_candidates_spec first_share second_share).
Proof. intros. start_function. Fail forward. Abort.

Goal forall first_share second_share,
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_destination_candidates_spec first_share second_share false).
Proof. intros. start_function. Fail forward. Abort.

Definition byte_qualified_spec id expression_type destination_type source_type :=
  DECLARE id
  WITH destination: val, source: val, old: list memval, bytes: list memval
  PRE [tptr expression_type, tptr expression_type]
    PROP (copy_aligned expression_type destination;
          copy_aligned expression_type source)
    PARAMS (destination; source)
    SEP (copy_bytes_at Ews destination_type old destination;
         copy_bytes_at Ers source_type bytes source)
  POST [tvoid]
    PROP () RETURN ()
    SEP (copy_bytes_at Ews destination_type bytes destination;
         copy_bytes_at Ers source_type bytes source).

Definition byte_qualified_attr :=
  {| attr_volatile := true; attr_alignas := Some 3%N |}.
Definition qualified_bitfield_struct_type :=
  Tstruct bitfield_struct_id byte_qualified_attr.
Definition qualified_bitfield_union_type :=
  Tunion bitfield_union_id byte_qualified_attr.

Lemma byte_qualified_struct_source:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_qualified_spec copy_bitfield_struct_id bitfield_struct_type
      bitfield_struct_type qualified_bitfield_struct_type).
Proof. start_function. forward. entailer!. Qed.

Lemma byte_qualified_struct_destination:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_qualified_spec copy_bitfield_struct_id bitfield_struct_type
      qualified_bitfield_struct_type bitfield_struct_type).
Proof. start_function. forward. entailer!. Qed.

Lemma byte_qualified_struct_both:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
    (byte_qualified_spec copy_bitfield_struct_id bitfield_struct_type
      qualified_bitfield_struct_type qualified_bitfield_struct_type).
Proof. start_function. forward. entailer!. Qed.

Lemma byte_qualified_union_source:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_union
    (byte_qualified_spec copy_bitfield_union_id bitfield_union_type
      bitfield_union_type qualified_bitfield_union_type).
Proof. start_function. forward. entailer!. Qed.

Lemma byte_qualified_union_destination:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_union
    (byte_qualified_spec copy_bitfield_union_id bitfield_union_type
      qualified_bitfield_union_type bitfield_union_type).
Proof. start_function. forward. entailer!. Qed.

Lemma byte_qualified_union_both:
  semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_union
    (byte_qualified_spec copy_bitfield_union_id bitfield_union_type
      qualified_bitfield_union_type qualified_bitfield_union_type).
Proof. start_function. forward. entailer!. Qed.

Goal semax_body BitfieldVprog BitfieldGprog f_copy_bitfield_struct
  (byte_qualified_spec copy_bitfield_struct_id bitfield_struct_type
    bitfield_struct_type bitfield_union_type).
Proof. start_function. Fail forward. Abort.
