(** * Discovery of aggregate ownership in canonical spatial lists. *)
From Ltac2 Require Import Ltac2.
Require Import VST.floyd.base2.
Require Import VST.floyd.field_at.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.veric.copy.

Set Default Proof Mode "Classic".

(** A matched spatial predicate with its original index, typed value and
    proved permission. [data_at_] supplies [default_val], which represents
    its unspecified contents. Alignment remains a separate obligation. *)
Ltac2 Type copy_candidate := {
  copy_candidate_index : constr;
  copy_candidate_share : constr;
  copy_candidate_value : constr;
  copy_candidate_type : constr;
  copy_candidate_permission : constr;
  copy_candidate_compatible : constr
}.

Ltac2 copy_missing_region (permission : constr) (requested_type : constr)
    (requested_pointer : constr) :=
  let message := Message.concat
    (Message.of_string "Aggregate copy cannot prove ")
    (Message.concat (Message.of_constr permission)
      (Message.concat (Message.of_string " for ownership of type ")
        (Message.concat (Message.of_constr requested_type)
          (Message.concat (Message.of_string " at pointer ")
            (Message.of_constr requested_pointer))))) in
  Control.zero (Tactic_failure (Some message)).

(** Permission must be established before a candidate is selected. An
    unsuccessful assertion backtracks together with that candidate. *)
Ltac2 copy_prove_permission (permission : constr) (share : constr) : constr :=
  let name := Fresh.in_goal @COPY_PERMISSION in
  Std.assert (Std.AssertType
    (Some (Std.IntroNaming (Std.IntroIdentifier name)))
    constr:($permission $share) (Some (fun () => solve [auto])));
  Control.hyp name.

(** Only the outer attributes of a struct or union with the same tag may
    differ. Nested qualifiers remain part of the composite definition.
    The proof enters inferred postconditions, so it must be closed over
    the caller context rather than a newly asserted hypothesis. *)
Ltac2 copy_prove_type (requested_type : constr) (stored_type : constr) : constr :=
  constr:(eq_refl : copy_type_compatible $requested_type $stored_type = true).

(** Search entries in caller order for [data_at] or [data_at_] whose type
    is compatible with the request and whose pointer unifies with it.
    Preserve the original type and index for framing and replacement.
    Fail with the requested region
    when no entry matches, without unfolding arbitrary spatial predicates. *)
Ltac2 rec copy_find_candidate (permission : constr) (predicates : constr) (requested_type : constr)
    (requested_pointer : constr) (index : constr) : copy_candidate :=
  lazy_match! predicates with
  | @nil _ => copy_missing_region permission requested_type requested_pointer
  | @cons _ ?predicate ?tail =>
      Control.plus
        (fun () =>
          let (share, stored_type, value, pointer) :=
            lazy_match! predicate with
            | @data_at _ ?share ?stored_type ?value ?pointer =>
                (share, stored_type, value, pointer)
            | @data_at_ ?cs ?share ?stored_type ?pointer =>
                (share, stored_type, constr:(@default_val $cs $stored_type), pointer)
            | _ => Control.zero Match_failure
            end in
          let compatible := copy_prove_type requested_type stored_type in
          Std.unify pointer requested_pointer;
          let permission := copy_prove_permission permission share in
          { copy_candidate_index := index;
            copy_candidate_share := share;
            copy_candidate_value := value;
            copy_candidate_type := stored_type;
            copy_candidate_permission := permission;
            copy_candidate_compatible := compatible })
        (fun _ =>
          copy_find_candidate permission tail requested_type requested_pointer constr:(S $index))
  end.
