(** * Typed field extraction and reconstruction interfaces.

    Ramification keeps the enclosing ownership available as a wand after
    exposing the selected fields. These spatial rules impose no share
    permissions themselves, assignment rules supply those requirements. *)
Require Import VST.floyd.base2.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.nested_loadstore.
Require Import VST.msl.ramification_lemmas.

Local Open Scope logic.

Section copy_fields.
Context {cs: compspecs}.

(** Expose one compatible field and reconstruct its enclosing object for
    every replacement using [upd_reptype]. The path may contain arrays,
    structure fields, or a selected union field. *)
Lemma data_at_field_ramify:
  forall sh t path (value: reptype t) p,
  field_compatible t path p ->
  data_at sh t value p |--
    field_at sh t path (proj_reptype t path value) p *
    (ALL replacement: reptype (nested_field_type t path),
      field_at sh t path replacement p -*
      data_at sh t (upd_reptype t path value replacement) p).
Proof.
intros sh t path value p COMPATIBLE.
pose proof (nested_field_ramif sh t nil path value) as RAMIFY.
rewrite app_nil_r in RAMIFY.
specialize (RAMIFY (proj_reptype t path value) p (JMeq_refl _) COMPATIBLE).
eapply derives_trans; [exact RAMIFY |].
apply sepcon_derives; [apply derives_refl |].
apply allp_right; intro replacement.
apply (allp_left _ replacement).
apply (allp_left _ replacement).
rewrite prop_imp by apply JMeq_refl.
apply derives_refl.
Qed.

(** Expose fields from separately owned enclosing objects. Replacing the
    destination preserves source ownership when projecting and restoring
    its selected field leaves the source value unchanged. This explicit
    identity matters for union paths whose projection selects a member. *)
Lemma separate_data_at_fields_ramify:
  forall sh1 t1 path1 (value1: reptype t1) p1
         sh2 t2 path2 (value2: reptype t2) p2,
  field_compatible t1 path1 p1 ->
  field_compatible t2 path2 p2 ->
  upd_reptype t2 path2 value2 (proj_reptype t2 path2 value2) = value2 ->
  data_at sh1 t1 value1 p1 * data_at sh2 t2 value2 p2 |--
    (field_at sh1 t1 path1 (proj_reptype t1 path1 value1) p1 *
     field_at sh2 t2 path2 (proj_reptype t2 path2 value2) p2) *
    (ALL replacement: reptype (nested_field_type t1 path1),
      (field_at sh1 t1 path1 replacement p1 *
       field_at sh2 t2 path2 (proj_reptype t2 path2 value2) p2) -*
      (data_at sh1 t1 (upd_reptype t1 path1 value1 replacement) p1 *
       data_at sh2 t2 value2 p2)).
Proof.
intros sh1 t1 path1 value1 p1 sh2 t2 path2 value2 p2
  COMPATIBLE1 COMPATIBLE2 SOURCE_UNCHANGED.
apply RAMIF_Q.split.
- apply data_at_field_ramify. exact COMPATIBLE1.
- eapply derives_trans; [apply data_at_field_ramify; exact COMPATIBLE2 |].
  apply sepcon_derives; [apply derives_refl |].
  apply allp_right; intro replacement.
  apply (allp_left _ (proj_reptype t2 path2 value2)).
  rewrite SOURCE_UNCHANGED.
  apply derives_refl.
Qed.

(** Specialize the two object ramification interface to one destination
    replacement. The source restoration identity remains required. *)
Lemma separate_data_at_fields_ramify_replacement:
  forall sh1 t1 path1 (value1: reptype t1) p1
         sh2 t2 path2 (value2: reptype t2) p2
         (replacement: reptype (nested_field_type t1 path1)),
  field_compatible t1 path1 p1 ->
  field_compatible t2 path2 p2 ->
  upd_reptype t2 path2 value2 (proj_reptype t2 path2 value2) = value2 ->
  data_at sh1 t1 value1 p1 * data_at sh2 t2 value2 p2 |--
    (field_at sh1 t1 path1 (proj_reptype t1 path1 value1) p1 *
     field_at sh2 t2 path2 (proj_reptype t2 path2 value2) p2) *
    ((field_at sh1 t1 path1 replacement p1 *
      field_at sh2 t2 path2 (proj_reptype t2 path2 value2) p2) -*
     (data_at sh1 t1 (upd_reptype t1 path1 value1 replacement) p1 *
      data_at sh2 t2 value2 p2)).
Proof.
intros sh1 t1 path1 value1 p1 sh2 t2 path2 value2 p2 replacement
  COMPATIBLE1 COMPATIBLE2 SOURCE_UNCHANGED.
eapply RAMIF_Q.plain_spec with
  (g' := fun replacement =>
    data_at sh1 t1 (upd_reptype t1 path1 value1 replacement) p1 *
    data_at sh2 t2 value2 p2)
  (l' := fun replacement =>
    field_at sh1 t1 path1 replacement p1 *
    field_at sh2 t2 path2 (proj_reptype t2 path2 value2) p2)
  (x := replacement).
apply separate_data_at_fields_ramify; assumption.
Qed.

(** Preserve the original owned ancestors while copying their descendants.
    Relative paths project and update values within each owned region. *)
Lemma separate_field_regions_ramify_replacement:
  forall sh1 root1 owned1 path1
         (value1: reptype (nested_field_type root1 owned1)) p1
         sh2 root2 owned2 path2
         (value2: reptype (nested_field_type root2 owned2)) p2
         (replacement: reptype (nested_field_type
           (nested_field_type root1 owned1) path1)),
  field_compatible root1 (path1 ++ owned1) p1 ->
  field_compatible root2 (path2 ++ owned2) p2 ->
  upd_reptype (nested_field_type root2 owned2) path2 value2
    (proj_reptype (nested_field_type root2 owned2) path2 value2) = value2 ->
  field_at sh1 root1 owned1 value1 p1 *
    field_at sh2 root2 owned2 value2 p2 |--
    (field_at sh1 (nested_field_type root1 owned1) path1
       (proj_reptype (nested_field_type root1 owned1) path1 value1)
       (field_address root1 owned1 p1) *
     field_at sh2 (nested_field_type root2 owned2) path2
       (proj_reptype (nested_field_type root2 owned2) path2 value2)
       (field_address root2 owned2 p2)) *
    ((field_at sh1 (nested_field_type root1 owned1) path1 replacement
        (field_address root1 owned1 p1) *
      field_at sh2 (nested_field_type root2 owned2) path2
        (proj_reptype (nested_field_type root2 owned2) path2 value2)
        (field_address root2 owned2 p2)) -*
     (field_at sh1 root1 owned1
        (upd_reptype (nested_field_type root1 owned1) path1 value1 replacement) p1 *
      field_at sh2 root2 owned2 value2 p2)).
Proof.
  intros sh1 root1 owned1 path1 value1 p1
    sh2 root2 owned2 path2 value2 p2 replacement
    COMPATIBLE1 COMPATIBLE2 SOURCE_UNCHANGED.
  rewrite (field_at_data_at sh1 root1 owned1 value1 p1).
  rewrite (field_at_data_at sh1 root1 owned1
    (upd_reptype (nested_field_type root1 owned1) path1 value1 replacement) p1).
  rewrite (field_at_data_at sh2 root2 owned2 value2 p2).
  apply separate_data_at_fields_ramify_replacement.
  - apply field_compatible_app. exact COMPATIBLE1.
  - apply field_compatible_app. exact COMPATIBLE2.
  - exact SOURCE_UNCHANGED.
Qed.

(** Build a ramification for two fields in one enclosing object from an
    explicit split and reconstruction. The split must establish separated
    field ownership, compatibility alone does not supply separation. *)
Lemma copy_field_ramify_from_split:
  forall sh t destination source (value: reptype t) p remainder,
  (data_at sh t value p |--
    (field_at sh t destination (proj_reptype t destination value) p *
     field_at sh t source (proj_reptype t source value) p) * remainder) ->
  (forall replacement: reptype (nested_field_type t destination),
    (field_at sh t destination replacement p *
     field_at sh t source (proj_reptype t source value) p) * remainder |--
    data_at sh t (upd_reptype t destination value replacement) p) ->
  data_at sh t value p |--
    (field_at sh t destination (proj_reptype t destination value) p *
     field_at sh t source (proj_reptype t source value) p) *
    (ALL replacement: reptype (nested_field_type t destination),
      (field_at sh t destination replacement p *
       field_at sh t source (proj_reptype t source value) p) -*
      data_at sh t (upd_reptype t destination value replacement) p).
Proof.
intros sh t destination source value p remainder EXTRACT RECONSTRUCT.
apply RAMIF_Q.solve with remainder.
- exact EXTRACT.
- intro replacement. rewrite sepcon_comm. apply RECONSTRUCT.
Qed.

End copy_fields.
