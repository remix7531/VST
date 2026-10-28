(** * Certified addresses for aggregate lvalues.

    Relate evaluated nested expressions to owned field paths. Expression
    decomposition, legal paths, and typechecking remain explicit premises. *)
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.floyd.copy_lvalue.
Require Import VST.floyd.copy_rules.

Import LiftNotation.
Local Open Scope logic.

Lemma copy_field_address_parent_compatible:
  forall {cs: compspecs} child child_path parent parent_path p,
  field_compatible child child_path (field_address parent parent_path p) ->
  field_compatible parent parent_path p.
Proof.
  intros cs child child_path parent parent_path p COMPATIBLE.
  apply isptr_field_address_lemma. exact (proj1 COMPATIBLE).
Qed.

(** Certify the type, field address, and lvalue checks of a [By_copy]
    expression using a compatible owned ancestor in [SEP]. The suffix
    equation connects the expression path to that ancestor, and the
    remaining path must be legal within its nested type. *)
Lemma copy_lvalue_field_address_owned:
  forall {cs: compspecs} n Delta sh P Q R (e: expr)
    T1 T2 GV e_root (efs: list efield) lr
    t_root_from_e gfs_from_e p_from_e
    (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
    (v: reptype (nested_field_type t_root gfs0)) Rn,
  local2ptree Q = (T1, T2, nil, GV) ->
  compute_nested_efield e = (e_root, efs, lr) ->
  access_mode (typeof e) = By_copy ->
  msubst_eval_LR Delta T1 T2 GV e_root lr = Some p_from_e ->
  msubst_efield_denote Delta T1 T2 GV efs gfs_from_e ->
  compute_root_type (typeof e_root) lr t_root_from_e ->
  field_address_gen (t_root_from_e, gfs_from_e, p_from_e)
    (t_root, gfs, p) ->
  nth_error R n = Some Rn ->
  (Rn |-- field_at sh t_root gfs0 v p) ->
  gfs = gfs1 ++ gfs0 ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (legal_nested_field (nested_field_type t_root gfs0) gfs1) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    denote_tc_assert
      (tc_andp (typecheck_LR Delta e_root lr) (typecheck_efield Delta efs)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (typeof e = nested_field_type t_root gfs) &&
    (local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) &&
      tc_lvalue Delta e).
Proof.
  intros cs n Delta sh P Q R e T1 T2 GV e_root efs lr
    t_root_from_e gfs_from_e p_from_e t_root gfs0 gfs1 gfs p v Rn
    LOCAL2PTREE COMPUTE_NESTED_EFIELD MODE EVAL_ROOT EVAL_EFIELD ROOT_TYPE
    FIELD_ADD_GEN NTH OWNED GFS LEGAL_FIELD TC.
  assert_PROP (exists tts,
    nested_efield e_root efs tts = e /\
    LR_of_type t_root_from_e = lr /\
    legal_nested_efield t_root_from_e e_root gfs_from_e tts lr = true /\
    nested_field_type t_root_from_e gfs_from_e = typeof e) as DECOMPOSE.
  {
    erewrite (local2ptree_soundness P Q R) by eauto.
    simpl app.
    apply (msubst_efield_denote_eq _ P _ _ GV R) in EVAL_EFIELD.
    eapply derives_trans; [apply EVAL_EFIELD |].
    intro rho; simpl; unfold local, lift1; unfold_lift.
    apply prop_derives; intros DENOTE.
    pose proof (compute_nested_efield_by_copy_lemma e rho MODE) as COMPUTE.
    rewrite COMPUTE_NESTED_EFIELD in COMPUTE.
    destruct (COMPUTE t_root_from_e gfs_from_e) as [tts DECOMPOSED].
    exists tts. apply DECOMPOSED; auto.
  }
  destruct DECOMPOSE as [tts [NESTED_EFIELD [LR [LEGAL_NESTED TYPEOF]]]].
  rewrite <- TYPEOF in MODE.
  assert_PROP (field_compatible t_root gfs0 p) as FIELD_COMPATIBLE.
  {
    rewrite <- (corable_sepcon_TT (prop _)) by auto.
    eapply nth_error_SEP_sepcon_TT'; [| exact NTH].
    apply andp_left2. apply andp_left2. apply andp_left2.
    intro rho; unfold SEPx; simpl. rewrite sepcon_emp.
    eapply derives_trans; [exact OWNED |].
    rewrite field_at_compatible'. normalize.
  }
  assert_PROP (legal_nested_field (nested_field_type t_root gfs0) gfs1)
    as LEGAL_NESTED_FIELD by auto.
  eapply field_compatible_app_inv' in FIELD_COMPATIBLE;
    [| exact LEGAL_NESTED_FIELD].
  rewrite <- GFS in FIELD_COMPATIBLE.
  apply field_address_gen_fact in FIELD_ADD_GEN.
  destruct FIELD_ADD_GEN as [FIELD_ADD_EQ [TYPE_EQ FIELD_COMPATIBLE_E]].
  specialize (FIELD_COMPATIBLE_E FIELD_COMPATIBLE).
  pose proof (nested_efield_facts_by_copy Delta _ _ efs _ _ _ _
    FIELD_COMPATIBLE_E LR LEGAL_NESTED MODE) as DERIVES.
  rewrite denote_tc_assert_andp in TC.
  apply (derives_trans
    (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)))) in DERIVES.
  2: {
    rewrite (andp_comm _ (local (efield_denote _ _))), <- !andp_assoc.
    rewrite (add_andp _ _ TC). rewrite LR.
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_left1.
    erewrite (local2ptree_soundness P Q R) by eauto.
    simpl app. apply andp_right.
    - apply (msubst_efield_denote_eq _ P _ _ GV R) in EVAL_EFIELD; auto.
    - apply (msubst_eval_LR_eq _ P _ _ GV R) in EVAL_ROOT; auto.
  }
  apply andp_right.
  - apply prop_right. congruence.
  - rewrite <- FIELD_ADD_EQ, <- NESTED_EFIELD. exact DERIVES.
Qed.

(** Outer aggregate attributes may differ between the expression root
    and its owned root. Ownership supplies their compatible field paths. *)
Lemma copy_lvalue_field_address_qualified:
  forall {cs: compspecs} n Delta sh P Q R (e: expr)
    T1 T2 GV e_root (efs: list efield) lr
    t_root_from_e gfs_from_e p_from_e
    (address_root t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
    (v: reptype (nested_field_type t_root gfs0)) Rn,
  local2ptree Q = (T1, T2, nil, GV) ->
  compute_nested_efield e = (e_root, efs, lr) ->
  access_mode (typeof e) = By_copy ->
  msubst_eval_LR Delta T1 T2 GV e_root lr = Some p_from_e ->
  msubst_efield_denote Delta T1 T2 GV efs gfs_from_e ->
  compute_root_type (typeof e_root) lr t_root_from_e ->
  field_address_gen (t_root_from_e, gfs_from_e, p_from_e)
    (address_root, gfs, p) ->
  (address_root = t_root \/ copy_type_compatible address_root t_root = true) ->
  nth_error R n = Some Rn ->
  (Rn |-- field_at sh t_root gfs0 v p) ->
  gfs = gfs1 ++ gfs0 ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (legal_nested_field (nested_field_type t_root gfs0) gfs1) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    denote_tc_assert
      (tc_andp (typecheck_LR Delta e_root lr) (typecheck_efield Delta efs)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (copy_type_compatible (typeof e) (nested_field_type t_root gfs) = true) &&
    (local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) &&
      tc_lvalue Delta e).
Proof.
  intros cs n Delta sh P Q R e T1 T2 GV e_root efs lr
    t_root_from_e gfs_from_e p_from_e address_root t_root gfs0 gfs1 gfs p v Rn
    LOCAL2PTREE COMPUTE_NESTED_EFIELD MODE EVAL_ROOT EVAL_EFIELD ROOT_TYPE
    FIELD_ADD_GEN ROOTS NTH OWNED GFS LEGAL_FIELD TC.
  assert_PROP (exists tts,
    nested_efield e_root efs tts = e /\
    LR_of_type t_root_from_e = lr /\
    legal_nested_efield t_root_from_e e_root gfs_from_e tts lr = true /\
    nested_field_type t_root_from_e gfs_from_e = typeof e) as DECOMPOSE.
  {
    erewrite (local2ptree_soundness P Q R) by eauto.
    simpl app.
    apply (msubst_efield_denote_eq _ P _ _ GV R) in EVAL_EFIELD.
    eapply derives_trans; [apply EVAL_EFIELD |].
    intro rho; simpl; unfold local, lift1; unfold_lift.
    apply prop_derives; intros DENOTE.
    pose proof (compute_nested_efield_by_copy_lemma e rho MODE) as COMPUTE.
    rewrite COMPUTE_NESTED_EFIELD in COMPUTE.
    destruct (COMPUTE t_root_from_e gfs_from_e) as [tts DECOMPOSED].
    exists tts. apply DECOMPOSED; auto.
  }
  destruct DECOMPOSE as [tts [NESTED_EFIELD [LR [LEGAL_NESTED TYPEOF]]]].
  assert_PROP (field_compatible t_root gfs0 p) as FIELD_COMPATIBLE.
  {
    rewrite <- (corable_sepcon_TT (prop _)) by auto.
    eapply nth_error_SEP_sepcon_TT'; [| exact NTH].
    apply andp_left2. apply andp_left2. apply andp_left2.
    intro rho; unfold SEPx; simpl. rewrite sepcon_emp.
    eapply derives_trans; [exact OWNED |].
    rewrite field_at_compatible'. normalize.
  }
  assert_PROP (legal_nested_field (nested_field_type t_root gfs0) gfs1)
    as LEGAL_NESTED_FIELD by auto.
  eapply field_compatible_app_inv' in FIELD_COMPATIBLE;
    [| exact LEGAL_NESTED_FIELD].
  rewrite <- GFS in FIELD_COMPATIBLE.
  assert (field_compatible address_root gfs p) as ADDRESS_COMPATIBLE_ROOT.
  {
    destruct ROOTS as [ROOTS | ROOTS]; [subst; exact FIELD_COMPATIBLE |].
    rewrite (copy_field_compatible _ _ _ _ ROOTS). exact FIELD_COMPATIBLE.
  }
  assert (field_address address_root gfs p = field_address t_root gfs p)
    as OWNED_ADDRESS.
  {
    destruct ROOTS as [ROOTS | ROOTS]; [subst; reflexivity |].
    apply copy_field_address; assumption.
  }
  apply field_address_gen_fact in FIELD_ADD_GEN.
  destruct FIELD_ADD_GEN as [FIELD_ADD_EQ [TYPE_EQ FIELD_COMPATIBLE_E]].
  specialize (FIELD_COMPATIBLE_E ADDRESS_COMPATIBLE_ROOT).
  assert (copy_type_compatible (typeof e) (nested_field_type t_root gfs) = true)
    as COPY_TYPES.
  {
    rewrite <- TYPEOF, TYPE_EQ in *.
    destruct ROOTS as [ROOTS | ROOTS].
    - subst. apply copy_type_compatible_refl. exact MODE.
    - apply copy_nested_field_type_compatible; assumption.
  }
  rewrite <- TYPEOF in MODE.
  pose proof (nested_efield_facts_by_copy Delta _ _ efs _ _ _ _
    FIELD_COMPATIBLE_E LR LEGAL_NESTED MODE) as DERIVES.
  rewrite denote_tc_assert_andp in TC.
  apply (derives_trans
    (local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)))) in DERIVES.
  2: {
    rewrite (andp_comm _ (local (efield_denote _ _))), <- !andp_assoc.
    rewrite (add_andp _ _ TC). rewrite LR.
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_right; [| solve_andp].
    apply andp_left1.
    erewrite (local2ptree_soundness P Q R) by eauto.
    simpl app. apply andp_right.
    - apply (msubst_efield_denote_eq _ P _ _ GV R) in EVAL_EFIELD; auto.
    - apply (msubst_eval_LR_eq _ P _ _ GV R) in EVAL_ROOT; auto.
  }
  apply andp_right.
  - apply prop_right. exact COPY_TYPES.
  - rewrite <- OWNED_ADDRESS, <- FIELD_ADD_EQ, <- NESTED_EFIELD. exact DERIVES.
Qed.

Lemma copy_lvalue_field_address:
  forall {cs: compspecs} n Delta sh P Q R (e: expr)
    T1 T2 GV e_root (efs: list efield) lr
    t_root_from_e gfs_from_e p_from_e
    (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
    (v: reptype (nested_field_type t_root gfs0)),
  local2ptree Q = (T1, T2, nil, GV) ->
  compute_nested_efield e = (e_root, efs, lr) ->
  access_mode (typeof e) = By_copy ->
  msubst_eval_LR Delta T1 T2 GV e_root lr = Some p_from_e ->
  msubst_efield_denote Delta T1 T2 GV efs gfs_from_e ->
  compute_root_type (typeof e_root) lr t_root_from_e ->
  field_address_gen (t_root_from_e, gfs_from_e, p_from_e)
    (t_root, gfs, p) ->
  nth_error R n = Some (field_at sh t_root gfs0 v p) ->
  gfs = gfs1 ++ gfs0 ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (legal_nested_field (nested_field_type t_root gfs0) gfs1) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    denote_tc_assert
      (tc_andp (typecheck_LR Delta e_root lr) (typecheck_efield Delta efs)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (typeof e = nested_field_type t_root gfs) &&
    (local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) &&
      tc_lvalue Delta e).
Proof.
  intros cs n Delta sh P Q R e T1 T2 GV e_root efs lr
    t_root_from_e gfs_from_e p_from_e t_root gfs0 gfs1 gfs p v.
  intros. eapply copy_lvalue_field_address_owned with
    (Rn := field_at sh t_root gfs0 v p); eauto using derives_refl.
Qed.

(** Use a certified [find_nth_preds] result instead of a direct spatial
    index. The result must identify the field predicate and its path
    suffix, with the same legality and expression checks as the direct
    address interface. *)
Lemma copy_lvalue_field_address_search:
  forall {cs: compspecs} n Rn Delta sh P Q R (e: expr)
    T1 T2 GV e_root (efs: list efield) lr
    t_root_from_e gfs_from_e p_from_e
    (t_root: type) (gfs0 gfs1 gfs: list gfield) (p: val)
    Rv (v: reptype (nested_field_type t_root gfs0)),
  local2ptree Q = (T1, T2, nil, GV) ->
  compute_nested_efield e = (e_root, efs, lr) ->
  access_mode (typeof e) = By_copy ->
  msubst_eval_LR Delta T1 T2 GV e_root lr = Some p_from_e ->
  msubst_efield_denote Delta T1 T2 GV efs gfs_from_e ->
  compute_root_type (typeof e_root) lr t_root_from_e ->
  field_address_gen (t_root_from_e, gfs_from_e, p_from_e)
    (t_root, gfs, p) ->
  find_nth_preds
    (fun Rn =>
      (Rn = Rv v /\ Rv = fun v => field_at sh t_root gfs0 v p) /\
      gfs = gfs1 ++ gfs0) R (Some (n, Rn)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (legal_nested_field (nested_field_type t_root gfs0) gfs1) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    denote_tc_assert
      (tc_andp (typecheck_LR Delta e_root lr) (typecheck_efield Delta efs)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    !! (typeof e = nested_field_type t_root gfs) &&
    (local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) &&
      tc_lvalue Delta e).
Proof.
  intros cs n Rn Delta sh P Q R e T1 T2 GV e_root efs lr
    t_root_from_e gfs_from_e p_from_e t_root gfs0 gfs1 gfs p Rv v
    LOCAL2PTREE COMPUTE_NESTED_EFIELD MODE EVAL_ROOT EVAL_EFIELD ROOT_TYPE
    FIELD_ADD_GEN SEARCH LEGAL_FIELD TC.
  apply find_nth_preds_Some in SEARCH.
  destruct SEARCH as [NTH [[PREDICATE VALUE] GFS]]. subst Rn Rv.
  eapply copy_lvalue_field_address; eauto.
Qed.
