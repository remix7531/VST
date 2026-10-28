(** * Transport and framing for aggregate copy preconditions.

    [copy_pre] describes separated readable source and writable
    destination bytes with a reconstruction wand. [selfcopy_pre] instead
    requires equal addresses and one writable byte region. These lemmas
    preserve that distinction through consequence, framing, and context
    extension without weakening the copy checks. *)
Require Import VST.floyd.SeparationLogicFacts.
Require Import VST.floyd.assert_lemmas.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.

Import LiftNotation.
Local Open Scope logic.

(** Transport the reconstructed postcondition through an entailment. *)
Lemma copy_pre_derives: forall {CS: compspecs} Delta e1 e2 P Q,
  (P |-- Q) ->
  copy_pre Delta e1 e2 P |-- copy_pre Delta e1 e2 Q.
Proof.
  intros CS Delta e1 e2 P Q H.
  unfold copy_pre.
  do 4 (apply exp_derives; intro).
  apply andp_derives; [apply derives_refl |].
  apply later_derives.
  apply andp_derives; [apply derives_refl |].
  apply sepcon_derives; [apply derives_refl |].
  apply wand_derives; [apply derives_refl | exact H].
Qed.

(** Transport the self-copy reconstruction through an entailment. *)
Lemma selfcopy_pre_derives: forall {CS: compspecs} Delta e1 e2 P Q,
  (P |-- Q) ->
  selfcopy_pre Delta e1 e2 P |-- selfcopy_pre Delta e1 e2 Q.
Proof.
  intros CS Delta e1 e2 P Q H.
  unfold selfcopy_pre.
  do 2 (apply exp_derives; intro).
  apply andp_derives; [apply derives_refl |].
  apply later_derives.
  apply andp_derives; [apply derives_refl |].
  apply sepcon_derives; [apply derives_refl |].
  apply wand_derives; [apply derives_refl | exact H].
Qed.

(** Transport copy reconstruction with the local type environment and
    function identifier facts available to the entailment. *)
Lemma copy_pre_ENTAILL: forall {CS: compspecs} Delta e1 e2 P Q,
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) &&
    (allp_fun_id Delta && copy_pre Delta e1 e2 P) |--
  copy_pre Delta e1 e2 Q.
Proof.
  intros CS Delta e1 e2 P Q H.
  unfold copy_pre.
  do 4 (apply exp_ENTAILL; intro).
  apply andp_ENTAILL; [solve_andp |].
  apply later_ENTAILL.
  apply andp_ENTAILL; [solve_andp |].
  apply sepcon_ENTAILL; [solve_andp |].
  apply wand_ENTAILL; [solve_andp | exact H].
Qed.

(** Transport self-copy reconstruction with the same local environment
    and function identifier facts. *)
Lemma selfcopy_pre_ENTAILL: forall {CS: compspecs} Delta e1 e2 P Q,
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) &&
    (allp_fun_id Delta && selfcopy_pre Delta e1 e2 P) |--
  selfcopy_pre Delta e1 e2 Q.
Proof.
  intros CS Delta e1 e2 P Q H.
  unfold selfcopy_pre.
  do 2 (apply exp_ENTAILL; intro).
  apply andp_ENTAILL; [solve_andp |].
  apply later_ENTAILL.
  apply andp_ENTAILL; [solve_andp |].
  apply sepcon_ENTAILL; [solve_andp |].
  apply wand_ENTAILL; [solve_andp | exact H].
Qed.

(** Extend the typing context while retaining the copy witnesses. The
    environment must typecheck under the extended context. *)
Lemma copy_pre_tycontext_sub: forall {CS: compspecs} Delta Delta' e1 e2 P,
  tycontext_sub Delta Delta' ->
  local (tc_environ Delta') && copy_pre Delta e1 e2 P |--
  copy_pre Delta' e1 e2 P.
Proof.
  intros CS Delta Delta' e1 e2 P Hsub.
  unfold copy_pre.
  do 4 (apply exp_ENTAIL; intro).
  apply andp_ENTAIL; [solve_andp |].
  apply later_ENTAIL.
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL.
  - unfold local, lift1; intro rho; simpl; normalize.
    constructor; apply Clight_assert_lemmas.tc_lvalue_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
  - unfold local, lift1; intro rho; simpl; normalize.
    constructor; apply Clight_assert_lemmas.tc_lvalue_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
Qed.

(** Extend the typing context for a shared-address copy with the same
    requirement on the environment. *)
Lemma selfcopy_pre_tycontext_sub: forall {CS: compspecs} Delta Delta' e1 e2 P,
  tycontext_sub Delta Delta' ->
  local (tc_environ Delta') && selfcopy_pre Delta e1 e2 P |--
  selfcopy_pre Delta' e1 e2 P.
Proof.
  intros CS Delta Delta' e1 e2 P Hsub.
  unfold selfcopy_pre.
  do 2 (apply exp_ENTAIL; intro).
  apply andp_ENTAIL; [solve_andp |].
  apply later_ENTAIL.
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL.
  - unfold local, lift1; intro rho; simpl; normalize.
    constructor; apply Clight_assert_lemmas.tc_lvalue_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
  - unfold local, lift1; intro rho; simpl; normalize.
    constructor; apply Clight_assert_lemmas.tc_lvalue_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
Qed.

(** Move a separated frame into the copy reconstruction postcondition.
    Lvalue checks remain valid when the heap is extended by that frame. *)
Lemma copy_pre_frame: forall {CS: compspecs} Delta e1 e2 P F,
  copy_pre Delta e1 e2 P * F |-- copy_pre Delta e1 e2 (P * F).
Proof.
  intros CS Delta e1 e2 P F.
  unfold copy_pre.
  do 4 (rewrite exp_sepcon1; apply exp_derives; intro).
  normalize.
  eapply derives_trans;
    [apply sepcon_derives; [apply derives_refl | apply now_later] |].
  rewrite <- later_sepcon.
  apply later_derives.
  apply andp_right.
  - apply andp_right; [apply andp_right; [apply andp_right |] |].
    + eapply derives_trans;
        [apply sepcon_derives;
          [apply andp_left1, andp_left1, andp_left1, andp_left1,
            derives_refl | apply derives_refl] |].
      intro rho; simpl.
      constructor; apply (predicates_sl.extend_sepcon
        (extend_tc.extend_tc_lvalue Delta e1 rho)).
    + eapply derives_trans;
        [apply sepcon_derives;
          [apply andp_left1, andp_left1, andp_left1, andp_left2,
            derives_refl | apply derives_refl] |].
      intro rho; simpl.
      constructor; apply (predicates_sl.extend_sepcon
        (extend_tc.extend_tc_lvalue Delta e2 rho)).
    + apply derives_left_sepcon_right_corable;
        [intro rho; apply corable_prop | solve_andp].
    + apply derives_left_sepcon_right_corable;
        [intro rho; apply corable_prop | solve_andp].
  - eapply derives_trans;
      [apply sepcon_derives;
        [apply andp_left2, derives_refl | apply derives_refl] |].
    apply RAMIF_PLAIN.frame, derives_refl.
Qed.

(** Frame a shared-address copy without duplicating its owned region. *)
Lemma selfcopy_pre_frame: forall {CS: compspecs} Delta e1 e2 P F,
  selfcopy_pre Delta e1 e2 P * F |-- selfcopy_pre Delta e1 e2 (P * F).
Proof.
  intros CS Delta e1 e2 P F.
  unfold selfcopy_pre.
  do 2 (rewrite exp_sepcon1; apply exp_derives; intro).
  normalize.
  eapply derives_trans;
    [apply sepcon_derives; [apply derives_refl | apply now_later] |].
  rewrite <- later_sepcon.
  apply later_derives.
  apply andp_right.
  - apply andp_right; [apply andp_right; [apply andp_right |] |].
    + eapply derives_trans;
        [apply sepcon_derives;
          [apply andp_left1, andp_left1, andp_left1, andp_left1,
            derives_refl | apply derives_refl] |].
      intro rho; simpl.
      constructor; apply (predicates_sl.extend_sepcon
        (extend_tc.extend_tc_lvalue Delta e1 rho)).
    + eapply derives_trans;
        [apply sepcon_derives;
          [apply andp_left1, andp_left1, andp_left1, andp_left2,
            derives_refl | apply derives_refl] |].
      intro rho; simpl.
      constructor; apply (predicates_sl.extend_sepcon
        (extend_tc.extend_tc_lvalue Delta e2 rho)).
    + apply derives_left_sepcon_right_corable;
        [intro rho; apply corable_prop | solve_andp].
    + apply derives_left_sepcon_right_corable;
        [intro rho; apply corable_prop | solve_andp].
  - eapply derives_trans;
      [apply sepcon_derives;
        [apply andp_left2, derives_refl | apply derives_refl] |].
    apply RAMIF_PLAIN.frame, derives_refl.
Qed.

Lemma lvalue_cenv_sub: forall {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta e rho,
  tc_environ Delta rho ->
  @tc_lvalue CS Delta e rho |-- !! (@eval_lvalue CS e rho = @eval_lvalue CS' e rho).
Proof.
  intros. apply derives_trans with (!! is_pointer_or_null (@eval_lvalue CS e rho) && @tc_lvalue CS Delta e rho).
  { apply andp_right; trivial. apply SeparationLogic.typecheck_lvalue_sound; trivial. }
  normalize. rewrite (expr_lemmas.eval_lvalue_cenv_sub_eq CSUB). normalize.
  intros N; rewrite N in H0; clear N. apply H0.
Qed.

Lemma lvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS') Delta e rho,
  tc_environ Delta rho ->
  @tc_lvalue CS Delta e rho |-- !! (@eval_lvalue CS e rho = @eval_lvalue CS' e rho).
Proof.
  intros. destruct CSUB as [CSUB _]. apply (lvalue_cenv_sub CSUB); trivial.
Qed.

Lemma copy_aligned_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS') t p,
  complete_type (@cenv_cs CS) t = true ->
  @copy_aligned CS t p = @copy_aligned CS' t p.
Proof.
  intros CS CS' CSUB t p Hcomplete.
  unfold copy_aligned.
  destruct p; auto.
  unfold sizeof.
  rewrite (expr_lemmas4.cenv_sub_sizeof (proj1 CSUB) t Hcomplete).
  rewrite (copy.cenv_sub_alignof_blockcopy (proj1 CSUB) t Hcomplete).
  reflexivity.
Qed.

(** Transport copy witnesses to an extending composite specification.
    Completeness preserves object size and copy alignment, and the local
    environment supplies preservation of both evaluated lvalues. *)
Lemma copy_pre_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS') Delta e1 e2 P,
  local (tc_environ Delta) && @copy_pre CS Delta e1 e2 P |--
  @copy_pre CS' Delta e1 e2 P.
Proof.
  intros CS CS' CSUB Delta e1 e2 P.
  unfold copy_pre.
  do 4 (apply exp_ENTAIL; intro).
  intro rho; simpl; unfold local, lift1.
  apply derives_extract_prop; intro Henv.
  apply derives_extract_prop; intro Hmetadata.
  destruct Hmetadata as
    [Htype [Hcopy [Hcomplete [Hwrite [Hread [Hold Hbytes]]]]]].
  assert (Hsize: @sizeof CS' (typeof e1) = @sizeof CS (typeof e1)) by
    (unfold sizeof;
     apply (expr_lemmas4.cenv_sub_sizeof (proj1 CSUB) _ Hcomplete)).
  assert (Hcomplete': complete_type (@cenv_cs CS') (typeof e1) = true) by
    exact (semax.complete_type_cspecs_sub CSUB _ Hcomplete).
  apply andp_right.
  - apply prop_right. rewrite Hsize. repeat first [assumption | split].
  - apply later_derives.
    eapply derives_trans with
      (!! (@eval_lvalue CS e1 rho = @eval_lvalue CS' e1 rho) &&
       !! (@eval_lvalue CS e2 rho = @eval_lvalue CS' e2 rho) && _).
    { apply andp_right; [apply andp_right | apply derives_refl].
      - eapply derives_trans;
          [| exact (lvalue_cspecs_sub CSUB Delta e1 rho Henv)].
        solve_andp.
      - eapply derives_trans;
          [| exact (lvalue_cspecs_sub CSUB Delta e2 rho Henv)].
        solve_andp. }
    normalize.
    unfold liftx, lift; simpl.
    rewrite <- H, <- H0.
    rewrite <- (copy_aligned_cspecs_sub CSUB (typeof e1) _ Hcomplete).
    rewrite <- (copy_aligned_cspecs_sub CSUB (typeof e1) _ Hcomplete).
    repeat apply andp_right; try solve [solve_andp].
    + eapply derives_trans;
        [| exact (tc_lvalue_cspecs_sub CSUB Delta e1 rho Henv)].
      solve_andp.
    + eapply derives_trans;
        [| exact (tc_lvalue_cspecs_sub CSUB Delta e2 rho Henv)].
      solve_andp.
Qed.

(** Transport self-copy witnesses to an extending composite specification
    while preserving address equality, size, and alignment. *)
Lemma selfcopy_pre_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS') Delta e1 e2 P,
  local (tc_environ Delta) && @selfcopy_pre CS Delta e1 e2 P |--
  @selfcopy_pre CS' Delta e1 e2 P.
Proof.
  intros CS CS' CSUB Delta e1 e2 P.
  unfold selfcopy_pre.
  do 2 (apply exp_ENTAIL; intro).
  intro rho; simpl; unfold local, lift1.
  apply derives_extract_prop; intro Henv.
  apply derives_extract_prop; intro Hmetadata.
  destruct Hmetadata as [Htype [Hcopy [Hcomplete [Hwrite Hbytes]]]].
  assert (Hsize: @sizeof CS' (typeof e1) = @sizeof CS (typeof e1)) by
    (unfold sizeof;
     apply (expr_lemmas4.cenv_sub_sizeof (proj1 CSUB) _ Hcomplete)).
  assert (Hcomplete': complete_type (@cenv_cs CS') (typeof e1) = true) by
    exact (semax.complete_type_cspecs_sub CSUB _ Hcomplete).
  apply andp_right.
  - apply prop_right. rewrite Hsize. repeat first [assumption | split].
  - apply later_derives.
    eapply derives_trans with
      (!! (@eval_lvalue CS e1 rho = @eval_lvalue CS' e1 rho) &&
       !! (@eval_lvalue CS e2 rho = @eval_lvalue CS' e2 rho) && _).
    { apply andp_right; [apply andp_right | apply derives_refl].
      - eapply derives_trans;
          [| exact (lvalue_cspecs_sub CSUB Delta e1 rho Henv)].
        solve_andp.
      - eapply derives_trans;
          [| exact (lvalue_cspecs_sub CSUB Delta e2 rho Henv)].
        solve_andp. }
    normalize.
    unfold liftx, lift; simpl.
    rewrite <- H, <- H0.
    rewrite <- (copy_aligned_cspecs_sub CSUB (typeof e1) _ Hcomplete).
    repeat apply andp_right; try solve [solve_andp].
    + eapply derives_trans;
        [| exact (tc_lvalue_cspecs_sub CSUB Delta e1 rho Henv)].
      solve_andp.
    + eapply derives_trans;
        [| exact (tc_lvalue_cspecs_sub CSUB Delta e2 rho Henv)].
      solve_andp.
Qed.
