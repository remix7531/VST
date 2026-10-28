(** * Structural laws for bitfield assignment preconditions. *)

Require Import VST.floyd.SeparationLogicFacts.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.copy_pre_lemmas.
Require Import VST.veric.bitfield.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.

Import LiftNotation.
Local Open Scope logic.

(** Weakening the requested postcondition preserves the bitfield store
    precondition, including its descriptor and carrier ownership. *)
Lemma bitfield_store_pre_derives: forall {CS: compspecs} Delta e1 e2 P Q,
  (P |-- Q) ->
  bitfield_store_pre Delta e1 e2 P |-- bitfield_store_pre Delta e1 e2 Q.
Proof.
  intros CS Delta e1 e2 P Q H.
  unfold bitfield_store_pre.
  do 11 (apply exp_derives; intro).
  apply andp_derives; [apply derives_refl |].
  apply later_derives.
  apply andp_derives; [apply derives_refl |].
  apply sepcon_derives; [apply derives_refl |].
  apply wand_derives; [apply derives_refl | exact H].
Qed.

(** Postcondition weakening may use the typechecking environment and
    function identifier facts supplied by the entailment context. *)
Lemma bitfield_store_pre_ENTAILL: forall {CS: compspecs} Delta e1 e2 P Q,
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) &&
    (allp_fun_id Delta && bitfield_store_pre Delta e1 e2 P) |--
  bitfield_store_pre Delta e1 e2 Q.
Proof.
  intros CS Delta e1 e2 P Q H.
  unfold bitfield_store_pre.
  do 11 (apply exp_ENTAILL; intro).
  apply andp_ENTAILL; [solve_andp |].
  apply later_ENTAILL.
  apply andp_ENTAILL; [solve_andp |].
  apply sepcon_ENTAILL; [solve_andp |].
  apply wand_ENTAILL; [solve_andp | exact H].
Qed.

(** A larger typing context preserves the precondition when the current
    environment satisfies that larger context. *)
Lemma bitfield_store_pre_tycontext_sub: forall {CS: compspecs} Delta Delta' e1 e2 P,
  tycontext_sub Delta Delta' ->
  local (tc_environ Delta') && bitfield_store_pre Delta e1 e2 P |--
  bitfield_store_pre Delta' e1 e2 P.
Proof.
  intros CS Delta Delta' e1 e2 P Hsub.
  unfold bitfield_store_pre.
  do 11 (apply exp_ENTAIL; intro).
  apply andp_ENTAIL; [solve_andp |].
  apply later_ENTAIL.
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL; [| solve_andp].
  apply andp_ENTAIL.
  - unfold local, lift1; intro rho; simpl; normalize.
    constructor; apply Clight_assert_lemmas.tc_lvalue_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
  - unfold local, lift1; intro rho; simpl; normalize.
    constructor; apply Clight_assert_lemmas.tc_expr_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
Qed.

(** A disjoint frame passes through the carrier update and is returned
    with the requested postcondition. *)
Lemma bitfield_store_pre_frame: forall {CS: compspecs} Delta e1 e2 P F,
  bitfield_store_pre Delta e1 e2 P * F |--
  bitfield_store_pre Delta e1 e2 (P * F).
Proof.
  intros CS Delta e1 e2 P F.
  unfold bitfield_store_pre.
  do 11 (rewrite exp_sepcon1; apply exp_derives; intro).
  normalize.
  eapply derives_trans;
    [apply sepcon_derives; [apply derives_refl | apply now_later] |].
  rewrite <- later_sepcon.
  apply later_derives.
  apply andp_right.
  - apply andp_right; [apply andp_right |].
    + eapply derives_trans;
        [apply sepcon_derives;
          [apply andp_left1, andp_left1, andp_left1, derives_refl |
           apply derives_refl] |].
      intro rho; simpl.
      constructor; apply (predicates_sl.extend_sepcon
        (extend_tc.extend_tc_lvalue Delta x rho)).
    + eapply derives_trans;
        [apply sepcon_derives;
          [apply andp_left1, andp_left1, andp_left2, derives_refl |
           apply derives_refl] |].
      intro rho; simpl.
      constructor; apply (predicates_sl.extend_sepcon
        (extend_tc.extend_tc_expr Delta (Ecast e2 _) rho)).
    + apply derives_left_sepcon_right_corable;
        [intro rho; apply corable_prop | solve_andp].
  - eapply derives_trans;
      [apply sepcon_derives;
        [apply andp_left2, derives_refl | apply derives_refl] |].
    apply RAMIF_PLAIN.frame, derives_refl.
Qed.

(** Extending composite specifications preserves a typechecked cast
    result under the current typing environment. *)
Lemma bitfield_cast_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS')
    Delta rhs target rho,
  tc_environ Delta rho ->
  @tc_expr CS Delta (Ecast rhs target) rho |--
  !! (force_val (sem_cast (typeof rhs) target (@eval_expr CS rhs rho)) =
      force_val (sem_cast (typeof rhs) target (@eval_expr CS' rhs rho))).
Proof.
  intros CS CS' CSUB Delta rhs target rho Henv.
  constructor; intros w W.
  change (@eval_expr CS (Ecast rhs target) rho =
          @eval_expr CS' (Ecast rhs target) rho).
  exact (expr_lemmas.typecheck_expr_sound_cenv_sub
    (proj1 CSUB) Delta rho Henv w (Ecast rhs target) W).
Qed.

(** Extending composite specifications preserves descriptor lookup,
    expression values and carrier resources in a store precondition. *)
Lemma bitfield_store_pre_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS')
    Delta e1 e2 P,
  local (tc_environ Delta) && @bitfield_store_pre CS Delta e1 e2 P |--
  @bitfield_store_pre CS' Delta e1 e2 P.
Proof.
  intros CS CS' CSUB Delta e1 e2 P.
  unfold bitfield_store_pre.
  do 11 (apply exp_ENTAIL; intro).
  intro rho; simpl; unfold local, lift1.
  apply derives_extract_prop; intro Henv.
  apply derives_extract_prop; intro Hmetadata.
  destruct Hmetadata as
    [He1 [Hfield [Hpos [Hwidth [Hcarrier [Hnonvol Hwrite]]]]]].
  apply andp_right.
  - apply prop_right.
    repeat first [assumption | split].
    exact (bitfield_field_cenv_sub _ _ _ _ _ (proj1 CSUB) Hfield).
  - apply later_derives.
    eapply derives_trans with
      (!! (@eval_lvalue CS x rho = @eval_lvalue CS' x rho) &&
       !! (force_val (sem_cast (typeof e2)
             (Ctypes.Tint x2 (if zlt x5 (bitsize_intsize x2) then Signed else x3) x6)
             (@eval_expr CS e2 rho)) =
           force_val (sem_cast (typeof e2)
             (Ctypes.Tint x2 (if zlt x5 (bitsize_intsize x2) then Signed else x3) x6)
             (@eval_expr CS' e2 rho))) && _).
    { apply andp_right; [apply andp_right | apply derives_refl].
      - eapply derives_trans;
          [| exact (lvalue_cspecs_sub CSUB Delta x rho Henv)].
        solve_andp.
      - eapply derives_trans;
          [| exact (bitfield_cast_cspecs_sub CSUB Delta e2 _ rho Henv)].
        solve_andp. }
    normalize.
    unfold liftx, lift; simpl.
    rewrite <- H, <- H0.
    repeat apply andp_right; try solve [solve_andp].
    + eapply derives_trans;
        [| exact (tc_lvalue_cspecs_sub CSUB Delta x rho Henv)].
      solve_andp.
    + eapply derives_trans;
        [| exact (tc_expr_cspecs_sub CSUB Delta (Ecast e2 _) rho Henv)].
      solve_andp.
Qed.
