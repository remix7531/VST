(** * Nested aggregate expressions evaluated as lvalues.

    [By_copy] expressions denote storage addresses. The interfaces below
    retain the path legality and typechecking required to use them. *)
Require Import VST.floyd.base2.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.

Import LiftNotation.
Local Open Scope logic.

(** A type copied through memory is evaluated in lvalue mode. *)
Lemma LR_of_type_by_copy: forall t,
  access_mode t = By_copy -> LR_of_type t = LLLL.
Proof.
  intros t MODE. destruct t; simpl in *; auto; discriminate.
Qed.

Section COPY_LVALUE.

Context {cs: compspecs}.

(** Combine compatible storage, a legal nested expression, and checked
    root and field expressions into its aggregate address and lvalue
    typechecking fact. The selected nested type must use [By_copy]. *)
Lemma nested_efield_facts_by_copy:
  forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  access_mode (nested_field_type t_root gfs) = By_copy ->
  local (`(eq p) (eval_LR e (LR_of_type t_root))) &&
  tc_LR Delta e (LR_of_type t_root) &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p))
    (eval_lvalue (nested_efield e efs tts))) &&
  tc_lvalue Delta (nested_efield e efs tts).
Proof.
  intros Delta t_root e efs gfs tts lr p
    COMPATIBLE LR LEGAL MODE.
  subst lr.
  eapply derives_trans;
    [apply eval_lvalue_nested_efield_aux; eauto |].
  rewrite (LR_of_type_by_copy _ MODE). apply derives_refl.
Qed.

Lemma eval_lvalue_nested_efield_by_copy:
  forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  access_mode (nested_field_type t_root gfs) = By_copy ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p))
    (eval_lvalue (nested_efield e efs tts))).
Proof.
  intros. subst lr.
  eapply derives_trans;
    [eapply nested_efield_facts_by_copy; eauto |].
  apply andp_left1. apply derives_refl.
Qed.

Lemma tc_lvalue_nested_efield_by_copy:
  forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  access_mode (nested_field_type t_root gfs) = By_copy ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  tc_lvalue Delta (nested_efield e efs tts).
Proof.
  intros. subst lr.
  eapply derives_trans;
    [eapply nested_efield_facts_by_copy; eauto |].
  apply andp_left2. apply derives_refl.
Qed.

(** Certify the computed decomposition of a [By_copy] expression. A
    matching root type and denoted field path reconstruct the expression
    with a legal nested path and exactly its original type. *)
Lemma compute_nested_efield_by_copy_lemma: forall e rho,
  access_mode (typeof e) = By_copy ->
  match compute_nested_efield e with
  | (e_root, efs, lr) =>
      forall t_root gfs,
      exists tts,
        compute_root_type (typeof e_root) lr t_root ->
        efield_denote efs gfs rho ->
        nested_efield e_root efs tts = e /\
        LR_of_type t_root = lr /\
        legal_nested_efield t_root e_root gfs tts lr = true /\
        nested_field_type t_root gfs = typeof e
  end.
Proof.
  intros e rho MODE.
  destruct (compute_nested_efield_aux e rho LLLL) as [COMPUTE _].
  unfold compute_nested_efield.
  destruct (compute_nested_efield_rec e LLLL) as [[e_root efs] lr].
  intros t_root gfs.
  spec COMPUTE;
    [unfold LR_possible; destruct (typeof e); simpl in *; auto;
      discriminate |].
  specialize (COMPUTE t_root gfs).
  destruct COMPUTE as [tts COMPUTE]. exists tts.
  intros ROOT DENOTE. specialize (COMPUTE ROOT DENOTE).
  destruct COMPUTE as [NESTED [LR [MATCH [LEGAL TYPE]]]].
  assert (TYPEOF: nested_field_type t_root gfs = typeof e).
  {
    destruct gfs; auto.
    destruct t_root, (typeof e); inv TYPE; auto; inv MODE.
  }
  split; [exact NESTED |]. split; [exact LR |].
  split; [| exact TYPEOF].
  unfold legal_nested_efield. rewrite LEGAL.
  destruct gfs; [| rewrite MATCH; reflexivity].
  change (t_root = typeof e) in TYPEOF.
  assert (ROOTLR: lr = LLLL).
  {
    rewrite <- LR. apply LR_of_type_by_copy.
    rewrite TYPEOF. exact MODE.
  }
  subst lr.
  unfold type_almost_match', type_almost_match in *.
  rewrite ROOTLR in MATCH |- *.
  destruct t_root; simpl in MATCH |- *; rewrite MATCH; reflexivity.
Qed.

End COPY_LVALUE.
