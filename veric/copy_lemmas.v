Require Import VST.veric.base.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.copy.
Require Import VST.veric.compspecs.

Lemma copy_type_compatible_sym: forall destination source,
  copy_type_compatible destination source = true ->
  copy_type_compatible source destination = true.
Proof.
  intros destination source Hcompatible.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    simpl; rewrite if_true by reflexivity; reflexivity.
Qed.

Lemma copy_type_compatible_sizeof: forall {cs: compspecs} destination source,
  copy_type_compatible destination source = true ->
  sizeof destination = sizeof source.
Proof.
  intros cs destination source Hcompatible.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0; reflexivity.
Qed.

Lemma aggregate_eval_expr: forall ge ve te m e b ofs,
  access_mode (typeof e) = By_copy ->
  Clight.eval_lvalue ge ve te m e b ofs Full ->
  Clight.eval_expr ge ve te m e (Vptr b ofs).
Proof.
  intros. eapply Clight.eval_Elvalue; eauto.
  apply Clight.deref_loc_copy; auto.
Qed.

Lemma aggregate_sem_cast: forall t b ofs m,
  access_mode t = By_copy ->
  Cop.sem_cast (Vptr b ofs) t t m = Some (Vptr b ofs).
Proof.
  intros t b ofs m Hcopy.
  destruct t; simpl in Hcopy; try discriminate; simpl.
  - destruct i, s; discriminate.
  - destruct f; discriminate.
  - unfold Cop.sem_cast, classify_cast.
    rewrite if_true by reflexivity. reflexivity.
  - unfold Cop.sem_cast, classify_cast.
    rewrite if_true by reflexivity. reflexivity.
Qed.

Lemma aggregate_sem_cast_compatible: forall destination source b ofs m,
  copy_type_compatible destination source = true ->
  Cop.sem_cast (Vptr b ofs) source destination m = Some (Vptr b ofs).
Proof.
  intros destination source b ofs m Hcompatible.
  destruct destination; destruct source; simpl in Hcompatible; try discriminate.
  all: destruct (ident_eq i i0); try discriminate; subst i0;
    unfold Cop.sem_cast, Cop.classify_cast;
    rewrite if_true by reflexivity; reflexivity.
Qed.
