Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_conseq.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.semax_straight.
Require Import VST.veric.memvals_at.
Require Import VST.veric.copy.
Require Import VST.veric.copy_lemmas.
Require Import VST.zlist.list_solver.

Local Open Scope pred.
Import LiftNotation.
Import compcert.lib.Maps.

Local Instance memval_default: Inhabitant memval := Undef.

Definition copy_compatible (n: Z) (destination source: val): Prop :=
  match destination, source with
  | Vptr b ofs, Vptr b' ofs' =>
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
      Ptrofs.unsigned ofs' + n <= Ptrofs.unsigned ofs \/
      Ptrofs.unsigned ofs + n <= Ptrofs.unsigned ofs'
  | _, _ => False
  end.

Lemma memvals_at_disjoint:
  forall sh1 sh2 bytes1 bytes2 b1 b2 ofs1 ofs2 phi,
  writable0_share sh1 ->
  Zlength bytes1 = Zlength bytes2 ->
  (memvals_at sh1 bytes1 (b1,ofs1) *
   memvals_at sh2 bytes2 (b2,ofs2))%pred phi ->
  b1 <> b2 \/ ofs1 + Zlength bytes1 <= ofs2 \/
    ofs2 + Zlength bytes1 <= ofs1.
Proof.
  intros sh1 sh2 bytes1 bytes2 b1 b2 ofs1 ofs2 phi WRITABLE LENGTH OWNED.
  destruct (eq_dec b1 b2) as [BLOCK | BLOCK]; auto.
  subst b2.
  destruct (Z_le_dec (ofs1 + Zlength bytes1) ofs2); auto.
  destruct (Z_le_dec (ofs2 + Zlength bytes1) ofs1); auto.
  exfalso.
  destruct OWNED as [left [right [JOIN [LEFT RIGHT]]]].
  destruct (memvals_at_resource sh1 bytes1 (b1,ofs1) left
    (b1,Z.max ofs1 ofs2) LEFT ltac:(split; auto; lia)) as [rsh1 RESOURCE1].
  destruct (memvals_at_resource sh2 bytes2 (b1,ofs2) right
    (b1,Z.max ofs1 ofs2) RIGHT ltac:(split; auto; lia)) as [rsh2 RESOURCE2].
  pose proof (resource_at_join _ _ _ (b1,Z.max ofs1 ofs2) JOIN) as AT.
  rewrite RESOURCE1, RESOURCE2 in AT.
  inv AT.
  contradiction (join_writable0_readable RJ WRITABLE rsh2).
Qed.

Lemma contents_cohere_getN:
  forall m phi bytes b ofs,
  contents_cohere m phi ->
  (forall z, ofs <= z < ofs + Zlength bytes ->
    exists sh rsh, phi @ (b,z) = YES sh rsh
      (VAL (Znth (z - ofs) bytes)) NoneP) ->
  Mem.getN (Z.to_nat (Zlength bytes)) ofs
    (PMap.get b (Mem.mem_contents m)) = bytes.
Proof.
  intros m phi bytes b ofs COHERE CONTENTS.
  apply Znth_eq_ext.
  * rewrite Zlength_correct, Mem.getN_length, Z2Nat.id
      by apply Zlength_nonneg; auto.
  * intros index BOUNDS.
    rewrite Zlength_correct, Mem.getN_length, Z2Nat.id in BOUNDS
      by apply Zlength_nonneg.
    specialize (CONTENTS (ofs + index) ltac:(lia)).
    destruct CONTENTS as [sh [rsh RESOURCE]].
    specialize (COHERE _ _ _ _ _ RESOURCE).
    destruct COHERE as [VALUE _].
    replace (ofs + index - ofs) with index in VALUE by lia.
    rewrite <- nth_Znth by (rewrite Zlength_correct, Mem.getN_length;
      rewrite Z2Nat.id by apply Zlength_nonneg; auto).
    pose proof (nth_getN m b ofs (ofs + index) (Zlength bytes)
      ltac:(lia) ltac:(pose proof (Zlength_nonneg bytes); lia)) as GET.
    replace (ofs + index - ofs) with index in GET by lia.
    change memval_default with Undef.
    rewrite <- GET.
    exact VALUE.
Qed.

(** Framed byte ownership determines the dry memory load. The proof
    first lifts each owned value resource through the frame, then uses
    juicy coherence to obtain both readable permissions and contents.
    No writable share or scalar decoding is needed. *)
Lemma memvals_at_loadbytes:
  forall jm sh bytes b ofs,
  (memvals_at sh bytes (b,ofs) * TT)%pred (m_phi jm) ->
  Mem.loadbytes (m_dry jm) b ofs (Zlength bytes) = Some bytes.
Proof.
  intros jm sh bytes b ofs OWNED.

  (* ===== Resource contents: the frame preserves each owned value ===== *)

  assert (CONTENTS: forall z, ofs <= z < ofs + Zlength bytes ->
    exists sh' rsh', m_phi jm @ (b,z) = YES sh' rsh'
      (VAL (Znth (z - ofs) bytes)) NoneP).
  {
    intros z RANGE.
    destruct OWNED as [owned [frame [JOIN [OWNED _]]]].
    destruct (memvals_at_resource sh bytes (b,ofs) owned (b,z)
      OWNED (conj eq_refl RANGE))
      as [rsh RESOURCE].
    pose proof (resource_at_join _ _ _ (b,z) JOIN) as AT.
    rewrite RESOURCE in AT.
    inv AT; eauto.
  }
  (* ===== Dry load: coherence supplies permissions and the byte list ===== *)

  assert (PERMISSION: Mem.range_perm (m_dry jm) b ofs
    (ofs + Zlength bytes) Cur Readable).
  {
    intros z RANGE.
    destruct (CONTENTS z RANGE) as [sh' [rsh' RESOURCE]].
    pose proof (juicy_mem_access jm (b,z)) as ACCESS.
    rewrite RESOURCE in ACCESS.
    unfold Mem.perm, access_at in *; simpl in *.
    rewrite ACCESS.
    unfold perm_of_sh.
    if_tac.
    { if_tac; constructor. }
    rewrite if_true by auto.
    constructor.
  }
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes.
  rewrite pred_dec_true by exact PERMISSION.
  f_equal.
  apply contents_cohere_getN with (phi := m_phi jm); auto.
  apply juicy_mem_contents.
Qed.

Lemma memvals_at_writable_perm:
  forall jm sh bytes b ofs,
  writable0_share sh ->
  (memvals_at sh bytes (b,ofs) * TT)%pred (m_phi jm) ->
  forall z, ofs <= z < ofs + Zlength bytes ->
    perm_order'' (perm_of_res (m_phi jm @ (b,z))) (Some Writable).
Proof.
  intros jm sh bytes b ofs WRITABLE OWNED z RANGE.
  destruct OWNED as [owned [frame [JOIN [OWNED _]]]].
  destruct (memvals_at_resource sh bytes (b,ofs) owned (b,z)
    OWNED (conj eq_refl RANGE)) as [rsh RESOURCE].
  pose proof (resource_at_join _ _ _ (b,z) JOIN) as AT.
  rewrite RESOURCE in AT.
  inv AT; simpl; apply join_writable01 in RJ; auto;
    unfold perm_of_sh; rewrite if_true by auto; if_tac; constructor.
Qed.

(** Writable ownership permits replacing a span by a list of the same
    length while preserving the exact frame. The result includes the
    dry store witness used to construct the new juicy memory. The proof
    builds an updated owned map, rejoins it with the original frame,
    and identifies its contents with the bytes stored by CompCert. *)
Lemma memvals_at_storebytes:
  forall jm sh old b ofs bytes frame,
  writable0_share sh ->
  Zlength bytes = Zlength old ->
  (memvals_at sh old (b,ofs) * exactly frame)%pred (m_phi jm) ->
  exists m', { STORE: Mem.storebytes (m_dry jm) b ofs bytes = Some m' |
    (memvals_at sh bytes (b,ofs) * exactly frame)%pred
      (m_phi (storebytes_juicy_mem jm m' b ofs bytes STORE)) }.
Proof.
  intros jm sh old b ofs bytes frame WRITABLE LENGTH OWNED.

  (* ===== Dry store: ownership supplies every writable permission ===== *)

  assert (PERMISSION: Mem.range_perm (m_dry jm) b ofs
    (ofs + Zlength bytes) Cur Writable).
  {
    intros z RANGE.
    assert (PERM: perm_order'' (perm_of_res (m_phi jm @ (b,z))) (Some Writable)).
    {
      apply memvals_at_writable_perm with (sh := sh) (bytes := old) (ofs := ofs); auto.
      destruct OWNED as [p [q [J [A B]]]].
      exists p, q.
      repeat split; auto.
      rewrite <- LENGTH; auto.
    }
    pose proof (juicy_mem_access jm (b,z)) as ACCESS.
    unfold Mem.perm, access_at in *; simpl in *.
    rewrite ACCESS.
    exact PERM.
  }
  destruct (Mem.range_perm_storebytes (m_dry jm) b ofs bytes)
    as [m' STORE].
  { rewrite <- Zlength_correct. exact PERMISSION. }
  exists m', STORE.

  (* ===== Updated ownership: only addresses in the span change ===== *)

  destruct OWNED as [owned [rest [JOIN [OWNED REST]]]].
  do 3 red in REST.
  pose (updated loc := if adr_range_dec (b,ofs) (Zlength bytes) loc
    then YES (Share.lub (res_retain (owned @ loc)) Share.Rsh)
      (readable_share_lub (writable0_readable writable0_Rsh))
      (VAL (contents_at m' loc)) NoneP
    else owned @ loc).
  destruct (make_rmap updated (ghost_of owned) (level jm))
    as [result [LEVEL [AT GHOST]]].
  {
    unfold updated, compose.
    extensionality loc.
    symmetry.
    if_tac.
    - unfold resource_fmap.
      rewrite preds_fmap_NoneP.
      reflexivity.
    - symmetry.
      rewrite level_juice_level_phi.
      apply join_level in JOIN as [<- _].
      apply resource_at_approx.
  }
  {
    rewrite level_juice_level_phi.
    apply join_level in JOIN as [<- _].
    apply ghost_of_approx.
  }
  exists result, rest.
  split3; auto.
  * (* Rejoining preserves the frame even inside the written span. *)
    apply resource_at_join2.
    - rewrite LEVEL. symmetry. simpl.
      unfold inflate_store; rewrite level_make_rmap; auto.
    - apply join_level in JOIN as [FIRST SECOND].
      rewrite SECOND. symmetry. simpl.
      unfold inflate_store; rewrite level_make_rmap; auto.
    - intro loc.
      rewrite AT.
      unfold updated.
      pose proof (resource_at_join _ _ _ loc JOIN) as RESJOIN.
      specialize (OWNED loc).
      hnf in OWNED.
      rewrite LENGTH.
      if_tac.
      + (* Writable ownership leaves the frame no readable value share. *)
        destruct OWNED as [rsh RESOURCE].
        hnf in RESOURCE.
        rewrite preds_fmap_NoneP in RESOURCE.
        rewrite RESOURCE in RESJOIN.
        rewrite (proof_irr rsh (writable0_readable WRITABLE)) in RESJOIN.
        destruct (YES_join_full _ _ _ _ _ _ RESJOIN)
          as [other_share [UNREADABLE WHOLE]]; auto.
        rewrite WHOLE.
        simpl.
        rewrite WHOLE in RESJOIN.
        inversion RESJOIN; subst.
        unfold inflate_store.
        rewrite resource_at_make_rmap.
        rewrite <- H5.
        rewrite RESOURCE.
        simpl.
        constructor.
        rewrite (semax_straight.writable0_lub_retainer_Rsh sh WRITABLE); auto.
      + (* Outside the span the original join remains valid. *)
        change (join (owned @ loc) (rest @ loc)
          (inflate_store m' (m_phi jm) @ loc)).
        unfold inflate_store.
        rewrite resource_at_make_rmap.
        case_eq (m_phi jm @ loc); intros;
          try solve [rewrite <- H0; exact RESJOIN].
        destruct k;
          try solve [rewrite <- H0; rewrite resource_at_approx; exact RESJOIN].
        destruct (juicy_mem_contents _ _ _ _ _ _ H0) as [_ PREDICATE].
        subst p.
        rewrite (storebytes_phi_elsewhere_eq jm _ _ _ _ STORE _ r m loc)
          by (try rewrite LENGTH; auto).
        rewrite H0 in RESJOIN.
        exact RESJOIN.
    - rewrite GHOST; simpl.
      unfold inflate_store; rewrite ghost_of_make_rmap.
      apply ghost_of_join; auto.
  * (* The new owned map describes precisely the stored byte list. *)
    unfold memvals_at.
    intro loc.
    hnf.
    if_tac.
    - exists (writable0_readable WRITABLE).
      hnf.
      rewrite preds_fmap_NoneP, AT.
      unfold updated.
      rewrite if_true by auto.
      specialize (OWNED loc).
      hnf in OWNED.
      rewrite <- LENGTH in OWNED.
      rewrite if_true in OWNED by auto.
      destruct OWNED as [rsh RESOURCE].
      hnf in RESOURCE.
      rewrite preds_fmap_NoneP in RESOURCE.
      rewrite RESOURCE.
      simpl.
      assert (contents_at m' loc = Znth (snd loc - ofs) bytes) as CONTENT.
      {
        destruct loc as [b' z].
        destruct H as [BLOCK RANGE].
        subst b'.
        pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as LOAD.
        rewrite <- Zlength_correct in LOAD.
        Transparent Mem.loadbytes.
        unfold Mem.loadbytes in LOAD.
        if_tac in LOAD; inv LOAD.
        rewrite (nth_getN m' b ofs z (Zlength bytes)) by
          (pose proof (Zlength_nonneg bytes); lia).
        rewrite H1.
        apply nth_Znth; simpl in *; lia.
      }
      rewrite CONTENT.
      apply YES_ext.
      apply (semax_straight.writable0_lub_retainer_Rsh sh WRITABLE).
    - do 3 red.
      rewrite AT.
      unfold updated.
      rewrite if_false by auto.
      specialize (OWNED loc).
      hnf in OWNED.
      rewrite <- LENGTH in OWNED.
      rewrite if_false in OWNED by auto.
      exact OWNED.
Qed.

Section copy_soundness.
Context {CS: compspecs} {Espec: OracleKind}.

(** The transfer rule reads source bytes from the whole resource map
    and replaces the destination while retaining [P]. Source ownership
    is a logical conjunct, so it can describe the destination itself.
    Clight copy compatibility must therefore be supplied explicitly.
    The proof evaluates both addresses, performs the framed byte store,
    then assembles the Clight step and the juicy resource guarantees. *)
Lemma semax_copy_transfer:
  forall Delta e1 e2 sh shsrc old bytes P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh ->
  Zlength old = sizeof (typeof e1) ->
  Zlength bytes = sizeof (typeof e1) ->
  semax Espec Delta
    (fun rho => |>
      (tc_lvalue Delta e1 rho && tc_lvalue Delta e2 rho &&
       !! (copy_aligned (typeof e1) (eval_lvalue e1 rho)) &&
       !! (copy_aligned (typeof e1) (eval_lvalue e2 rho)) &&
       !! (copy_compatible (sizeof (typeof e1))
         (eval_lvalue e1 rho) (eval_lvalue e2 rho)) &&
       (memvals_at_ptr shsrc bytes (eval_lvalue e2 rho) * TT) &&
       (memvals_at_ptr sh old (eval_lvalue e1 rho) * P rho)))%pred
    (Sassign e1 e2)
    (normal_ret_assert (fun rho =>
      (memvals_at_ptr sh bytes (eval_lvalue e1 rho) * P rho)%pred)).
Proof.
  intros Delta e1 e2 sh shsrc old bytes P TYPE MODE COMPLETE WRITABLE OLD_LENGTH LENGTH.

  (* ===== Evaluation: relate typed lvalues to concrete addresses ===== *)

  apply semax_pre with
    (fun rho => (|> tc_lvalue Delta e1 rho && |> tc_lvalue Delta e2 rho) &&
      |> (!! (copy_aligned (typeof e1) (eval_lvalue e1 rho)) &&
          !! (copy_aligned (typeof e1) (eval_lvalue e2 rho)) &&
          !! (copy_compatible (sizeof (typeof e1))
            (eval_lvalue e1 rho) (eval_lvalue e2 rho)) &&
          (memvals_at_ptr shsrc bytes (eval_lvalue e2 rho) * TT) &&
          (memvals_at_ptr sh old (eval_lvalue e1 rho) * P rho)))%pred.
  {
    intro rho.
    apply andp_left2.
    rewrite !predicates_hered.later_andp.
    intros w H. simpl in H |- *; tauto.
  }
  apply semax_straight_simple; auto.
  intros jm jm1 Delta' ge ve te rho k F f TS [TC1 TC2] TC4 Hcl Hge Hage
    [SPATIAL FUNASSERT] SUB.
  specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
  specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
  assert (TC: typecheck_environ Delta rho).
  { destruct TC4. eapply typecheck_environ_sub; eauto. }
  pose proof TC1 as TC1'.
  pose proof TC2 as TC2'.
  apply (tc_lvalue_sub _ _ _ TS) in TC1'; auto.
  apply (tc_lvalue_sub _ _ _ TS) in TC2'; auto.
  destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 SUB Hge
    (guard_environ_e1 _ _ _ TC4)) as [b [ofs [EVAL1 ADDRESS1]]]; auto.
  destruct (eval_lvalue_relate _ _ _ _ _ e2 jm1 SUB Hge
    (guard_environ_e1 _ _ _ TC4)) as [b' [ofs' [EVAL2 ADDRESS2]]]; auto.
  apply later_sepcon2 in SPATIAL.
  specialize (SPATIAL _ (age_laterR (age_jm_phi Hage))).
  destruct SPATIAL as [frame [owned [JOIN [FRAME OWNED]]]].
  destruct OWNED as [[[[ALIGN1 ALIGN2] COMPATIBLE] SOURCE] DESTINATION].
  rewrite ADDRESS1 in ALIGN1, COMPATIBLE, DESTINATION.
  rewrite ADDRESS2 in ALIGN2, COMPATIBLE, SOURCE.
  destruct DESTINATION as [destination [rest [DESTJOIN [[BOUND DESTINATION] REST]]]].
  destruct (join_assoc DESTJOIN (join_comm JOIN)) as [combined [COMBINED1 COMBINED2]].

  (* ===== Transfer: the exact frame includes all nondestination resources ===== *)

  assert (SOURCE_LOAD: Mem.loadbytes (m_dry jm1) b' (Ptrofs.unsigned ofs')
    (Zlength bytes) = Some bytes).
  {
    apply memvals_at_loadbytes with (sh := shsrc).
    destruct SOURCE as [src [other [SOURCE_JOIN [[SOURCE_BOUND SOURCE] _]]]].
    destruct (join_assoc SOURCE_JOIN (join_comm JOIN)) as [combined_source [J1 J2]].
    exists src, combined_source.
    repeat split; auto.
  }
  assert (STORE_OWNED:
    (memvals_at sh old (b,Ptrofs.unsigned ofs) * exactly combined)%pred (m_phi jm1)).
  {
    exists destination, combined.
    repeat split; auto.
    hnf; eauto.
  }
  destruct (memvals_at_storebytes jm1 sh old b (Ptrofs.unsigned ofs)
    bytes combined (writable_writable0 WRITABLE) ltac:(lia) STORE_OWNED)
    as [m' [STORE UPDATED]].

  (* ===== Soundness: the dry assignment and juicy invariants agree ===== *)

  exists (storebytes_juicy_mem jm1 m' b (Ptrofs.unsigned ofs) bytes STORE), te, rho.
  split3; auto.
  - subst; simpl; auto.
  - rewrite level_storebytes_juicy_mem. apply age_level; auto.
  - split; auto.
    split.
    + split3; auto.
      * (* Clight sees the same load, cast and block-copy store. *)
        rewrite <- (age_jm_dry Hage) in EVAL1, EVAL2, SOURCE_LOAD.
        econstructor; try eassumption.
        eapply aggregate_eval_expr; eauto.
        apply copy_type_compatible_source with (typeof e1); auto.
        apply aggregate_sem_cast_compatible; auto.
        eapply Clight.assign_loc_copy with (bytes := bytes); eauto.
        unfold copy_aligned in ALIGN2.
        rewrite (cenv_sub_sizeof SUB _ COMPLETE),
          (cenv_sub_alignof_blockcopy SUB _ COMPLETE); auto.
        unfold copy_aligned in ALIGN1.
        rewrite (cenv_sub_sizeof SUB _ COMPLETE),
          (cenv_sub_alignof_blockcopy SUB _ COMPLETE); auto.
        rewrite (cenv_sub_sizeof SUB _ COMPLETE); exact COMPATIBLE.
        rewrite (cenv_sub_sizeof SUB _ COMPLETE).
        change (Mem.loadbytes (m_dry jm) b' (Ptrofs.unsigned ofs')
          (sizeof (typeof e1)) = Some bytes).
        rewrite <- LENGTH.
        exact SOURCE_LOAD.
        simpl.
        rewrite (age_jm_dry Hage); exact STORE.
      * (* Aging followed by writable replacement permits resource decay. *)
        apply (resource_decay_trans _ (nextblock (m_dry jm1)) _ (m_phi jm1)).
        rewrite (age_jm_dry Hage); lia.
        apply age1_resource_decay; auto.
        apply resource_nodecay_decay, juicy_storebytes_nodecay.
        intros z RANGE.
        apply memvals_at_writable_perm with
          (sh := sh) (bytes := old) (ofs := Ptrofs.unsigned ofs); auto.
        exists destination, combined.
        repeat split; auto.
        rewrite OLD_LENGTH, <- LENGTH; auto.
      * (* The store preserves the aged level and ghost state. *)
        rewrite level_storebytes_juicy_mem.
        split.
        -- apply age_level; auto.
        -- simpl.
           unfold inflate_store.
           rewrite ghost_of_make_rmap.
           apply age1_ghost_of, age_jm_phi; auto.
    + split.
      * (* Recover the pointer bound and the hereditary framed assertion. *)
        rewrite ADDRESS1.
        unfold memvals_at_ptr.
        rewrite sepcon_comm, sepcon_assoc.
        eapply sepcon_derives; [| |exact UPDATED].
        -- intros result OWNED.
           split; auto.
           rewrite LENGTH, <- OLD_LENGTH; exact BOUND.
        -- intros result EXACT.
           destruct EXACT as [prior [NECESSARILY EXTENDS]].
           destruct (nec_join2 COMBINED1 NECESSARILY)
             as [rest' [frame' [REST_AGE [FRAME_AGE JOIN']]]].
           eapply pred_upclosed; eauto.
           exists rest', frame'; split3; auto;
             eapply pred_nec_hereditary; eauto.
      * (* Function assertions depend only on the preserved core. *)
        eapply (corable_core _ (m_phi jm1)), pred_hereditary;
          eauto; [|apply age_jm_phi; auto].
        symmetry. simpl. apply core_inflate_store.
Qed.

(** Separated destination and source ownership derives the nonoverlap
    required by Clight. The destination share is writable and the source
    share readable. Both byte lists have the destination size. The
    source assertion and arbitrary frame survive the assignment.
    The proof frames the source around transfer and rules out overlap
    by incompatibility of writable and readable shares at one address. *)
Lemma semax_copy:
  forall Delta e1 e2 sh1 sh2 old bytes P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true ->
  writable_share sh1 -> readable_share sh2 ->
  Zlength old = sizeof (typeof e1) -> Zlength bytes = sizeof (typeof e1) ->
  semax Espec Delta
    (fun rho => |>
      (tc_lvalue Delta e1 rho && tc_lvalue Delta e2 rho &&
       !! (copy_aligned (typeof e1) (eval_lvalue e1 rho)) &&
       !! (copy_aligned (typeof e1) (eval_lvalue e2 rho)) &&
       ((memvals_at_ptr sh1 old (eval_lvalue e1 rho) *
         memvals_at_ptr sh2 bytes (eval_lvalue e2 rho)) * P rho)))%pred
    (Sassign e1 e2)
    (normal_ret_assert (fun rho =>
      ((memvals_at_ptr sh1 bytes (eval_lvalue e1 rho) *
        memvals_at_ptr sh2 bytes (eval_lvalue e2 rho)) * P rho)%pred)).
Proof.
  intros Delta e1 e2 sh1 sh2 old bytes P TYPE MODE COMPLETE WRITABLE READABLE
    OLD_LENGTH LENGTH.
  assert (POST:
    (fun rho => ((memvals_at_ptr sh1 bytes (eval_lvalue e1 rho) *
      memvals_at_ptr sh2 bytes (eval_lvalue e2 rho)) * P rho)%pred) =
    (fun rho => (memvals_at_ptr sh1 bytes (eval_lvalue e1 rho) *
      (memvals_at_ptr sh2 bytes (eval_lvalue e2 rho) * P rho))%pred)).
  { extensionality rho. apply sepcon_assoc. }
  rewrite POST.
  eapply semax_pre.
  2: { apply semax_copy_transfer with (shsrc := sh2) (old := old); eauto. }
  intro rho.
  apply andp_left2.
  apply later_derives.
  intros phi [[[[TC1 TC2] ALIGN1] ALIGN2] SPATIAL].
  rewrite sepcon_assoc in SPATIAL.

  (* ===== Source view: expose readable bytes without consuming the frame ===== *)

  assert (SOURCE: (memvals_at_ptr sh2 bytes (eval_lvalue e2 rho) * TT)%pred phi).
  {
    destruct SPATIAL as [destination [rest [JOIN [DESTINATION SOURCE]]]].
    destruct SOURCE as [source [other [SOURCE_JOIN [SOURCE OTHER]]]].
    destruct (join_assoc SOURCE_JOIN (join_comm JOIN)) as [combined [J1 J2]].
    exists source, combined.
    repeat split; auto.
  }
  (* ===== Nonoverlap: separated shares exclude a shared byte address ===== *)

  assert (COMPATIBLE: copy_compatible (sizeof (typeof e1))
    (eval_lvalue e1 rho) (eval_lvalue e2 rho)).
  {
    rewrite <- sepcon_assoc in SPATIAL.
    destruct SPATIAL as [pair [other [JOIN [BOTH OTHER]]]].
    destruct BOTH as [destination [source [PAIR [DESTINATION SOURCE_BYTES]]]].
    destruct (eval_lvalue e1 rho); try contradiction.
    destruct (eval_lvalue e2 rho); try contradiction.
    destruct DESTINATION as [DESTINATION_BOUND DESTINATION].
    destruct SOURCE_BYTES as [SOURCE_BOUND SOURCE_BYTES].
    assert (DISJOINT:
      b <> b0 \/ Ptrofs.unsigned i + Zlength old <= Ptrofs.unsigned i0 \/
      Ptrofs.unsigned i0 + Zlength old <= Ptrofs.unsigned i).
    {
      apply memvals_at_disjoint with (sh1 := sh1) (sh2 := sh2)
        (bytes1 := old) (bytes2 := bytes) (phi := pair); auto; try lia.
      exists destination, source; repeat split; auto.
    }
    unfold copy_compatible.
    rewrite <- OLD_LENGTH.
    destruct DISJOINT as [BLOCK | [BEFORE | AFTER]].
    - (* Different memory blocks cannot overlap. *)
      left; congruence.
    - (* The destination ends before the source starts. *)
      right; right; right; exact BEFORE.
    - (* The source ends before the destination starts. *)
      right; right; left; exact AFTER.
  }
  repeat split; auto.
Qed.

(** Equal evaluated addresses permit self-copy with a single writable
    ownership assertion. No separated source assertion is required.
    The proof reuses that ownership as the readable source view and
    establishes the equal-address case of Clight copy compatibility. *)
Lemma semax_selfcopy:
  forall Delta e1 e2 sh bytes P,
  copy_type_compatible (typeof e1) (typeof e2) = true ->
  access_mode (typeof e1) = By_copy ->
  complete_type cenv_cs (typeof e1) = true -> writable_share sh ->
  Zlength bytes = sizeof (typeof e1) ->
  semax Espec Delta
    (fun rho => |>
      (tc_lvalue Delta e1 rho && tc_lvalue Delta e2 rho &&
       !! (eval_lvalue e1 rho = eval_lvalue e2 rho) &&
       !! (copy_aligned (typeof e1) (eval_lvalue e1 rho)) &&
       (memvals_at_ptr sh bytes (eval_lvalue e1 rho) * P rho)))%pred
    (Sassign e1 e2)
    (normal_ret_assert (fun rho =>
      (memvals_at_ptr sh bytes (eval_lvalue e1 rho) * P rho)%pred)).
Proof.
  intros Delta e1 e2 sh bytes P TYPE MODE COMPLETE WRITABLE LENGTH.
  eapply semax_pre.
  2: { apply semax_copy_transfer with (shsrc := sh) (old := bytes); eauto. }
  intro rho.
  apply andp_left2.
  apply later_derives.
  intros phi [[[[TC1 TC2] EQUAL] ALIGN] SPATIAL].
  assert (SOURCE: (memvals_at_ptr sh bytes (eval_lvalue e2 rho) * TT)%pred phi).
  {
    rewrite <- EQUAL.
    destruct SPATIAL as [destination [rest [JOIN [DESTINATION REST]]]].
    exists destination, rest.
    repeat split; auto.
  }
  assert (COMPATIBLE: copy_compatible (sizeof (typeof e1))
    (eval_lvalue e1 rho) (eval_lvalue e2 rho)).
  {
    rewrite <- EQUAL.
    destruct SPATIAL as [destination [rest [JOIN [DESTINATION REST]]]].
    destruct (eval_lvalue e1 rho); try contradiction.
    unfold copy_compatible.
    right; left; reflexivity.
  }
  repeat split; auto.
  rewrite <- EQUAL; auto.
Qed.

End copy_soundness.
