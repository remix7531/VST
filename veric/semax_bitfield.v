(** * Soundness of carrier-based bitfield assignment. *)

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
Require Import VST.veric.copy_lemmas.
Require Import VST.veric.bitfield.

Local Open Scope pred.
Import LiftNotation.
Import compcert.lib.Maps.

(** Writable carrier ownership supplies writable dry memory permissions
    at every byte in its chunk. *)
Lemma bitfield_carrier_writable_perm: forall jm ch v sh b ofs,
  writable0_share sh ->
  (address_mapsto ch v sh (b,ofs) * TT)%pred (m_phi jm) ->
  forall z, ofs <= z < ofs + size_chunk ch ->
  perm_order'' (perm_of_res (m_phi jm @ (b,z))) (Some Writable).
Proof.
  intros jm ch v sh b ofs WRITE OWNED z RANGE.
  destruct OWNED as [owned [rest [JOIN [OWNED _]]]].
  destruct OWNED as [bytes [_ OWNED]].
  specialize (OWNED (b,z)). hnf in OWNED.
  rewrite if_true in OWNED by (split; auto).
  destruct OWNED as [rsh RESOURCE]. hnf in RESOURCE.
  pose proof (resource_at_join _ _ _ (b,z) JOIN) as AT.
  rewrite RESOURCE in AT. inv AT; simpl; apply join_writable01 in RJ; auto;
    unfold perm_of_sh; rewrite if_true by auto; if_tac; constructor.
Qed.

(** A root lvalue and its layout descriptor determine the field lvalue.
    The descriptor is retained for the CompCert bitfield assignment. *)
Lemma bitfield_eval_lvalue: forall ge ve te m root field target_type b ofs delta descriptor,
  bitfield_field (genv_cenv ge) (typeof root) field delta descriptor ->
  Clight.eval_lvalue ge ve te m root b ofs Full ->
  Clight.eval_lvalue ge ve te m (Efield root field target_type)
    b (Ptrofs.add ofs (Ptrofs.repr delta)) descriptor.
Proof.
  intros ge ve te m root field target_type b ofs delta descriptor FIELD ROOT.
  assert (EVAL: Clight.eval_expr ge ve te m root (Vptr b ofs)).
  { eapply aggregate_eval_expr; eauto using bitfield_field_by_copy. }
  destruct (typeof root) eqn:TYPE; simpl in FIELD; try contradiction.
  - destruct FIELD as [co [LOOKUP OFFSET]].
    eapply Clight.eval_Efield_struct; eauto.
  - destruct FIELD as [co [LOOKUP OFFSET]].
    eapply Clight.eval_Efield_union; eauto.
Qed.

Section BitfieldStore.
Context {CS: compspecs} {Espec: OracleKind}.

(** Store a cast integer into a nonvolatile bitfield of a struct or
    union. The descriptor must have positive width within the declared
    integer size and fit at its nonnegative position in the carrier.
    The effective target is signed when the field is narrower than the
    declared size, otherwise it retains the descriptor signedness.
    Writable ownership covers the initialized whole carrier at the
    root address plus [delta]. The postcondition returns that carrier
    after [Int.bitfield_insert] and chunk normalization, with [P].

    The proof obtains the typed root and cast evaluations, uses carrier
    ownership to construct a juicy memory store, then realizes the
    Clight bitfield step and restores the untouched resources. *)
Lemma semax_store_bitfield:
  forall Delta root field rhs delta sz sg pos width attr sh carrier new_value P,
  bitfield_field cenv_cs (typeof root) field delta (Bits sz sg pos width) ->
  0 <= pos -> 0 < width <= bitsize_intsize sz ->
  pos + width <= Cop.bitsize_carrier sz ->
  attr_volatile attr = false -> writable0_share sh ->
  let target_type := Tint sz (if zlt width (bitsize_intsize sz) then Signed else sg) attr in
  semax Espec Delta
    (fun rho => |>
      (tc_lvalue Delta root rho && tc_expr Delta (Ecast rhs target_type) rho &&
       !! (force_val (sem_cast (typeof rhs) target_type (eval_expr rhs rho)) =
           Vint new_value) &&
       (mapsto sh (bitfield_carrier_type sz)
          (offset_val delta (eval_lvalue root rho)) (Vint carrier) * P rho)))
    (Sassign (Efield root field target_type) rhs)
    (normal_ret_assert (fun rho =>
      mapsto sh (bitfield_carrier_type sz)
        (offset_val delta (eval_lvalue root rho))
        (Val.load_result (Cop.chunk_for_carrier sz)
          (Vint (Int.bitfield_insert (Cop.first_bit sz pos width) width carrier new_value))) *
      P rho)).
Proof.
  intros Delta root field rhs delta sz sg pos width attr sh carrier new_value P
    FIELD POS WIDTH RANGE NONVOL WRITE target_type.

  (* ===== Setup: expose the later typechecking obligations ===== *)

  apply semax_pre with
    (fun rho => (|> tc_lvalue Delta root rho &&
       |> tc_expr Delta (Ecast rhs target_type) rho) &&
       |> (!! (force_val (sem_cast (typeof rhs) target_type (eval_expr rhs rho)) =
                Vint new_value) &&
          (mapsto sh (bitfield_carrier_type sz)
             (offset_val delta (eval_lvalue root rho)) (Vint carrier) * P rho))).
  { intro rho.
    apply andp_left2.
    rewrite !later_andp.
    intros phi H.
    simpl in H |- *.
    tauto. }
  apply semax_straight_simple; auto.
  intros jm jm1 Delta' ge ve te rho k F f TS [TC1 TC2] TC4 Hcl Hge Hage
    [SPATIAL FUNASSERT] SUB.
  specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
  specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
  assert (TC: typecheck_environ Delta rho).
  { destruct TC4.
    eapply typecheck_environ_sub; eauto. }
  pose proof TC1 as TC1'.
  pose proof TC2 as TC2'.
  apply (tc_lvalue_sub _ _ _ TS) in TC1'; auto.
  apply (tc_expr_sub _ _ _ TS) in TC2'; auto.
  unfold tc_expr in TC2, TC2'.
  simpl in TC2, TC2'.
  rewrite denote_tc_assert_andp in TC2, TC2'.
  simpl in TC2, TC2'.
  super_unfold_lift.
  destruct TC2 as [TC2 TC3].
  destruct TC2' as [TC2' TC3'].
  destruct (eval_lvalue_relate _ _ _ _ _ root jm1 SUB Hge
    (guard_environ_e1 _ _ _ TC4)) as [b [ofs [ROOT ROOT_ADDRESS]]]; auto.

  (* ===== Ownership: isolate the initialized carrier and its frame ===== *)

  apply later_sepcon2 in SPATIAL.
  specialize (SPATIAL _ (age_laterR (age_jm_phi Hage))).
  destruct SPATIAL as [frame [owned [JOIN [FRAME [CAST OWNED]]]]].
  rewrite ROOT_ADDRESS in OWNED.
  unfold offset_val in OWNED.
  destruct OWNED as [destination [rest [DESTJOIN [DEST REST]]]].
  unfold mapsto in DEST.
  rewrite bitfield_carrier_access_mode, bitfield_carrier_nonvolatile in DEST.
  rewrite if_true in DEST by auto using writable0_readable.
  assert (CARRIER_MAPSTO:
    address_mapsto (Cop.chunk_for_carrier sz) (Vint carrier) sh
      (b,Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) destination).
  { destruct DEST as [[VALUE DEST] | [IMPOSSIBLE _]].
    - exact DEST.
    - discriminate. }
  clear DEST.
  destruct (join_assoc DESTJOIN (join_comm JOIN))
    as [combined [COMBINED1 COMBINED2]].
  pose (inserted := Int.bitfield_insert (Cop.first_bit sz pos width)
    width carrier new_value).
  assert (OLD_OWNED:
    (address_mapsto (Cop.chunk_for_carrier sz) (Vint carrier) sh
      (b,Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) * TT)%pred (m_phi jm1)).
  { exists destination, combined.
    repeat split; auto. }
  assert (STORE_OWNED:
    (address_mapsto (Cop.chunk_for_carrier sz) (Vint carrier) sh
      (b,Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) *
      exactly combined)%pred (m_phi jm1)).
  { exists destination, combined.
    repeat split; auto.
    hnf; eauto. }
  assert (LOAD: Mem.load (Cop.chunk_for_carrier sz) (m_dry jm1) b
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = Some (Vint carrier)).
  { apply core_load_load'.
    apply mapsto_core_load with sh.
    exact OLD_OWNED. }

  (* ===== Store: preserve the other resources around the carrier ===== *)

  destruct (address_mapsto_can_store' jm1 (Cop.chunk_for_carrier sz)
    (Cop.chunk_for_carrier sz) (Vint carrier) sh WRITE b
    (Ptrofs.add ofs (Ptrofs.repr delta)) (Vint inserted) combined STORE_OWNED)
    as [m' [STORE UPDATED]].
  { apply decode_encode_val_ok_same. }
  { pose proof CARRIER_MAPSTO as ALIGNED.
    rewrite address_mapsto_align in ALIGNED.
    exact (proj2 ALIGNED). }
  rewrite exp_sepcon1 in UPDATED.
  destruct UPDATED as [updated UPDATED].
  rewrite sepcon_andp_prop1 in UPDATED.
  destruct UPDATED as [DE UPDATED].
  change (decode_encode_val (Vint inserted) (Cop.chunk_for_carrier sz)
    (Cop.chunk_for_carrier sz) updated) in DE.
  apply decode_encode_val_similar in DE; auto.
  subst updated.

  (* ===== Clight step: connect the carrier store to field assignment ===== *)

  exists (store_juicy_mem _ _ _ _ _ _ STORE), te, rho.
  split3; auto.
  - (* The store keeps the evaluation environment. *)
    subst.
    simpl; auto.
  - (* A juicy store preserves the required execution level. *)
    rewrite level_store_juicy_mem.
    apply age_level; auto.
  - split; auto.
    split.
    + split3; auto.
      { assert (RHS: Clight.eval_expr ge ve te (m_dry jm1) rhs (eval_expr rhs rho)).
        { eapply eval_expr_relate; eauto using guard_environ_e1. }
        rewrite <- (age_jm_dry Hage) in ROOT, RHS, LOAD.
        econstructor; try eassumption.
        - eapply bitfield_eval_lvalue.
          + eapply bitfield_field_cenv_sub; eauto.
          + exact ROOT.
        - instantiate (1 := Vint new_value).
          simpl.
          assert (RHS_TYPED: tc_val (typeof rhs) (eval_expr rhs rho)).
          { eapply typecheck_expr_sound; eauto. }
          rewrite (age_jm_dry Hage).
          rewrite <- (CAST : force_val
            (sem_cast (typeof rhs) target_type (eval_expr rhs rho)) = Vint new_value).
          rewrite cop2_sem_cast' by auto.
          eapply cast_exists; eauto.
        - eapply Clight.assign_loc_bitfield.
          unfold target_type.
          eapply Cop.store_bitfield_intro with (c := carrier); eauto.
          + unfold Mem.loadv.
            destruct (zle _ _); auto.
            pose proof (address_mapsto_offset_range CARRIER_MAPSTO) as BOUND.
            lia.
          + unfold Mem.storev.
            simpl m_dry.
            destruct (zle _ _).
            * rewrite (age_jm_dry Hage).
              exact STORE.
            * pose proof (address_mapsto_offset_range CARRIER_MAPSTO) as BOUND.
              lia. }
      { apply (resource_decay_trans _ (nextblock (m_dry jm1)) _ (m_phi jm1)).
        rewrite (age_jm_dry Hage); lia.
        apply age1_resource_decay; auto.
        apply resource_nodecay_decay.
        apply juicy_store_nodecay.
        eapply bitfield_carrier_writable_perm; eauto. }
      { rewrite level_store_juicy_mem.
        split.
        - apply age_level; auto.
        - simpl.
          unfold inflate_store.
          rewrite ghost_of_make_rmap.
          apply age1_ghost_of.
          apply age_jm_phi; auto. }
    + split.
      { (* The updated carrier rejoins the aged frame and [P]. *)
        rewrite ROOT_ADDRESS.
        unfold offset_val.
        rewrite sepcon_comm, sepcon_assoc.
        eapply sepcon_derives with (q := exactly combined).
        - unfold mapsto.
          rewrite bitfield_carrier_access_mode, bitfield_carrier_nonvolatile.
          rewrite if_true by auto using writable0_readable.
          apply orp_right1.
          rewrite prop_true_andp by apply bitfield_carrier_load_result_type.
          apply derives_refl.
        - intros result EXACT.
          destruct EXACT as [prior [NECESSARILY EXTENDS]].
          destruct (nec_join2 COMBINED1 NECESSARILY)
            as [rest' [frame' [REST_AGE [FRAME_AGE JOIN']]]].
          eapply pred_upclosed; eauto.
          exists rest', frame'.
          split3; auto;
            eapply pred_nec_hereditary; eauto.
        - exact UPDATED. }
      { (* The store leaves the core facts needed by function assertions. *)
        eapply (corable_core _ (m_phi jm1)).
        - apply corable_funassert.
        - symmetry.
          simpl.
          apply core_inflate_store.
        - eapply pred_hereditary; eauto.
          apply age_jm_phi; auto. }
Qed.

End BitfieldStore.
