Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mpred.
Require Import VST.veric.shares.
Require Import VST.zlist.sublist.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.memvals_at.
Require Import VST.veric.val_lemmas.

Import RML. Import R.
Local Open Scope Z_scope.
Local Open Scope pred.

(** A readable block owns arbitrary readable memory values over its
    nonnegative size. Its exclusive end must stay below the pointer
    modulus, as required by [memory_block]. *)
Lemma memory_block_readable_VALspec_range: forall sh n b ofs,
  readable_share sh ->
  0 <= n ->
  memory_block sh n (Vptr b ofs) =
    !! (Ptrofs.unsigned ofs + n < Ptrofs.modulus) &&
    VALspec_range n sh (b, Ptrofs.unsigned ofs).
Proof.
  intros sh n b ofs Hreadable Hnonnegative.
  unfold memory_block.
  apply pred_ext.
  - intros phi [Hbound Hblock].
    rewrite memory_block'_eq in Hblock by
      (pose proof (Ptrofs.unsigned_range ofs);
       try rewrite Z2Nat.id by exact Hnonnegative;
       simpl in Hbound; lia).
    unfold memory_block'_alt in Hblock.
    rewrite if_true in Hblock by exact Hreadable.
    rewrite Z2Nat.id in Hblock by exact Hnonnegative.
    split; auto.
  - intros phi [Hbound Hblock].
    split; [exact Hbound |].
    rewrite memory_block'_eq by
      (pose proof (Ptrofs.unsigned_range ofs);
       try rewrite Z2Nat.id by exact Hnonnegative;
       simpl in Hbound; lia).
    unfold memory_block'_alt.
    rewrite if_true by exact Hreadable.
    rewrite Z2Nat.id by exact Hnonnegative.
    exact Hblock.
Qed.

(** A readable block is ownership of some list of CompCert memory
    values of exactly the block size. The pure pointer condition
    retains the stricter end bound of [memory_block]. No decoding or
    initialization condition is imposed on the memory values.

    The proof exposes readable range ownership, then transfers the
    existential list while retaining the pointer bound. *)
Lemma memory_block_memvals_at_ptr_eq: forall sh n p,
  readable_share sh ->
  0 <= n ->
  memory_block sh n p =
    !! (match p with
        | Vptr _ ofs => Ptrofs.unsigned ofs + n < Ptrofs.modulus
        | _ => False
        end) &&
    (EX bytes: list memval,
      !! (Zlength bytes = n) && memvals_at_ptr sh bytes p).
Proof.
  intros sh n p Hreadable Hnonnegative.
  destruct p; try (apply pred_ext; intros phi H; simpl in *; tauto).

  (* ===== Range ownership: expose the readable memory values ===== *)

  rewrite memory_block_readable_VALspec_range by auto.
  rewrite VALspec_range_memvals_at_eq by exact Hnonnegative.

  (* ===== Pointer ownership: retain the exclusive end bound ===== *)

  apply pred_ext.
  - intros phi [Hbound [bytes [Hlength Hbytes]]].
    assert (Hpointer : Ptrofs.unsigned i + Zlength bytes <= Ptrofs.modulus).
    { rewrite Hlength.
      simpl in Hbound.
      lia. }
    split.
    + exact Hbound.
    + exists bytes.
      split.
      * exact Hlength.
      * simpl.
        split.
        -- exact Hpointer.
        -- exact Hbytes.
  - intros phi [Hbound [bytes [Hlength [Hpointer Hbytes]]]].
    split.
    + exact Hbound.
    + exists bytes.
      split.
      * exact Hlength.
      * exact Hbytes.
Qed.

(** At a pointer whose exclusive end is below the modulus, a readable
    block is exactly existential ownership of a list of the requested
    nonnegative length. The list may contain undefined memory values. *)
Lemma memory_block_memvals_at_ptr_eq_in_range: forall sh n p,
  readable_share sh ->
  0 <= n ->
  (match p with
   | Vptr _ ofs => Ptrofs.unsigned ofs + n < Ptrofs.modulus
   | _ => False
   end) ->
  memory_block sh n p =
    EX bytes: list memval,
      !! (Zlength bytes = n) && memvals_at_ptr sh bytes p.
Proof.
  intros sh n p Hreadable Hnonnegative Hbound.
  rewrite memory_block_memvals_at_ptr_eq by auto.
  apply pred_ext.
  - intros phi [_ Hbytes].
    exact Hbytes.
  - intros phi Hbytes.
    split.
    + exact Hbound.
    + exact Hbytes.
Qed.

(** Readable block ownership reveals some memory values of the block
    size. This entailment discards the block end bound, unlike the
    preceding equivalences. *)
Lemma memory_block_memvals_at_ptr: forall sh n p,
  readable_share sh ->
  0 <= n ->
  memory_block sh n p |--
    EX bytes: list memval,
      !! (Zlength bytes = n) && memvals_at_ptr sh bytes p.
Proof.
  intros sh n p Hreadable Hnonnegative.
  rewrite memory_block_memvals_at_ptr_eq by auto.
  intros phi [Hbound Hbytes].
  exact Hbytes.
Qed.

Lemma memvals_at_ptr_split: forall sh bytes b ofs n,
  0 <= n <= Zlength bytes ->
  Ptrofs.unsigned ofs + Zlength bytes < Ptrofs.modulus ->
  memvals_at_ptr sh bytes (Vptr b ofs) =
    (memvals_at_ptr sh (sublist 0 n bytes) (Vptr b ofs) *
     memvals_at_ptr sh (sublist n (Zlength bytes) bytes)
       (offset_val n (Vptr b ofs)))%pred.
Proof.
  intros sh bytes b ofs n Hn Hbound.
  assert (Hsplit: bytes = sublist 0 n bytes ++ sublist n (Zlength bytes) bytes).
  { rewrite <- sublist_split by lia. symmetry. apply sublist_same; reflexivity. }
  rewrite Hsplit at 1.
  rewrite memvals_at_ptr_app by (rewrite <- Hsplit; auto).
  rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma memvals_at_ptr_sepcon: forall sh n1 n2 (R1 R2: list memval -> Prop) b ofs,
  0 <= n1 -> 0 <= n2 ->
  Ptrofs.unsigned ofs + (n1 + n2) < Ptrofs.modulus ->
  ((EX bytes1: list memval,
      !! (Zlength bytes1 = n1 /\ R1 bytes1) &&
      memvals_at_ptr sh bytes1 (Vptr b ofs)) *
   (EX bytes2: list memval,
      !! (Zlength bytes2 = n2 /\ R2 bytes2) &&
      memvals_at_ptr sh bytes2 (offset_val n1 (Vptr b ofs))))%pred =
  (EX bytes: list memval,
    !! (Zlength bytes = n1 + n2 /\
        R1 (sublist 0 n1 bytes) /\ R2 (sublist n1 (n1 + n2) bytes)) &&
    memvals_at_ptr sh bytes (Vptr b ofs))%pred.
Proof.
  intros sh n1 n2 R1 R2 b ofs Hn1 Hn2 Hbound. apply pred_ext.
  - intros phi [phi1 [phi2 [Hjoin
      [[bytes1 [[Hlen1 HR1] Hbytes1]] [bytes2 [[Hlen2 HR2] Hbytes2]]]]]].
    exists (bytes1 ++ bytes2). split.
    + split; [rewrite Zlength_app; lia |]. split.
      * rewrite sublist_app1 by lia. rewrite sublist_same by auto. exact HR1.
      * rewrite sublist_app2 by lia.
        replace (n1 - Zlength bytes1) with 0 by lia.
        replace (n1 + n2 - Zlength bytes1) with n2 by lia.
        rewrite sublist_same by auto. exact HR2.
    + rewrite memvals_at_ptr_app by (rewrite Zlength_app; lia).
      rewrite Hlen1. exists phi1, phi2.
      split; [exact Hjoin |]. split; assumption.
  - intros phi [bytes [[Hlen [HR1 HR2]] Hbytes]].
    rewrite (memvals_at_ptr_split sh bytes b ofs n1) in Hbytes by lia.
    destruct Hbytes as [phi1 [phi2 [Hjoin [Hbytes1 Hbytes2]]]].
    exists phi1, phi2. split; auto. split.
    + exists (sublist 0 n1 bytes). split; auto.
      split; auto. rewrite Zlength_sublist by lia. lia.
    + exists (sublist n1 (Zlength bytes) bytes). split; auto.
      split.
      * rewrite Zlength_sublist by lia. lia.
      * rewrite Hlen. exact HR2.
Qed.
