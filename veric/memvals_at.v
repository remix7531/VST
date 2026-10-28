Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mpred.
Require Import VST.veric.val_lemmas.
Require Import VST.zlist.sublist.

Import RML. Import R.
Local Open Scope Z_scope.
Local Open Scope pred.

(** [memvals_at sh bytes loc] owns exactly the consecutive addresses
    beginning at [loc], with share [sh] and the listed CompCert memory
    values. Outside that span it owns no resources. Memory values retain
    undefined bytes and pointer fragments, so this predicate does not
    impose a scalar decoding or a C type. A nonempty span requires a
    readable share through [yesat]. The empty list denotes [emp]. *)
Definition memvals_at (sh: share) (bytes: list memval) (loc: address)
    : mpred :=
  allp (jam (adr_range_dec loc (Zlength bytes))
    (fun address => yesat NoneP
      (VAL (@Znth memval Undef (snd address - snd loc) bytes)) sh address)
    noat).

Lemma memvals_at_nil: forall sh loc, memvals_at sh nil loc = emp.
Proof.
  intros. unfold memvals_at. rewrite emp_no.
  apply pred_ext; intros phi H address; simpl in *.
  all: specialize (H address); rewrite Zlength_nil in *;
    destruct (adr_range_dec loc 0 address); auto;
    unfold adr_range in a; destruct loc, address; simpl in a; lia.
Qed.

Lemma memvals_at_app: forall sh bytes1 bytes2 b ofs,
  memvals_at sh (bytes1 ++ bytes2) (b, ofs) =
  memvals_at sh bytes1 (b, ofs) *
  memvals_at sh bytes2 (b, ofs + Zlength bytes1).
Proof.
  intros. unfold memvals_at. rewrite Zlength_app.
  apply allp_jam_split2.
  - eexists; apply is_resource_pred_YES_VAL'.
  - eexists; apply is_resource_pred_YES_VAL'.
  - eexists; apply is_resource_pred_YES_VAL'.
  - split; intros [block offset]; unfold adr_range; simpl;
      pose proof (Zlength_nonneg bytes1);
      pose proof (Zlength_nonneg bytes2); intuition lia.
  - intros [block offset] H. unfold adr_range in H; simpl in *.
    rewrite app_Znth1 by lia. reflexivity.
  - intros [block offset] H. unfold adr_range in H; simpl in *.
    rewrite app_Znth2 by lia.
    replace (offset - ofs - Zlength bytes1)
      with (offset - (ofs + Zlength bytes1)) by lia.
    reflexivity.
  - intros address phi sh' kind Hrange Hyes Hresource.
    simpl in Hyes. destruct Hyes as [readable Hyes].
    rewrite Hyes in Hresource. inversion Hresource; subst. auto.
Qed.

Lemma memvals_at_split: forall sh bytes b ofs n,
  0 <= n <= Zlength bytes ->
  memvals_at sh bytes (b, ofs) =
  memvals_at sh (sublist 0 n bytes) (b, ofs) *
  memvals_at sh (sublist n (Zlength bytes) bytes) (b, ofs + n).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength bytes) bytes) at 1 by lia.
  rewrite (sublist_split 0 n (Zlength bytes) bytes) by lia.
  rewrite memvals_at_app, Zlength_sublist by lia.
  rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma memvals_at_resource: forall sh bytes loc phi address,
  memvals_at sh bytes loc phi ->
  adr_range loc (Zlength bytes) address ->
  exists readable: shares.readable_share sh,
    phi @ address = YES sh readable
      (VAL (@Znth memval Undef (snd address - snd loc) bytes))
      (SomeP (rmaps.ConstType unit) (fun _ => tt)).
Proof.
  intros. specialize (H address). simpl in H.
  rewrite if_true in H by auto. exact H.
Qed.

Lemma memvals_at_VALspec_range: forall sh bytes loc,
  memvals_at sh bytes loc |-- VALspec_range (Zlength bytes) sh loc.
Proof.
  intros sh bytes loc phi H address. specialize (H address).
  unfold memvals_at, VALspec_range in *. simpl in *.
  destruct (adr_range_dec loc (Zlength bytes) address); auto.
  eexists; eauto.
Qed.

Lemma VALspec_range_memvals_at: forall n sh loc,
  0 <= n ->
  VALspec_range n sh loc |--
  EX bytes: list memval, !! (Zlength bytes = n) && memvals_at sh bytes loc.
Proof.
  intros n sh loc Hn phi H.
  assert (n = Z.of_nat (Z.to_nat n))
    by (rewrite Z2Nat.id by lia; reflexivity).
  rewrite H0 in H |- *. remember (Z.to_nat n) as count in *.
  clear n Hn H0 Heqcount.
  assert (EXTRACT: exists bytes: list memval,
    length bytes = count /\
    forall address, adr_range loc (Z.of_nat count) address ->
      exists readable: shares.readable_share sh,
        phi @ address = YES sh readable
          (VAL (nth (Z.to_nat (snd address - snd loc)) bytes Undef))
          (SomeP (rmaps.ConstType unit) (fun _ => tt))).
  {
    assert (RESOURCES: forall address,
      adr_range loc (Z.of_nat count) address ->
      exists byte: memval, exists readable: shares.readable_share sh,
        phi @ address = YES sh readable (VAL byte)
          (SomeP (rmaps.ConstType unit) (fun _ => tt))).
    {
      intros address Hrange. specialize (H address). simpl in H.
      rewrite if_true in H by auto. exact H.
    }
    clear H. destruct loc as [block offset].
    revert offset RESOURCES. induction count; intros offset RESOURCES.
    - exists nil. split; auto. intros address Hrange.
      apply adr_range_non_zero in Hrange. simpl in Hrange. lia.
    - specialize (IHcount (offset + 1)). spec IHcount.
      + intros address Hrange. apply RESOURCES.
        apply adr_range_shift_1; auto.
      + assert (Hrange:
          adr_range (block, offset) (Z.of_nat (S count)) (block, offset))
          by (rewrite Nat2Z.inj_succ; repeat split; auto; lia).
        destruct (RESOURCES _ Hrange) as [head Hhead].
        destruct IHcount as [tail [Hlength Htail]].
        exists (head :: tail). split; [simpl; lia |].
        intros address Haddress. apply adr_range_S_split in Haddress.
        destruct Haddress as [Haddress | Haddress].
        * destruct (Htail address Haddress) as [readable Htailbyte].
          destruct address as [other_block other_offset].
          destruct Haddress as [_ Haddress]. exists readable. simpl in *.
          replace (Z.to_nat (other_offset - offset))
            with (S (Z.to_nat (other_offset - (offset + 1))));
            [exact Htailbyte |].
          replace (other_offset - offset)
            with (Z.succ (other_offset - (offset + 1))) by lia.
          rewrite Z2Nat.inj_succ by lia. reflexivity.
        * subst address. rewrite Z.sub_diag. simpl nth. exact Hhead.
  }
  destruct EXTRACT as [bytes [Hlength Hbytes]]. exists bytes. split.
  - change (Zlength bytes = Z.of_nat count).
    rewrite Zlength_correct, Hlength. reflexivity.
  - unfold memvals_at. intros address. specialize (H address).
    simpl in H |- *.
    assert (HlengthZ: Zlength bytes = Z.of_nat count)
      by (rewrite Zlength_correct, Hlength; reflexivity).
    rewrite HlengthZ. destruct (adr_range_dec loc (Z.of_nat count) address);
      auto.
    unfold Znth.
    rewrite if_false by
      (unfold adr_range in a; destruct loc, address; simpl in *; lia).
    apply Hbytes; auto.
Qed.

Lemma VALspec_range_memvals_at_eq: forall n sh loc,
  0 <= n ->
  VALspec_range n sh loc =
  EX bytes: list memval, !! (Zlength bytes = n) && memvals_at sh bytes loc.
Proof.
  intros. apply pred_ext.
  - apply VALspec_range_memvals_at; auto.
  - apply exp_left; intro bytes. apply prop_andp_left; intro Hlength.
    rewrite <- Hlength. apply memvals_at_VALspec_range.
Qed.

(** The pointer interface adds the bound needed to use machine offsets
    without wrapping the represented span. Nonpointer values denote
    [FF], including for an empty list. The bound permits a span to end
    at [Ptrofs.modulus]. Splitting with [offset_val] below uses a strict
    bound so the second start stays representable even for an empty
    suffix. *)
Definition memvals_at_ptr (sh: share) (bytes: list memval) (p: val)
    : mpred :=
  match p with
  | Vptr b ofs =>
      !! (Ptrofs.unsigned ofs + Zlength bytes <= Ptrofs.modulus) &&
      memvals_at sh bytes (b, Ptrofs.unsigned ofs)
  | _ => FF
  end.

Lemma memvals_at_ptr_isptr: forall sh bytes p,
  memvals_at_ptr sh bytes p |-- !! isptr p.
Proof.
  intros. destruct p; simpl; intros phi H; simpl in *; auto.
Qed.

Lemma memvals_at_ptr_bounds: forall sh bytes b ofs,
  memvals_at_ptr sh bytes (Vptr b ofs) |--
  !! (Ptrofs.unsigned ofs + Zlength bytes <= Ptrofs.modulus).
Proof.
  intros sh bytes b ofs phi H. exact (proj1 H).
Qed.

Lemma memvals_at_ptr_nil: forall sh p,
  memvals_at_ptr sh nil p = !! isptr p && emp.
Proof.
  intros. destruct p; simpl;
    try (apply pred_ext; intros phi H; simpl in *; tauto).
  rewrite memvals_at_nil, Zlength_nil.
  apply pred_ext; intros phi H; destruct H; split; auto.
  simpl. pose proof (Ptrofs.unsigned_range i); lia.
Qed.

Lemma memvals_at_ptr_app: forall sh bytes1 bytes2 b ofs,
  Ptrofs.unsigned ofs + Zlength (bytes1 ++ bytes2) < Ptrofs.modulus ->
  memvals_at_ptr sh (bytes1 ++ bytes2) (Vptr b ofs) =
  memvals_at_ptr sh bytes1 (Vptr b ofs) *
  memvals_at_ptr sh bytes2 (offset_val (Zlength bytes1) (Vptr b ofs)).
Proof.
  intros sh bytes1 bytes2 b ofs Hbound. rewrite Zlength_app in Hbound.
  pose proof (Zlength_nonneg bytes1). pose proof (Zlength_nonneg bytes2).
  pose proof (Ptrofs.unsigned_range ofs).
  assert (Hoffset:
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Zlength bytes1))) =
    Ptrofs.unsigned ofs + Zlength bytes1).
  {
    rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr (Zlength bytes1))
      by (unfold Ptrofs.max_unsigned; lia).
    rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    reflexivity.
  }
  unfold offset_val, memvals_at_ptr. rewrite Hoffset, Zlength_app.
  rewrite !prop_true_andp by lia. apply memvals_at_app.
Qed.

Lemma memvals_at_nth: forall sh bytes loc,
  memvals_at sh bytes loc =
  allp (jam (adr_range_dec loc (Zlength bytes))
    (fun address => yesat NoneP
      (VAL (nth (Z.to_nat (snd address - snd loc)) bytes Undef)) sh address)
    noat).
Proof.
  intros. unfold memvals_at. f_equal.
  apply functional_extensionality; intro address.
  destruct (adr_range_dec loc (Zlength bytes) address) as [Hrange | Hrange].
  - rewrite !jam_true by auto. unfold Znth.
    rewrite if_false by
      (destruct loc, address; unfold adr_range in Hrange; simpl in *; lia).
    reflexivity.
  - rewrite !jam_false by auto. reflexivity.
Qed.

(** A chunk assertion is exact ownership of some memory values of the
    chunk size whose decoding is [v]. Alignment and the nonwrapping
    bound are supplied by the caller. Decoding need not select a unique
    representation, which is why the byte list is existential. *)
Lemma address_mapsto_memvals_at: forall ch v sh loc,
  snd loc + size_chunk ch <= Ptrofs.modulus ->
  (align_chunk ch | snd loc) ->
  address_mapsto ch v sh loc =
  EX bytes: list memval,
    !! (Zlength bytes = size_chunk ch /\ decode_val ch bytes = v) &&
    memvals_at sh bytes loc.
Proof.
  intros ch v sh loc Hbound Halign. apply pred_ext.
  - intros phi [bytes [[Hlength [Hdecode [Hsize Haligned]]] Hbytes]].
    exists bytes. split.
    + split; auto. rewrite Zlength_correct, Hlength.
      symmetry; apply size_chunk_conv.
    + rewrite memvals_at_nth.
      assert (HlengthZ: Zlength bytes = size_chunk ch)
        by (rewrite Zlength_correct, Hlength;
            symmetry; apply size_chunk_conv).
      rewrite HlengthZ. exact Hbytes.
  - intros phi [bytes [[Hlength Hdecode] Hbytes]]. exists bytes. split.
    + split.
      * rewrite size_chunk_conv, Zlength_correct in Hlength.
        apply Nat2Z.inj; auto.
      * repeat split; auto.
    + rewrite memvals_at_nth, Hlength in Hbytes. exact Hbytes.
Qed.
