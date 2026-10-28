Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.compact_prod_sum.
Require Import VST.floyd.aggregate_pred.
Require Import VST.floyd.fieldlist.
Require Import VST.floyd.memory_block_memvals.
Require Import VST.zlist.sublist.

Import LiftNotation.
Local Open Scope logic.

(** The member intervals partition the interval from [start] to
    [finish] in declaration order. Empty intervals are allowed, and
    an empty member list requires equal endpoints. *)
Fixpoint contiguous_member_ranges (m: members) (start finish: Z)
    (lo hi: member -> Z): Prop :=
  match m with
  | nil => start = finish
  | it :: rest =>
      lo it = start /\ start <= hi it /\
      contiguous_member_ranges rest (hi it) finish lo hi
  end.

Lemma contiguous_member_ranges_bounds: forall m start finish lo hi,
  contiguous_member_ranges m start finish lo hi ->
  start <= finish /\
  forall it, In it m -> start <= lo it /\ lo it <= hi it /\ hi it <= finish.
Proof.
  induction m as [| a m IH]; intros start finish lo hi H.
  - simpl in H. subst finish. split; [lia |]. intros it H; contradiction.
  - destruct H as [Hlo [Hhi Htail]].
    destruct (IH _ _ _ _ Htail) as [Hend Hbounds].
    split; [lia |]. intros it [Heq | Hin].
    + subst it. rewrite Hlo. lia.
    + specialize (Hbounds it Hin). lia.
Qed.

Lemma contiguous_member_ranges_ext: forall m start finish lo hi lo' hi',
  (forall it, In it m -> lo it = lo' it /\ hi it = hi' it) ->
  contiguous_member_ranges m start finish lo hi ->
  contiguous_member_ranges m start finish lo' hi'.
Proof.
  induction m as [| a m IH];
    intros start finish lo hi lo' hi' Hext Hranges; simpl in *; auto.
  destruct (Hext a (or_introl eq_refl)) as [Hlo Hhi].
  destruct Hranges as [Hstart [Hbound Htail]]. rewrite <- Hlo, <- Hhi.
  split; [exact Hstart |]. split; [exact Hbound |].
  apply (IH _ _ lo hi); auto.
Qed.

Lemma struct_Prop_ext: forall m {A: member -> Type}
    (P Q: forall it, A it -> Prop) v,
  (forall it, In it m -> forall x, P it x <-> Q it x) ->
  struct_Prop m P v <-> struct_Prop m Q v.
Proof.
  intros m. destruct m as [| a m]; intros; simpl; [tauto |].
  revert a v H. induction m as [| b m IH]; intros a v H.
  - simpl. apply H. left; reflexivity.
  - change (P a (fst v) /\ struct_Prop (b :: m) P (snd v) <->
      Q a (fst v) /\ struct_Prop (b :: m) Q (snd v)).
    rewrite (H a (or_introl eq_refl)).
    change (forall (a0: member) (v0: compact_prod (map A (a0 :: m))),
      (forall it, In it (a0 :: m) -> forall x, P it x <-> Q it x) ->
      struct_Prop (a0 :: m) P v0 <-> struct_Prop (a0 :: m) Q v0) in IH.
    rewrite (IH b (snd v)); [tauto |].
    intros it Hin. apply H. right; exact Hin.
Qed.

(** A nonempty union selects one member relation over a shared list
    of memory values and owns that list once. No ownership of inactive
    members is required. The nonempty premise is essential because
    the empty union predicate owns no memory. *)
Lemma union_pred_memvals_at_ptr_nonempty: forall sh m sz
    {A: member -> Type} (v: compact_sum (map A m))
    (R: forall it, A it -> list memval -> Prop) p,
  m <> nil ->
  union_pred m
    (fun it x p => EX bytes: list memval,
      !! (Zlength bytes = sz /\ R it x bytes) && memvals_at_ptr sh bytes p) v p =
  EX bytes: list memval,
    !! (Zlength bytes = sz /\ union_Prop m (fun it x => R it x bytes) v) &&
    memvals_at_ptr sh bytes p.
Proof.
  intros sh m. destruct m as [| a m]; intros; [contradiction |].
  revert a v H. induction m as [| b m IH]; intros a v H.
  - reflexivity.
  - destruct v as [v | v].
    + reflexivity.
    + apply IH. discriminate.
Qed.

Local Lemma memvals_at_ptr_sepcon_logic: forall sh n1 n2
    (R1 R2: list memval -> Prop) b ofs,
  0 <= n1 -> 0 <= n2 ->
  Ptrofs.unsigned ofs + (n1 + n2) < Ptrofs.modulus ->
  (EX bytes1: list memval,
    !! (Zlength bytes1 = n1 /\ R1 bytes1) &&
    memvals_at_ptr sh bytes1 (Vptr b ofs)) *
  (EX bytes2: list memval,
    !! (Zlength bytes2 = n2 /\ R2 bytes2) &&
    memvals_at_ptr sh bytes2 (offset_val n1 (Vptr b ofs))) =
  EX bytes: list memval,
    !! (Zlength bytes = n1 + n2 /\
        R1 (sublist 0 n1 bytes) /\ R2 (sublist n1 (n1 + n2) bytes)) &&
    memvals_at_ptr sh bytes (Vptr b ofs).
Proof.
  intros. exact (memvals_at_ptr_sepcon sh n1 n2 R1 R2 b ofs H H0 H1).
Qed.

(** Contiguous member slots combine into one owned memory value list.
    Each relation sees its slot relative to [start]. The interval and
    pointer bounds prevent modular wraparound. This statement only
    combines ownership, it does not prescribe slot contents. *)
Lemma struct_pred_memvals_contiguous: forall sh m start finish lo hi
    {A: member -> Type} (v: compact_prod (map A m))
    (R: forall it, A it -> list memval -> Prop) b ofs p,
  contiguous_member_ranges m start finish lo hi ->
  0 <= ofs -> 0 <= start -> ofs + finish < Ptrofs.modulus ->
  struct_pred m
    (fun it x _ => EX bytes: list memval,
      !! (Zlength bytes = hi it - lo it /\ R it x bytes) &&
      memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr (ofs + lo it)))) v p =
  EX bytes: list memval,
    !! (Zlength bytes = finish - start /\
      struct_Prop m
        (fun it x => R it x (sublist (lo it - start) (hi it - start) bytes)) v) &&
    memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr (ofs + start))).
Proof.
  intros sh m. destruct m as [| a m].
  - intros start finish lo hi A v R b ofs p Hranges Hofs Hstart Hend.
    simpl in Hranges. subst finish.
    replace (start - start) with 0 by lia.
    simpl struct_pred; simpl struct_Prop.
    apply pred_ext.
    + apply exp_right with (@nil memval).
      rewrite memvals_at_ptr_nil.
      change (emp |-- !! (Zlength (@nil memval) = 0 /\ True) &&
        (!! True && emp)).
      rewrite Zlength_nil. normalize.
      apply andp_right; [apply prop_right; auto | apply derives_refl].
    + apply exp_left; intro bytes. normalize.
      assert (bytes = nil) by (apply Zlength_nil_inv; lia). subst bytes.
      rewrite memvals_at_ptr_nil.
      change ((!! True && emp) |-- emp). normalize.
  - revert a.
    induction m as [| a' m IH];
      intros a start finish lo hi A v R b ofs p Hranges Hofs Hstart Hend.
    + destruct Hranges as [Hlo [Hrange Hfinish]]. simpl in Hfinish.
      subst finish.
      change ((EX bytes: list memval,
        !! (Zlength bytes = hi a - lo a /\ R a v bytes) &&
        memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr (ofs + lo a)))) =
        (EX bytes: list memval,
        !! (Zlength bytes = hi a - start /\
          R a v (sublist (lo a - start) (hi a - start) bytes)) &&
        memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr (ofs + start))))).
      rewrite Hlo. replace (start - start) with 0 by lia.
      apply pred_ext; apply exp_left; intro bytes;
        apply derives_extract_prop; intros [Hlen HR];
        apply exp_right with bytes; rewrite sublist_same in * by lia;
        apply andp_right;
        [apply prop_right; auto | apply derives_refl |
         apply prop_right; auto | apply derives_refl].
    + destruct Hranges as [Hlo [Hsplit Htail]].
      destruct (contiguous_member_ranges_bounds _ _ _ _ _ Htail)
        as [Htailend Hbounds].
      match goal with
      | |- struct_pred (a :: a' :: m) ?P v p = _ =>
          change (struct_pred (a :: a' :: m) P v p) with
            (P a (fst v) p * struct_pred (a' :: m) P (snd v) p)
      end.
      rewrite (IH a' (hi a) finish lo hi A (snd v) R b ofs p) by (auto; lia).
      rewrite Hlo.
      assert (Hptr: Vptr b (Ptrofs.repr (ofs + hi a)) =
        offset_val (hi a - start) (Vptr b (Ptrofs.repr (ofs + start)))).
      { unfold offset_val. simpl. unfold Ptrofs.add.
        rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
        f_equal. f_equal. lia. }
      rewrite Hptr.
      rewrite (memvals_at_ptr_sepcon_logic sh (hi a - start) (finish - hi a))
        by (try rewrite Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
      replace (hi a - start + (finish - hi a)) with (finish - start) by lia.
      apply f_equal. extensionality bytes.
      apply f_equal2; [| reflexivity]. apply f_equal.
      change ((Zlength bytes = finish - start /\
        R a (fst v) (sublist 0 (hi a - start) bytes) /\
        struct_Prop (a' :: m)
          (fun it x => R it x (sublist (lo it - hi a) (hi it - hi a)
            (sublist (hi a - start) (finish - start) bytes))) (snd v)) =
        (Zlength bytes = finish - start /\
        R a (fst v) (sublist (lo a - start) (hi a - start) bytes) /\
        struct_Prop (a' :: m)
          (fun it x => R it x (sublist (lo it - start) (hi it - start) bytes))
          (snd v))).
      rewrite Hlo. replace (start - start) with 0 by lia.
      f_equal. f_equal. apply prop_ext.
      apply struct_Prop_ext. intros it Hin x.
      specialize (Hbounds it Hin).
      rewrite sublist_sublist by lia.
      replace (lo it - hi a + (hi a - start)) with (lo it - start) by lia.
      replace (hi it - hi a + (hi a - start)) with (hi it - start) by lia.
      tauto.
Qed.

Lemma field_rec_contiguous_ranges: forall {cs: compspecs} m i t z sz,
  plain_members (Member_plain i t :: m) = true ->
  members_no_replicate (Member_plain i t :: m) = true ->
  0 <= z -> sizeof_struct cenv_cs z (Member_plain i t :: m) <= sz ->
  contiguous_member_ranges (Member_plain i t :: m) (align z (alignof t)) sz
    (fun it => field_offset_rec cenv_cs (name_member it) (Member_plain i t :: m) z)
    (fun it => field_offset_next_rec cenv_cs (name_member it)
      (Member_plain i t :: m) (align z (alignof t)) sz).
Proof.
  intros cs m. induction m as [| a m IH];
    intros i t z sz Hplain Hunique Hz Hsize.
  - simpl. rewrite if_true by auto. simpl in Hsize.
    fold (sizeof t) in Hsize. fold (alignof t) in Hsize.
    pose proof (sizeof_pos t). repeat split; lia.
  - destruct a as [i' t' |]; try discriminate.
    simpl in Hplain.
    rewrite members_no_replicate_ind in Hunique.
    destruct Hunique as [Hnotin Hunique].
    specialize (IH i' t' (align z (alignof t) + sizeof t) sz Hplain Hunique).
    assert (Halign: z <= align z (alignof t)) by apply align_le, alignof_pos.
    assert (Hnext: align z (alignof t) + sizeof t <=
      align (align z (alignof t) + sizeof t) (alignof t'))
      by apply align_le, alignof_pos.
    pose proof (sizeof_pos t) as Hnonnegative.
    specialize (IH ltac:(lia) ltac:(exact Hsize)).
    change (field_offset_rec cenv_cs i
        (Member_plain i t :: Member_plain i' t' :: m) z = align z (alignof t) /\
      align z (alignof t) <= field_offset_next_rec cenv_cs i
        (Member_plain i t :: Member_plain i' t' :: m) (align z (alignof t)) sz /\
      contiguous_member_ranges (Member_plain i' t' :: m)
        (field_offset_next_rec cenv_cs i
          (Member_plain i t :: Member_plain i' t' :: m) (align z (alignof t)) sz)
        sz
        (fun it => field_offset_rec cenv_cs (name_member it)
          (Member_plain i t :: Member_plain i' t' :: m) z)
        (fun it => field_offset_next_rec cenv_cs (name_member it)
          (Member_plain i t :: Member_plain i' t' :: m) (align z (alignof t)) sz)).
    assert (Hlo: field_offset_rec cenv_cs i
      (Member_plain i t :: Member_plain i' t' :: m) z = align z (alignof t))
      by (simpl; rewrite if_true by auto; reflexivity).
    assert (Hhi: field_offset_next_rec cenv_cs i
      (Member_plain i t :: Member_plain i' t' :: m) (align z (alignof t)) sz =
      align (align z (alignof t) + sizeof t) (alignof t'))
      by (simpl; rewrite if_true by auto; reflexivity).
    rewrite Hlo, Hhi. split; [reflexivity |]. split; [lia |].
    eapply contiguous_member_ranges_ext; [| exact IH]. intros it Hin.
    assert (Hneq: name_member it <> i).
    { intro Heq. apply Hnotin. unfold in_members. simpl name_member.
      rewrite <- Heq. apply in_map. exact Hin. }
    split.
    + symmetry. apply neq_field_offset_rec_cons; auto.
    + symmetry. apply neq_field_offset_next_rec_cons; auto.
Qed.

Lemma field_contiguous_ranges: forall {cs: compspecs} m sz,
  (m = nil -> sz = 0) -> plain_members m = true ->
  members_no_replicate m = true -> sizeof_struct cenv_cs 0 m <= sz ->
  contiguous_member_ranges m 0 sz
    (fun it => field_offset cenv_cs (name_member it) m)
    (fun it => field_offset_next cenv_cs (name_member it) m sz).
Proof.
  intros cs m sz Hnil Hplain Hunique Hsize.
  destruct m as [| [i t |] m]; try discriminate.
  - simpl. symmetry. apply Hnil; reflexivity.
  - pose proof (field_rec_contiguous_ranges m i t 0 sz Hplain Hunique
      ltac:(lia) Hsize) as Hranges.
    rewrite align_0 in Hranges by apply alignof_pos.
    exact Hranges.
Qed.

Lemma struct_pred_ext_members: forall m {A: member -> Type}
    (P Q: forall it, A it -> val -> mpred) v p,
  (forall it, In it m -> forall x, P it x p = Q it x p) ->
  struct_pred m P v p = struct_pred m Q v p.
Proof.
  intros m. destruct m as [| a m]; intros A P Q v p H; [reflexivity |].
  revert a v H. induction m as [| b m IH]; intros a v H.
  - simpl. apply H. left; reflexivity.
  - change (P a (fst v) p * struct_pred (b :: m) P (snd v) p =
      Q a (fst v) p * struct_pred (b :: m) Q (snd v) p).
    f_equal.
    + apply H. left; reflexivity.
    + apply IH. intros it Hin. apply H. right; exact Hin.
Qed.

(** Plain members with distinct names partition a structure into
    owned slots ending at the next field offset. A slot includes any
    padding after its field. The size and pointer bounds permit a
    single list covering the structure, including trailing padding. *)
Lemma struct_pred_memvals_at_ptr_slots: forall {cs: compspecs} sh m sz
    {A: member -> Type} (v: compact_prod (map A m))
    (R: forall it, A it -> list memval -> Prop) b ofs,
  (m = nil -> sz = 0) -> plain_members m = true ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  struct_pred m
    (fun it x p => EX bytes: list memval,
      !! (Zlength bytes = field_offset_next cenv_cs (name_member it) m sz -
          field_offset cenv_cs (name_member it) m /\ R it x bytes) &&
      memvals_at_ptr sh bytes (offset_val (field_offset cenv_cs (name_member it) m) p))
    v (Vptr b (Ptrofs.repr ofs)) =
  EX bytes: list memval,
    !! (Zlength bytes = sz /\
      struct_Prop m (fun it x => R it x
        (sublist (field_offset cenv_cs (name_member it) m)
          (field_offset_next cenv_cs (name_member it) m sz) bytes)) v) &&
    memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros cs sh m sz A v R b ofs Hnil Hplain Hunique Hsize [Hofs Hend].
  pose proof (struct_pred_memvals_contiguous sh m 0 sz
    (fun it => field_offset cenv_cs (name_member it) m)
    (fun it => field_offset_next cenv_cs (name_member it) m sz) v R b ofs
    (Vptr b (Ptrofs.repr ofs))
    (field_contiguous_ranges m sz Hnil Hplain Hunique (proj1 Hsize))
    Hofs ltac:(lia) Hend) as Hfold.
  rewrite !Z.sub_0_r, Z.add_0_r in Hfold.
  match type of Hfold with ?lhs = _ => transitivity lhs end.
  - apply struct_pred_ext_members. intros it Hin x.
    unfold offset_val. simpl. solve_mod_modulus. reflexivity.
  - rewrite Hfold.
    apply f_equal. extensionality bytes.
    apply f_equal2; [| reflexivity]. apply f_equal.
    f_equal. f_equal. extensionality it. extensionality x.
    rewrite !Z.sub_0_r. reflexivity.
Qed.

(** Structure ownership combines all field slots into a list of size
    [sz]. Each field relation constrains only its own size within its
    slot, leaving padding unconstrained but owned. Members must be
    plain and distinct, the layout must fit, and the owned interval
    must stay strictly below the pointer modulus. *)
Lemma struct_pred_memvals_at_ptr: forall {cs: compspecs} sh m sz
    {A: member -> Type} (v: compact_prod (map A m))
    (R: forall it, A it -> list memval -> Prop) b ofs,
  (m = nil -> sz = 0) -> plain_members m = true ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  struct_pred m
    (fun it x p => EX bytes: list memval,
      !! (Zlength bytes = field_offset_next cenv_cs (name_member it) m sz -
          field_offset cenv_cs (name_member it) m /\
        R it x (sublist 0 (sizeof (field_type (name_member it) m)) bytes)) &&
      memvals_at_ptr sh bytes (offset_val (field_offset cenv_cs (name_member it) m) p))
    v (Vptr b (Ptrofs.repr ofs)) =
  EX bytes: list memval,
    !! (Zlength bytes = sz /\
      struct_Prop m (fun it x => R it x
        (sublist (field_offset cenv_cs (name_member it) m)
          (field_offset cenv_cs (name_member it) m +
            sizeof (field_type (name_member it) m)) bytes)) v) &&
    memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros cs sh m sz A v R b ofs Hnil Hplain Hunique Hsize Hbound.
  rewrite (struct_pred_memvals_at_ptr_slots sh m sz v
    (fun it x bytes => R it x (sublist 0 (sizeof (field_type (name_member it) m)) bytes))
    b ofs Hnil Hplain Hunique Hsize Hbound).
  apply f_equal. extensionality bytes.
  apply f_equal2; [| reflexivity]. apply f_equal. f_equal.
  apply prop_ext. apply struct_Prop_ext. intros it Hin x.
  assert (Hinmem: in_members (name_member it) m) by
    (unfold in_members; apply in_map; exact Hin).
  pose proof (field_offset_next_in_range (name_member it) m Hplain sz
    Hinmem (proj1 Hsize)) as Hnext.
  pose proof (in_members_field_offset_pos cenv_cs (name_member it) m Hplain Hinmem)
    as Hoffset.
  pose proof (sizeof_pos (field_type (name_member it) m)) as Hwidth.
  rewrite sublist_sublist by lia.
  rewrite Z.add_0_l.
  replace (sizeof (field_type (name_member it) m) + field_offset cenv_cs (name_member it) m)
    with (field_offset cenv_cs (name_member it) m + sizeof (field_type (name_member it) m))
    by lia.
  tauto.
Qed.
