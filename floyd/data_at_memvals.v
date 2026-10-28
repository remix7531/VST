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
Require Import VST.floyd.memory_block_memvals.
Require Import VST.veric.Cop2.

Local Open Scope pred.
Local Open Scope Z_scope.

(** Readable nonvolatile scalar ownership is ownership of memory
    values decoded by the access chunk. A defined value must decode
    exactly, while [Vundef] imposes no decoding constraint. The chunk
    must fit within the pointer modulus and satisfy its alignment. *)
Lemma mapsto_memvals_raw : forall sh t v b ofs ch,
  readable_share sh -> access_mode t = By_value ch -> type_is_volatile t = false ->
  Ptrofs.unsigned ofs + size_chunk ch <= Ptrofs.modulus ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  mapsto sh t (Vptr b ofs) v =
  EX bytes : list memval,
    !! (tc_val' t v /\ Zlength bytes = size_chunk ch /\ (v = Vundef \/ decode_val ch bytes = v)) &&
    memvals_at_ptr sh bytes (Vptr b ofs).
Proof.
  intros sh t v b ofs ch Hread Haccess Hvolatile Hbound Haligned.
  unfold mapsto. rewrite Haccess, Hvolatile. simpl.
  destruct (readable_share_dec sh); [|contradiction].
  apply pred_ext.
  - intros phi [[Htc Haddress] | [Hundef [v' Haddress]]];
      rewrite address_mapsto_memvals_at in Haddress by (simpl; auto);
      destruct Haddress as [bytes [[Hlen Hdecode] Hbytes]].
    + exists bytes. repeat split; auto using tc_val_tc_val'.
      rewrite Hlen. exact Hbound.
    + change (v = Vundef) in Hundef. subst v.
      exists bytes. repeat split; auto using tc_val'_Vundef.
      rewrite Hlen. exact Hbound.
  - intros phi [bytes [[Htc [Hlen Hvalue]] [Hsize Hbytes]]].
    destruct (Val.eq v Vundef) as [Hundef | Hdefined].
    + right. split; auto. exists (decode_val ch bytes).
      rewrite address_mapsto_memvals_at by (simpl; auto).
      exists bytes. repeat split; auto.
    + left. split.
      * apply Htc; auto.
      * rewrite address_mapsto_memvals_at by (simpl; auto).
        exists bytes. repeat split; auto. destruct Hvalue; congruence.
Qed.

Lemma memvals_at_bytes_injective : forall sh1 sh2 bytes1 bytes2 loc phi,
  Zlength bytes1 = Zlength bytes2 ->
  memvals_at sh1 bytes1 loc phi -> memvals_at sh2 bytes2 loc phi ->
  bytes1 = bytes2.
Proof.
  intros sh1 sh2 bytes1 bytes2 [b ofs] phi Hlen Hbytes1 Hbytes2.
  assert (Hlength : length bytes1 = length bytes2).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact Hlen. }
  rewrite (@list_Znth_eq memval Undef bytes1), (@list_Znth_eq memval Undef bytes2), Hlength.
  apply map_ext_in. intros i Hi. rewrite In_upto in Hi.
  destruct (memvals_at_resource sh1 bytes1 (b, ofs) phi (b, ofs + i) Hbytes1)
    as [rsh1 Hresource1].
  { unfold adr_range; simpl. rewrite Zlength_correct, Hlength. split; auto; lia. }
  destruct (memvals_at_resource sh2 bytes2 (b, ofs) phi (b, ofs + i) Hbytes2)
    as [rsh2 Hresource2].
  { unfold adr_range; simpl. rewrite Zlength_correct. split; auto; lia. }
  simpl in Hresource1, Hresource2.
  replace (ofs + i - ofs) with i in Hresource1, Hresource2 by lia.
  rewrite Hresource1 in Hresource2. inversion Hresource2. reflexivity.
Qed.

Lemma array_memvals_cons : forall {A} {d : Inhabitant A} n (R : A -> list memval -> Prop) v vs bytes,
  0 <= n -> Zlength bytes = n * Zlength (v :: vs) ->
  (forall i, 0 <= i < Zlength (v :: vs) ->
    R (Znth i (v :: vs)) (sublist (n * i) (n * (i + 1)) bytes)) =
  (R v (sublist 0 n bytes) /\ forall i, 0 <= i < Zlength vs ->
    R (Znth i vs) (sublist (n * i) (n * (i + 1)) (sublist n (Zlength bytes) bytes))).
Proof.
  intros A d n R v vs bytes Hn Hlen. apply prop_ext. split.
  - intro H. split.
    + specialize (H 0). rewrite Znth_0_cons in H.
      replace (n * 0) with 0 in H by ring.
      replace (n * (0 + 1)) with n in H by ring.
      apply H. rewrite Zlength_cons. pose proof (Zlength_nonneg vs); lia.
    + intros i Hi. specialize (H (i + 1)).
      rewrite Znth_pos_cons in H by lia.
      replace (i + 1 - 1) with i in H by ring.
      rewrite sublist_sublist by (rewrite Zlength_cons in Hlen; nia).
      replace (n * i + n) with (n * (i + 1)) by ring.
      replace (n * (i + 1) + n) with (n * ((i + 1) + 1)) by ring.
      apply H. rewrite Zlength_cons; lia.
  - intros [Hhead Htail] i Hi.
    destruct (zeq i 0) as [Hzero | Hnonzero].
    + subst i. rewrite Znth_0_cons.
      replace (n * 0) with 0 by ring.
      replace (n * (0 + 1)) with n by ring. exact Hhead.
    + rewrite Znth_pos_cons by lia.
      specialize (Htail (i - 1)).
      rewrite sublist_sublist in Htail by (rewrite Zlength_cons in Hlen, Hi; nia).
      replace (n * (i - 1) + n) with (n * i) in Htail by ring.
      replace (n * (i - 1 + 1) + n) with (n * (i + 1)) in Htail by ring.
      apply Htail. rewrite Zlength_cons in Hi; lia.
Qed.

(** Own consecutive slots of size [n], one per list element, with
    relation [R] constraining each slot. The empty list owns [emp].
    Nonnegative sizes and address bounds are premises of the bridges. *)
Fixpoint iter_memvals_at {A} (sh : share) (n : Z) (R : A -> list memval -> Prop)
  (vs : list A) (p : val) : mpred :=
  match vs with
  | nil => predicates_sl.emp
  | v :: vs => ((EX bytes : list memval, !! (Zlength bytes = n /\ R v bytes) && memvals_at_ptr sh bytes p) *
      iter_memvals_at sh n R vs (offset_val n p))%pred
  end.

Lemma iter_memvals_at_eq : forall {A} {d : Inhabitant A} (sh : share) (n : Z)
  (R : A -> list memval -> Prop) (vs : list A) b ofs,
  0 <= n -> Ptrofs.unsigned ofs + n * Zlength vs < Ptrofs.modulus ->
  iter_memvals_at sh n R vs (Vptr b ofs) =
  (EX bytes : list memval,
    !! (Zlength bytes = (n * Zlength vs)%Z /\ forall i, 0 <= i < Zlength vs ->
      R (Znth i vs) (sublist (n * i)%Z (n * (i + 1))%Z bytes)) &&
    memvals_at_ptr sh bytes (Vptr b ofs))%pred.
Proof.
  intros A d sh n R vs. induction vs as [|v vs IH]; intros b ofs Hn Hbound.
  - simpl iter_memvals_at. rewrite Zlength_nil, Z.mul_0_r.
    apply pred_ext.
    + intros phi Hemp. exists nil. split.
      * split; [reflexivity |]. intros i Hi; lia.
      * rewrite memvals_at_ptr_nil. split; auto.
    + intros phi [bytes [[Hlen HR] Hbytes]].
      apply Zlength_nil_inv in Hlen. subst bytes.
      rewrite memvals_at_ptr_nil in Hbytes. exact (proj2 Hbytes).
  - simpl iter_memvals_at.
    assert (Hoffset : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr n)) = Ptrofs.unsigned ofs + n).
    { rewrite Ptrofs.add_unsigned.
      rewrite (Ptrofs.unsigned_repr n) by
        (pose proof (Ptrofs.unsigned_range ofs); rewrite Zlength_cons in Hbound;
         pose proof (Zlength_nonneg vs); unfold Ptrofs.max_unsigned; nia).
      rewrite Ptrofs.unsigned_repr by
        (pose proof (Ptrofs.unsigned_range ofs); rewrite Zlength_cons in Hbound;
         pose proof (Zlength_nonneg vs); unfold Ptrofs.max_unsigned; nia).
      reflexivity. }
    rewrite IH by (auto; rewrite Hoffset; rewrite Zlength_cons in Hbound; nia).
    change (Vptr b (Ptrofs.add ofs (Ptrofs.repr n))) with (offset_val n (Vptr b ofs)).
    change (!! (Ptrofs.unsigned ofs + Zlength ?bs <= Ptrofs.modulus) &&
      memvals_at sh ?bs (b, Ptrofs.unsigned ofs))%pred with (memvals_at_ptr sh bs (Vptr b ofs)).
    rewrite memvals_at_ptr_sepcon by
      (auto; pose proof (Zlength_nonneg vs); rewrite Zlength_cons in Hbound; nia).
    f_equal. apply functional_extensionality; intro bytes.
    f_equal. f_equal. apply prop_ext.
    replace (n * Zlength (v :: vs)) with (n + n * Zlength vs) by (rewrite Zlength_cons; ring).
    split; intros [Hlen HR]; split; auto.
    + rewrite <- Hlen in HR.
      rewrite (array_memvals_cons n R v vs bytes Hn) by (rewrite Zlength_cons; nia).
      exact HR.
    + rewrite (array_memvals_cons n R v vs bytes Hn) in HR by (rewrite Zlength_cons; nia).
      rewrite <- Hlen. exact HR.
Qed.

(** Readable padding extends an owned representation prefix by [m]
    unconstrained memory values. The relation sees only the original
    [n] values. Both lengths are nonnegative and the combined interval
    must end strictly below the pointer modulus. *)
Lemma memvals_at_ptr_padding : forall sh n m (R : list memval -> Prop) b ofs,
  readable_share sh -> 0 <= n -> 0 <= m ->
  Ptrofs.unsigned ofs + (n + m) < Ptrofs.modulus ->
  ((EX bytes : list memval, !! (Zlength bytes = n /\ R bytes) && memvals_at_ptr sh bytes (Vptr b ofs)) *
    memory_block sh m (offset_val n (Vptr b ofs)))%pred =
  (EX bytes : list memval, !! (Zlength bytes = n + m /\ R (sublist 0 n bytes)) &&
    memvals_at_ptr sh bytes (Vptr b ofs))%pred.
Proof.
  intros sh n m R b ofs Hread Hn Hm Hbound.
  assert (Hoffset : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr n)) = Ptrofs.unsigned ofs + n).
  { rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr n) by
      (pose proof (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia).
    rewrite Ptrofs.unsigned_repr by
      (pose proof (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia).
    reflexivity. }
  rewrite memory_block_memvals_at_ptr_eq_in_range by (auto; simpl; rewrite Hoffset; lia).
  replace (EX bytes : list memval, !! (Zlength bytes = m) &&
    memvals_at_ptr sh bytes (offset_val n (Vptr b ofs)))%pred
    with (EX bytes : list memval, !! (Zlength bytes = m /\ True) &&
      memvals_at_ptr sh bytes (offset_val n (Vptr b ofs)))%pred.
  2: { f_equal. apply functional_extensionality; intro bytes.
       f_equal. f_equal. apply prop_ext; tauto. }
  rewrite memvals_at_ptr_sepcon by auto.
  f_equal. apply functional_extensionality; intro bytes.
  f_equal. f_equal. apply prop_ext; tauto.
Qed.

Local Close Scope pred.

Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.veric.align_mem.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.aggregate_pred.
Require Import VST.floyd.aggregate_memvals.
Require Import VST.floyd.field_at.
Require Import VST.floyd.field_compat.
Require Import VST.floyd.data_at_lemmas.
Import VST.floyd.aggregate_pred.aggregate_pred.
Import VST.floyd.aggregate_pred.auxiliary_pred.
Import ListNotations.

Local Open Scope logic.
Local Transparent Nveric Sveric.

Lemma rangespec_memvals_iter : forall {A} {d : Inhabitant A} sh n
  (R : A -> list memval -> Prop) vs i p,
  rangespec i (length vs)
    (fun j p => EX bytes : list memval, !! (Zlength bytes = n /\ R (Znth (j - i) vs) bytes) &&
      memvals_at_ptr sh bytes (offset_val (n * j) p)) p =
  iter_memvals_at sh n R vs (offset_val (n * i) p).
Proof.
  intros A d sh n R vs. induction vs as [|v vs IH]; intros i p.
  - reflexivity.
  - cbn [rangespec iter_memvals_at length].
    rewrite Z.sub_diag, Znth_0_cons.
    change ((?P * ?Q) p) with (P p * Q p).
    change (predicates_sl.sepcon ?P ?Q) with (P * Q)%logic.
    f_equal. rewrite offset_offset_val.
    replace (n * i + n)%Z with (n * Z.succ i)%Z by ring.
    rewrite <- IH. apply rangespec_ext. intros j Hj.
    rewrite Znth_pos_cons by lia.
    replace (j - i - 1)%Z with (j - Z.succ i)%Z by lia. reflexivity.
Qed.

Lemma array_pred_memvals_iter : forall {A} {d : Inhabitant A} sh n
  (R : A -> list memval -> Prop) vs p,
  isptr p ->
  array_pred 0 (Zlength vs)
    (fun i v p => EX bytes : list memval, !! (Zlength bytes = n /\ R v bytes) &&
      memvals_at_ptr sh bytes (offset_val (n * i) p)) vs p =
  iter_memvals_at sh n R vs p.
Proof.
  intros A d sh n R vs p Hptr.
  unfold array_pred, floyd.aggregate_pred.array_pred. rewrite Z.sub_0_r.
  rewrite prop_true_andp by reflexivity.
  rewrite Zlength_correct, Nat2Z.id, rangespec_memvals_iter.
  rewrite Z.mul_0_r, isptr_offset_val_zero by auto. reflexivity.
Qed.

Lemma array_pred_memvals_eq : forall {A} {d : Inhabitant A} sh n
  (R : A -> list memval -> Prop) vs b ofs,
  0 <= n -> Ptrofs.unsigned ofs + n * Zlength vs < Ptrofs.modulus ->
  array_pred 0 (Zlength vs)
    (fun i v p => EX bytes : list memval, !! (Zlength bytes = n /\ R v bytes) &&
      memvals_at_ptr sh bytes (offset_val (n * i) p)) vs (Vptr b ofs) =
  (EX bytes : list memval,
    !! (Zlength bytes = (n * Zlength vs)%Z /\ forall i, 0 <= i < Zlength vs ->
      R (Znth i vs) (sublist (n * i)%Z (n * (i + 1))%Z bytes)) &&
    memvals_at_ptr sh bytes (Vptr b ofs))%pred.
Proof.
  intros. rewrite array_pred_memvals_iter by exact I. apply iter_memvals_at_eq; auto.
Qed.

Section MemvalsBridge.
Context {cs : compspecs}.

(** A layout contains no union at any recursive array or structure
    position. Scalars satisfy this property. The representation
    bridges also support unions and do not require this property. *)
Definition union_free_layout : type -> Prop :=
  type_func (fun _ => Prop)
    (fun _ => True)
    (fun _ _ _ P => P)
    (fun _ _ P => Forall (fun P => P) (decay P))
    (fun _ _ _ => False).

(** Apply member relations to the compact structure value. Layout
    offsets and types come from [m0], and [m] selects the recursive
    members. Each relation sees only its field bytes, excluding padding.
    This is a pure constraint and carries no ownership. *)
Definition struct_memvals_aux (m m0 : members)
  (P : ListType (map (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) m))
  (v : compact_prod (map (fun it => reptype (field_type (name_member it) m0)) m))
  (bytes : list memval) : Prop.
Proof.
  destruct m as [|a0 m]; [exact True|].
  revert a0 v P; induction m as [|a0 m]; intros it v P.
  - simpl in v, P. inversion P; subst.
    exact (a v (sublist (field_offset cenv_cs (name_member it) m0)
      (field_offset cenv_cs (name_member it) m0 + sizeof (field_type (name_member it) m0)) bytes)).
  - simpl in v, P. inversion P; subst.
    exact (a (fst v) (sublist (field_offset cenv_cs (name_member it) m0)
      (field_offset cenv_cs (name_member it) m0 + sizeof (field_type (name_member it) m0)) bytes) /\ IHm a0 (snd v) b).
Defined.

(** Apply only the selected compact union member relation to the
    prefix of its field size. Inactive members and remaining bytes
    impose no constraints. The empty member list gives [True]. *)
Definition union_memvals_aux (m m0 : members)
  (P : ListType (map (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) m))
  (v : compact_sum (map (fun it => reptype (field_type (name_member it) m0)) m))
  (bytes : list memval) : Prop.
Proof.
  destruct m as [| a0 m]; [exact True |].
  revert a0 v P; induction m as [| a0 m]; intros it v P.
  - simpl in v, P. inversion P; subst.
    exact (a v (sublist 0 (sizeof (field_type (name_member it) m0)) bytes)).
  - simpl in v, P. inversion P; subst.
    destruct v as [v | v].
    + exact (a v (sublist 0 (sizeof (field_type (name_member it) m0)) bytes)).
    + exact (IHm a0 v b).
Defined.

(** Relate a typed value to CompCert memory values without ownership.
    Scalars use chunk decoding, preserving pointer fragments. Undefined
    scalar values and volatile scalars impose no decoding constraint.
    Arrays constrain element slices, structures constrain field slices,
    and unions constrain only the selected member prefix. Padding is
    unconstrained. Length and value fitting are specified separately. *)
Definition value_memvals_rec : forall t, reptype t -> list memval -> Prop :=
  type_func (fun t => reptype t -> list memval -> Prop)
    (fun t v bytes => if type_is_volatile t then True else
       match access_mode t with
       | By_value ch => repinject t v = Vundef \/ decode_val ch bytes = repinject t v
       | _ => False
       end)
    (fun t n a P v bytes => forall i, 0 <= i < Z.max 0 n ->
       P (Znth i (unfold_reptype v)) (sublist (sizeof t * i) (sizeof t * (i + 1)) bytes))
    (fun id a P v bytes => struct_memvals_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v) bytes)
    (fun id a P v bytes => union_memvals_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v) bytes).

(** A full object representation has a fitting typed value, exactly
    [sizeof t] memory values, and the recursive decoding constraints.
    This pure predicate owns no memory and gives no address alignment
    guarantee. Padding remains unconstrained, and unions constrain only
    their selected member. Memory values need not be concrete bytes. *)
Definition data_at_memvals (t : type) (v : reptype t) (bytes : list memval) : Prop :=
  value_fits t v /\ Zlength bytes = sizeof t /\ value_memvals_rec t v bytes.

Lemma struct_memvals_aux_spec : forall m m0 v P bytes,
  struct_memvals_aux m m0
    (ListTypeGen (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) P m) v bytes =
  struct_Prop m (fun it v => P it v (sublist (field_offset cenv_cs (name_member it) m0)
    (field_offset cenv_cs (name_member it) m0 + sizeof (field_type (name_member it) m0)) bytes)) v.
Proof.
  intros.
  destruct m as [|a0 m]; [reflexivity|].
  revert a0 v; induction m as [|a0 m]; intros; [reflexivity|].
  change (struct_memvals_aux (a1 :: a0 :: m) m0
    (ListTypeGen (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) P (a1 :: a0 :: m)) v bytes)
    with (P a1 (fst v)
      (sublist (field_offset cenv_cs (name_member a1) m0)
        (field_offset cenv_cs (name_member a1) m0 + sizeof (field_type (name_member a1) m0)) bytes) /\
      struct_memvals_aux (a0 :: m) m0
        (ListTypeGen (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) P (a0 :: m)) (snd v) bytes).
  rewrite IHm. reflexivity.
Qed.

Lemma union_memvals_aux_spec : forall m m0 v P bytes,
  union_memvals_aux m m0
    (ListTypeGen (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) P m) v bytes =
  union_Prop m (fun it v => P it v (sublist 0 (sizeof (field_type (name_member it) m0)) bytes)) v.
Proof.
  intros. destruct m as [| a0 m]; [reflexivity |].
  revert a0 v; induction m as [| a0 m]; intros; [reflexivity |].
  destruct v as [v | v]; [reflexivity |].
  change (union_memvals_aux (a0 :: m) m0
    (ListTypeGen (fun it => reptype (field_type (name_member it) m0) -> list memval -> Prop) P (a0 :: m)) v bytes =
    union_Prop (a0 :: m) (fun it v => P it v (sublist 0 (sizeof (field_type (name_member it) m0)) bytes)) v).
  apply IHm.
Qed.

Lemma union_free_layout_eq : forall t,
  union_free_layout t =
  match t with
  | Tarray t _ _ => union_free_layout t
  | Tstruct id _ => Forall (fun it => union_free_layout (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id))
  | Tunion _ _ => False
  | _ => True
  end.
Proof.
  intros. unfold union_free_layout at 1. rewrite type_func_eq.
  destruct t; try reflexivity.
  unfold FTI_aux. rewrite decay_spec.
  apply prop_ext. rewrite Forall_map. reflexivity.
Qed.

(** Unfold the recursive representation by type. Structure fields use
    their layout offsets, and only the selected union member constrains
    the prefix. This equation adds neither length nor ownership. *)
Lemma value_memvals_rec_eq : forall t v bytes,
  value_memvals_rec t v bytes =
  match t as t0 return reptype t0 -> Prop with
  | Tarray t n a => fun v => forall i, 0 <= i < Z.max 0 n ->
      value_memvals_rec t (Znth i (unfold_reptype v)) (sublist (sizeof t * i) (sizeof t * (i + 1)) bytes)
  | Tstruct id a => fun v => struct_Prop (co_members (get_co id))
      (fun it v => value_memvals_rec (field_type (name_member it) (co_members (get_co id))) v
        (sublist (field_offset cenv_cs (name_member it) (co_members (get_co id)))
          (field_offset cenv_cs (name_member it) (co_members (get_co id)) + sizeof (field_type (name_member it) (co_members (get_co id)))) bytes)) (unfold_reptype v)
  | Tunion id a => fun v => union_Prop (co_members (get_co id))
      (fun it v => value_memvals_rec (field_type (name_member it) (co_members (get_co id))) v
        (sublist 0 (sizeof (field_type (name_member it) (co_members (get_co id)))) bytes)) (unfold_reptype v)
  | t => fun v => if type_is_volatile t then True else
      match access_mode t with
      | By_value ch => repinject t v = Vundef \/ decode_val ch bytes = repinject t v
      | _ => False
      end
  end v.
Proof.
  intros. unfold value_memvals_rec at 1. rewrite type_func_eq.
  destruct t; try reflexivity.
  - apply struct_memvals_aux_spec.
  - apply union_memvals_aux_spec.
Qed.

Lemma data_at_memvals_local_facts : forall t v bytes,
  data_at_memvals t v bytes -> value_fits t v /\ Zlength bytes = sizeof t.
Proof. intros t v bytes [? [? ?]]. auto. Qed.

(** The default value of a complete legal type constrains no memory
    values, including padding and selected union member contents. This
    fact imposes no size condition and provides no ownership. *)
Lemma value_memvals_rec_default : forall t bytes,
  complete_legal_cosu_type t = true ->
  value_memvals_rec t (default_val t) bytes.
Proof.
  intro t. type_induction t; intros bytes Hcomplete;
    rewrite value_memvals_rec_eq;
    try solve [discriminate Hcomplete];
    try solve [simpl; destruct (attr_volatile a); auto; destruct i; auto];
    try solve [simpl; destruct (attr_volatile a); auto; destruct f; auto].
  - destruct i; simpl; destruct (attr_volatile a); auto.
    all: destruct s; simpl; auto.
  - rewrite (default_val_eq (Tarray t z a)), unfold_fold_reptype.
    intros i Hi. rewrite Znth_Zrepeat by lia. apply IH; auto.
  - rewrite (default_val_eq (Tstruct id a)), unfold_fold_reptype.
    unfold struct_default_val.
    apply struct_Prop_compact_prod_gen.
    + apply get_co_members_no_replicate.
    + intros i Hi. rewrite Forall_forall in IH.
      apply IH.
      * apply in_get_member; auto.
      * rewrite name_member_get by auto.
        apply complete_legal_cosu_type_field_type; auto.
        eapply complete_Tstruct_plain; eauto.
  - rewrite (default_val_eq (Tunion id a)), unfold_fold_reptype.
    unfold union_default_val.
    apply union_Prop_compact_sum_gen.
    + apply get_co_members_no_replicate.
    + intros i Hi. rewrite Forall_forall in IH.
      apply IH.
      * apply in_get_member; auto.
      * rewrite name_member_get by auto.
        apply complete_legal_cosu_type_field_type; auto.
        eapply complete_Tunion_plain; eauto.
Qed.

(** Every memory value list of the object size represents the default
    value of a complete legal type. Default values therefore express
    uninitialized contents rather than a concrete byte pattern. *)
Lemma data_at_memvals_default : forall t bytes,
  complete_legal_cosu_type t = true ->
  Zlength bytes = sizeof t -> data_at_memvals t (default_val t) bytes.
Proof.
  intros. repeat split; auto using default_value_fits, value_memvals_rec_default.
Qed.

(** A readable scalar object at an aligned address is exactly an
    owned representation list of its size. A fitting value and a
    strictly bounded address interval are required. Volatile scalars
    retain ownership while imposing no decoding constraint. *)
Lemma data_at_rec_memvals_by_value : forall sh t v b ofs,
  type_is_by_value t = true -> readable_share sh -> value_fits t v ->
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  data_at_rec sh t v (Vptr b (Ptrofs.repr ofs)) =
  EX bytes : list memval, !! (Zlength bytes = sizeof t /\ value_memvals_rec t v bytes) &&
    memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh t v b ofs Hby Hread Hfit Hbound Halign.
  assert (Hofs : Ptrofs.unsigned (Ptrofs.repr ofs) = ofs).
  { apply Ptrofs.unsigned_repr. pose proof (sizeof_pos t). unfold Ptrofs.max_unsigned; lia. }
  assert (Hrec : forall bytes, value_memvals_rec t v bytes =
    if type_is_volatile t then True else match access_mode t with
      | By_value ch => repinject t v = Vundef \/ decode_val ch bytes = repinject t v
      | _ => False end).
  { intro bytes. rewrite value_memvals_rec_eq. destruct t; try discriminate; reflexivity. }
  assert (Hfit' : (if type_is_volatile t then True else tc_val' t (repinject t v))).
  { rewrite value_fits_eq in Hfit. destruct t; try discriminate; exact Hfit. }
  destruct (type_is_volatile t) eqn:Hvol.
  - rewrite by_value_data_at_rec_volatile by auto.
    rewrite memory_block_memvals_at_ptr_eq_in_range by
      (auto; try (pose proof (sizeof_pos t); lia); simpl; rewrite Hofs; lia).
    change (predicates_hered.exp ?P) with (@exp mpred Nveric _ P).
    f_equal. apply functional_extensionality; intro bytes.
    change (predicates_hered.andp ?P ?Q) with (P && Q)%logic.
    f_equal. change (predicates_hered.prop ?P) with (!! P)%logic.
    f_equal. apply prop_ext. rewrite Hrec. tauto.
  - destruct (access_mode_by_value t Hby) as [ch Haccess].
    assert (Hsize : sizeof t = size_chunk ch).
    { unfold sizeof. eapply size_chunk_sizeof; eauto. }
    rewrite by_value_data_at_rec_nonvolatile by auto.
    unfold mapsto at 1.
    match goal with |- ?L = ?R =>
      change (mapsto_memory_block.mapsto sh t (Vptr b (Ptrofs.repr ofs)) (repinject t v) = R)
    end.
    rewrite (mapsto_memvals_raw sh t (repinject t v) b (Ptrofs.repr ofs) ch) by
      (auto; rewrite Hofs; try rewrite <- Hsize; try lia;
       eapply align_compatible_rec_by_value_inv; eauto).
    change (predicates_hered.exp ?P) with (@exp mpred Nveric _ P).
    f_equal. apply functional_extensionality; intro bytes.
    change (predicates_hered.andp ?P ?Q) with (P && Q)%logic.
    f_equal. change (predicates_hered.prop ?P) with (!! P)%logic.
    f_equal. apply prop_ext. rewrite Hrec, Haccess. rewrite <- Hsize. tauto.
Qed.

(** At a compatible address, uninitialized typed ownership is exactly
    readable ownership of any list of the object size. No recursive
    value constraints or initialization guarantees are imposed. *)
Lemma data_at__memvals_in_range : forall sh t p,
  readable_share sh -> field_compatible t nil p ->
  data_at_ sh t p =
  EX bytes : list memval, !! (Zlength bytes = sizeof t) && memvals_at_ptr sh bytes p.
Proof.
  intros sh t p Hread Hfc.
  rewrite data_at__memory_block, prop_true_andp by auto.
  apply memory_block_memvals_at_ptr_eq_in_range.
  - exact Hread.
  - pose proof (sizeof_pos t); lia.
  - destruct Hfc as [Hptr [_ [Hsize _]]].
    destruct p; try contradiction. exact Hsize.
Qed.

(** A field representation and its readable trailing spacer combine
    into one owned slot. The relation constrains only the field prefix,
    leaving padding unconstrained. Slot ordering and the strict address
    bound ensure that the field and spacer form one interval. *)
Lemma withspacer_memvals_at_ptr : forall sh start width finish (R : list memval -> Prop) b ofs,
  readable_share sh -> 0 <= start -> 0 <= width -> start + width <= finish ->
  0 <= ofs /\ ofs + finish < Ptrofs.modulus ->
  withspacer sh (start + width) finish
    (fun p => EX bytes : list memval, !! (Zlength bytes = width /\ R bytes) &&
      memvals_at_ptr sh bytes (offset_val start p)) (Vptr b (Ptrofs.repr ofs)) =
  EX bytes : list memval, !! (Zlength bytes = finish - start /\ R (sublist 0 width bytes)) &&
    memvals_at_ptr sh bytes (offset_val start (Vptr b (Ptrofs.repr ofs))).
Proof.
  intros sh start width finish R b ofs Hread Hstart Hwidth Hfinish Hbound.
  rewrite withspacer_spacer, spacer_memory_block by exact I.
  rewrite sepcon_comm. simpl.
  assert (Hptr : offset_val (start + width) (Vptr b (Ptrofs.repr ofs)) =
    offset_val width (offset_val start (Vptr b (Ptrofs.repr ofs)))).
  { rewrite offset_offset_val. f_equal; lia. }
  change (((EX bytes : list memval, !! (Zlength bytes = width /\ R bytes) &&
      memvals_at_ptr sh bytes (offset_val start (Vptr b (Ptrofs.repr ofs)))) *
    memory_block sh (finish - (start + width))
      (offset_val (start + width) (Vptr b (Ptrofs.repr ofs))))%pred =
    (EX bytes : list memval, !! (Zlength bytes = finish - start /\ R (sublist 0 width bytes)) &&
      memvals_at_ptr sh bytes (offset_val start (Vptr b (Ptrofs.repr ofs))))%pred).
  rewrite Hptr.
  change (memory_block sh ?n ?p) with (mapsto_memory_block.memory_block sh n p).
  assert (Hoffset : Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr start)) = ofs + start).
  { rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr ofs) by (unfold Ptrofs.max_unsigned; lia).
    rewrite (Ptrofs.unsigned_repr start) by (unfold Ptrofs.max_unsigned; lia).
    rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia). reflexivity. }
  change (offset_val start (Vptr b (Ptrofs.repr ofs))) with
    (Vptr b (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr start))).
  rewrite memvals_at_ptr_padding by (auto; try lia; rewrite Hoffset; lia).
  replace (width + (finish - (start + width)))%Z with (finish - start)%Z by lia.
  reflexivity.
Qed.

(** Recursive typed ownership is exactly ownership of a representation
    list for a fitting value of a complete legal type. The readable
    share, alignment and strict address bound allow scalar and aggregate
    ownership to combine. Padding is owned but unconstrained. Unions
    constrain only their selected member. Empty unions own an empty
    representation list.

    The proof handles scalars by their access chunks, combines array
    elements, and folds structure slots with padding. The union cases
    separate empty ownership from selected member ownership. *)
Lemma data_at_rec_memvals : forall sh t v b ofs,
  readable_share sh -> complete_legal_cosu_type t = true ->
  value_fits t v -> 0 <= ofs /\ ofs+sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  data_at_rec sh t v (Vptr b (Ptrofs.repr ofs)) =
  EX bytes:list memval, !!(Zlength bytes=sizeof t /\ value_memvals_rec t v bytes) &&
    memvals_at_ptr sh bytes (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh t.
  (* ===== Scalar cases: use the access chunk bridge ===== *)

  type_induction t;
    intros v b ofs Hread Hlegal Hfit Hbounds Halign;
    try solve [discriminate Hlegal];
    try solve [apply data_at_rec_memvals_by_value; auto].
  - (* Arrays combine equally sized element representations. *)
    rewrite value_fits_eq in Hfit.
    destruct Hfit as [Hlen Hfits].
    rewrite data_at_rec_eq.
    rewrite array_pred_ext with
      (P1 := fun i v p => EX bytes:list memval,
        !!(Zlength bytes=sizeof t /\ value_memvals_rec t v bytes) &&
        memvals_at_ptr sh bytes (offset_val (sizeof t*i) p))
      (v1 := unfold_reptype v).
    + assert (Hsize : sizeof (Tarray t z a) =
        (sizeof t * Zlength (unfold_reptype v))%Z).
      {
        unfold sizeof.
        simpl.
        fold (sizeof t).
        rewrite Hlen.
        ring.
      }
      assert (Hofs : Ptrofs.unsigned (Ptrofs.repr ofs) = ofs).
      {
        apply Ptrofs.unsigned_repr.
        pose proof (sizeof_pos (Tarray t z a)).
        unfold Ptrofs.max_unsigned; lia.
      }
      rewrite <- Hlen.
      rewrite array_pred_memvals_eq by
        (pose proof (sizeof_pos t); rewrite ?Hofs; rewrite Hsize in Hbounds; lia).
      change (predicates_hered.exp ?P) with (@exp mpred Nveric _ P).
      f_equal.
      apply functional_extensionality.
      intro bytes.
      change (predicates_hered.andp ?P ?Q) with (P && Q)%logic.
      f_equal.
      change (predicates_hered.prop ?P) with (!! P)%logic.
      f_equal.
      rewrite value_memvals_rec_eq, Hsize, Hlen.
      reflexivity.
    + reflexivity.
    + intros i Hi.
      assert (Helementfit : value_fits t (Znth i (unfold_reptype v))).
      { apply Forall_Znth; auto.
        rewrite Hlen.
        lia. }
      assert (Helementbounds : 0 <= ofs + sizeof t * i /\
        ofs + sizeof t * i + sizeof t < Ptrofs.modulus).
      { pose proof (sizeof_pos t) as Helementsize.
        unfold sizeof, Ctypes.sizeof in Hbounds.
        fold @Ctypes.sizeof in Hbounds.
        fold (sizeof t) in Hbounds.
        nia. }
      assert (Helementalign :
        align_compatible_rec cenv_cs t (ofs + sizeof t * i)).
      { eapply align_compatible_rec_Tarray_inv.
        - exact Halign.
        - apply range_max0; auto. }

      rewrite at_offset_eq3.
      unfold offset_val.
      rewrite ptrofs_add_repr.
      rewrite Z.sub_0_r.
      rewrite IH by assumption.
      reflexivity.
  - (* Structure slots own both their fields and following padding. *)
    rewrite value_fits_eq in Hfit.
    rewrite data_at_rec_eq.
    rewrite struct_pred_ext with
      (P1 := fun it x p => EX bytes:list memval,
        !!(Zlength bytes =
          field_offset_next cenv_cs (name_member it) (co_members (get_co id))
            (co_sizeof (get_co id)) -
          field_offset cenv_cs (name_member it) (co_members (get_co id)) /\
          value_memvals_rec (field_type (name_member it) (co_members (get_co id))) x
            (sublist 0 (sizeof (field_type (name_member it)
              (co_members (get_co id)))) bytes)) &&
        memvals_at_ptr sh bytes
          (offset_val (field_offset cenv_cs (name_member it)
            (co_members (get_co id))) p))
      (v1 := unfold_reptype v).
    + unfold struct_pred at 1.
      rewrite (@struct_pred_memvals_at_ptr cs sh (co_members (get_co id))
        (co_sizeof (get_co id))
        (fun it => reptype (field_type (name_member it) (co_members (get_co id))))
        (unfold_reptype v)
        (fun it x bytes => value_memvals_rec
          (field_type (name_member it) (co_members (get_co id))) x bytes) b ofs).
      * f_equal.
        apply functional_extensionality.
        intro bytes.
        f_equal.
        f_equal.
        rewrite value_memvals_rec_eq, sizeof_Tstruct.
        reflexivity.
      * apply get_co_members_nil_sizeof_0.
      * eapply complete_Tstruct_plain; eauto.
      * apply get_co_members_no_replicate.
      * pose proof (co_consistent_sizeof cenv_cs (get_co id)
          (get_co_consistent id)) as Hsize.
        erewrite complete_legal_cosu_type_Tstruct in Hsize by eauto.
        unfold sizeof_composite in Hsize.
        rewrite <- plain_members_sizeof_struct in Hsize by
          (eapply complete_Tstruct_plain; eauto).
        rewrite sizeof_Tstruct in Hbounds.
        revert Hsize.
        pose_align_le.
        intros.
        lia.
      * rewrite sizeof_Tstruct in Hbounds.
        exact Hbounds.
    + apply get_co_members_no_replicate.
    + intros i d0 d1 Hin.
      assert (Hproj : proj_struct i (co_members (get_co id)) (unfold_reptype v) d0 =
        proj_struct i (co_members (get_co id)) (unfold_reptype v) d1).
      {
        apply JMeq_eq.
        eapply (@proj_struct_JMeq i (co_members (get_co id))
          (fun it => reptype (field_type (name_member it) (co_members (get_co id))))
          (fun it => reptype (field_type (name_member it) (co_members (get_co id))))
          (unfold_reptype v) (unfold_reptype v) d0 d1).
        - intros.
          reflexivity.
        - apply get_co_members_no_replicate.
        - exact Hin.
        - apply JMeq_refl.
      }
      rewrite <- Hproj.
      pose proof Hfit as Hfieldfit.
      apply struct_Prop_proj with (i:=i) (d:=d0) in Hfieldfit; [|exact Hin].
      assert (Hfieldlegal : complete_legal_cosu_type
        (field_type (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id))) = true).
      { rewrite name_member_get.
        apply complete_legal_cosu_type_field_type; auto.
        eapply complete_Tstruct_plain; eauto. }
      assert (Hfieldbounds :
        0 <= ofs + field_offset cenv_cs
          (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)) /\
        ofs + field_offset cenv_cs
          (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)) +
          sizeof (field_type
            (name_member (get_member i (co_members (get_co id))))
            (co_members (get_co id))) < Ptrofs.modulus).
      { rewrite name_member_get.
        pose_field.
        lia. }
      assert (Hfieldalign : align_compatible_rec cenv_cs
        (field_type (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)))
        (ofs + field_offset cenv_cs
          (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)))).
      { rewrite name_member_get.
        eapply align_compatible_rec_Tstruct_inv'; eauto. }

      (* The recursive bridge covers the field before its spacer. *)
      rewrite withspacer_spacer.
      rewrite at_offset_eq3.
      unfold offset_val.
      rewrite ptrofs_add_repr.
      rewrite Forall_forall in IH.
      specialize (IH (get_member i (co_members (get_co id))) (in_get_member _ _ Hin)).
      rewrite IH by assumption.

      (* The spacer extends ownership without constraining padding. *)
      rewrite <- ptrofs_add_repr.
      change (Vptr b (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr
        (field_offset cenv_cs (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)))))) with
        (offset_val (field_offset cenv_cs
          (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id))) (Vptr b (Ptrofs.repr ofs))).
      rewrite <- (withspacer_spacer sh
        (field_offset cenv_cs (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)) +
         sizeof (field_type (name_member (get_member i (co_members (get_co id))))
           (co_members (get_co id))))
        (field_offset_next cenv_cs
          (name_member (get_member i (co_members (get_co id))))
          (co_members (get_co id)) (co_sizeof (get_co id)))
        (fun p => EX bytes:list memval,
          !!(Zlength bytes=sizeof
            (field_type (name_member (get_member i (co_members (get_co id))))
              (co_members (get_co id))) /\
            value_memvals_rec
              (field_type (name_member (get_member i (co_members (get_co id))))
                (co_members (get_co id)))
              (proj_struct i (co_members (get_co id)) (unfold_reptype v) d0) bytes) &&
          memvals_at_ptr sh bytes
            (offset_val (field_offset cenv_cs
              (name_member (get_member i (co_members (get_co id))))
              (co_members (get_co id))) p))
        (Vptr b (Ptrofs.repr ofs))).
      apply withspacer_memvals_at_ptr.
      * exact Hread.
      * rewrite name_member_get.
        pose_field.
        apply in_members_field_offset_pos; auto.
        eapply complete_Tstruct_plain; eauto.
      * pose proof (sizeof_pos
          (field_type (name_member (get_member i (co_members (get_co id))))
            (co_members (get_co id)))) as Hfieldsize.
        lia.
      * rewrite !name_member_get.
        pose_field.
        lia.
      * rewrite name_member_get.
        pose_field.
        rewrite sizeof_Tstruct in Hbounds.
        lia.
  - (* Unions own a single selected representation, never all members. *)
    assert (Hempty: co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct Hempty as [Hempty | Hnonempty].
    + (* An empty union has zero size and an empty representation. *)
      rewrite data_at_rec_eq.
      assert (Hrec: forall bytes, value_memvals_rec (Tunion id a) v bytes = True).
      {
        intro bytes.
        rewrite value_memvals_rec_eq.
        generalize (unfold_reptype v).
        rewrite Hempty.
        reflexivity.
      }
      rewrite sizeof_Tunion, (get_co_members_nil_sizeof_0 _ Hempty).
      generalize (unfold_reptype v).
      rewrite Hempty.
      intro empty_value.
      simpl union_pred.
      apply pred_ext.
      * apply exp_right with (@nil memval).
        apply andp_right.
        -- apply prop_right.
           rewrite Hrec, Zlength_nil.
           auto.
        -- rewrite memvals_at_ptr_nil.
           change (emp |-- !! True && emp).
           normalize.
      * apply exp_left.
        intro bytes.
        apply derives_extract_prop.
        intros [Hlen _].
        assert (Hemptybytes : bytes = nil) by (apply Zlength_nil_inv; lia).
        subst bytes.
        rewrite memvals_at_ptr_nil.
        change (!! True && emp |-- emp).
        normalize.
    + (* The selected member is extended to the whole union size. *)
      rewrite value_fits_eq in Hfit.
      rewrite data_at_rec_eq.
      rewrite union_pred_ext with
        (P1 := fun it x p => EX bytes:list memval,
          !!(Zlength bytes=co_sizeof (get_co id) /\
            value_memvals_rec (field_type (name_member it) (co_members (get_co id))) x
              (sublist 0 (sizeof (field_type (name_member it)
                (co_members (get_co id)))) bytes)) &&
          memvals_at_ptr sh bytes p)
        (v1 := unfold_reptype v).
      * rewrite union_pred_memvals_at_ptr_nonempty by exact Hnonempty.
        f_equal.
        apply functional_extensionality.
        intro bytes.
        f_equal.
        f_equal.
        rewrite value_memvals_rec_eq, sizeof_Tunion.
        reflexivity.
      * apply get_co_members_no_replicate.
      * reflexivity.
      * intros i Hin d0 d1 Hactive0 Hactive1.
        assert (Hproj: proj_union i (co_members (get_co id)) (unfold_reptype v) d0 =
          proj_union i (co_members (get_co id)) (unfold_reptype v) d1).
        {
          apply JMeq_eq.
          eapply (@proj_union_JMeq i (co_members (get_co id))
            (fun it => reptype (field_type (name_member it) (co_members (get_co id))))
            (fun it => reptype (field_type (name_member it) (co_members (get_co id))))).
          -- intros.
             reflexivity.
          -- apply get_co_members_no_replicate.
          -- exact Hactive0.
          -- apply JMeq_refl.
        }
        rewrite <- Hproj.
        pose proof Hfit as Hfieldfit.
        apply union_Prop_proj with (i:=i) (d:=d0) in Hfieldfit; [|exact Hactive0].
        assert (Hfieldlegal : complete_legal_cosu_type
          (field_type (name_member (get_member i (co_members (get_co id))))
            (co_members (get_co id))) = true).
        { rewrite name_member_get.
          apply complete_legal_cosu_type_field_type; auto.
          eapply complete_Tunion_plain; eauto. }
        assert (Hfieldbounds : 0 <= ofs /\ ofs +
          sizeof (field_type
            (name_member (get_member i (co_members (get_co id))))
            (co_members (get_co id))) < Ptrofs.modulus).
        { rewrite name_member_get.
          pose_field.
          lia. }
        assert (Hfieldalign : align_compatible_rec cenv_cs
          (field_type (name_member (get_member i (co_members (get_co id))))
            (co_members (get_co id))) ofs).
        { rewrite name_member_get.
          eapply align_compatible_rec_Tunion_inv'; eauto. }

        rewrite withspacer_spacer.
        rewrite Forall_forall in IH.
        specialize (IH (get_member i (co_members (get_co id))) (in_get_member _ _ Hin)).
        rewrite IH by assumption.

        (* Unconstrained bytes fill the remainder after the member. *)
        pose proof (withspacer_memvals_at_ptr sh 0
          (sizeof (field_type (name_member (get_member i (co_members (get_co id))))
            (co_members (get_co id))))
          (co_sizeof (get_co id))
          (fun bytes => value_memvals_rec
            (field_type (name_member (get_member i (co_members (get_co id))))
              (co_members (get_co id)))
            (proj_union i (co_members (get_co id)) (unfold_reptype v) d0) bytes)
          b ofs) as Hpadding.
        rewrite withspacer_spacer in Hpadding.
        rewrite Z.add_0_l, Z.sub_0_r, !offset_val_zero_Vptr in Hpadding.
        apply Hpadding.
        -- exact Hread.
        -- lia.
        -- pose proof (sizeof_pos
             (field_type (name_member (get_member i (co_members (get_co id))))
               (co_members (get_co id)))) as Hfieldsize.
           lia.
        -- rewrite name_member_get by auto.
           pose_field.
           lia.
        -- rewrite (sizeof_Tunion id a) in Hbounds.
           exact Hbounds.
Qed.

(** At a compatible address, readable typed ownership is exactly
    ownership of some [data_at_memvals] representation of the fitting
    value. Padding remains owned without a prescribed value. Unions
    constrain only the selected member and require no union-free layout.

    Compatibility supplies the recursive bridge premises, then value
    fitting is packaged into the pure representation predicate. *)
Lemma data_at_memvals_in_range : forall sh t v p,
  readable_share sh -> field_compatible t nil p -> value_fits t v ->
  data_at sh t v p = EX bytes:list memval, !!(data_at_memvals t v bytes) && memvals_at_ptr sh bytes p.
Proof.
  intros sh t v p Hread Hfc Hfit.
  pose proof (proj1 Hfc) as Hptr.
  destruct p; try contradiction.

  (* ===== Compatibility: extract recursive bridge premises ===== *)

  assert (Hlegal : complete_legal_cosu_type t = true)
    by (destruct Hfc as [_ [? _]]; auto).
  assert (Hbounds : 0 <= Ptrofs.unsigned i /\
    Ptrofs.unsigned i + sizeof t < Ptrofs.modulus).
  { destruct Hfc as [_ [_ [Hsize _]]].
    split.
    - pose proof (Ptrofs.unsigned_range i) as Hrange.
      lia.
    - exact Hsize. }
  assert (Halign : align_compatible_rec cenv_cs t (Ptrofs.unsigned i)).
  { destruct Hfc as [_ [_ [_ [Halign _]]]].
    exact Halign. }
  pose proof (data_at_rec_memvals sh t v b (Ptrofs.unsigned i)
    Hread Hlegal Hfit Hbounds Halign) as Hraw.
  rewrite Ptrofs.repr_unsigned in Hraw.

  (* ===== Representation: package fitting with the memory values ===== *)

  unfold data_at, field_at, at_offset.
  simpl.
  rewrite ptrofs_add_repr_0_r, predicates_hered.prop_true_andp by auto.
  rewrite Hraw.
  change (predicates_hered.exp ?P) with (@exp mpred Nveric _ P).
  f_equal.
  apply functional_extensionality.
  intro bytes.
  change (predicates_hered.andp ?P ?Q) with (P && Q)%logic.
  f_equal.
  change (predicates_hered.prop ?P) with (!! P)%logic.
  f_equal.
  apply prop_ext.
  unfold data_at_memvals.
  tauto.
Qed.

(** Readable typed ownership retains field compatibility explicitly
    and exposes an owned representation list. A value that does not fit
    makes both sides false. The whole object is owned, while padding
    and inactive union interpretations add no constraints. *)
Lemma data_at_memvals_eq : forall sh t v p,
  readable_share sh ->
  data_at sh t v p = !!(field_compatible t nil p) &&
    (EX bytes:list memval, !!(data_at_memvals t v bytes) && memvals_at_ptr sh bytes p).
Proof.
  intros sh t v p Hread.
  destruct (field_compatible_dec t nil p) as [Hfc | Hfc].
  - (* Compatible objects use the bridge when their values fit. *)
    rewrite prop_true_andp by auto.
    destruct (Classical_Prop.classic (value_fits t v)) as [Hfit | Hfit].
    + apply data_at_memvals_in_range; auto.
    + (* Both representations reject values that do not fit. *)
      apply pred_ext.
      * eapply derives_trans.
        -- apply data_at_local_facts.
        -- normalize.
      * unfold data_at_memvals.
        normalize.
  - (* Incompatible addresses make both predicates false. *)
    unfold data_at, field_at.
    rewrite !prop_false_andp by exact Hfc.
    reflexivity.
Qed.

(** Uninitialized readable typed ownership is compatible ownership
    of any memory value list of the object size. This equivalence
    requires no decoded value and covers structure and union padding. *)
Lemma data_at__memvals_eq : forall sh t p,
  readable_share sh ->
  data_at_ sh t p = !! (field_compatible t nil p) &&
    (EX bytes : list memval, !! (Zlength bytes = sizeof t) && memvals_at_ptr sh bytes p).
Proof.
  intros sh t p Hread.
  destruct (field_compatible_dec t nil p) as [Hfc | Hfc].
  - (* Compatibility discharges the block end condition. *)
    rewrite prop_true_andp by auto.
    apply data_at__memvals_in_range; auto.
  - (* The compatibility guard rejects the address on both sides. *)
    rewrite data_at__memory_block.
    rewrite !prop_false_andp by auto.
    reflexivity.
Qed.

(* The array decomposition lemmas below are adapted from secp256k1 proof/vst/array_data_at.v.

Copyright (C) 2026 remix7531
SPDX-License-Identifier: MIT

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)
(** Own the typed list elements at consecutive [sizeof t] offsets.
    The empty list owns [emp]. Compatibility is required by the array
    equivalences, rather than by this recursive definition. *)
Fixpoint iter_data_at_offset (sh : share) (t : type) (p : val)
  (vs : list (reptype t)) {struct vs} : mpred :=
  match vs with
  | nil => emp
  | v :: vs' => data_at sh t v p * iter_data_at_offset sh t (offset_val (sizeof t) p) vs'
  end.

Lemma data_at_tarray_cons : forall sh t v (vs : list (reptype t)) p,
  field_compatible (tarray t (Z.succ (Zlength vs))) nil p ->
  data_at sh (tarray t (Z.succ (Zlength vs))) (v :: vs) p =
  data_at sh t v p * data_at sh (tarray t (Zlength vs)) vs (offset_val (sizeof t) p).
Proof.
  intros. change (v :: vs) with ([v] ++ vs).
  rewrite (split2_data_at_Tarray_app 1 (Z.succ (Zlength vs)) sh t [v] vs p)
    by (rewrite ?Zlength_cons, ?Zlength_nil; lia).
  rewrite (data_at_singleton_array_eq sh t v [v] p eq_refl).
  replace (Z.succ (Zlength vs) - 1) with (Zlength vs) by lia.
  rewrite (arr_field_address0 t (Z.succ (Zlength vs)) p 1 H)
    by (pose proof (Zlength_nonneg vs); lia).
  rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma field_compatible_tarray_shift : forall t k p,
  0 < k -> field_compatible (tarray t k) nil p ->
  field_compatible (tarray t (k - 1)) nil (offset_val (sizeof t) p).
Proof.
  intros t k p Hk Hfc.
  pose proof (proj1 (field_compatible_Tarray_split t 1 k p ltac:(lia)) Hfc)
    as [_ Hfc'].
  rewrite (arr_field_address0 t k p 1 Hfc) in Hfc' by lia.
  rewrite Z.mul_1_r in Hfc'. exact Hfc'.
Qed.

Lemma data_at_tarray_iter_offset : forall sh t (vs : list (reptype t)) p,
  field_compatible (tarray t (Zlength vs)) nil p ->
  data_at sh (tarray t (Zlength vs)) vs p = iter_data_at_offset sh t p vs.
Proof.
  intros sh t vs. induction vs as [|v vs' IH]; intros p Hfc;
    cbn [iter_data_at_offset].
  - rewrite Zlength_nil in *.
    destruct Hfc as [Hptr [Hcosu _]]. cbn in Hcosu.
    apply data_at_zero_array_eq; auto.
  - rewrite Zlength_cons in *.
    rewrite data_at_tarray_cons by auto.
    f_equal. apply IH.
    pose proof (Zlength_nonneg vs').
    apply field_compatible_tarray_shift in Hfc; [|lia].
    replace (Z.succ (Zlength vs') - 1) with (Zlength vs') in Hfc by lia.
    exact Hfc.
Qed.

(** Own the typed list elements at array field addresses starting at
    index [i] in an array of declared length [n]. The empty list owns
    [emp]. The address equivalence requires compatible array bounds. *)
Fixpoint iter_data_at_at (sh : share) (t : type) (n : Z) (p : val) (i : Z)
  (vs : list (reptype t)) {struct vs} : mpred :=
  match vs with
  | nil => emp
  | v :: vs' => data_at sh t v (field_address (tarray t n) (SUB i) p) *
      iter_data_at_at sh t n p (Z.succ i) vs'
  end.

Lemma iter_data_at_offset_eq_at : forall sh t (vs : list (reptype t)) n i p,
  field_compatible (tarray t n) nil p ->
  0 <= i -> i + Zlength vs <= n ->
  iter_data_at_offset sh t (offset_val (sizeof t * i) p) vs =
  iter_data_at_at sh t n p i vs.
Proof.
  intros sh t vs. induction vs as [|v vs' IH]; intros n i p Hfc Hi Hsum;
    cbn [iter_data_at_offset iter_data_at_at]; [reflexivity|].
  rewrite Zlength_cons in *.
  pose proof (Zlength_nonneg vs').
  rewrite (arr_field_address t n p i Hfc) by lia.
  f_equal. rewrite offset_offset_val. rewrite <- Z.mul_succ_r.
  apply IH; [auto | lia | lia].
Qed.

Lemma data_at_tarray_iter_at : forall sh t (vs : list (reptype t)) p,
  field_compatible (tarray t (Zlength vs)) nil p ->
  data_at sh (tarray t (Zlength vs)) vs p =
  iter_data_at_at sh t (Zlength vs) p 0 vs.
Proof.
  intros sh t vs p Hfc.
  rewrite data_at_tarray_iter_offset by auto.
  pose proof (Zlength_nonneg vs).
  rewrite <- (iter_data_at_offset_eq_at sh t vs (Zlength vs) 0 p) by (auto || lia).
  rewrite Z.mul_0_r.
  rewrite isptr_offset_val_zero by (destruct Hfc as [? _]; auto).
  reflexivity.
Qed.

Lemma data_at_tarray_iter_at' : forall sh t (vs : list (reptype t)) n p,
  Zlength vs = n -> field_compatible (tarray t n) nil p ->
  data_at sh (tarray t n) vs p = iter_data_at_at sh t n p 0 vs.
Proof. intros. subst. apply data_at_tarray_iter_at; auto. Qed.

Lemma data_at__tarray_iter_at : forall sh t n p,
  0 <= n -> field_compatible (tarray t n) nil p ->
  data_at_ sh (tarray t n) p =
  iter_data_at_at sh t n p 0 (Zrepeat (default_val t) n).
Proof.
  intros sh t n p Hn Hfc. rewrite data_at__tarray.
  apply data_at_tarray_iter_at'; [apply Zlength_Zrepeat; lia | auto].
Qed.

End MemvalsBridge.
