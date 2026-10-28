(** * Array decomposition for aggregate field copies.

    Expose elements as separated [field_at] predicates while retaining
    their enclosing root and path. Native decomposition requires an
    explicit finite element list and provable bounds and lengths. *)
From Ltac2 Require Import Ltac2.
Require Import VST.floyd.base2.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.field_at.

Set Default Proof Mode "Classic".

Import ListNotations.
Local Open Scope logic.

Section ArrayCopy.
Context {cs: compspecs}.

(** Split a nonempty array interval into its first element and remaining
    interval. The length equation fixes the represented interval and
    [JMeq] connects the dependent element representation at [lo]. *)
Lemma array_at_cons: forall sh t path lo hi
  (first: reptype (nested_field_type t (ArraySubsc 0 :: path))) rest
  (element: reptype (nested_field_type t (ArraySubsc lo :: path))) p,
  lo < hi -> Zlength (first :: rest) = hi - lo -> JMeq first element ->
  array_at sh t path lo hi (first :: rest) p =
    (field_at sh t (ArraySubsc lo :: path) element p *
     array_at sh t path (lo + 1) hi rest p)%logic.
Proof.
  intros sh t path lo hi first rest element p BOUNDS LENGTH ELEMENT.
  rewrite (split2_array_at sh t path lo (lo + 1) hi) by lia.
  replace (lo + 1 - lo) with 1 by lia.
  rewrite sublist_1_cons, Zlength_cons.
  replace (Z.succ (Zlength rest) - 1) with (Zlength rest) by lia.
  rewrite (sublist_same 0 (Zlength rest) rest) by lia.
  change ((array_at sh t path lo (lo + 1) [first] p *
    array_at sh t path (lo + 1) hi rest p)%logic =
    (field_at sh t (ArraySubsc lo :: path) element p *
     array_at sh t path (lo + 1) hi rest p)%logic).
  rewrite array_at_len_1 with (v' := element) by exact ELEMENT.
  reflexivity.
Qed.

(** Expose both elements of an array interval from zero to two, preserving
    the dependent field types through explicit representation equalities. *)
Lemma array_at_two_elements: forall sh t path
  (first second: reptype (nested_field_type t (ArraySubsc 0 :: path)))
  (first_element: reptype (nested_field_type t (ArraySubsc 0 :: path)))
  (second_element: reptype (nested_field_type t (ArraySubsc 1 :: path))) p,
  JMeq first first_element -> JMeq second second_element ->
  array_at sh t path 0 2 [first; second] p =
    (field_at sh t (ArraySubsc 0 :: path) first_element p *
     field_at sh t (ArraySubsc 1 :: path) second_element p)%logic.
Proof.
  intros sh t path first second first_element second_element p FIRST SECOND.
  rewrite (split2_array_at sh t path 0 1 2)
    by (rewrite ?Zlength_cons, ?Zlength_nil; lia).
  change ((array_at sh t path 0 (0 + 1) [first] p *
    array_at sh t path 1 (1 + 1) [second] p)%logic =
    (field_at sh t (ArraySubsc 0 :: path) first_element p *
     field_at sh t (ArraySubsc 1 :: path) second_element p)%logic).
  rewrite (array_at_len_1 sh t path 0 first first_element p FIRST).
  rewrite (array_at_len_1 sh t path 1 second second_element p SECOND).
  reflexivity.
Qed.

(** Expose a two element array field as two separated element
    fields in the same enclosing object. The selected path must be legal. *)
Lemma field_at_array_two_elements: forall sh t path element attributes
  (value: reptype (nested_field_type t path))
  (first second: reptype (nested_field_type t (ArraySubsc 0 :: path)))
  (first_element: reptype (nested_field_type t (ArraySubsc 0 :: path)))
  (second_element: reptype (nested_field_type t (ArraySubsc 1 :: path))) p,
  legal_nested_field t path ->
  nested_field_type t path = Tarray element 2 attributes ->
  JMeq value [first; second] ->
  JMeq first first_element -> JMeq second second_element ->
  field_at sh t path value p =
    (field_at sh t (ArraySubsc 0 :: path) first_element p *
     field_at sh t (ArraySubsc 1 :: path) second_element p)%logic.
Proof.
  intros sh t path element attributes value first second
    first_element second_element p LEGAL TYPE VALUE FIRST SECOND.
  erewrite field_at_Tarray by (eauto; lia).
  apply array_at_two_elements; assumption.
Qed.

End ArrayCopy.

(* Convertible dependent arguments must be canonical before rewriting. *)
Ltac2 copy_array_canonicalize (replacement : constr) :=
  repeat (
    match! goal with
    | [ |- context surrounding [@array_at ?cs ?share ?root ?path ?lo ?hi ?values ?pointer] ] =>
        let original := constr:(@array_at $cs $share $root $path
          $lo $hi $values $pointer) in
        match Constr.equal original replacement with
        | true => Control.zero Match_failure
        | false =>
            Std.unify original replacement;
            let changed := Pattern.instantiate surrounding replacement in
            change $changed
        end
    end).

Ltac2 copy_array_rewrite_decomposition_run (equation : constr) :=
  lazy_match! Constr.type equation with
  | ?lhs = _ =>
      copy_array_canonicalize lhs;
      rewrite $equation
  end.

Ltac2 copy_array_unfold_singleton (cs : constr) (share : constr) (root : constr)
    (path : constr) (lo : constr) (hi : constr) (values : constr) (pointer : constr) :=
  let element := open_constr:(_ : @reptype $cs
    (@nested_field_type $cs $root (ArraySubsc $lo :: $path))) in
  let decomposition := Fresh.in_goal @COPY_ARRAY_DECOMPOSITION in
  assert ($decomposition :
    @array_at $cs $share $root $path $lo $hi $values $pointer =
    @field_at $cs $share $root (ArraySubsc $lo :: $path) $element $pointer)
    by (
      let endpoint := Fresh.in_goal @COPY_ARRAY_ENDPOINT in
      assert ($endpoint : $hi = $lo + 1) by ltac1:(lia);
      let equation := Control.hyp endpoint in
      rewrite $equation;
      apply (@array_at_len_1 $cs);
      apply JMeq_refl);
  copy_array_rewrite_decomposition_run (Control.hyp decomposition);
  Std.clear [decomposition].

Ltac2 copy_array_unfold_cons (cs : constr) (share : constr) (root : constr)
    (path : constr) (lo : constr) (hi : constr) (values : constr)
    (tail : constr) (pointer : constr) :=
  let element := open_constr:(_ : @reptype $cs
    (@nested_field_type $cs $root (ArraySubsc $lo :: $path))) in
  let decomposition := Fresh.in_goal @COPY_ARRAY_DECOMPOSITION in
  assert ($decomposition :
    @array_at $cs $share $root $path $lo $hi $values $pointer =
    (@field_at $cs $share $root (ArraySubsc $lo :: $path) $element $pointer *
     @array_at $cs $share $root $path ($lo + 1) $hi $tail $pointer)%logic)
    by (
      apply (@array_at_cons $cs) >
      [ ltac1:(lia)
      | rewrite ?Zlength_cons, ?Zlength_nil; ltac1:(lia)
      | apply JMeq_refl ]);
  copy_array_rewrite_decomposition_run (Control.hyp decomposition);
  Std.clear [decomposition].

(** Decompose an array interval along its explicit element list. Empty
    and singleton tails require matching endpoints, longer lists require
    the interval length equation. Reject values that cannot expose a
    finite list, and retain the element order. *)
Ltac2 rec copy_array_unfold_at_run (cs : constr) (share : constr) (root : constr)
    (path : constr) (lo : constr) (hi : constr) (values : constr) (pointer : constr) :=
  let values := eval hnf in $values in
  lazy_match! values with
  | @nil _ =>
      let endpoint := Fresh.in_goal @COPY_ARRAY_ENDPOINT in
      assert ($endpoint : $hi = $lo) by ltac1:(lia);
      let equation := Control.hyp endpoint in
      rewrite ?($equation), array_at_len_0;
      Std.clear [endpoint]
  | @cons _ _ ?tail =>
      lazy_match! tail with
      | @nil _ =>
          copy_array_unfold_singleton cs share root path lo hi values pointer
      | _ =>
          copy_array_unfold_cons cs share root path lo hi values tail pointer;
          let next := eval cbn in ($lo + 1) in
          copy_array_canonicalize
            constr:(@array_at $cs $share $root $path $next $hi $tail $pointer);
          copy_array_unfold_at_run cs share root path next hi tail pointer
      end
  | _ =>
      Control.zero (Tactic_failure (Some
        (Message.of_string "Aggregate array copy requires an explicit finite element list")))
  end.

Ltac2 copy_array_expose_data_at (cs : constr) (share : constr)
    (root : constr) (path : constr) (pointer : constr) :=
  Control.plus
    (fun () =>
      lazy_match! path with
      | @nil _ =>
          repeat (
            match! goal with
            | [ |- context surrounding [@data_at ?actual_cs ?actual_share ?stored ?value ?actual_pointer] ] =>
                Std.unify actual_cs cs;
                Std.unify actual_share share;
                Std.unify actual_pointer pointer;
                Std.unify stored root;
                let changed := Pattern.instantiate surrounding
                  constr:(@field_at $cs $share $stored nil $value $pointer) in
                change $changed
            end)
      end)
    (fun _ => ()).

Ltac2 copy_array_unfold_field (cs : constr) (share : constr) (root : constr)
    (path : constr) (value : constr) (pointer : constr) :=
  let array_type := eval hnf in (@nested_field_type $cs $root $path) in
  lazy_match! array_type with
  | Tarray _ ?length _ =>
      let values := eval vm_compute in $value in
      let decomposition := Fresh.in_goal @COPY_ARRAY_DECOMPOSITION in
      assert ($decomposition :
        @field_at $cs $share $root $path $value $pointer =
        @array_at $cs $share $root $path 0 $length $values $pointer)
        by (
          eapply (@field_at_Tarray $cs) >
          [ first [ solve [ltac1:(auto)]
                  | repeat constructor; simpl; ltac1:(auto); ltac1:(lia) ]
          | reflexivity
          | ltac1:(lia)
          | apply JMeq_refl ]);
      let equation := Control.hyp decomposition in
      rewrite $equation;
      Std.clear [decomposition];
      copy_array_unfold_at_run cs share root path constr:(0) length values pointer
  | _ =>
      Control.zero (Tactic_failure (Some
        (Message.of_string "Aggregate array copy requires an array ancestor")))
  end.

(** Expose an array ancestor of the selected field, including a root
    [data_at]. Require matching root, share, path, and pointer ownership,
    an array type, and a value reducible to a finite element list. *)
Ltac2 copy_field_unfold_array_ancestor_run (cs : constr) (share : constr)
    (root : constr) (path : constr) (pointer : constr) :=
  copy_array_expose_data_at cs share root path pointer;
  match! goal with
  | [ |- context [@field_at ?actual_cs ?actual_share ?stored ?actual ?value ?actual_pointer] ] =>
      Std.unify actual_cs cs;
      Std.unify actual_share share;
      Std.unify actual_pointer pointer;
      Std.unify stored root;
      Std.unify actual path;
      copy_array_unfold_field cs share stored actual value pointer
  end.
