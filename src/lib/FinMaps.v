Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Import
     Base Tactics.

Section FIN_MAP.

  Context `{FinMap K M} {A : Type}.

  Lemma partial_alter_empty f k
  : partial_alter (M:=M A) f k ∅ = from_option (λ a, {[k := a]}) ∅ (f None).
  Proof.
    apply map_eq. intros. destruct (decide (k = i)) as [->|];
    rewrite ?lookup_partial_alter_eq,?lookup_partial_alter_ne,lookup_empty by auto;
    destruct (f None); cbn; rewrite ?lookup_empty,?lookup_singleton_eq,?lookup_singleton_ne by auto;
    reflexivity.
  Qed.

  Lemma partial_alter_insert_delete f k (m : M A)
  : partial_alter f k m = from_option (insert k) (delete k) (f (m !! k)) m.
  Proof.
    apply map_eq; intros. destruct (decide (k = i)) as [->|Hne].
    - rewrite lookup_partial_alter_eq. destruct (f (m !! i)); cbn;
      [ rewrite lookup_insert_eq | rewrite lookup_delete_eq ]; reflexivity.
    - rewrite lookup_partial_alter_ne by done. destruct (f (m !! k)); cbn;
      [ rewrite lookup_insert_ne | rewrite lookup_delete_ne ]; auto.
  Qed.

  Definition map_values : M A → list A := map_fold (λ _ a acc, a :: acc) [].

  Lemma map_values_partial_alter k f m
  : map_values (partial_alter f k m) ≡ₚ
    from_option cons id (f (m !! k)) (map_values (delete k m)).
  Proof.
    unfold map_values. induction m using map_ind.
    - rewrite partial_alter_empty,delete_empty,map_fold_empty,lookup_empty.
      destruct (f None); cbn; rewrite ?map_fold_singleton,?map_fold_empty; reflexivity.
    - destruct (decide (k = i)) as [->|].
      + rewrite partial_alter_insert_eq,delete_insert_id,lookup_insert_eq,
          partial_alter_insert_delete by auto; eq_norm; cbn. destruct (f (Some x)); cbn.
        * rewrite map_fold_insert; [ reflexivity | typeclasses eauto
          | intros **?**; eq_norm; reflexivity | intros; solve_Permutation | auto ].
        * rewrite delete_id by auto; reflexivity.
      + rewrite partial_alter_insert_ne,delete_insert_ne,lookup_insert_ne by auto.
        rewrite map_fold_insert; [| typeclasses eauto | intros **?**; eq_norm; reflexivity
        | intros; solve_Permutation | rewrite lookup_partial_alter_ne; auto].
        rewrite IHm. destruct (f (m !! k)); cbn; [rewrite Permutation_swap; apply Permutation_skip |];
        [> rewrite map_fold_insert; [ reflexivity | typeclasses eauto | intros **?**; eq_norm; reflexivity
           | intros; solve_Permutation | rewrite lookup_delete_ne; auto ] ..].
  Qed.

  Lemma map_values_insert k a m
  : map_values (<[k := a]> m) ≡ₚ a :: map_values (delete k m).
  Proof. unfold insert,map_insert. apply map_values_partial_alter. Qed.

  Lemma map_values_lookup_Some k a m
    (LU : m !! k = Some a)
  : map_values m ≡ₚ a :: map_values (delete k m).
  Proof.
    revert k a LU; induction m using map_ind; intros.
    - rewrite lookup_empty in LU; congruence.
    - case_map_update_lookup in LU.
      + rewrite delete_insert_eq. apply map_values_insert.
      + erewrite delete_insert_ne,!map_values_insert,delete_delete,delete_id,IHm by eauto.
        solve_Permutation.
  Qed.

End FIN_MAP.
