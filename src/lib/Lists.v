Set Implicit Arguments.

From refinement.lib Require Import
     Base Tactics Logic.

From stdpp Require Export list.

Section GENERAL.

  Context {A : Type}.

  Lemma list_app_neq_nil
    (l : list A)
    (x : A)
  : l ++ [x] <> [].
  Proof. intros; destruct l; intro; discriminate. Qed.

  Lemma list_app_cases
    (l : list A)
  : { l = [] } + { exists x l', l = l' @@ x }.
  Proof.
    destruct l as [| a l].
    - left; reflexivity.
    - right. revert a. induction l as [| a' l IH]; intros.
      + eexists; exists []; reflexivity.
      + specialize (IH a'); destruct IH as (? & ? & IH).
        repeat eexists; rewrite IH,app_comm_cons; reflexivity.
  Qed.

  Lemma elem_of_app_shortcircuit
    `{!EqDecision A}
    {l1 l2 : list A}
    {e : A}
    (E : e ∈ l1 ++ l2)
  : e ∈ l1 \/ (e ∉ l1 /\ e ∈ l2).
  Proof.
    apply disj_shortcircuit; [ typeclasses eauto | apply elem_of_app; assumption ].
  Qed.

  Lemma last_app
    (l0 l1 : list A)
    (d : A)
    (NE : l1 <> [])
  : List.last (l0 ++ l1) d = List.last l1 d.
  Proof.
    induction l0 as [| a l0].
    - reflexivity.
    - simpl; rewrite IHl0. destruct (l0 ++ l1) as [| ? l] eqn:El01.
      + exfalso; apply NE. eapply app_eq_nil. eassumption.
      + reflexivity.
  Qed.

  Lemma lookup_snoc_l_Some
    a (l : list A) i x
    (LU : l !! i = Some x)
  : (l @@ a) !! i = Some x.
  Proof. apply (lookup_app_l_Some _ [a]),LU. Qed.

  Lemma lookup_snoc_r_Some
    a (l : list A)
  : (l @@ a) !! (length l) = Some a.
  Proof. exact (proj2 (lookup_snoc_Some _ _ _ _) (or_intror (conj eq_refl eq_refl))). Qed.

  Lemma Exists_lookup
    (l : list A)
    (P : A -> Prop)
  : Exists P l <->
    exists i a, l !! i = Some a /\ P a.
  Proof.
    split.
    - intros AN. apply Exists_exists in AN as (? & EO & ?).
      apply list_elem_of_lookup_1 in EO as (? & ?).
      repeat eexists; eassumption.
    - intros (? & ? & ? & ?). apply Exists_exists. eexists; split;
      [ eapply list_elem_of_lookup; eexists |]; eassumption.
  Qed.

  Lemma Exists_lookup_1
    (l : list A)
    (P : A -> Prop)
    (AN : Exists P l)
  : exists i a, l !! i = Some a /\ P a.
  Proof. eapply Exists_lookup; eassumption. Qed.

  Lemma Exists_lookup_2
    (l : list A)
    (P : A -> Prop)
    (a : A)
    i
    (LU : l !! i = Some a)
    (HP : P a)
  : Exists P l.
  Proof. eapply Exists_lookup. do 2 eexists; split; eassumption. Qed.

  Lemma lookup_app_r_Some
    (l1 l2 : list A)
    `(LU : l2 !! i = Some x)
  : (l1 ++ l2) !! (length l1 + i) = Some x.
  Proof.
    induction l1.
    - eassumption.
    - rewrite <-app_comm_cons; eassumption.
  Qed.

  Lemma list_eq_iff
    (l1 l2 : list A)
  : (∀ i, l1 !! i = l2 !! i) <-> l1 = l2.
  Proof.
    split; [eapply list_eq | intros; subst; reflexivity].
  Qed.

  Lemma Forall_sse
    (l1 : list A)
    `(FA : Forall P l1)
    `(SSE : l2 ⊆ l1)
  : Forall P l2.
  Proof.
    rewrite Forall_forall in *.
    intros ? EO. apply FA, SSE, EO.
  Qed.

  Lemma Forall_snoc (P : A → Prop) (l : list A) (a : A)
  : Forall P (l @@ a) ↔ Forall P l ∧ P a.
  Proof.
    revert a; induction l; intros.
    - split; cbn; intros HH; [ inv HH | econstructor ]; tauto.
    - split; rewrite <-app_comm_cons.
      + intros HH. inv HH as [| ??? HH1]. eapply IHl in HH1. split; [econstructor |]; tauto.
      + intros [HH ?]. inv HH. econstructor; [eassumpt |]. apply IHl. tauto.
  Qed.

  Definition Forall_snoc_2 (P : A → Prop) (l : list A) (a : A)
    (FA : Forall P l)
    (Pa : P a)
  : Forall P (l @@ a) := (proj2 (Forall_snoc P l a) (conj FA Pa)).

  Lemma Exists_sse
    (l1 : list A)
    `(EX : Exists P l1)
    `(SSE : l1 ⊆ l2)
  : Exists P l2.
  Proof.
    rewrite Exists_exists in *; destruct EX as (?&?&?).
    eexists; split; [apply SSE |]; eassumption.
  Qed.

  Lemma Forall2_elem_of_l
    {B : Type} (P : A → B → Prop)
    `(FA : Forall2 P l k)
    `(EO : x ∈ l)
  : ∃ y, y ∈ k ∧ P x y.
  Proof.
    apply list_elem_of_lookup_1 in EO as (?&LU).
    pose proof (Forall2_lookup_l _ _ _ _ _ FA LU) as (?&LU'&HP).
    eexists; split; [eapply list_elem_of_lookup_2,LU' | exact HP].
  Qed.

  Lemma Forall2_elem_of_r
    {B : Type} (P : A → B → Prop)
    `(FA : Forall2 P l k)
    `(EO : y ∈ k)
  : ∃ x, x ∈ l ∧ P x y.
  Proof.
    apply list_elem_of_lookup_1 in EO as (?&LU).
    pose proof (Forall2_lookup_r _ _ _ _ _ FA LU) as (?&LU'&HP).
    eexists; split; [eapply list_elem_of_lookup_2,LU' | exact HP].
  Qed.

  Lemma elem_of_elt
    (x : A) (l1 l2 : list A)
  : x ∈ l1 ++ x :: l2.
  Proof. rewrite list_elem_of_In. apply in_elt. Qed.

  Lemma not_elem_of_list_singleton
    (a x : A)
  : x ∉ [a] <-> x ≠ a.
  Proof.
    split; intros HH C; apply HH; subst; set_solver.
  Qed.

  Lemma elem_of_snoc
    (a : A) (l : list A) (x : A)
  : x ∈ l @@ a ↔ x ∈ l ∨ x = a.
  Proof.
    intros. split; intros HH.
    - apply elem_of_app in HH.
      rewrite list_elem_of_singleton in HH.
      assumption.
    - apply elem_of_app.
      rewrite list_elem_of_singleton.
      assumption.
  Qed.

  Lemma not_elem_of_snoc
    (a : A) (l : list A) (x : A)
  : x ∉ l @@ a ↔ (x ∉ l) ∧ x ≠ a.
  Proof.
    intros. split; intros HH.
    - apply not_elem_of_app in HH.
      rewrite not_elem_of_list_singleton in HH.
      assumption.
    - apply not_elem_of_app.
      rewrite not_elem_of_list_singleton.
      assumption.
  Qed.

  Lemma elem_of_take_elem_of
    (x : A) (n : nat) (l : list A)
    (EO : x ∈ take n l)
  : x ∈ l.
  Proof.
    apply elem_of_take in EO as (?&LU&?). eapply list_elem_of_lookup_2,LU.
  Qed.

  Lemma elem_of_drop
    (x : A) (n : nat) (l : list A)
  : x ∈ drop n l ↔ ∃ i, l !! i = Some x ∧ n ≤ i.
  Proof.
    revert n; induction l; intros.
    - rewrite drop_nil; split; intros HH; [set_solver | naive_solver].
    - destruct n; cbn.
      + split; [intros EO | intros (j&LU&?)].
        * apply elem_of_cons in EO as [->|EO].
          { exists 0; split; [reflexivity | lia]. }
          { apply list_elem_of_lookup_1 in EO as (?&LU).
            eexists (S _); split; [ exact LU | lia ]. }
        * exact (list_elem_of_lookup_2 _ _ _ LU).
      + split; [intros EO | intros (j&LU&?)].
        * pose proof (proj1 (IHl _) EO) as (j&LU&LT).
          eexists (S _); split; [exact LU | lia].
        * destruct j; [exfalso; lia |]; cbn in *.
          exact (proj2 (IHl n) ltac:(eexists;split;[exact LU|lia])).
  Qed.

  Lemma elem_of_drop_elem_of
    (x : A) (n : nat) (l : list A)
    (EO : x ∈ drop n l)
  : x ∈ l.
  Proof.
    apply elem_of_drop in EO as (?&LU&?). eapply list_elem_of_lookup_2,LU.
  Qed.

  Lemma submseteq_iff
    (xs1 : list A) (xs2 : list A)
    : xs1 ⊆+ xs2 <-> ∃ xs : list A, xs1 ++ xs ≡ₚ xs2.
  Proof using.
    split.
    - intros SUBMSETEQ. induction SUBMSETEQ.
      + exists []; eauto.
      + destruct IHSUBMSETEQ as [xs IH]. exists xs. simpl. now rewrite IH.
      + exists []. rewrite app_nil_r. econstructor.
      + destruct IHSUBMSETEQ as [xs IH]. exists (x :: xs). simpl. rewrite <- IH. now rewrite <-Permutation_middle.
      + destruct IHSUBMSETEQ1 as [xs1 IH1], IHSUBMSETEQ2 as [xs2 IH2]. exists (xs1 ++ xs2).
        rewrite app_assoc. rewrite IH1. now rewrite IH2.
    - intros [xs PERM]. rewrite Permutation_app_comm in PERM. revert xs1 xs2 PERM. induction xs as [ | x xs IH]; simpl; intros.
      + now rewrite PERM.
      + rewrite <- PERM. econstructor 4. now eapply IH.
  Qed.

  Lemma submseteq_seq
    `(ND : NoDup l)
    `(EO_UP : ∀ `(EO : n ∈ l), n < m)
  : l ⊆+ seq 0 m.
  Proof.
    revert m EO_UP; induction l; intros.
    - apply submseteq_nil_l.
    - inv ND as [| ? ? ? ND'].
      assert (a < m ∧ ∀ n, n ∈ l → n < m) as [? LT].
      { split.
        - specialize (EO_UP a ltac:(set_solver)). assumption.
        - intros n EO; specialize (EO_UP n ltac:(set_solver)). assumption. }
      specialize (IHl ND' m LT).
      assert (a ∈ seq 0 m) as aEO by (eapply elem_of_seq; lia).
      apply elem_of_Permutation in aEO as [? EQ]; rewrite EQ in *.
      apply submseteq_cons_r in IHl as [IH|(? & ? & ?)].
      + apply submseteq_skip; assumption.
      + eq_norm; set_solver.
  Qed.

  Lemma submseteq_app_drop_l
    (l1 l2 l3 : list A)
    (SMSE : l1 ++ l2 ⊆+ l3)
  : l2 ⊆+ l3.
  Proof.
    eapply submseteq_app_l in SMSE as (? & ? & PERM & ? & ?).
    rewrite PERM. apply submseteq_inserts_l. assumption.
  Qed.

  Lemma submseteq_app_drop_r
    (l1 l2 l3 : list A)
    (SMSE : l1 ++ l2 ⊆+ l3)
  : l1 ⊆+ l3.
  Proof.
    eapply submseteq_app_l in SMSE as (? & ? & PERM & ? & ?).
    rewrite PERM. apply submseteq_inserts_r. assumption.
  Qed.

  Definition cons_submseteq
    (l k : list A) (x : A)
    `(SMSE : x :: l ⊆+ k)
  : ∃ j, k !! j = Some x := lookup_submseteq (x :: l) k 0 x eq_refl SMSE.

  Lemma lookup_lookup_submseteq
    (l k : list A) i1 x1 i2 x2
    (LU1 : l !! i1 = Some x1)
    (LU2 : l !! i2 = Some x2)
    (NE : i1 ≠ i2)
    (SMSE : l ⊆+ k)
  : ∃ j1 j2,
      k !! j1 = Some x1 ∧
      k !! j2 = Some x2 ∧
      j1 ≠ j2.
  Proof.
    revert i1 x1 i2 x2 LU1 LU2 NE;
    induction SMSE as [| x l1 l2 SMSE IH | x y l0 | x l1 l2 SMSE IH
                      | l1 l2 l3 SMSE12 IH12 SMSE23 IH23 ]; intros.
    - naive_solver.
    - destruct i1 as [|i1]; destruct i2 as [|i2]; simpl in *; simplify_eq.
      + destruct (lookup_submseteq _ _ _ _ LU2 SMSE) as [j LU2'].
        exists 0,(S j); naive_solver.
      + destruct (lookup_submseteq _ _ _ _ LU1 SMSE) as [j LU1'].
        exists (S j),0; naive_solver.
      + destruct (IH _ _ _ _ LU1 LU2 ltac:(lia)) as (j1&j2&LU1'&LU2'&NE').
        exists (S j1),(S j2); naive_solver.
    - destruct i1 as [|[|i1]], i2 as [|[|i2]]; simplify_eq/=;
      [ exists 1,0 | exists 1,(S (S i2)) | exists 0,1 | exists 0,(S (S i2)) | exists (S (S i1)),1
      | exists (S (S i1)),0 | exists (S (S i1)),(S (S i2)) ]; naive_solver.
    - destruct (IH _ _ _ _ LU1 LU2 NE) as (j1&j2&LU1'&LU2'&NE').
      exists (S j1), (S j2); naive_solver.
    - destruct (IH12 _ _ _ _ LU1 LU2 NE) as (j1&j2&LU1'&LU2'&NE').
      by apply (IH23 _ _ _ _ LU1' LU2' NE').
  Qed.

  Definition cons_cons_submseteq
    (l k : list A) x1 x2
    `(SMSE : x1 :: x2 :: l ⊆+ k)
  : ∃ j1 j2,
      k !! j1 = Some x1 ∧
      k !! j2 = Some x2 ∧
      j1 ≠ j2 :=
  @lookup_lookup_submseteq (x1 :: x2 :: l) k 0 x1 1 x2 eq_refl eq_refl ltac:(lia) SMSE.

  Lemma submseteq_cons_drop
    x (l1 l2 : list A)
    (SMSE : x :: l1 ⊆+ l2)
  : l1 ⊆+ l2.
  Proof.
    trans (x :: l1); [|done].
    apply submseteq_cons. reflexivity.
  Qed.

  Definition lookup_take_Some_2
    (l : list A) (n i : nat) (a : A)
    (LU : l !! i = Some a)
    (LT : i < n)
  : take n l !! i = Some a :=
    proj2 (lookup_take_Some _ _ _ _) (conj LU LT).

End GENERAL.

Section SUBLIST_LOOKUP.

  Context {A : Type}.

  Lemma sublist_lookup_drop_cons
    (l : list A) i n a
  : sublist_lookup (S i) n (a :: l) =
    sublist_lookup i n l.
  Proof.
    destruct (decide (i + n <= length l)).
    - rewrite !sublist_lookup_Some by (cbn;lia); reflexivity.
    - rewrite !sublist_lookup_None by (cbn;lia); reflexivity.
  Qed.

  Lemma sublist_lookup_take_cons
    (l : list A) n a
  : sublist_lookup 0 (S n) (a :: l) =
    fmap (cons a) (sublist_lookup 0 n l).
  Proof.
    destruct (decide (n <= length l)).
    - rewrite !sublist_lookup_Some by (cbn;lia); cbn; rewrite drop_0; reflexivity.
    - rewrite !sublist_lookup_None by (cbn;lia); reflexivity.
  Qed.

  Lemma sublist_lookup_drop_app
    (l1 l2 : list A) i
  : sublist_lookup (length l1) i (l1 ++ l2) =
    sublist_lookup 0 i l2.
  Proof.
    induction l1; cbn in *; [| rewrite sublist_lookup_drop_cons,IHl1]; reflexivity.
  Qed.

  Lemma sublist_lookup_take_app
    (l1 l2 : list A)
  : sublist_lookup 0 (length l1) (l1 ++ l2) = Some l1.
  Proof.
    induction l1.
    - reflexivity.
    - cbn. rewrite sublist_lookup_take_cons,IHl1. reflexivity.
  Qed.

  Lemma sublist_lookup_elt
    i n (l : list A) l'
    (LU : sublist_lookup i n l = Some l')
  : ∃ l1 l2,
      l = l1 ++ l' ++ l2 ∧
      i = length l1 ∧
      n = length l'.
  Proof.
    eapply sublist_lookup_Some' in LU as HH; destruct HH; subst.
    exists (take i l), (drop (i + n) l); split; [|split].
    - rewrite app_assoc,take_take_drop,take_drop; reflexivity.
    - rewrite length_take_le by lia; reflexivity.
    - rewrite length_take_le by (rewrite length_drop; lia); reflexivity.
  Qed.

  Lemma sublist_lookup_lookup
    (l : list A)
    `(SLU : sublist_lookup i n l = Some l')
    `(LT : j < n)
  : l !! (i + j) = l' !! j.
  Proof.
    apply sublist_lookup_elt in SLU as HH; destruct HH as (? & ? & ? & ? & ?); subst.
    apply sublist_lookup_length in SLU as HH; subst.
    rewrite lookup_app_r,lookup_app_l,Nat.add_sub' by lia; reflexivity.
  Qed.

  Lemma sublist_lookup_lookup_Some_1
    (l : list A)
    `(SLU : sublist_lookup i n l = Some l')
    `(LU : l' !! j = Some e)
  : l !! (i + j) = Some e.
  Proof.
    erewrite sublist_lookup_lookup; try eassumption.
    apply sublist_lookup_length in SLU; apply lookup_lt_Some in LU; lia.
  Qed.

  Lemma sublist_lookup_lookup_Some_2
    (l : list A)
    `(SLU : sublist_lookup i n l = Some l')
    `(LU : l !! j = Some e)
    `(LE : i <= j < i + n)
  : l' !! (j - i) = Some e.
  Proof.
    erewrite <- sublist_lookup_lookup; try eassumption;
    [match goal with |- _ !! ?a = _ => assert (a = j) as E by lia end; rewrite E |];
    eassumption || lia.
  Qed.

  Lemma sublist_lookup_length'
    (l : list A) i n k
    `(LU : sublist_lookup i n l = Some k)
  : length k ≤ length l.
  Proof.
    eapply sublist_lookup_Some' in LU as (? & ?); subst.
    rewrite length_take_le by (rewrite length_drop; lia); lia.
  Qed.

  Lemma sublist_lookup_Some_singleton
    i (l : list A) e
  : sublist_lookup i 1 l = Some [e] <->
    l !! i = Some e.
  Proof.
    split; intros HH.
    - eapply sublist_lookup_elt in HH as (? & ? & ? & ? & ?); subst; cbn.
      apply list_lookup_middle; reflexivity.
    - apply list_elem_of_split_length in HH as (? & ? & ? & ?); subst.
      rewrite sublist_lookup_drop_app; reflexivity.
  Qed.

  Lemma sublist_lookup_app_Some
    (l1 l l2 : list A)
    `(LU : sublist_lookup i n l1 = Some l)
  : sublist_lookup i n (l1 ++ l2) = Some l.
  Proof.
    eapply sublist_lookup_elt in LU as (? & ? & ? & ? & ?); subst.
    rewrite <-!app_assoc,sublist_lookup_drop_app,sublist_lookup_take_app.
    reflexivity.
  Qed.

  Lemma sublist_lookup_app_l
    (l1 l2 : list A) i n
    (LT : i + n <= length l1)
  : sublist_lookup i n (l1 ++ l2) = sublist_lookup i n l1.
  Proof.
    rewrite !sublist_lookup_Some by (rewrite ?length_app;lia).
    rewrite drop_app_le,take_app_le by (rewrite ?length_drop; lia); reflexivity.
  Qed.

  Lemma sublist_lookup_app_r
    (l1 l2 : list A) i n
    (LT : length l1 <= i)
  : sublist_lookup i n (l1 ++ l2) = sublist_lookup (i - length l1) n l2.
  Proof.
    destruct (decide (i + n <= length (l1 ++ l2))) as [LE | LE];
    eassert (_) as LE' by (apply LE); rewrite length_app in LE'.
    - rewrite !sublist_lookup_Some by (cbn;lia).
      rewrite drop_app_ge by assumption; reflexivity.
    - rewrite !sublist_lookup_None by (cbn;lia); reflexivity.
  Qed.

  Lemma sublist_lookup_Some_app_l
    (l : list A)
    `(SLLU : sublist_lookup i n l = Some (l1 ++ l2))
  : sublist_lookup i (n - length l2) l = Some l1.
  Proof.
    eapply sublist_lookup_elt in SLLU as HH; destruct HH as (? & ? & ? & ? & ?); subst.
    rewrite ?length_app,?Nat.add_sub,<-?app_assoc in *.
    rewrite sublist_lookup_drop_app,sublist_lookup_take_app; reflexivity.
  Qed.

  Lemma sublist_lookup_Some_app_l'
    (l : list A)
    `(SLLU : sublist_lookup i n l = Some (l1 ++ l2))
  : sublist_lookup i (length l1) l = Some l1.
  Proof.
    eapply sublist_lookup_Some_app_l in SLLU as HH.
    eapply sublist_lookup_length in HH as ?.
    eq_norm; reflexivity.
  Qed.

  Lemma sublist_lookup_Some_app_r
    (l : list A)
    `(SLLU : sublist_lookup i n l = Some (l1 ++ l2))
  : sublist_lookup (i + length l1) (n - length l1) l = Some l2.
  Proof.
    eapply sublist_lookup_elt in SLLU as HH; destruct HH as (l3 & l4 & ? & ? & ?); subst.
    rewrite ?length_app,?Nat.add_sub',<-?app_assoc in *.
    rewrite (ltac:(symmetry; apply length_app) : length l3 + length l1 = length (l3 ++ l1)).
    rewrite (ltac:(rewrite app_assoc; reflexivity) : l3 ++ l1 ++ _ = (l3 ++ l1) ++ _).
    rewrite sublist_lookup_drop_app,sublist_lookup_take_app; reflexivity.
  Qed.

  Lemma sublist_lookup_Some_app_r'
    (l : list A)
    `(SLLU : sublist_lookup i n l = Some (l1 ++ l2))
  : sublist_lookup (i + length l1) (length l2) l = Some l2.
  Proof.
    eapply sublist_lookup_Some_app_r in SLLU as HH.
    eapply sublist_lookup_length in HH as ?.
    eq_norm; reflexivity.
  Qed.

End SUBLIST_LOOKUP.

Section SUBLIST.

  Context {A : Type}.

  Lemma sublist_elem_of
    (l1 l2 : list A)
    `(SBL : l1 `sublist_of` l2)
    `(EO : a ∈ l1)
  : a ∈ l2.
  Proof.
    apply sublist_submseteq in SBL.
    eapply elem_of_submseteq; eassumption.
  Qed.

  Lemma sublist_NoDup_split
    (la lb lc : list A)
    (a b : A)
    (sub : list A)
    (SUB : sub `sublist_of` (la ++ a :: lb ++ b :: lc))
    (A_IN : a ∈ sub)
    (B_IN : b ∈ sub)
    (ND : NoDup (la ++ a :: lb ++ b :: lc))
  : ∃ s1 s2 s3,
      sub = s1 ++ a :: s2 ++ b :: s3.
  Proof.
    revert sub SUB A_IN B_IN; induction la as [| h la IH]; intros.
    - cbn in SUB; inversion SUB; subst.
      + apply elem_of_cons in B_IN as [<- | B_IN'].
        * exfalso; apply NoDup_cons in ND as [NI _]; apply NI;
          apply elem_of_app; right; apply elem_of_cons; left; reflexivity.
        * apply list_elem_of_split in B_IN' as (s_mid & s_end & ->);
          exists [], s_mid, s_end; reflexivity.
      + exfalso; apply NoDup_cons in ND as [NI _]; apply NI;
        eapply sublist_elem_of; eassumption.
    - cbn in SUB; inversion SUB; subst.
      + apply elem_of_cons in A_IN as [<- | A_IN'].
        * exfalso; apply NoDup_cons in ND as [NI _]; apply NI.
          apply elem_of_app; right. apply elem_of_cons; left. reflexivity.
        * apply elem_of_cons in B_IN as [<- | B_IN'].
          { exfalso; apply NoDup_cons in ND as [NI _]; apply NI.
            apply elem_of_app; right; apply elem_of_cons; right.
            apply elem_of_app; right; apply elem_of_cons; left; reflexivity. }
          { apply NoDup_cons in ND as [_ ND'].
            specialize (IH ND' l1 H1 A_IN' B_IN') as (s1 & s2 & s3 & ->).
            exists (h :: s1), s2, s3; reflexivity. }
      + apply NoDup_cons in ND as [_ ND']; exact (IH ND' _ H1 A_IN B_IN).
  Qed.

End SUBLIST.

Section LAST_SPLIT.

  Context {A : Type} `{EqDecision A}.

  (* A list containing [x] can be split at its *last* occurrence:
     [l = X ++ x :: Y] with [x ∉ Y].  By reverse induction. *)
  Lemma elem_of_last_split
    (x : A) (l : list A)
    (IN : x ∈ l)
  : ∃ X Y, l = X ++ x :: Y ∧ x ∉ Y.
  Proof.
    induction l as [| z l IHl] using rev_ind.
    { exfalso. exact (not_elem_of_nil _ IN). }
    destruct (decide (z = x)) as [-> | ZNE].
    - (* tail is [x]: split there with empty [Y]. *)
      exists l, []. split; [reflexivity | apply not_elem_of_nil].
    - (* tail [z ≠ x]: the occurrence is in [l]; recurse. *)
      apply elem_of_app in IN as [INl | INz].
      + destruct (IHl INl) as (X & Y & LEQ & NIN).
        exists X, (Y @@ z). split.
        * rewrite LEQ. rewrite app_comm_cons, app_assoc. reflexivity.
        * intros HIN. apply elem_of_app in HIN as [HY | HZ].
          -- exact (NIN HY).
          -- apply list_elem_of_singleton in HZ. exact (ZNE (eq_sym HZ)).
      + exfalso. apply list_elem_of_singleton in INz. exact (ZNE (eq_sym INz)).
  Qed.

End LAST_SPLIT.

(* Argument-explicit (as at the original proof sites). *)
Unset Implicit Arguments.
Section NODUP_FMAP.

  Context {A B : Type}.

  (* A sub-multiset of a list whose [f]-images are duplicate-free also has
     duplicate-free [f]-images. *)
  Lemma NoDup_fmap_submseteq
    (f : A → B) (l k : list A)
    (SUB : l ⊆+ k)
    (ND : NoDup (f <$> k))
  : NoDup (f <$> l).
  Proof.
    apply (fmap_submseteq f) in SUB.
    apply submseteq_Permutation in SUB as [r EQ].
    rewrite EQ in ND. apply NoDup_app in ND as (ND' & _ & _). exact ND'.
  Qed.

  (* If a list's [f]-images are duplicate-free, then so are those of any
     suffix [drop n]: [fmap] commutes with [drop] and a [drop] is a sublist. *)
  Lemma NoDup_fmap_drop
    (f : A → B) (n : nat) (l : list A)
    (ND : NoDup (f <$> l))
  : NoDup (f <$> drop n l).
  Proof.
    rewrite fmap_drop. eapply sublist_NoDup; [ exact ND | apply sublist_drop ].
  Qed.

End NODUP_FMAP.
Set Implicit Arguments.

Section MARKING.

  (* Pointwise order on boolean marking lists of equal length: [lhs] is below
     [rhs] when every position marked in [lhs] is also marked in [rhs].  Used
     by protocols that track "already handled" flags alongside a request list. *)
  Variant marking_le (lhs : list bool) (rhs : list bool) : Prop :=
    | marking_le_intro
      (LEN_EQ : length lhs = length rhs)
      (MARK_LE : forall i : nat, lhs !! i = Some true -> rhs !! i = Some true).

  #[global] Instance marking_le_Reflexive
    : Reflexive marking_le.
  Proof using.
    intros bs1; split; eauto.
  Qed.

  #[global] Instance marking_le_Transitive
    : Transitive marking_le.
  Proof using.
    intros bs1 bs2 bs3 [? ?] [? ?]; split; eauto. etransitivity; eauto.
  Qed.

  #[global] Instance marking_le_Antisymmetric
    : Antisymmetric _ eq marking_le.
  Proof using.
    intros bs1 bs2 [H1 H2] [H1' H2']. revert bs1 bs2 H1 H2 H1' H2'.
    induction bs1 as [ | b1 bs1 IH], bs2 as [ | b2 bs2]; simpl; intros; try congruence. f_equal.
    - destruct b1, b2; trivial;
      [now pose proof (H2 0 eq_refl) | now pose proof (H2' 0 eq_refl)].
    - eapply IH; eauto; intros i H_i; [exact (H2 (S i) H_i) | exact (H2' (S i) H_i)].
  Qed.

  Lemma marking_le_upd
    (bs : list bool) (i : nat)
  : marking_le bs (alter (const true) i bs).
  Proof using.
    split; [now rewrite length_alter |]. intros j H_j. destruct (Nat.eq_dec i j) as [-> | ?].
    - now rewrite list_lookup_alter_eq, H_j.
    - now rewrite list_lookup_alter_ne.
  Qed.

End MARKING.

Section REMOVE_DUPS.

  Context {A : Type} `{EqDecision A}.

  Lemma remove_dups_perm
    (l1 l2 : list A)
    (SSE1 : ∀ x, x ∈ l1 → x ∈ l2)
    (SSE2 : ∀ x, x ∈ l2 → x ∈ l1)
  : remove_dups l1 ≡ₚ remove_dups l2.
  Proof.
    apply submseteq_length_Permutation.
    - apply NoDup_submseteq.
      + apply NoDup_remove_dups.
      + setoid_rewrite elem_of_remove_dups; eassumption.
    - apply submseteq_length,NoDup_submseteq.
      + apply NoDup_remove_dups.
      + setoid_rewrite elem_of_remove_dups; eassumption.
  Qed.

  Lemma length_remove_dups_app_l
    (l1 l2 : list A)
  : length (remove_dups l2) <= length (remove_dups (l1 ++ l2)).
  Proof.
    induction l1; cbn.
    - reflexivity.
    - cases in goal; cbn.
      + assumption.
      + etransitivity; [eassumption | lia].
  Qed.

  Lemma remove_dups_app
    (l1 l2 : list A)
  : remove_dups (l1 ++ l2) =
    take (length (remove_dups (l1 ++ l2)) - length (remove_dups l2))
         (remove_dups (l1 ++ l2))
    ++ remove_dups l2.
  Proof.
    induction l1; cbn.
    - rewrite Nat.sub_diag,take_0; reflexivity.
    - cases in goal; cbn.
      + eassumption.
      + assert (∀ a b, b <= a → (S a) - b = S (a - b)) as -> by lia;
        [| apply length_remove_dups_app_l ].
        rewrite firstn_cons,<-app_comm_cons; f_equal; assumption.
  Qed.

End REMOVE_DUPS.

Section PERM.

  Lemma Permutation_elem_of
    {A : Type}
    (l l' : list A)
    (x : A)
    (PRM : l ≡ₚ l')
    (EO : x ∈ l)
  : x ∈ l'.
  Proof.
    rewrite list_elem_of_In in EO |- *.
    eapply Permutation_in; eassumption.
  Qed.

End PERM.

Section REVERSE.

  Lemma elem_of_reverse_1 : ∀
    {A : Type} (x : A) (l : list A),
    x ∈ reverse l →
    x ∈ l.
  Proof.
    intros; eapply elem_of_reverse; assumption.
  Qed.

End REVERSE.

Section LIST_FIND.

  Context {A : Type}.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma list_find_Some_lt : ∀ (l : list A) i x,
    list_find P l = Some (i, x) →
    i < length l.
  Proof.
    induction l; intros; cbn in *.
    - congruence.
    - cases * by simplify_eq.
      + lia.
      + destruct (list_find P l) as [[]|]; cbn in *; simplify_eq.
        specialize (IHl _ _ eq_refl); lia.
  Qed.

End LIST_FIND.

Section FMAP.

  Context {A B : Type}.

  Lemma list_fmap_do_undo
    (f : B → A) (g : A → B)
    (UNDO : ∀ x, f (g x) = x)
    (m : list A)
  : f <$> (g <$> m) = m.
  Proof.
    induction m; cbn; [| rewrite UNDO,IHm]; reflexivity.
  Qed.

End FMAP.

Section FOLDLUNTIL.

  Fixpoint foldluntil {A B : Type} (f : A → B → A * bool) (a : A) (l : list B) : A * bool :=
    match l with
    | x :: l' =>
      let '(a', cont) := f a x in
      if cont then foldluntil f a' l' else (a', cont)
    | [] => (a, true)
    end.

  Context {A B : Type}.

  Lemma foldluntil_fmap {C : Type} (f : A → B → A * bool) (g : C → B) (a : A) (l : list C)
  : foldluntil f a (g <$> l) = foldluntil (λ a c, f a (g c)) a l.
  Proof.
    revert a; induction l as [|x l' IH]; intros; [reflexivity | cbn].
    destruct (f a (g x)) as [a' cont]. destruct cont; [apply IH | reflexivity].
  Qed.

  Lemma foldluntil_app (f : A → B → A * bool) (a : A) (l k : list B)
  : foldluntil f a (l ++ k) =
    let '(a', cont) := foldluntil f a l in
    if cont then foldluntil f a' k else (a', false).
  Proof.
    revert a; induction l as [|x l' IH]; intros; cbn.
    - reflexivity.
    - destruct (f a x) as [a' cont]. destruct cont; cbn; [|reflexivity]. apply IH.
  Qed.

  Lemma foldluntil_snoc (f : A → B → A * bool) (a : A) (l : list B) (x : B)
  : foldluntil f a (l ++ [x]) =
    let '(a', cont) := foldluntil f a l in
    if cont then f a' x else (a', false).
  Proof.
    rewrite foldluntil_app.
    destruct (foldluntil f a l) as [a' cont]. destruct cont; [|reflexivity].
    cbn. destruct (f a' x) as [a'' c]. destruct c; reflexivity.
  Qed.

End FOLDLUNTIL.

Section IFOLDL.

  Fixpoint ifoldl {A B : Type} (f : A → nat → B → A) (a : A) (l : list B) : A :=
    match l with
    | [] => a
    | x :: l' => ifoldl (λ a i, f a (S i)) (f a 0 x) l'
    end.

  Context {A B : Type}.

  (* Step functions that agree on the elements of the list give the same fold. *)
  Lemma ifoldl_ext (f g : A → nat → B → A) (a : A) (l : list B)
    (EXT : ∀ a i x, l !! i = Some x → f a i x = g a i x)
  : ifoldl f a l = ifoldl g a l.
  Proof.
    revert f g a EXT; induction l as [|x l' IH]; intros f g a EXT; cbn; [reflexivity |].
    rewrite (EXT a 0 x eq_refl). apply IH. intros. by apply EXT.
  Qed.

  Lemma ifoldl_fmap {C : Type} (f : A → nat → B → A) (g : C → B) (a : A) (l : list C)
  : ifoldl f a (g <$> l) = ifoldl (λ a j c, f a j (g c)) a l.
  Proof. revert f a; induction l as [|x l' IH]; intros f a; [reflexivity | apply IH]. Qed.

  Lemma ifoldl_app (f : A → nat → B → A) (a : A) (l k : list B)
  : ifoldl f a (l ++ k) = ifoldl (λ a i, f a (length l + i)) (ifoldl f a l) k.
  Proof. revert f a; induction l as [|x l' IH]; intros f a; [reflexivity | apply IH]. Qed.

  Lemma ifoldl_snoc (f : A → nat → B → A) (a : A) (l : list B) (x : B)
  : ifoldl f a (l ++ [x]) = f (ifoldl f a l) (length l) x.
  Proof. rewrite ifoldl_app. cbn. by rewrite Nat.add_0_r. Qed.

End IFOLDL.

Section IFOLDR.

  Fixpoint ifoldr {A B : Type} (f : nat → B → A → A) (a : A) (l : list B) : A :=
    match l with
    | [] => a
    | x :: l' => f 0 x (ifoldr (λ i, f (S i)) a l')
    end.

  Context {A B : Type}.

  (* Step functions that agree on the elements of the list give the same fold. *)
  Lemma ifoldr_ext (f g : nat → B → A → A) (a : A) (l : list B)
    (EXT : ∀ i x a, l !! i = Some x → f i x a = g i x a)
  : ifoldr f a l = ifoldr g a l.
  Proof.
    revert f g EXT; induction l as [|x l' IH]; intros f g EXT; cbn; [reflexivity |].
    rewrite (EXT 0 x _ eq_refl). f_equal. apply IH. intros. by apply EXT.
  Qed.

  Lemma ifoldr_fmap {C : Type} (f : nat → B → A → A) (g : C → B) (a : A) (l : list C)
  : ifoldr f a (g <$> l) = ifoldr (λ j c, f j (g c)) a l.
  Proof. revert f; induction l as [|x l' IH]; intros f; cbn; [reflexivity | by rewrite IH]. Qed.

  Lemma ifoldr_app (f : nat → B → A → A) (a : A) (l k : list B)
  : ifoldr f a (l ++ k) = ifoldr f (ifoldr (λ i, f (length l + i)) a k) l.
  Proof. revert f; induction l as [|x l' IH]; intros f; cbn; [reflexivity | by rewrite IH]. Qed.

  Lemma ifoldr_snoc (f : nat → B → A → A) (a : A) (l : list B) (x : B)
  : ifoldr f a (l ++ [x]) = ifoldr f (f (length l) x a) l.
  Proof. rewrite ifoldr_app. cbn. by rewrite Nat.add_0_r. Qed.

End IFOLDR.

Section IFOLDLUNTIL.

  Fixpoint ifoldluntil {A B : Type} (f : A → nat → B → A * bool) (a : A) (l : list B) : A * bool :=
    match l with
    | x :: l' =>
      let '(a', cont) := f a 0 x in
      if cont then ifoldluntil (λ a i, f a (S i)) a' l' else (a', cont)
    | [] => (a, true)
    end.

  Context {A B : Type}.

  (* Step functions that agree on the elements of the list give the same fold. *)
  Lemma ifoldluntil_ext (f g : A → nat → B → A * bool) (a : A) (l : list B)
    (EXT : ∀ a i x, l !! i = Some x → f a i x = g a i x)
  : ifoldluntil f a l = ifoldluntil g a l.
  Proof.
    revert f g a EXT; induction l as [|x l' IH]; intros f g a EXT; cbn; [reflexivity |].
    rewrite (EXT a 0 x eq_refl). destruct (g a 0 x) as [a' []]; [| reflexivity].
    apply IH. intros. by apply EXT.
  Qed.

  Lemma ifoldluntil_fmap {C : Type} (f : A → nat → B → A * bool) (g : C → B)
      (a : A) (l : list C)
  : ifoldluntil f a (g <$> l) = ifoldluntil (λ a j c, f a j (g c)) a l.
  Proof.
    revert f a; induction l as [|x l' IH]; intros f a; cbn; [reflexivity |].
    destruct (f a 0 (g x)) as [a' []]; [apply IH | reflexivity].
  Qed.

  Lemma ifoldluntil_app (f : A → nat → B → A * bool) (a : A) (l k : list B)
  : ifoldluntil f a (l ++ k) =
    let '(a', cont) := ifoldluntil f a l in
    if cont then ifoldluntil (λ a i, f a (length l + i)) a' k else (a', false).
  Proof.
    revert f a; induction l as [|x l' IH]; intros f a; cbn; [reflexivity |].
    destruct (f a 0 x) as [a' []]; [apply IH | reflexivity].
  Qed.

  Lemma ifoldluntil_snoc (f : A → nat → B → A * bool) (a : A) (l : list B) (x : B)
  : ifoldluntil f a (l ++ [x]) =
    let '(a', cont) := ifoldluntil f a l in
    if cont then f a' (length l) x else (a', false).
  Proof.
    rewrite ifoldluntil_app. destruct (ifoldluntil f a l) as [a' []]; [| reflexivity].
    cbn. rewrite Nat.add_0_r. destruct (f a' (length l) x) as [a'' []]; reflexivity.
  Qed.

  (* For a "stationary" step function, which leaves the accumulator unchanged whenever it
     continues, the fold either continues past every element, or stops at the first element whose
     step stops. *)
  Lemma ifoldluntil_stationary (f : A → nat → B → A * bool)
    (STAT : ∀ a j x, (f a j x).2 = true → (f a j x).1 = a)
    (a : A) (l : list B)
  : match ifoldluntil f a l with
    | (a', true) => a' = a ∧ ∀ j x, l !! j = Some x → (f a j x).2 = true
    | (a', false) =>
      ∃ j x, l !! j = Some x ∧
        (∀ k y, k < j → l !! k = Some y → (f a k y).2 = true) ∧
        f a j x = (a', false)
    end.
  Proof.
    revert f STAT; induction l as [|x l IH]; intros f STAT; cbn; [split; [done | by intros ? ?] |].
    destruct (f a 0 x) as [a1 []] eqn:F.
    - assert (a1 = a) as -> by (pose proof (STAT a 0 x) as S; rewrite F in S; by apply S).
      specialize (IH (λ a i, f a (S i)) (λ a j x, STAT a (S j) x)).
      destruct (ifoldluntil _ a l) as [a' []].
      + destruct IH as [-> IH]. split; [done |].
        intros [|j] y LU; cbn in LU; [simplify_eq; by rewrite F |]. by apply IH.
      + destruct IH as (j & y & LU & PRE & FJ). exists (S j), y. split_and!; [done | | done].
        intros [|k] z LT LUk; cbn in LUk; [simplify_eq; by rewrite F |]. apply PRE; [lia | done].
    - exists 0, x. split_and!; [done | intros; lia | done].
  Qed.

End IFOLDLUNTIL.

Section IFOLDRUNTIL.

  Fixpoint ifoldruntil {A B : Type} (f : nat → B → A → A * bool) (a : A) (l : list B) : A * bool :=
    match l with
    | [] => (a, true)
    | x :: l' =>
      match ifoldruntil (λ i, f (S i)) a l' with
      | (a', true) => f 0 x a'
      | (a', false) => (a', false)
      end
    end.

  Context {A B : Type}.

  (* Step functions that agree on the elements of the list give the same fold. *)
  Lemma ifoldruntil_ext (f g : nat → B → A → A * bool) (a : A) (l : list B)
    (EXT : ∀ i x a, l !! i = Some x → f i x a = g i x a)
  : ifoldruntil f a l = ifoldruntil g a l.
  Proof.
    revert f g EXT; induction l as [|x l' IH]; intros f g EXT; cbn; [reflexivity |].
    rewrite (IH _ (λ i, g (S i))) by (intros; by apply EXT).
    destruct (ifoldruntil _ a l') as [a' []]; [by apply EXT | reflexivity].
  Qed.

  Lemma ifoldruntil_fmap {C : Type} (f : nat → B → A → A * bool) (g : C → B)
      (a : A) (l : list C)
  : ifoldruntil f a (g <$> l) = ifoldruntil (λ j c, f j (g c)) a l.
  Proof. revert f; induction l as [|x l' IH]; intros f; cbn; [reflexivity | by rewrite IH]. Qed.

  Lemma ifoldruntil_app (f : nat → B → A → A * bool) (a : A) (l k : list B)
  : ifoldruntil f a (l ++ k) =
    let '(a', cont) := ifoldruntil (λ i, f (length l + i)) a k in
    if cont then ifoldruntil f a' l else (a', false).
  Proof.
    revert f; induction l as [|x l' IH]; intros f; cbn.
    - by destruct (ifoldruntil f a k) as [? []].
    - rewrite IH. by destruct (ifoldruntil _ a k) as [? []].
  Qed.

  Lemma ifoldruntil_snoc (f : nat → B → A → A * bool) (a : A) (l : list B) (x : B)
  : ifoldruntil f a (l ++ [x]) =
    let '(a', cont) := f (length l) x a in
    if cont then ifoldruntil f a' l else (a', false).
  Proof. rewrite ifoldruntil_app. cbn. by rewrite Nat.add_0_r. Qed.

  (* For a "stationary" step function, which leaves the accumulator unchanged whenever it
     continues, the fold either continues past every element, or stops at the last element whose
     step stops (the fold runs from the end of the list). *)
  Lemma ifoldruntil_stationary (f : nat → B → A → A * bool)
    (STAT : ∀ j x a, (f j x a).2 = true → (f j x a).1 = a)
    (a : A) (l : list B)
  : match ifoldruntil f a l with
    | (a', true) => a' = a ∧ ∀ j x, l !! j = Some x → (f j x a).2 = true
    | (a', false) =>
      ∃ j x, l !! j = Some x ∧
        (∀ k y, j < k → l !! k = Some y → (f k y a).2 = true) ∧
        f j x a = (a', false)
    end.
  Proof.
    revert f STAT; induction l as [|x l IH]; intros f STAT; cbn; [split; [done | by intros ? ?] |].
    specialize (IH (λ i, f (S i)) (λ j x a, STAT (S j) x a)).
    destruct (ifoldruntil _ a l) as [a' []].
    - destruct IH as [-> IH]. destruct (f 0 x a) as [a1 []] eqn:F.
      + assert (a1 = a) as -> by (pose proof (STAT 0 x a) as S; rewrite F in S; by apply S).
        split; [done |]. intros [|j] y LU; cbn in LU; [simplify_eq; by rewrite F | by apply IH].
      + exists 0, x. split_and!; [done | | done].
        intros [|k] z LT LUk; cbn in LUk; [lia | by apply IH].
    - destruct IH as (j & y & LU & PRE & FJ). exists (S j), y. split_and!; [done | | done].
      intros [|k] z LT LUk; cbn in LUk; [lia |]. apply PRE; [lia | done].
  Qed.

End IFOLDRUNTIL.

Section IFOLDLFROMUNTIL.

  Definition ifoldlfromuntil {A B : Type} (f : A → nat → B → A * bool) (n : nat) (a : A) (l : list B)
  : A * bool := ifoldluntil (λ a i, f a (n + i)) a (drop n l).

  Context {A B : Type}.

  Lemma ifoldlfromuntil_eq (f : A → nat → B → A * bool) (n : nat) (a : A) (l : list B)
  : ifoldlfromuntil f n a l = ifoldluntil (λ a i, f a (n + i)) a (drop n l).
  Proof. reflexivity. Qed.

  Lemma ifoldlfromuntil_0 (f : A → nat → B → A * bool) (a : A) (l : list B)
  : ifoldlfromuntil f 0 a l = ifoldluntil f a l.
  Proof. reflexivity. Qed.

  (* Starting past the end of the list, the fold does nothing. *)
  Lemma ifoldlfromuntil_ge (f : A → nat → B → A * bool) (n : nat) (a : A) (l : list B)
    (LE : length l ≤ n)
  : ifoldlfromuntil f n a l = (a, true).
  Proof. unfold ifoldlfromuntil. by rewrite drop_ge. Qed.

  (* Unfold one step of the fold, at the element at the starting index. *)
  Lemma ifoldlfromuntil_lookup (f : A → nat → B → A * bool) (n : nat) (a : A) (l : list B) (x : B)
    (LU : l !! n = Some x)
  : ifoldlfromuntil f n a l =
    let '(a', cont) := f a n x in if cont then ifoldlfromuntil f (S n) a' l else (a', false).
  Proof.
    unfold ifoldlfromuntil. rewrite (drop_S _ _ _ LU). cbn. rewrite Nat.add_0_r.
    destruct (f a n x) as [? []]; [| reflexivity].
    apply ifoldluntil_ext. intros. by rewrite Nat.add_succ_r.
  Qed.

  (* [ifoldluntil_stationary] stated with indices into the whole list. *)
  Lemma ifoldlfromuntil_stationary (f : A → nat → B → A * bool)
    (STAT : ∀ a j x, (f a j x).2 = true → (f a j x).1 = a)
    (n : nat) (a : A) (l : list B)
  : match ifoldlfromuntil f n a l with
    | (a', true) => a' = a ∧ ∀ j x, n ≤ j → l !! j = Some x → (f a j x).2 = true
    | (a', false) =>
      ∃ j x, n ≤ j ∧ l !! j = Some x ∧
        (∀ k y, n ≤ k → k < j → l !! k = Some y → (f a k y).2 = true) ∧
        f a j x = (a', false)
    end.
  Proof.
    pose proof (ifoldluntil_stationary _ (λ a j x, STAT a (n + j) x) a (drop n l)) as SPEC.
    unfold ifoldlfromuntil. destruct (ifoldluntil _ a (drop n l)) as [a' []].
    - destruct SPEC as [-> ALL]. split; [done |]. intros j x LE LU.
      replace j with (n + (j - n)) by lia. apply ALL. rewrite lookup_drop.
      by replace (n + (j - n)) with j by lia.
    - destruct SPEC as (j & x & LU & PRE & F). rewrite lookup_drop in LU.
      exists (n + j), x. split_and!; [lia | done | | done].
      intros k y LE LT LUk. replace k with (n + (k - n)) by lia. apply PRE; [lia |].
      rewrite lookup_drop. by replace (n + (k - n)) with k by lia.
  Qed.

End IFOLDLFROMUNTIL.

Section OMAPFOLDL.

  Definition omapfoldl
    {A B L : Type}
    (f : L → option A) (g : B → A → B) (b : B) (lbs : list L)
  : B := foldl g b (omap (M:=list) f lbs).

  Lemma omapfoldl_snoc
    {A B L : Type}
    (f : L → option A) (g : B → A → B) (b : B) (l : list L) x
  : omapfoldl f g b (l @@ x) =
    match f x with
    | Some a => g (omapfoldl f g b l) a
    | None => omapfoldl f g b l
    end.
  Proof.
    unfold omapfoldl. rewrite !omap_app,!foldl_app; cbn.
    cases in goal; reflexivity.
  Qed.

  Lemma omapfoldl_app
    {A B L : Type}
    (f : L → option A) (g : B → A → B) (b : B) (l1 l2 : list L)
  : omapfoldl f g b (l1 ++ l2) = omapfoldl f g (omapfoldl f g b l1) l2.
  Proof.
    unfold omapfoldl. rewrite !omap_app,!foldl_app; reflexivity.
  Qed.

  Lemma omapfoldl_union_snoc
    `{SemiSet A C,!LeibnizEquiv C} {L : Type}
    (f : L -> option C) b (l : list L) x
  : omapfoldl f union b (l @@ x) = omapfoldl f union b l ∪ default ∅ (f x).
  Proof.
    rewrite omapfoldl_snoc; cases in goal;
    unfold omapfoldl; cbn; [| rewrite ?union_empty_r_L]; reflexivity.
  Qed.

End OMAPFOLDL.
