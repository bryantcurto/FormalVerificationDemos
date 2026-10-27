Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Export
     Prelude.

From stdpp Require Export
     sorting.

Section INSERT_RIGHTMOST.

  Context {A : Type}.
  Context (R : relation A) `{Transitive _ R,RelDecision _ _ R}.

  Fixpoint insertRMost (a : A) (l : list A) : list A :=
    match l with
    | [] => [a]
    | x :: l' =>
      if decide (R a x)
      then a :: x :: l'
      else x :: insertRMost a l'
    end.

  Fixpoint sortRMost (l: list A) : list A :=
    match l with
    | [] => []
    | x :: l' => insertRMost x (sortRMost l')
    end.

  Lemma insertRMost_perm l a
  : insertRMost a l ≡ₚ a :: l.
  Proof.
    induction l as [| x l].
    - reflexivity.
    - simpl; destruct (decide _).
      + reflexivity.
      + rewrite IHl; constructor.
  Qed.

  Lemma insertRMost_spec (a : A) (l : list A)
  : ∃ l1 l2,
      l = l1 ++ l2 ∧
      insertRMost a l = l1 ++ a :: l2 ∧
      (∀ x, x ∈ l1 → ¬ R a x) ∧
      match head l2 with
      | Some x => R a x
      | None => True
      end.
  Proof.
    induction l as [| x l]; cbn.
    - exists [], []; repeat split; set_solver.
    - destruct IHl as (l1 & l2 & -> & IH1 & IH2 & IH3). destruct (decide _).
      + eexists [], (x :: l1 ++ l2).
        repeat split; set_solver.
      + eq_norm. exists (x :: l1), l2.
        repeat split; [| assumption].
        intros ? EO. apply elem_of_cons in EO as [->|EO]; [assumption | eauto].
  Qed.

  Lemma sortRMost_perm l
  : sortRMost l ≡ₚ l.
  Proof.
    induction l.
    - reflexivity.
    - simpl; rewrite insertRMost_perm. constructor; assumption.
  Qed.

End INSERT_RIGHTMOST.

Arguments insertRMost {_} (_) {_} (_ _).
Arguments sortRMost {_} (_) {_} (_).

Definition AntiSymmLocally `{ElemOf A C} (R S : relation A) (c : C) : Prop :=
  ∀ x y
    (EOx : x ∈ c)
    (EOy : y ∈ c)
    (Sxy : S x y)
    (Syx : S y x),
    R x y.

Lemma anti_symm_local_sse
  `{ElemOf A C}
  {S : relation A}
  (c c' : C)
  `(ASL : !AntiSymmLocally R S c')
  (SSE : c ⊆ c')
: AntiSymmLocally R S c.
Proof. intros ? **. eapply ASL; eassumption || set_solver. Qed.

Section SORTED_PARTIAL.

  Context {A : Type}.
  Context (R : relation A) `{Transitive _ R,RelDecision _ _ R}.
  Context (E : relation A) `{Equivalence _ E}.
  Context `{Proper _ (E ==> E ==> iff)%signature R}.

  (* NOTE: `E a b` is necessary in case `R` is reflexive. In such a case and without it, partially
     sorted lists could not contain duplicate elements. *)
  Definition SortedPartial : list A -> Prop :=
    StronglySorted (λ a b, E a b ∨ ¬ R b a).

  Lemma SortedPartial_cons a l
  : SortedPartial (a :: l) <->
    Forall (λ b, E a b ∨ ¬ R b a) l ∧ SortedPartial l.
  Proof.
    split; [intros HH | intros []].
    - inversion HH; subst. split; eassumption.
    - econstructor; eassumption.
  Qed.

  Lemma SortedPartial_cons_1 a l
    (SP : SortedPartial (a :: l))
  : Forall (λ b, E a b ∨ ¬ R b a) l ∧ SortedPartial l.
  Proof. eapply SortedPartial_cons; eassumption. Qed.

  Lemma SortedPartial_cons_2 a l
    (FA : Forall (λ b, E a b ∨ ¬ R b a) l)
    (SP : SortedPartial l)
  : SortedPartial (a :: l).
  Proof. eapply SortedPartial_cons; split; eassumption. Qed.

  Lemma SortedPartial_inv_app_r
    `(SP : SortedPartial (l1 ++ l2))
  : SortedPartial l2.
  Proof.
    revert SP; induction l1 as [| a l1]; intro SP; [exact SP |].
    rewrite <-app_comm_cons in SP. apply IHl1. exact (proj2 (SortedPartial_cons_1 SP)).
  Qed.

  Lemma SortedPartial_inv_remove_middle
    `(SP : SortedPartial (l1 ++ op :: l2))
  : SortedPartial (l1 ++ l2).
  Proof.
    revert SP; induction l1 as [| a l1]; intro SP; cbn in *.
    - exact (proj2 (SortedPartial_cons_1 SP)).
    - apply SortedPartial_cons_1 in SP as [FA SP'].
      apply SortedPartial_cons_2.
      + eapply Forall_sse; [exact FA |]; intros y Hy; set_solver.
      + exact (IHl1 SP').
  Qed.

  Lemma SortedPartial_filter
    (P : A → Prop) `{∀ x, Decision (P x)}
    `(SP : SortedPartial l)
  : SortedPartial (filter P l).
  Proof.
    induction l as [| x l]; cbn; [exact SP |].
    apply SortedPartial_cons_1 in SP as [FA SPl].
    destruct (decide (P x)); cbn.
    - apply SortedPartial_cons_2.
      + eapply Forall_sse; [exact FA |].
        intros y Hy; exact (sublist_elem_of (sublist_filter P l) Hy).
      + exact (IHl SPl).
    - exact (IHl SPl).
  Qed.

  Lemma SortedPartial_app_sorted
    (l1 l2 : list A)
    (SP1 : SortedPartial l1)
    (SP2 : SortedPartial l2)
    (ORD : ∀ `(EO1 : a ∈ l1) `(EO2 : b ∈ l2), E a b ∨ ¬ R b a)
  : SortedPartial (l1 ++ l2).
  Proof.
    revert ORD SP2; induction l1; cbn; intros.
    - assumption.
    - eapply SortedPartial_cons in SP1 as [SPa1 SP1].
      eapply SortedPartial_cons; split.
      + apply Forall_app; split.
        * assumption.
        * apply Forall_forall.
          intros; eapply ORD; eauto || set_solver.
      + eapply IHl1; eauto.
        intros; eapply ORD; eauto || set_solver.
  Qed.

  (* For partial ordering relations R, inserting a requires (1) finding the first element x s.t. a
     is "less than" x and (2) inserting a before x -- i.e., rightmost insertion. This is instead
     of inserting before the first element w s.t. w is not "less than" a -- i.e., leftmost
     insertion. Consider, a, b, and c s.t. c ≺ a and the remaining pairs are unordered; inserting
     a into [b; c] produces list [b; c; a] by the first approach -- maintaining the ordering --
     and [a; b; c] by the second -- violating the ordering. *)
  Lemma insertRMost_SortedPartial_strong l a
    (ASl : AntiSymmLocally E R l)
    (ASa : ∀ `(EO : y ∈ l) (R1 : R a y) (R2 : R y a), E a y)
    (SP : SortedPartial l)
  : SortedPartial (insertRMost R a l).
  Proof.
    revert a ASl ASa; induction l as [| x l IHl]; intros.
    - repeat constructor.
    - eapply SortedPartial_cons in SP as HH; destruct HH as (FA & SPl).
      simpl; destruct (decide _).
      + (* R a x *)
        eapply SortedPartial_cons_2; try eassumption.
        rewrite Forall_forall in *; intros x' EOx'.
        eapply elem_of_cons in EOx' as [| EOx']; try subst x';
        [| eapply FA in EOx' as HH; destruct HH as [Exx' | Rx'x] ].
        1,2: [>
          destruct (decide (R x a)); try rewrite <-Exx' in *;
          [ left; eapply ASa; eassumption || set_solver
          | right; eassumption ] ..].
        right; intros C.
        eapply Rx'x. etransitivity; eassumption.
      + (* ~ R a x *)
        eapply SortedPartial_cons; split.
        * rewrite insertRMost_perm. constructor;
          [ right |]; eassumption.
        * eapply IHl; try eassumption.
          { eapply anti_symm_local_sse; set_solver. }
          { intros; eapply ASa; eassumption || set_solver. }
  Qed.

  Lemma insertRMost_SortedPartial l a
    `{AS : AntiSymm _ E R}
    (SP : SortedPartial l)
  : SortedPartial (insertRMost R a l).
  Proof.
    eapply insertRMost_SortedPartial_strong; try eassumption;
    intros ? **; eapply AS; eassumption.
  Qed.

  Lemma sortRMost_sorted_strong l
    (ASl : AntiSymmLocally E R l)
  : SortedPartial (sortRMost R l).
  Proof.
    induction l.
    - constructor.
    - pose proof (anti_symm_local_sse ASl (c:=l) ltac:(set_solver)) as HH.
      specialize (IHl HH).
      cbn; eapply insertRMost_SortedPartial_strong.
      + eapply (anti_symm_local_sse (c':=l)); try eassumption.
        (* TODO : figure out why we cannot just use rewrite *)
        pose proof (sortRMost_perm (R:=R) l).
        eapply list_subseteq_Permutation; eassumption || reflexivity.
      + intros. rewrite (sortRMost_perm l) in EO. eapply ASl; try set_solver.
      + eassumption.
  Qed.

  Lemma sortRMost_sorted l
    `{AS : AntiSymm _ E R}
  : SortedPartial (sortRMost R l).
  Proof.
    eapply sortRMost_sorted_strong.
    intros ? **; eapply AS; eassumption.
  Qed.

  Lemma sortRMost_app_sorted
    `{AS : AntiSymm _ E R}
    (l1 l2 : list A)
    (ORD : ∀ `(EO1 : a ∈ l1) `(EO2 : b ∈ l2), E a b ∨ ¬ R b a)
  : SortedPartial (sortRMost R l1 ++ sortRMost R l2).
  Proof.
    eapply SortedPartial_app_sorted; try typeclasses eauto.
    - eapply sortRMost_sorted; typeclasses eauto.
    - eapply sortRMost_sorted; typeclasses eauto.
    - intros; rewrite !(sortRMost_perm _) in *. eapply ORD; assumption.
  Qed.

End SORTED_PARTIAL.

Section EQUIV_DUP.

  Context {A : Type} (E : relation A).

  Definition NoEquivDup `{!Equivalence E} : list A -> Prop := StronglySorted (λ x y, ¬ E x y).

  Context `{!Equivalence E}.

  Lemma NoEquivDup_perm
    `(DUP : NoEquivDup l1)
    `(PERM : l1 ≡ₚ l2)
  : NoEquivDup l2.
  Proof.
    induction PERM.
    - eassumption.
    - inv DUP as [| ? ? SS FA].
      specialize (IHPERM SS). rewrite PERM in FA.
      constructor; assumption.
    - inv DUP as [| ? ? SS FA]; inv SS; inv FA.
      do 2 constructor; try eassumption.
      intros C; symmetry in C; revert C; assumption.
    - apply IHPERM2, IHPERM1, DUP.
  Qed.

  Lemma NoEquivDup_NoDup_strong'
    `(INJ : ∀ (x y : A), ¬ E x y → ¬ x = y)
    `(NED : NoEquivDup l)
  : NoDup l.
  Proof.
    induction l; constructor; inv NED as [|? ? NED' FA]; rewrite Forall_forall in FA.
    - intros EO. specialize (FA _ EO). apply INJ in FA. congruence.
    - exact (IHl NED').
  Qed.

  Lemma NoEquivDup_unique
    `(NED : NoEquivDup l)
  : ∀ x y, x ∈ l → y ∈ l → E x y → x = y.
  Proof.
    induction NED as [| a l SSl IH FA]; intros x y EOx EOy EQ.
    - inversion EOx.
    - apply elem_of_cons in EOx as [-> | EOx];
      apply elem_of_cons in EOy as [-> | EOy].
      + reflexivity.
      + exfalso; rewrite Forall_forall in FA; eapply (FA y EOy EQ).
      + exfalso; rewrite Forall_forall in FA; eapply (FA x EOx); symmetry; exact EQ.
      + eapply IH; eassumption.
  Qed.

End EQUIV_DUP.

Arguments NoEquivDup {_} (_) {_} (_).

Section STRONGLY_SORTED.

  Lemma StronglySorted_lookup_lt {A : Type} {R : relation A} {l : list A}
    `(SS : StronglySorted R l)
    `(LT : i < j)
    `(Hi : l !! i = Some x)
    `(Hj : l !! j = Some y)
  : R x y.
  Proof.
    apply (StronglySorted_app_1_elem_of R (take j l) (y :: drop (S j) l) x y).
    - rewrite (take_drop_middle l j y Hj). exact SS.
    - apply (list_elem_of_lookup_2 (take j l) i x). rewrite lookup_take_lt by lia. exact Hi.
    - apply list_elem_of_here.
  Qed.

  Unset Implicit Arguments.

  (* From a [StronglySorted] list split at an element, every element AFTER the
     split point is related (by [R]) to it. *)
  Lemma StronglySorted_mid_Forall {A} (R : A → A → Prop)
    (l1 : list A) (x : A) (l2 : list A)
    (SS : StronglySorted R (l1 ++ x :: l2))
  : Forall (R x) l2.
  Proof.
    induction l1 as [| a l1 IH]; cbn in SS.
    - apply StronglySorted_inv in SS as [_ F]. exact F.
    - apply StronglySorted_inv in SS as [SS' _]. exact (IH SS').
  Qed.

  Set Implicit Arguments.

End STRONGLY_SORTED.
