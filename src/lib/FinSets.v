Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Import
     Base Tactics Logic Lists.

From stdpp Require Import
     fin_sets.

Section SET_LEMMAS.

  Lemma elem_of_union_shortcircuit
    {A C : Type}
    `{FinSet A C}
    {s1 s2 : C}
    {e : A}
    (E : e ∈ s1 ∪ s2)
  : e ∈ s1 \/ e ∈ s2 ∖ s1.
  Proof.
    rewrite elem_of_difference,Logic.and_comm; apply disj_shortcircuit;
    [ apply elem_of_dec_slow | apply elem_of_union; assumption ].
  Qed.

  (* TODO : make this more general *)
  Lemma gset_elements_inj {A : Type} `{Countable A}
    (a b : gset A)
    (AN : elements a = elements b)
  : a = b.
  Proof.
    eapply set_eq. intros. split; intro EO; apply elem_of_elements in EO;
    [rewrite -> AN in EO | rewrite <- AN in EO]; apply elem_of_elements in EO; assumption.
  Qed.

  Lemma union_empty_l_L
    `{SemiSet A C,!LeibnizEquiv C}
    (X : C)
  : ∅ ∪ X = X.
  Proof.
    eapply subseteq_union_1_L; set_solver.
  Qed.

  Lemma union_empty_r_L
    `{SemiSet A C,!LeibnizEquiv C}
    (X : C)
  : X ∪ ∅ = X.
  Proof.
    rewrite union_comm_L; eapply union_empty_l_L.
  Qed.

  Lemma set_Forall_sse
    `{SemiSet A C}
    (X1 : C)
    `(FA : set_Forall P X1)
    `(SSE : X2 ⊆ X1)
  : set_Forall P X2.
  Proof.
    intros ? EO; apply FA, SSE, EO.
  Qed.

  Lemma set_Exists_sse
    `{SemiSet A C}
    (X1 : C)
    `(EX : set_Exists P X1)
    `(SSE : X1 ⊆ X2)
  : set_Exists P X2.
  Proof.
    destruct EX as (?&?&?).
    eexists; split; [apply SSE |]; eassumption.
  Qed.

  Lemma foldl_union_sse
    `{SemiSet A C}
    a b (l : list C)
    (SSE : b ⊆ a)
  : b ⊆ foldl union a l.
  Proof.
    revert a SSE; induction l; intros; cbn.
    - eassumption.
    - eapply IHl. set_solver.
  Qed.

  Lemma set_map_sse
    `{FinSet A C,!LeibnizEquiv C,FinSet B D,!LeibnizEquiv D}
    `(SSE : s1 ⊆ s2) (f : A → B)
  : set_map (C:=C)(D:=D) f s1 ⊆ set_map f s2.
  Proof.
    revert s2 SSE; induction s1 using set_ind_L; intros.
    - rewrite set_map_empty. set_solver.
    - apply union_subseteq in SSE as [EO SSE].
      rewrite set_map_union_L. apply union_subseteq; split;
      [rewrite set_map_singleton_L; apply singleton_subseteq_l in EO; apply singleton_subseteq_l;
       apply elem_of_map_2 |]; eauto.
  Qed.

  Lemma list_to_set_sse
    `{SemiSet A C}
    `(SSE : l1 ⊆ l2)
  : list_to_set (C:=C) l1 ⊆ list_to_set l2.
  Proof.
    revert l2 SSE; induction l1; intros; cbn; [ set_solver |].
    apply list_subseteq_cons_iff in SSE as [EO SSE].
    apply union_subseteq; split; [set_solver | eauto].
  Qed.

End SET_LEMMAS.

Section OMAPFOLDL.

  Lemma omapfoldl_union_app
    `{SemiSet A C,!LeibnizEquiv C} {L : Type}
    (f : L -> option C) b (l1 l2 : list L)
  : omapfoldl f union b (l1 ++ l2) = omapfoldl f union b l1 ∪ (omapfoldl f union b l2).
  Proof.
    induction l2 using rev_ind; cbn.
    - unfold omapfoldl.
      pose proof (foldl_union_sse (b:=b) (omap f l1) ltac:(reflexivity)).
      rewrite app_nil_r. set_solver.
    - rewrite app_assoc,!omapfoldl_union_snoc,IHl2,union_assoc_L.
      reflexivity.
  Qed.

  Lemma omapfoldl_union_lookup
    `{SemiSet A C} {L : Type}
    {f : L -> option C} b (l : list L) x
    `(LU : l !! i = Some x)
    `(F_SOME : f x = Some c)
  : c ⊆ omapfoldl f union b l.
  Proof.
    revert i x LU c F_SOME b; induction l as [| x' l]; intros.
    - naive_solver.
    - apply lookup_cons_Some in LU as [(? & ?)| (? & LU)]; subst.
      + unfold omapfoldl; repeat (cbn; eq_norm).
        eapply foldl_union_sse; set_solver.
      + cbn; cases in goal; eapply IHl; try eassumption.
  Qed.

End OMAPFOLDL.
