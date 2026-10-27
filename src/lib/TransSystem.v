
From refinement.lib Require Export
     Prelude.

From Stdlib Require Import
     Prelude
     Relations.Relation_Operators.

Class TSCom (A : Type) : Type := mkTSCom {
  init : A -> Prop;
}.

Arguments mkTSCom {_} _.

Class TSParams (A : Type) : Type := mkTSParams {
  tscom :: TSCom A;
  step : relation A;
}.

Arguments mkTSParams {_} _ _.

Section TRANS_SYS.

  Context `{A : Type,TSParams A}.

  Definition stepStar := clos_refl_trans _ step.
  Definition stepPlus := clos_trans _ step.

  #[global] Instance stepStar_Transitive : Transitive stepStar.
  Proof. red; unfold stepStar; intros. eapply rt_trans; eassumption. Qed.

  #[global] Instance stepPlus_Transitive : Transitive stepPlus.
  Proof. red; unfold stepPlus; intros. eapply t_trans; eassumption. Qed.

End TRANS_SYS.

Infix "~>" := step (at level 70).
Infix "~>*" := stepStar (at level 70).
Infix "~>+" := stepPlus (at level 70).
Arguments step _ _ _ _ : simpl never.
Arguments stepStar _ _ _ _ : simpl never.
Arguments stepPlus _ _ _ _ : simpl never.

Lemma stepStar_ind
  `(A : Type, TSParams A)
  (x : A)
  (P : A -> Prop)
  (B : P x)
  (I : forall y z (STP : step y z) (STPS : stepStar x y) (IH : P y), P z)
: forall a (STPS : stepStar x a), P a.
Proof.
  intros ? HH. apply Operators_Properties.clos_rt_rtn1_iff in HH; induction HH;
  [| eapply I; try apply Operators_Properties.clos_rt_rtn1_iff]; eassumption.
Qed.

Lemma stepPlus_ind
  `(A : Type, TSParams A)
  (x : A)
  (P : A -> Prop)
  (B : forall y (STPP : stepPlus x y), P y)
  (I : forall y z (STP : step y z) (STPP : stepPlus x y) (IH : P y), P z)
: forall a (STPP : stepPlus x a), P a.
Proof.
  intros ? HH. apply Operators_Properties.clos_trans_tn1_iff in HH; induction HH;
  [apply B; constructor | eapply I; try apply Operators_Properties.clos_trans_tn1_iff];
  eassumption.
Qed.

Section TRANS_SYS.

  Context `{A : Type,TSParams A}.

  Variant reachable : A -> Prop :=
  | reachableCstr
      si st
      (SI : init si)
      (ST : si ~>* st)
    : reachable st.

  Lemma init_reachable
    st
    (I : init st)
  : reachable st.
  Proof.
    eexists; [eassumption | apply rt_refl].
  Qed.

  Lemma step_reachable
    st st'
    (RCH : reachable st)
    (STP : step st st')
  : reachable st'.
  Proof.
    inversion RCH; subst. econstructor; try eassumption.
    etransitivity; [| constructor]; eassumption.
  Qed.

End TRANS_SYS.

Lemma reach_ind
  `(A : Type, TSParams A)
  (P : A -> Prop)
  (B : forall si (INIT : init si), P si)
  (I : forall st st' (RCH : reachable st) (STEP : step st st') (IH : P st) , P st')
: forall st (RCH : reachable st), P st.
Proof.
  intros. inversion RCH; subst.
  induction ST as [| st st' ST STS IH] using stepStar_ind.
  - apply B; assumption.
  - rename RCH into RCH'. assert (reachable st) as RCH by (econstructor;eassumption).
    specialize (IH RCH). eapply I; try eassumption.
Qed.

Class LTSParams (A B : Type) : Type := mkLTSParams {
  ltscom :: TSCom A;
  lstep : A -> B -> A -> Prop;
}.

Arguments mkLTSParams {_} {_} _ _.

Section LABEL_TRANS_SYS.

  Context `{LTSParams T L}.

  Inductive lstepStar (st : T) : list L -> T -> Prop :=
  | lstpStarNil
    : lstepStar st [] st
  | lstpStarCons
      lb st2 lbs st3
      (STP : lstep st lb st2)
      (STPS : lstepStar st2 lbs st3)
    : lstepStar st (lb :: lbs) st3.

End LABEL_TRANS_SYS.

Notation "a ~[ lbl ]~> b" := (lstep a lbl b) (at level 70).
Notation "a ~[ l ]~>* b" := (lstepStar a l b) (at level 70).
Arguments lstep _ _ _ _ _ _ : simpl never.

Definition LTSParams2TSParams {A B : Type} (lts : LTSParams A B) : TSParams A :=
  let step := λ st st', exists l, lstep st l st' in
  mkTSParams ltscom step.

(* TODO : What is the effective difference between Coercion and Instance? *)
Coercion LTSParams2TSParams : LTSParams >-> TSParams.

#[global] Instance LTSParams_TSParams {A B : Type} {lts : LTSParams A B} : TSParams A :=
  lts.

Section LABEL_TRANS_SYS.

  Context `{LTSParams T L}.

  Variant lreachable : list L -> T -> Prop :=
  | lreachableCstr
      si l st
      (SI : init si)
      (ST : si ~[ l ]~>* st)
    : lreachable l st.

  Lemma init_lreachable
    st
    (I : init st)
  : lreachable [] st.
  Proof.
    eexists; [eassumption | constructor].
  Qed.

End LABEL_TRANS_SYS.

Class DLTS (A B : Type) `{LTSParams A B} : Prop := {
  deterministic_step :
    forall st lb st1 st2
      (STP1 : st ~[ lb ]~> st1)
      (STP2 : st ~[ lb ]~> st2),
      st1 = st2;
}.

Section LTS_LEMMAS.

  Context `{LTSP : LTSParams T L}.

  Lemma lstepStar_cons
    st1 st2 lbs lb
  : st1 ~[ lb :: lbs ]~>* st2 <->
    exists st',
      st1 ~[ lb ]~> st' /\
      st' ~[ lbs ]~>* st2.
  Proof.
    split; intros HH.
    - inversion HH; subst. eexists; split; eassumption.
    - destruct HH as (? & ? & ?). econstructor; eassumption.
  Qed.

  Lemma lstepStar_cons_1
    `(STP : st1 ~[ lb ]~> st2)
    `(STPS : st2 ~[ lbs ]~>* st3)
  : st1 ~[ lb :: lbs ]~>* st3.
  Proof.
    eapply lstepStar_cons. eexists; split; eassumption.
  Qed.

  Lemma lstepStar_app
    st1 st2 lbs1 lbs2
  : st1 ~[ lbs1 ++ lbs2 ]~>* st2 <->
    exists st',
      st1 ~[ lbs1 ]~>* st' /\
      st' ~[ lbs2 ]~>* st2.
  Proof.
    revert st1 st2 lbs2. induction lbs1; intros.
    - split; intros HH.
      + eexists; split; econstructor || eassumption.
      + destruct HH as (? & HH & ?); inversion HH; subst; eassumption.
    - split; intros HH; rewrite <- app_comm_cons in *.
      + inversion HH; subst. apply IHlbs1 in STPS as (? & ? & ?).
        eexists; split; try econstructor; eassumption.
      + destruct HH as (? & HH & ?). inversion HH; subst.
        econstructor; try (eapply IHlbs1; eexists; split); eassumption.
  Qed.

  Lemma lstepStar_app_1
    `(STPS1 : st1 ~[ lbs1 ]~>* st2)
    `(STPS2 : st2 ~[ lbs2 ]~>* st3)
  : st1 ~[ lbs1 ++ lbs2 ]~>* st3.
  Proof.
    eapply lstepStar_app. eexists; split; eassumption.
  Qed.

  Lemma lstepStar_snoc
    st1 st2 lbs lb
  : st1 ~[ lbs @@ lb ]~>* st2 <->
    exists st',
      st1 ~[ lbs ]~>* st' /\
      st' ~[ lb ]~> st2.
  Proof.
    split; intros HH.
    - apply lstepStar_app in HH as (? & ? & HH). inversion HH; inversion STPS; subst.
      eexists; split; eassumption.
    - destruct HH as (? & ? & ?). apply lstepStar_app; eexists; split;
      repeat econstructor; eassumption.
  Qed.

  Lemma lstepStar_snoc_1
    `(STPS : st1 ~[ lbs ]~>* st2)
    `(STP : st2 ~[ lb ]~> st3)
  : st1 ~[ lbs @@ lb ]~>* st3.
  Proof.
    eapply lstepStar_snoc. eexists; split; eassumption.
  Qed.

  Lemma lreachable_app
    lbs1 lbs2 st2
  : lreachable (lbs1 ++ lbs2) st2 <->
    exists st1,
      lreachable lbs1 st1 /\
      st1 ~[ lbs2 ]~>* st2.
  Proof.
    split; [intros RCH | intros (? & RCH & ?)].
    - (* -> *) inversion RCH; subst. apply lstepStar_app in ST as (? & ? & ?).
      eexists. split; [econstructor |]; eassumption.
    - (* <- *) inversion RCH; subst.
      econstructor; [| eapply lstepStar_app; eexists; split]; eassumption.
  Qed.

  Lemma lreachable_app_1
    `(RCH : lreachable lbs1 st1)
    `(STPS : st1 ~[ lbs2 ]~>* st2)
  : lreachable (lbs1 ++ lbs2) st2.
  Proof. apply lreachable_app; eexists; split; eassumption. Qed.

  Lemma lreachable_snoc
    lbs lb st2
  : lreachable (lbs @@ lb) st2 <->
    exists st1,
      lreachable lbs st1 /\
      st1 ~[ lb ]~> st2.
  Proof.
    split; [intros RCH | intros (? & RCH & ?)].
    - (* -> *) inversion RCH; subst. apply lstepStar_snoc in ST as (? & ? & ?).
      eexists. split; [econstructor |]; eassumption.
    - (* <- *) inversion RCH; subst.
      econstructor; [| eapply lstepStar_snoc; eexists; split]; eassumption.
  Qed.

  Lemma lreachable_snoc_1
    `(RCH : lreachable lbs st1)
    `(STPS : st1 ~[ lb ]~> st2)
  : lreachable (lbs @@ lb) st2.
  Proof. apply lreachable_snoc; eexists; split; eassumption. Qed.

  Lemma lstepStar_singleton
    `{LTSParams T L} (st : T) (lb : L) (st' : T)
  : st ~[ [lb] ]~>* st' <-> st ~[ lb ]~> st'.
  Proof.
    split; intros HH; [inv HH; inv STPS; eassumpt | repeat (eassumpt || econstructor) ].
  Qed.

  Lemma deterministic_steps
    `{!DLTS T L}
    `(STPS1 : st ~[ lbs' ]~>* st1)
    `(STPS2 : st ~[ lbs' ]~>* st2)
  : st1 = st2.
  Proof.
    revert st1 STPS1 st2 STPS2. induction lbs' using rev_ind; intros.
    - inversion STPS1; inversion STPS2; subst. reflexivity.
    - apply lstepStar_snoc in STPS1 as (? & S1 & ?),STPS2 as (? & S2 & ?).
      specialize (IHlbs' _ S1 _ S2); subst.
      eapply deterministic_step; revgoals; try eassumption.
  Qed.

End LTS_LEMMAS.

Lemma lstepStar_snoc_ind
  (T L : Type)
  `(LTSParams T L)
  (st0 : T)
  (P : list L -> T -> Prop)
  (B : P [] st0)
  (I : forall lbs st1 lb st2 (STPS : st0 ~[ lbs ]~>* st1) (STP : st1 ~[ lb ]~> st2) (IH : P lbs st1), P (lbs @@ lb) st2)
: forall lbs st (STPS : st0 ~[ lbs ]~>* st), P lbs st.
Proof.
  intros ? . revert st0 B I. induction lbs using rev_ind; intros.
  - inversion STPS; subst; eassumption.
  - apply lstepStar_snoc in STPS as HH; destruct HH as (? & ? & ?).
    eapply I; try eassumption. eapply IHlbs; try (intros; eapply I); eassumption.
Qed.

Lemma lreachable_snoc_ind
  (T L : Type)
  `(LTSParams T L)
  (P : list L -> T -> Prop)
  (B : forall si (INIT : init si), P [] si)
  (I : forall lbs st lb st' (RCH : lreachable lbs st) (STEP : lstep st lb st') (RCH' : lreachable (lbs @@ lb) st') (IH : P lbs st), P (lbs @@ lb) st')
: forall lbs st (RCH : lreachable lbs st), P lbs st.
Proof.
  intros. inversion RCH; subst. eapply lstepStar_snoc_ind; intros;
  try apply B; try eapply I; try eassumption; econstructor; try eassumption.
  eapply lstepStar_snoc; eexists; split; eassumption.
Qed.

Section LTS_LEMMAS.

  Context `{LTSParams T L}.

  Lemma lstepStar_take_state_ex
    n
    `(STPS : st ~[ lbs ]~>* st')
  : ∃ st1,
      st ~[ take n lbs ]~>* st1 /\
      st1 ~[ drop n lbs ]~>* st'.
  Proof.
    revert n. induction STPS using lstepStar_snoc_ind; intros.
    - rewrite take_nil,drop_nil. eexists; split; econstructor.
    - destruct (decide (n <= length lbs)).
      + rewrite take_app_le,drop_app_le by lia.
        specialize (IHSTPS n) as (? & ? & ?).
        eexists; split; [| eapply lstepStar_snoc_1]; eassumption.
      + rewrite take_ge,drop_ge by (rewrite last_length; lia).
        eexists; split; try solve [ econstructor | eapply lstepStar_snoc_1; eassumption ].
  Qed.

  Lemma lreachable_take_state_ex
    n
    `(RCH : lreachable lbs st)
  : ∃ st1,
      lreachable (take n lbs) st1 /\
      st1 ~[ drop n lbs ]~>* st.
  Proof.
    inversion RCH; clear RCH; subst.
    eapply lstepStar_take_state_ex in ST as (? & ? & ?).
    eexists; split; try econstructor; eassumption.
  Qed.

  Lemma lstepStar_lookup_state_ex
    `(STPS : st ~[ lbs ]~>* st')
    `(LB_LU : lbs !! i = Some lb)
  : ∃ st1 st2,
      st ~[ take i lbs ]~>* st1 /\
      st1 ~[ lb ]~> st2 /\
      st2 ~[ drop (i + 1) lbs ]~>* st'.
  Proof.
    revert st st' STPS i lb LB_LU; induction lbs; intros.
    - rewrite lookup_nil in LB_LU. congruence.
    - inversion STPS as [|? ? ? ? ? STPS']; clear STPS; subst.
      apply lookup_cons_Some in LB_LU as [(? & ?) | (? & ?)]; subst;
      cbn in *.
      + rewrite drop_0.
        do 2 eexists; repeat (eassumption || econstructor || split).
      + destruct i; try lia.
        eapply IHlbs in STPS' as HH; try eassumption.
        destruct HH as (? & ? & ? & ? & ?).
        try rewrite (Nat.add_comm 1),Nat.add_sub in * |- ; cbn.
        do 2 eexists; repeat (eassumption || econstructor || split).
  Qed.

  Lemma lreachable_lookup_state_ex
    `(RCH : lreachable lbs st)
    `(LB_LU : lbs !! i = Some lb)
  : ∃ st1 st2,
      lreachable (take i lbs) st1 /\
      st1 ~[ lb ]~> st2 /\
      st2 ~[ drop (i + 1) lbs ]~>* st.
  Proof.
    inversion RCH; clear RCH; subst.
    eapply lstepStar_lookup_state_ex in ST as HH; try eassumption.
    destruct HH as (? & ? & ? & ? & ?).
    do 2 eexists; repeat (eassumption || split).
    econstructor; eassumption.
  Qed.

  Lemma lstep_lookup_prop_carry
    (P : L → Prop)
    (STEP_H : ∀
      `(RCH : lreachable lbs st)
      `(STEP : st ~[ lb ]~> st'),
      P lb)
    `(RCH : lreachable lbs st)
    `(LB_LU : lbs !! i = Some lb)
  : P lb.
  Proof.
    induction RCH using lreachable_snoc_ind.
    - naive_solver.
    - apply lookup_snoc_Some in LB_LU as [[? LB_LU]|[-> ->]].
      + exact (IHRCH1 LB_LU).
      + exact (STEP_H _ _ RCH1 _ _ STEP).
  Qed.

End LTS_LEMMAS.

Section TRANSLATION.

  Context {A B : Type} `{LTSP : LTSParams A B}.

  Lemma step_lstep
    (st st' : A)
  : st ~> st' <->
    exists lbl,
      st ~[ lbl ]~> st'.
  Proof.
    split; intros HH.
    - inversion HH; eexists; eassumption.
    - destruct HH as (? & ?). econstructor; eassumption.
  Qed.

  Lemma stepStar_lstepStar
    (st st' : A)
  : st ~>* st' <->
    exists l : list B,
      st ~[ l ]~>* st'.
  Proof.
    split; intros HH.
    - induction HH using stepStar_ind.
      + exists []; econstructor.
      + destruct IHHH as (? & ?). eapply step_lstep in STP as (? & ?).
        eexists (_ @@ _); eapply lstepStar_snoc; eexists; split; eassumption.
    - destruct HH as (lbs & HH).
      pattern lbs, st'. eapply lstepStar_snoc_ind; try eassumption; intros.
      + econstructor 2.
      + econstructor 3; [| econstructor 1; apply step_lstep; eexists]; eassumption.
  Qed.

  Lemma reachable_lreachable
    (st : A)
  : reachable st <->
    exists lbs,
      lreachable lbs st.
  Proof.
    split; intros HH.
    - inversion HH; subst. eapply stepStar_lstepStar in ST as (? & ?).
      eexists; econstructor; eassumption.
    - destruct HH as (? & HH). inversion HH; subst.
      econstructor; [| eapply stepStar_lstepStar; eexists]; eassumption.
  Qed.

End TRANSLATION.

Ltac simpl_lsteps_base H :=
  match type of H with
  | _ ~[ [] ]~>* _ =>
    let d0 := fresh in
    let Heq := fresh H "_EQ" in
    inversion H as [ d0 Heq |]; clear d0;
    clear H;
    match type of Heq with ?a = ?b =>
      subst a || subst b || symmetry in Heq
    end
  | ?st ~[ _ :: _ ]~>* _ =>
    let d0 := fresh in
    let d1 := fresh in
    let d2 := fresh in
    let st' := fresh "st" in
    let Hs := fresh H "_S" in
    let Hss := fresh H "_SS" in
    inversion H as [| d0 st' d1 d2 Hs Hss];
    subst d0 d1 d2;
    clear H;
    try simpl_lsteps_base Hss
  | _ ~[ _ @@ _ ]~>* _ =>
    let st' := fresh "st" in
    let Hs := fresh H "_S" in
    let Hss := fresh H "_SS" in
    eapply lstepStar_snoc in H as (st' & Hss & Hs);
    try simpl_lsteps_base Hss
  end.

Tactic Notation "simpl_lsteps" ident(H) :=
  simpl_lsteps_base H.

Tactic Notation "simpl_lsteps_keep" ident(H) :=
  let H' := fresh H in
  let eqHH' := fresh H "_eq" in
  remember H as H' eqn:eqHH';
  rewrite <-?eqHH' in *;
  clear eqHH';
  lock H';
  simpl_lsteps_base H;
  unlock H';
  rename H' into H.

Tactic Notation "simpl_lsteps" "*" :=
  repeat
    match goal with
    | [H : _ |- _] => simpl_lsteps H
    end.

Tactic Notation "simpl_lsteps_keep" "*" :=
  repeat
    match goal with
    | [H : _ |- _] => simpl_lsteps_keep H
    end.
