From stdpp Require Export
     prelude.

From refinement Require Import
     TransSystem
     LTSRefine.

From Stdlib Require Import
     Relations
     Relations.Relation_Operators.

From Stdlib Require Export
     Streams.Streams.

From Paco Require Export
     paco.

Module LTL.

  Section LTL_DEFS.

    Context {St: Type}.

    Definition StrPred := Stream St → Prop.
    Definition StPred := St → Prop.

    Definition indep_StrPred (f: StrPred) :=
      ∀ st sub1 sub2, f (Cons st sub1) ↔ f (Cons st sub2).

    Lemma indep_StrPred_to_StPred
      `(IND: indep_StrPred f)
    : ∃ (g: StPred), ∀ st sub, f (Cons st sub) ↔ g st.
    Proof.
      exists (λ st, ∃ sub, f (Cons st sub)).
      split; intros.
      - exists sub. assumption.
      - destruct H as [sub' H]. unfold indep_StrPred in IND. rewrite IND. apply H.
    Qed.

    (* `Globally`, or `G` in temporal logic *)
    Inductive always_gen always : StrPred → StrPred :=
    | alwGenCstr (pred: StrPred) st str
        (SAT: pred (Cons st str))
        (NXT: always pred str)
      : always_gen always pred (Cons st str).
    Hint Constructors always_gen : core.

    (* Alternative and equivalent definition of `always_gen`. It considers a chunk at once.
       It makes some proofs easier (e.g., `mlit_ast_trace`). *)
    Inductive always_n_gen always : StrPred → StrPred :=
    | alwNGenCstr n (pred: StrPred) str
        (MIN: n ≠ 0)
        (SAT: ∀ m, m < n → pred (Str_nth_tl m str))
        (NXT: always pred (Str_nth_tl n str))
      : always_n_gen always pred str.
    Hint Constructors always_n_gen : core.

    (* `Globally`, or `G` in temporal logic *)
    Definition always pred str := paco2 always_gen bot2 pred str.
    Hint Unfold always : core.
    Lemma always_gen_mon : monotone2 always_gen. Proof. pmonauto. Qed.
    Hint Resolve always_gen_mon : paco.

    Definition always_n pred str := paco2 always_n_gen bot2 pred str.
    Hint Unfold always_n : core.
    Lemma always_n_gen_mon : monotone2 always_n_gen. Proof. pmonauto. Qed.
    Hint Resolve always_n_gen_mon : paco.

    Lemma always_n_tl
      pred str
      (ALW: always_n pred str)
    : always_n pred (tl str).
    Proof.
      pinversion ALW; subst. destruct (decide (n = 1)); [subst; apply NXT |].
      pfold. eapply alwNGenCstr with (n := n - 1); [lia | |].
      * intros. specialize (SAT (m + 1) ltac: (lia)). rewrite <- Str_nth_tl_plus in SAT.
        simpl in SAT. apply SAT.
      * left. assert (∃ x, n = S (S x)). { exists (n - 2). lia. } destruct H.
        subst. simpl in *. apply NXT.
    Qed.

    Lemma always_n_equiv pred str :
      always pred str ↔ always_n pred str.
    Proof.
      split; generalize dependent str.
      - pcofix CIH. pfold. destruct str. intros ALW.
        eapply alwNGenCstr with (n := 1); [lia | |].
        + intros. assert (m = 0) by lia. subst. pinversion ALW; subst. apply SAT.
        + right. simpl. apply CIH. pinversion ALW; subst. apply NXT.
      - pcofix CIH. pfold. destruct str. intros ALW. econstructor.
        + pinversion ALW; subst. apply (SAT 0 ltac: (lia)).
        + right. apply CIH. apply always_n_tl in ALW. apply ALW.
    Qed.

    (* `Finally`, or `F` in temporal logic *)
    Inductive eventually (pred: StrPred) : StrPred :=
    | evHere str
        (SAT: pred str)
      : eventually pred str
    | evCons s str
        (NXT: eventually pred str)
      : eventually pred (Cons s str).
    Hint Constructors eventually : core.

    (* `G F` in temporal logic *)
    Definition infinitely_often (pred: StrPred) : StrPred :=
      always (eventually pred).

    Definition implies (P Q : StrPred) : StrPred :=
      always (λ str, P str → Q str).

    Definition followed (P Q : StrPred) (str : Stream St) : Prop :=
      P str → eventually Q str.

    Definition always_followed (P Q : StrPred) : StrPred :=
      always (followed P Q).

    Inductive substream : relation (Stream St) :=
    | ssBase str
      : substream str str
    | ssCons st sup sub
        (NXT: substream sup sub)
      : substream (Cons st sup) sub.

    Lemma substream_alt x y : substream x y ↔ ∃ n, Str_nth_tl n x = y.
    Proof.
      split.
      - intros SUB. induction SUB.
        + by exists O.
        + destruct IHSUB as [n EQ]. exists (S n). apply EQ.
      - intros [n EQ]. generalize dependent x. generalize dependent y. induction n.
        + intros; simpl in EQ; subst; apply ssBase.
        + intros. destruct x. simpl in EQ. apply ssCons. apply IHn. apply EQ.
    Qed.

    Lemma substream_alt_dec_L
      (univ x y: Stream St) (n m: nat)
      (SUB1: Str_nth_tl n univ = x)
      (SUB2: Str_nth_tl m univ = y)
      (REL: n ≤ m)
    : Str_nth_tl (m - n) x = y.
    Proof.
      remember (m - n) as d. assert (M: m = d + n) by lia. rewrite M in *.
      rewrite <- Str_nth_tl_plus in SUB2. rewrite SUB1 in SUB2. apply SUB2.
    Qed.

    Lemma substream_alt_dec_R
      (univ x y: Stream St) (n m: nat)
      (SUB1: Str_nth_tl n univ = x)
      (SUB2: Str_nth_tl m univ = y)
      (REL: m ≤ n)
    : Str_nth_tl (n - m) y = x.
    Proof.
      remember (n - m) as d. assert (M: n = d + m) by lia. rewrite M in *.
      rewrite <- Str_nth_tl_plus in SUB1. rewrite SUB2 in SUB1. apply SUB1.
    Qed.

    Lemma substream_alt_dec_under_univ
      (univ x y: Stream St) (n m: nat)
      (SUB1: Str_nth_tl n univ = x)
      (SUB2: Str_nth_tl m univ = y)
    : (n = m ∧ x = y) ∨
      (m > n ∧ Str_nth_tl (m - n) x = y) ∨
      (n > m ∧ Str_nth_tl (n - m) y = x).
    Proof.
      destruct (decide (n = m)). { subst. left. done. }
      right. destruct (decide (n < m)).
      - left. split; [lia |]. eapply substream_alt_dec_L; eauto. lia.
      - right. split; [lia |]. eapply substream_alt_dec_R; eauto. lia.
    Qed.

    Lemma substream_dec_under_univ
      `(SUB1: substream univ x)
      `(SUB2: substream univ y)
    : substream x y ∨ substream y x.
    Proof.
      generalize dependent y. induction SUB1; [auto |].
      intros. inversion SUB2; subst.
      - right. apply ssCons, SUB1.
      - apply IHSUB1, NXT.
    Qed.

    #[global] Instance substream_trans : Transitive substream.
    Proof.
      intros ????. induction H; auto.
      intros. apply ssCons. auto.
    Qed.

    #[global] Instance substream_refl : Reflexive substream.
    Proof. constructor. Qed.

    Inductive subsequence_gen subsequence : relation (Stream St) :=
    | sqGenCstr sup sup' sub
        (SUB: substream sup sup')
        (MAT: (hd sup') = (hd sub))
        (SEQ: subsequence (tl sup') (tl sub))
      : subsequence_gen subsequence sup sub.
    Hint Constructors subsequence_gen : core.

    Definition subsequence sup sub := paco2 subsequence_gen bot2 sup sub.
    Hint Unfold subsequence : core.
    Lemma subsequence_gen_mon : monotone2 subsequence_gen. Proof. pmonauto. Qed.
    Hint Resolve subsequence_gen_mon : paco.

    Lemma unwrap_always
      `(ALW: always P str)
    : P str.
    Proof. pinversion ALW. assumption. Qed.

    Lemma always_trivial
      (P: StrPred) str
      (SAT: ∀ str', P str')
    : always P str.
    Proof.
      generalize dependent str. pcofix CIH.
      destruct str. pfold. constructor; auto.
    Qed.

    Lemma always_cons
      P st str
      (ALW: always P (Cons st str))
    : always P str.
    Proof. pinversion ALW. assumption. Qed.

    Lemma implies_always
      P Q str
      (IMP: implies P Q str)
      (ALW: always P str)
    : always Q str.
    Proof.
      generalize dependent str. pcofix CIH.
      destruct str. intros. pfold; constructor; [| right; apply CIH];
      pinversion IMP; pinversion ALW; auto.
    Qed.

    Lemma neg_eventually
      P str
      (NEV: ¬ eventually P str)
    : always (λ str', ¬ (P str')) str.
    Proof.
      generalize dependent str. pcofix CIH.
      destruct str. intros. pfold. constructor.
      - intros CONT. apply evHere in CONT. contradiction.
      - right. apply CIH. intros CONT. eapply evCons in CONT.
        apply NEV in CONT. contradiction.
    Qed.

    Lemma neg_always
      P str
      (NEV: ¬ always P str)
    : eventually (λ str', ¬ (P str')) str.
    Proof.
      apply Ax.NNPP. intros CONT. apply neg_eventually in CONT.
      assert (CONT': always P str).
      { clear NEV. generalize dependent str. pcofix CIH. destruct str.
        pfold. constructor.
        - apply unwrap_always in CONT. simpl in CONT. by apply Ax.NNPP.
        - right. apply CIH. by apply always_cons in CONT. }
      contradiction.
    Qed.

    Lemma implies_eventually
      P Q str
      (IMP: implies P Q str)
      (EVE: eventually P str)
    : eventually Q str.
    Proof.
      destruct str. induction EVE.
      - apply evHere. apply unwrap_always in IMP. auto.
      - apply evCons. apply always_cons in IMP. auto.
    Qed.

    Lemma implies_infoften
      P Q str
      (IMP: implies P Q str)
      (INF: infinitely_often P str)
    : infinitely_often Q str.
    Proof.
      generalize dependent str. pcofix CIH. destruct str. pfold; constructor.
      - pinversion INF; subst. apply (implies_eventually _ _ _ IMP SAT).
      - right. apply CIH; pinversion IMP; pinversion INF; auto.
    Qed.

    Lemma evalw_cons
      P str st
      (EVE: eventually (always P) (Cons st str))
    : eventually (always P) str.
    Proof.
      inversion EVE; subst; [pinversion SAT; apply evHere |]; assumption.
    Qed.

    Lemma evalw_implies_infoften
      P str
      (EVE: eventually (always P) str)
    : infinitely_often P str.
    Proof.
      generalize dependent str. pcofix CIH. destruct str. pfold. constructor.
      - apply implies_eventually with (P := (always P)); try assumption.
        unfold implies. eapply always_trivial. intros str' ALW. apply (unwrap_always ALW).
      - right. apply CIH. eapply evalw_cons. apply EVE.
    Qed.

    Lemma infoften_cons
      P st str
    : infinitely_often P str ↔ infinitely_often P (Cons st str).
    Proof.
      enough (ONE: infinitely_often P str → infinitely_often P (Cons st str)).
      { split; intros H; eauto. eapply always_cons. apply H. }
      generalize dependent str. generalize dependent st.
      pcofix CIH. pfold. intros st str INF. constructor.
      - apply unwrap_always in INF. apply evCons, INF.
      - right. destruct str. apply CIH. apply always_cons in INF; auto.
    Qed.

    Lemma infoften_substream_iff
      P sup sub
      (SUB: substream sup sub)
    : infinitely_often P sup ↔ infinitely_often P sub.
    Proof.
      induction SUB.
      - split; auto.
      - specialize (infoften_cons P st sup) as CON. rewrite <- CON. assumption.
    Qed.

    Lemma infoften_substream
      P sup sub
      (SUB: substream sup sub)
      (INF: infinitely_often P sup)
    : infinitely_often P sub.
    Proof. rewrite <- infoften_substream_iff. apply INF. assumption. Qed.

    Lemma substream_tl str : substream str (tl str).
    Proof. destruct str. apply ssCons. constructor. Qed.

    Lemma substream_sub_tl
      `(SUB: substream str sub)
    : substream str (tl sub).
    Proof.
      induction SUB; [apply substream_tl |].
      eapply substream_trans; [apply substream_tl | apply IHSUB].
    Qed.

    Lemma substream_sub_tl_n
      `(SUB: substream str sub)
    : ∀ n, substream str (Str_nth_tl n sub).
    Proof.
      intros n. induction n; [apply SUB |].
      simpl. rewrite <- tl_nth_tl. apply substream_sub_tl. assumption.
    Qed.

    Lemma eventually_exists
      P sup
    : eventually P sup ↔ (∃ sub, substream sup sub ∧ P sub).
    Proof.
      split.
      - intros EVE. induction EVE; subst.
        + exists str. split. constructor. assumption.
        + destruct IHEVE as [str' [SUB SAT]]. exists str'. split;
          [apply ssCons |]; assumption.
      - intros (sub & SUB & SAT).
        induction SUB; [apply evHere | apply evCons]; auto.
    Qed.

    Lemma always_forall
      P sup
    : always P sup ↔ (∀ sub, substream sup sub → P sub).
    Proof.
      split.
      - intros ALW sub SUB. induction SUB;
        [apply unwrap_always | apply always_cons in ALW]; auto.
      - generalize dependent sup.
        pcofix CIH. intros sup SAT. destruct sup. pfold. constructor.
        + apply SAT. constructor.
        + right. apply CIH. intros. apply SAT. apply ssCons. assumption.
    Qed.

    Lemma eventually_contra
      P str
      (CONT: ¬ always (λ str', ¬ (P str')) str)
    : eventually P str.
    Proof.
      apply neg_always in CONT. eapply implies_eventually; [| apply CONT].
      apply always_forall. intros. by apply Ax.NNPP.
    Qed.

    Lemma always_contra
      P str
      (CONT: ¬ eventually (λ str', ¬ (P str')) str)
    : always P str.
    Proof.
      apply neg_eventually in CONT. eapply implies_always; [| apply CONT].
      apply always_forall. intros. by apply Ax.NNPP.
    Qed.

    Lemma eventually_substream
      P sup sub
      (SUB: substream sup sub)
      (EVE: eventually P sub)
    : eventually P sup.
    Proof. induction SUB; [| apply evCons]; auto. Qed.

    Lemma always_substream
      P sup sub
      (SUB: substream sup sub)
      (ALW: always P sup)
    : always P sub.
    Proof. induction SUB; [| apply always_cons in ALW]; auto. Qed.

    (* ♢♢P ⟹ ♢P : flatten nested eventually. *)
    Lemma eventually_eventually
      P str
      (EE: eventually (λ sub, eventually P sub) str)
    : eventually P str.
    Proof.
      induction EE as [str SAT | s str EE IH].
      - exact SAT.
      - apply evCons. exact IH.
    Qed.

    (* ♢P and a pointwise (on every stream) implication P ⟹ Q ⟹ ♢Q. *)
    Lemma eventually_mono
      P Q str
      (EV: eventually P str)
      (IMP: ∀ sub, P sub → Q sub)
    : eventually Q str.
    Proof.
      induction EV as [str SAT | s str EV IH].
      - apply evHere. apply IMP. exact SAT.
      - apply evCons. exact IH.
    Qed.

    (* Classical dichotomy for [eventually]: either [P] eventually holds, or it
       is always false.  This is the shape the fairness arguments need, and it
       is the intended entry point for them: going through it keeps those
       proofs free of any direct appeal to [Ax.classic].  (For the raw
       ¬-form, use [Ax.classic] with [neg_eventually].) *)
    Lemma eventually_or_always_not
      P str
    : eventually P str ∨ always (λ s, ¬ P s) str.
    Proof.
      destruct (Ax.classic (eventually P str)) as [EVE | NEV];
        [left; exact EVE | right; exact (neg_eventually _ _ NEV)].
    Qed.

    (* ♢P and □¬P are contradictory. *)
    Lemma eventually_always_not_False
      {P : StrPred} {str : Stream St}
      (EVE: eventually P str)
      (ALW: always (λ s, ¬ P s) str)
    : False.
    Proof.
      revert ALW. induction EVE as [str0 SAT | s0 str0 EVE IH]; intros ALW.
      - exact (unwrap_always ALW SAT).
      - exact (IH (always_cons _ _ _ ALW)).
    Qed.

    (* Recurrence: if from every suffix where [P] is false [P] eventually
       holds, then [P] holds infinitely often. *)
    Lemma infinitely_often_recurrent
      P str
      (REC: always (λ s, ¬ P s → eventually P s) str)
    : infinitely_often P str.
    Proof.
      unfold infinitely_often. revert str REC. pcofix CIH. intros str REC.
      destruct str as [x str']. pinversion REC; subst. pfold. constructor.
      - destruct (Ax.classic (P (Cons x str'))) as [HP | HNP];
          [apply evHere, HP | apply SAT, HNP].
      - right. apply CIH. exact NXT.
    Qed.

    (* ♢P and □Q ⟹ ♢(P ∧ Q): the always-fact Q survives down to the
       substream witnessing P. *)
    Lemma eventually_and_always
      P Q str
      (EV: eventually P str)
      (AL: always Q str)
    : eventually (λ sub, P sub ∧ Q sub) str.
    Proof.
      apply eventually_exists in EV as (sub & SUB & HP).
      apply eventually_exists. exists sub. split; [exact SUB |].
      split; [exact HP | eapply unwrap_always, always_substream; eassumption].
    Qed.

    Lemma eventually_first
      P str
      (EVE: eventually P str)
    : ∃ n, (∀ m, m < n → ¬ P (Str_nth_tl m str)) ∧ P (Str_nth_tl n str).
    Proof.
      induction EVE.
      - exists 0. split; [lia | assumption].
      - destruct (Ax.classic (P (Cons s str))).
        + exists 0. split; [lia | assumption].
        + destruct IHEVE as (n & ? & ?). exists (S n). split; [| assumption].
          intros. destruct (decide (n = 0)); subst.
          * assert (m = 0) by lia. subst. assumption.
          * destruct m; [assumption | simpl]. apply H0. lia.
    Qed.

    Lemma always_conj
      P Q str
      (ALW1: always P str)
      (ALW2: always Q str)
    : always (λ sub, P sub ∧ Q sub) str.
    Proof.
      apply always_forall. intros sub SUB.
      split; [rewrite always_forall in ALW1; apply ALW1 |
              rewrite always_forall in ALW2; apply ALW2]; assumption.
    Qed.

    Lemma evalw_conj
      P Q str
      (EAW1: eventually (always P) str)
      (EAW2: eventually (always Q) str)
    : eventually (always (λ sub, P sub ∧ Q sub)) str.
    Proof.
      apply eventually_exists in EAW1, EAW2.
      destruct EAW1 as [sub1 [SUB1 ALW1]]. destruct EAW2 as [sub2 [SUB2 ALW2]].
      destruct (substream_dec_under_univ SUB1 SUB2); apply eventually_exists; eexists.
      - split; [apply SUB2 | eapply always_conj;
        solve [eapply always_substream; eassumption | eassumption]].
      - split; [apply SUB1 | eapply always_conj;
        solve [eapply always_substream; eassumption | eassumption]].
    Qed.

    Lemma subsequence_trunc_sub
      `(SEQ: subsequence sup sub)
      `(SUB: substream sub sub')
    : subsequence sup sub'.
    Proof.
      generalize dependent sup. induction SUB; [auto |].
      intros sub' ?. apply IHSUB. pinversion SEQ. pinversion SEQ0; simpl in *.
      subst. pfold. econstructor.
      - apply (substream_trans _ _ _ (substream_trans _ _ _ SUB0 (substream_tl sup')) SUB1).
      - assumption.
      - left. apply SEQ1.
    Qed.

    #[global] Instance subsequence_trans : Transitive subsequence.
    Proof.
      pcofix CIH. intros ??? SEQ1 SEQ2.
      pinversion SEQ2. specialize (subsequence_trunc_sub SEQ1 SUB) as SEQi.
      pinversion SEQi. pfold. econstructor.
      - apply SUB0.
      - rewrite <- MAT. apply MAT0.
      - right. eapply CIH. apply SEQ0. apply SEQ.
    Qed.

    #[global] Instance subsequence_refl : Reflexive subsequence.
    Proof.
      pcofix CIH. pfold. econstructor;
      [apply substream_refl | reflexivity | right; auto].
    Qed.

    Lemma subsequence_always
      P sup sub
      (IND: indep_StrPred P)
      (SEQ: subsequence sup sub)
      (ALW: always P sup)
    : always P sub.
    Proof.
      apply always_forall. intros sub' SUB. specialize (subsequence_trunc_sub SEQ SUB) as SEQ'.
      pinversion SEQ'; subst. apply (always_substream P sup sup' SUB0) in ALW.
      apply unwrap_always in ALW.  specialize (indep_StrPred_to_StPred IND) as IND'.
      destruct IND' as [Q EQ]. destruct sub', sup'. simpl in *; subst.
      apply EQ. apply EQ in ALW. assumption.
    Qed.

  End LTL_DEFS.

  #[global] Hint Resolve always_gen_mon : paco.
  #[global] Hint Resolve subsequence_gen_mon : paco.

End LTL.

Section TRACE.

  Context {A B : Type}.
  Context {LTS : LTSParams A B}.

  (* one step between two trace points: the label-history grows by the taken label *)
  Definition pstep (p p' : list B * A) : Prop :=
    ∃ lb, p'.1 = p.1 @@ lb ∧ p.2 ~[ lb ]~> p'.2.

  Definition trace (str: Stream (list B * A)) : Prop :=
    lreachable (hd str).1 (hd str).2 ∧
    LTL.always (λ s, pstep (hd s) (hd (tl s))) str.

  Definition ltrace (ilbs: list B) (str: Stream (list B * A)) : Prop :=
    (hd str).1 = ilbs ∧
    lreachable ilbs (hd str).2 ∧
    LTL.always (λ s, pstep (hd s) (hd (tl s))) str.

  Lemma trace_ltrace
      str
    : trace str ↔ ∃ ilbs, ltrace ilbs str.
  Proof.
    split; intros.
    - destruct H as [REC ADJ]. exists (hd str).1. split; [reflexivity | split; assumption].
    - destruct H as (ibls & EQ & REC & ADJ). split; [rewrite EQ |]; assumption.
  Qed.

  Lemma trace_cons
      st str
      (TR: trace (Cons st str))
    : trace str.
  Proof.
    destruct TR as [INI CON]; split.
    - apply LTL.unwrap_always in CON. simpl in CON. destruct CON as [lb [HEQ STP]].
      rewrite HEQ. eapply lreachable_snoc_1; eassumption.
    - apply (LTL.always_cons _ _ _ CON).
  Qed.

  Lemma trace_tl
      `(TR: trace str)
    : trace (tl str).
  Proof.
    destruct str. eapply trace_cons. apply TR.
  Qed.

  Lemma trace_substr
      sup sub
      (SUB: LTL.substream sup sub)
      (TR : trace sup)
    : trace sub.
  Proof.
    induction SUB; auto.
    apply IHSUB. eapply trace_cons. apply TR.
  Qed.

  Lemma trace_substr_ss
      sup sub
      (TR : trace sup)
      (SUB: LTL.substream sup sub)
    : (hd sup).2 ~>* (hd sub).2.
  Proof.
    induction SUB.
    - apply rt_refl.
    - apply trace_cons in TR as TR'. apply IHSUB in TR' as SS; auto.
      apply rt_trans with (y := (hd sup).2). 2: apply SS.
      destruct TR as [INI CON]. apply LTL.unwrap_always in CON. simpl in CON.
      destruct CON as [lb [_ STP]]. apply rt_step. eexists. apply STP.
  Qed.

End TRACE.


Section STEP_STAR_TRACE.

  Context {A B : Type}.
  Context {LTS : LTSParams A B}.

  (* Determines whether the prefix of the trace is generated by the given sequence of labels. *)
  Inductive stepStarTrace : Stream (list B * A) -> list B -> Stream (list B * A) -> Prop :=
  | prefLbsInit
      str
    : stepStarTrace str [] str
  | prefLbsCons
      hst lb preStr slbs postStr
      (STP : (hd preStr).1 = hst.1 @@ lb /\ hst.2 ~[ lb ]~> (hd preStr).2)
      (CON : stepStarTrace preStr slbs postStr)
    : stepStarTrace (Cons hst preStr) (lb :: slbs) postStr.

  Lemma sst_substream
    `(SST : stepStarTrace str lbs sub)
  : LTL.substream str sub.
  Proof.
    induction SST; constructor; assumption.
  Qed.

  Lemma substream_sst
    `(TRC : trace str)
    `(SUB : LTL.substream str sub)
  : ∃ lbs, stepStarTrace str lbs sub.
  Proof.
    induction SUB.
    - exists []. constructor.
    - assert (TRC': trace sup) by eapply trace_cons, TRC.
      apply trace_substr in SUB; [| apply TRC']. destruct (IHSUB TRC') as [lbs SST].
      destruct TRC as [REC ADJ]. apply LTL.unwrap_always in ADJ. simpl in ADJ.
      destruct ADJ as [lb [HEQ STP]].
      exists (lb :: lbs). eapply prefLbsCons; [split; [apply HEQ | apply STP] |]. apply SST.
  Qed.

  Lemma sst_stepStar
    `(SST : stepStarTrace str lbs sub)
  : sub = Str_nth_tl (length lbs) str ∧ (hd str).2 ~[ lbs ]~>* (hd sub).2.
  Proof.
    induction SST.
    - split; [reflexivity | constructor].
    - split.
      + apply IHSST.
      + simpl. destruct STP as [_ STP]. econstructor; [apply STP | apply IHSST].
  Qed.

  Lemma sst_adj_steps
    `(SST : stepStarTrace str lbs sub)
  : sub = Str_nth_tl (length lbs) str ∧
    ∀ m, m < length lbs → pstep (hd (Str_nth_tl m str)) (hd (tl (Str_nth_tl m str))).
  Proof.
    induction SST.
    - split; [reflexivity | intros; simpl in *; lia].
    - split; [apply IHSST |]. simpl. destruct IHSST as [EQ IHSST]; subst. intros.
      destruct m; simpl; [destruct STP as [HEQ STP]; eexists; split; [apply HEQ | apply STP]
                         | apply IHSST; lia].
  Qed.

  Lemma sst_trans
    `(SST1 : stepStarTrace str1 lbs1 str2)
    `(SST2 : stepStarTrace str2 lbs2 str3)
  : stepStarTrace str1 (lbs1 ++ lbs2) str3.
  Proof.
    generalize dependent str1; generalize dependent str2; generalize dependent str3;
    generalize dependent lbs2. induction lbs1; simpl in *; intros.
    - inversion SST1; subst. assumption.
    - destruct str1. constructor; inversion SST1; subst; [eassumption | eapply IHlbs1; eauto].
  Qed.

  Lemma sst_Str_nth_tl
    `(SST : stepStarTrace str lbs sub)
  : sub = Str_nth_tl (length lbs) str.
  Proof.
    generalize dependent str; generalize dependent sub. induction lbs; intros.
    - inversion SST; subst; reflexivity.
    - eapply IHlbs. inversion SST; subst. apply CON.
  Qed.

  Lemma sst_trunc
    `(SST1 : stepStarTrace astr albs asub)
    `(SST2 : stepStarTrace astr albs' asub')
    `(LEN : length albs ≤ length albs')
  : stepStarTrace asub (drop (length albs) albs') asub'.
  Proof.
    generalize dependent albs. generalize dependent astr.
    generalize dependent asub. generalize dependent asub'. induction albs'.
    - intros. simpl in LEN. destruct (nil_or_length_pos albs); [| lia].
      subst. simpl. inversion SST1; inversion SST2; subst. constructor.
    - intros. destruct albs. { inversion SST1; subst. simpl. apply SST2. }
      assert (T1: stepStarTrace (tl astr) albs asub). { inversion SST1; subst. apply CON. }
      assert (T2: stepStarTrace (tl astr) albs' asub'). { inversion SST2; subst. apply CON. }
      assert (LEN': length albs ≤ length albs'). { simpl in LEN. lia. }
      specialize (IHalbs' asub' asub (tl astr) T2 albs T1 LEN'). simpl. apply IHalbs'.
  Qed.

End STEP_STAR_TRACE.


Section FAIRNESS.

  Context {A B : Type}.
  Context {LTS : LTSParams A B}.

  (** Basic strong and weak fairness definitions and their properties. **)

  (* An event is a predicate over (1) a single label and (2) a paired post-state.
     The post-state is paired (list B * A): its `.1` carries the label-history-so-far,
     which lets state-predicate events read the actual labels an execution has taken
     (e.g. "op applied at node nid"). *)
  Definition Event := B -> (list B * A) -> Prop.

  (* An event is enabled if a corresponding single next-step state exists. *)
  Definition enabled (event: Event) (st: list B * A) : Prop :=
    ∃ lb next, event lb next ∧ st.2 ~[ lb ]~> next.2 ∧ next.1 = st.1 @@ lb.

  (* An event is taken at str's FIRST step: the step from (hd str) to (hd (tl str))
     is an event-step. `eventually`/`infinitely_often` lift this point predicate to
     "taken at some/infinitely-many points". *)
  Definition taken (event: Event) (str: Stream (list B * A)) : Prop :=
    ∃ lb, (hd str).2 ~[ lb ]~> (hd (tl str)).2
        ∧ (hd (tl str)).1 = (hd str).1 @@ lb
        ∧ event lb (hd (tl str)).

  (* ☐ ♢ Enabled(e) => ☐ ♢ Taken(e) *)
  Definition strong_fairness (event: Event) (str: Stream (list B * A)) : Prop :=
    LTL.infinitely_often (λ sub, enabled event (hd sub)) str ->
    LTL.infinitely_often (taken event) str.

  (* Another equivalent form of strong fairness: ☐ ♢ Enabled(e) => ♢ Taken(e) *)
  Definition strong_fairness_ev (event: Event) (str: Stream (list B * A)) : Prop :=
    LTL.infinitely_often (λ sub, enabled event (hd sub)) str ->
    LTL.eventually (taken event) str.

  (* ♢ ☐ Enabled(e) => ☐ ♢ Taken(e) *)
  Definition weak_fairness (event: Event) (str: Stream (list B * A)) : Prop :=
    LTL.eventually (LTL.always (λ sub, enabled event (hd sub))) str ->
    LTL.infinitely_often (taken event) str.

  (* Another equivalent form of weak fairness: ♢ ☐ Enabled(e) => ♢ Taken(e) *)
  Definition weak_fairness_ev (event: Event) (str: Stream (list B * A)) : Prop :=
    LTL.eventually (LTL.always (λ sub, enabled event (hd sub))) str ->
    LTL.eventually (taken event) str.

  Lemma strong_implies_weak
      event str
      (FAR: strong_fairness event str)
    : weak_fairness event str.
  Proof.
    intro WPR. apply LTL.evalw_implies_infoften in WPR. apply (FAR WPR).
  Qed.

  Lemma strfair_substr
      event sup sub
      (SS : LTL.substream sup sub)
      (FAR: strong_fairness event sup)
    : strong_fairness event sub.
  Proof.
    enough (BASE: ∀ lb s str,
      strong_fairness lb (Cons s str) -> strong_fairness lb str).
    { induction SS; eauto. }
    intros ??? FAR' SPR. unfold strong_fairness in FAR'.
    rewrite <- LTL.infoften_cons in FAR'. apply FAR' in SPR.
    apply LTL.always_cons in SPR; auto.
  Qed.

  Lemma weakfair_substr
      event sup sub
      (SS : LTL.substream sup sub)
      (FAR: weak_fairness event sup)
    : weak_fairness event sub.
  Proof.
    intros EVE. apply LTL.eventually_substream with (sup := sup) in EVE; auto.
    specialize (FAR EVE). apply (LTL.always_substream _ _ _ SS). assumption.
  Qed.

  (** Additional variants for some special usages. **)

  (*** Variants for a predicate over a post-state. **)

  (* state-predicate events read the PAIRED post-state: P can read both the post-state's
     label-history (`.1`) and its state (`.2`). *)
  Definition PsEvent := (list B * A) -> Prop.

  Definition pse2event (event: PsEvent) : Event := λ _ post,
    event post.
  (* note: the label argument is now a single B (ignored here). *)

  Definition enabled_st (event: PsEvent) (st: list B * A) : Prop :=
    enabled (pse2event event) st.

  Definition taken_st (event: PsEvent) (str: Stream (list B * A)) : Prop :=
    taken (pse2event event) str.

  Definition strong_fairness_st (event: PsEvent) (str: Stream (list B * A)) : Prop :=
    strong_fairness (pse2event event) str.

  Definition weak_fairness_st (event: PsEvent) (str: Stream (list B * A)) : Prop :=
    weak_fairness (pse2event event) str.

  Lemma taken_st_effect
    pse str
    (TAK : taken (pse2event pse) str)
  : LTL.eventually (λ sub, pse (hd sub)) str.
  Proof.
    destruct TAK as (lb & _ & _ & P2E).
    apply LTL.eventually_exists. exists (tl str). split.
    - apply LTL.substream_sub_tl. constructor.
    - eapply P2E.
  Qed.

  (** Variants for a predicate over a single label. **)

  Definition SLbEvent := B -> Prop.

  Definition sle2event (event: SLbEvent) : Event := λ lb _,
    event lb.

  Definition enabled_sle (event: SLbEvent) (st: list B * A) : Prop :=
    enabled (sle2event event) st.

  Definition taken_sle (event: SLbEvent) (str: Stream (list B * A)) : Prop :=
    taken (sle2event event) str.

  Definition strong_fairness_sle (event: SLbEvent) (str: Stream (list B * A)) : Prop :=
    strong_fairness (sle2event event) str.

  Definition weak_fairness_sle (event: SLbEvent) (str: Stream (list B * A)) : Prop :=
    weak_fairness (sle2event event) str.

End FAIRNESS.


Section LABEL_ALGEBRA.

  Context {A B : Type}.
  Context {LTS : LTSParams A B}.

  (* 1. The in-stream history IS the accumulated labels. Foundational. *)
  Lemma stepStarTrace_hist str lbs sub
    (SST : stepStarTrace str lbs sub)
  : (hd sub).1 = (hd str).1 ++ lbs.
  Proof.
    induction SST.
    - simpl. by rewrite app_nil_r.
    - destruct STP as [HEQ _]. simpl in *.
      rewrite IHSST, HEQ. by rewrite <- app_assoc.
  Qed.

  (* 2. History monotonicity along a trace. *)
  Lemma trace_hist_mono str sub
    (TR : trace str) (SUB : LTL.substream str sub)
  : ∃ mid, (hd sub).1 = (hd str).1 ++ mid.
  Proof.
    destruct (substream_sst TR SUB) as [lbs SST].
    exists lbs. by apply stepStarTrace_hist.
  Qed.

  (* 3. Generic monotone-persist: a label-function value that's upward-closed
        under appended labels persists for the rest of the trace. *)
  Lemma hist_mono_persist {X : Type} (f : list B → X) (Q : X → Prop) str
    (MONO : ∀ l m, Q (f l) → Q (f (l ++ m)))
    (TR : trace str)
    (HQ : Q (f (hd str).1))
  : LTL.always (λ s, Q (f (hd s).1)) str.
  Proof.
    apply LTL.always_forall. intros sub SUB.
    destruct (trace_hist_mono str sub TR SUB) as [mid HEQ].
    rewrite HEQ. by apply MONO.
  Qed.

  (* 4. A taken single-label event leaves its label in the history (eventually). *)
  Lemma taken_sle_in_hist (P : B → Prop) str
    (TAK : taken_sle P str)
  : LTL.eventually (λ s, ∃ lb, lb ∈ (hd s).1 ∧ P lb) str.
  Proof.
    destruct TAK as (lb & _ & HEQ & HP).
    apply LTL.eventually_exists.
    exists (tl str). split.
    - apply LTL.substream_sub_tl. constructor.
    - exists lb. split; [| assumption]. rewrite HEQ.
      apply elem_of_app. right. apply list_elem_of_singleton. reflexivity.
  Qed.

  (* 5. ... and it stays in the history forever after (eventually-always). *)
  Lemma taken_sle_in_hist_persist (P : B → Prop) str
    (TR : trace str)
    (TAK : taken_sle P str)
  : LTL.eventually (LTL.always (λ s, ∃ lb, lb ∈ (hd s).1 ∧ P lb)) str.
  Proof.
    apply taken_sle_in_hist in TAK.
    apply LTL.eventually_exists in TAK as (sub & SUB & HQ).
    apply LTL.eventually_substream with (sub := sub); [assumption |].
    apply LTL.eventually_exists. exists sub. split; [constructor |].
    apply trace_substr in SUB as TRsub; [| assumption].
    apply (hist_mono_persist (λ h, h) (λ h, ∃ lb, lb ∈ h ∧ P lb) sub).
    - intros l m (lb & HIN & HP). exists lb. split; [| assumption].
      apply elem_of_app. by left.
    - assumption.
    - assumption.
  Qed.

End LABEL_ALGEBRA.
