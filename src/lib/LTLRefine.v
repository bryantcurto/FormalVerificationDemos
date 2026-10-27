From stdpp Require Export
     prelude.

From refinement Require Import
     TransSystem
     LTSRefine
     LTL.

From Stdlib Require Import
     Relations
     Relations.Relation_Operators.

From Stdlib Require Export
     Streams.Streams.

From Paco Require Export
     paco.

(* Redesigned `MatchLTSInfTrace` (the infinite/coinductive stuttering-refinement
   relation) over *paired* streams `Stream (list _ * _)`.

   Both the concrete and abstract streams carry their per-stream label-history in
   the `.1` component of each trace point. This removes the explicit `clbs`/`albs`
   arguments threaded through the old (paco5) version: the history growth is now
   structural, forced by the paired `stepStarTrace` premises. The result is a
   paco3 relation. *)

Section REFINE.

  Context `{REF : LTSRef}.

  (* Variant of MatchLTSTrace (LTSRefine.v) for an infinite trace.
     "It may infinitely stutter": all CSts may be refined to the first ASt.

     The per-stream label-history lives in `(hd cstr).1` / `(hd astr).1`; the
     paired `stepStarTrace cstr [clb'] csub` already forces
     `(hd csub).1 = (hd cstr).1 @@ clb'` (and similarly for the abstract chunk),
     so `NXT` no longer needs to mention the grown histories. *)
  Inductive MatchLTSInfTrace_gen
    (MIT : A → Stream (list CLb * CSt) → Stream (list ALb * ASt) → Prop)
    (a : A) (cstr : Stream (list CLb * CSt)) (astr : Stream (list ALb * ASt)) : Prop :=
  | mchLTSStrGenCstr clb' albs' csub asub
      (CUR : MatchLTSTrace a (hd cstr).1 (hd cstr).2 (hd astr).1 (hd astr).2)
      (CST : stepStarTrace cstr [clb'] csub)
      (AST : stepStarTrace astr albs' asub)
      (NXT : MIT a csub asub)
    : MatchLTSInfTrace_gen MIT a cstr astr.
  Hint Constructors MatchLTSInfTrace_gen : core.

  Definition MatchLTSInfTrace a cstr astr :=
    paco3 MatchLTSInfTrace_gen bot3 a cstr astr.
  Hint Unfold MatchLTSInfTrace : core.
  Lemma MatchLTSInfTrace_gen_mon : monotone3 MatchLTSInfTrace_gen.
  Proof. pmonauto. Qed.

End REFINE.

#[global] Hint Resolve MatchLTSInfTrace_gen_mon : paco.


Section REFINE_PROPS.

  (* LTSRefInitStep (rather than bare LTSRef) so that `lts_ref_inf_trace` can
     extend a carried MatchLTSTrace by the trace's next concrete step via
     `lts_refine_step`.  The LTSRef the other mlit_* lemmas use is derived from
     it by the global `LTSRefInitStep_LTSRef` instance.  All real instantiations
     (eventual/rwdep Fairness.v) build their LTSRef this way, so this is in scope
     at every call site. *)
  Context `{RIS : LTSRefInitStep}.

  (* The MatchLTSTrace carried at the head of an infinite match: the paired
     label-histories at the two stream heads already match. *)
  Lemma mlit_head
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
  : MatchLTSTrace a (hd cstr).1 (hd cstr).2 (hd astr).1 (hd astr).2.
  Proof. pinversion MAT; subst. exact CUR. Qed.

  Lemma mlit_cst_steps
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
  : ∀ n, ∃ clbs' csub albs' asub,
      n = length clbs' ∧
      stepStarTrace cstr clbs' csub ∧
      stepStarTrace astr albs' asub ∧
      MatchLTSInfTrace a csub asub.
  Proof.
    induction n.
    - exists [], cstr, [], astr. split; [| split; [| split]];
      [reflexivity | constructor | constructor | apply MAT].
    - destruct IHn as (clbs' & csub & albs' & asub & LEN & CST & AST & MAT').
      pinversion MAT'; subst. exists (clbs' @@ clb'), csub0, (albs' ++ albs'0), asub0.
      split; [| split; [| split]].
      + rewrite length_app. simpl. lia.
      + eapply sst_trans; [apply CST | apply CST0].
      + eapply sst_trans; [apply AST | apply AST0].
      + apply NXT.
  Qed.

  Lemma mlit_cst_trace
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
  : trace cstr.
  Proof.
    split.
    - pinversion MAT; subst. apply MatchLTSTrace_lreachable in CUR. apply CUR.
    - apply LTL.always_forall. intros csub SUB.
      apply LTL.substream_alt in SUB. destruct SUB as [n SUB].
      destruct (mlit_cst_steps _ _ _ MAT (S n)) as (? & ? & ? & ? & ? & CST & ? & ?). subst.
      apply sst_adj_steps in CST as (? & STP). apply STP. lia.
  Qed.

  Lemma mlit_cst_substream
    a cstr csub astr
    (MAT : MatchLTSInfTrace a cstr astr)
    (SUB : LTL.substream cstr csub)
  : ∃ asub,
      MatchLTSInfTrace a csub asub ∧
      LTL.substream astr asub.
  Proof.
    apply LTL.substream_alt in SUB as [n RW]. rewrite <- RW.
    destruct (mlit_cst_steps _ _ _ MAT n) as (? & ? & ? & ? & ? & CST & AST & ?).
    apply sst_substream in AST. apply sst_Str_nth_tl in CST. subst. eexists. split; eauto.
  Qed.

  (* `ast_advances` over paired trace points: the abstract layer is *forced* to
     advance at this concrete step (i.e. cannot stutter and stay refining the same
     abstract state). The histories `cp.1` / `cp'.1` are read directly from the
     paired points; `cp'.1 = cp.1 @@ clb` is forced by the surrounding
     `stepStarTrace`, so no explicit `clbs`/`clb` arg is needed.

     Note: ¬ ast_advances implies that the abstract layer *may* stutter. *)
  Definition ast_advances a (cp cp' : list CLb * CSt) : Prop :=
    ∀ albs ast albs' ast',
      MatchLTSTrace a cp.1 cp.2 albs ast →
      MatchLTSTrace a cp'.1 cp'.2 (albs ++ albs') ast' →
      ¬ MatchLTSTrace a cp'.1 cp'.2 albs ast.

  Lemma ast_adv_effect
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
    (ADV : ast_advances a (hd cstr) (hd (tl cstr)))
  : ∃ clb albs' asub,
      stepStarTrace cstr [clb] (tl cstr) ∧
      stepStarTrace astr albs' asub ∧
      MatchLTSInfTrace a (tl cstr) asub ∧
      albs' ≠ [].
  Proof.
    pinversion MAT; subst.
    assert (CEQ : csub = tl cstr). { inversion CST; inversion CON; done. } subst.
    destruct (decide (albs' = [])).
    2: { do 3 eexists. split; [apply CST | split; [apply AST | split; [apply NXT | apply n]]]. }
    (* AST is empty: asub = astr, so NXT's CUR contradicts ADV. *)
    subst. assert (AEQ : asub = astr) by (inversion AST; reflexivity). rewrite AEQ in NXT.
    pinversion NXT; subst.
    exfalso. specialize (ADV (hd astr).1 (hd astr).2 [] (hd astr).2 CUR).
    rewrite app_nil_r in ADV. exact (ADV CUR0 CUR0).
  Qed.

  (* One-step unfold of the carried match: at the trace's next step,
     [MAT] either stutters (empty abstract chunk) or advances
     (non-empty chunk).  No stutter-possibility hypothesis is needed —
     the disjunction just reports which chunk [MAT] carries. *)
  Lemma ast_may_stt_effect
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
  : (∃ clb,
      stepStarTrace cstr [clb] (tl cstr) ∧
      MatchLTSInfTrace a (tl cstr) astr) ∨
    (∃ clb albs' asub,
      stepStarTrace cstr [clb] (tl cstr) ∧
      stepStarTrace astr albs' asub ∧
      MatchLTSInfTrace a (tl cstr) asub ∧
      albs' ≠ []).
  Proof.
    pinversion MAT; subst.
    assert (csub = tl cstr). { inversion CST; inversion CON; done. } subst.
    destruct (decide (albs' = [])); [left | right].
    - subst. inversion AST; subst. eexists. split; eassumption.
    - do 3 eexists. split; [apply CST | split; [apply AST | split; [apply NXT | apply n]]].
  Qed.

  (* Walk the carried match [MAT] across [n] concrete steps.  Either
     [MAT] stuttered through all [n] of them (left), or [MAT] advanced
     the abstract stream at one of the first [≤ n] steps (right).

     Like [ast_may_stt_effect], this takes no [¬ ast_advances]
     hypothesis (an earlier version carried one; it was semantically
     inert): [¬ ast_advances] at a step only says a stuttering
     refinement of that step EXISTS — it does not constrain the
     PARTICULAR coinductive match [MAT], whose per-step chunks are
     fixed data and may be non-empty at such a step.  The disjunction
     merely reports what [MAT] did.

     (For per-label length-deterministic relations — all instances of
     this development: EvReplLbRel, RWDepReplLbRel, lview_env_ref_rel —
     every match stutters wherever stuttering is possible, so under a
     stutter-run hypothesis the left disjunct would necessarily hold;
     the lemma does not need that fact.  Callers [mlit_ast_trace] and
     [mlit_ast_steps] hunt for a non-empty abstract advance, so for
     them the right side is the "found it early" shortcut.) *)
  Lemma ast_chunk_may_stt_effect
    a cstr astr n
    (MAT : MatchLTSInfTrace a cstr astr)
  : (∃ clbs',
      stepStarTrace cstr clbs' (Str_nth_tl n cstr) ∧
      MatchLTSInfTrace a (Str_nth_tl n cstr) astr ∧
      length clbs' = n) ∨
    (* [MAT] advanced voluntarily — see the header comment. *)
    (∃ clbs' csub albs' asub,
      stepStarTrace cstr clbs' csub ∧
      stepStarTrace astr albs' asub ∧
      MatchLTSInfTrace a csub asub ∧
      length clbs' ≤ n ∧ albs' ≠ []).
  Proof.
    induction n. { left. exists []. simpl. split; [constructor | eauto]. }
    destruct IHn as [H | H].
    - destruct H as (clbs' & CST & MAT' & N).
      destruct (ast_may_stt_effect _ _ _ MAT') as [H | H].
      + left. destruct H as (clb & CST' & MAT''). rewrite tl_nth_tl in *. simpl in *.
        exists (clbs' @@ clb). split.
        * eapply sst_trans; [apply CST | apply CST'].
        * split; [assumption | rewrite length_app; simpl; lia].
      + right. destruct H as (clb & albs' & asub & CST' & AST & MAT'' & NEM).
        rewrite tl_nth_tl in *.
        exists (clbs' @@ clb), (Str_nth_tl n (tl cstr)), albs', asub.
        split; [| split; [assumption |]].
        * eapply sst_trans; [apply CST | apply CST'].
        * split; [assumption | split; [rewrite length_app; simpl; lia | assumption]].
    - right. destruct H as (clbs' & csub & albs' & asub & CST & AST & MAT' & LEN & NEM).
      exists clbs', csub, albs', asub. split; [| split; [| split; [| split]]]; eauto.
  Qed.

  Definition finitely_stutter a (cstr : Stream (list CLb * CSt)) :=
    LTL.infinitely_often
      (λ csub, ast_advances a (hd csub) (hd (tl csub)))
      cstr.

  Lemma mlit_ast_trace
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
    (FST : finitely_stutter a cstr)
  : trace astr.
  Proof.
    specialize (mlit_cst_trace _ _ _ MAT) as CTR.
    split. { pinversion MAT; subst. apply MatchLTSTrace_lreachable in CUR. apply CUR. }
    apply LTL.always_n_equiv.
    generalize dependent astr; generalize dependent cstr.
    pcofix CIH. intros. pfold. apply LTL.unwrap_always in FST as FST'.
    apply LTL.eventually_first in FST'. destruct FST' as (n & _ & ADV).
    destruct (ast_chunk_may_stt_effect _ _ _ n MAT).
    - destruct H as (clbs' & CST & MAT' & LEN). specialize (ast_adv_effect _ _ _ MAT' ADV) as EFF.
      destruct EFF as (? & albs' & ? & ? & SST & MAT'' & ?).
      apply LTL.alwNGenCstr with (n := length albs').
      + intros CONT. apply nil_length_inv in CONT. contradiction.
      + eapply sst_adj_steps. apply SST.
      + right. apply sst_stepStar in SST as [??]. subst. eapply CIH; [| | apply MAT''].
        * eapply LTL.infoften_substream with (sup := cstr); [| apply FST].
          rewrite tl_nth_tl. apply LTL.substream_sub_tl_n, LTL.substream_tl.
        * eapply trace_tl, trace_substr; [apply LTL.substream_sub_tl_n, LTL.ssBase | apply CTR].
    - destruct H as (clbs' & csub  & albs' & asub &?& SST & MAT'' &?&?).
      apply LTL.alwNGenCstr with (n := length albs').
      + intros CONT. apply nil_length_inv in CONT. contradiction.
      + eapply sst_adj_steps. apply SST.
      + right. apply sst_stepStar in SST as [??]. subst. eapply CIH; [| | apply MAT''].
        * eapply LTL.infoften_substream with (sup := cstr); [by eapply sst_substream | apply FST].
        * eapply trace_substr; [eapply sst_substream, H | apply CTR].
  Qed.

  Lemma mlit_ast_steps
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
    (FST : finitely_stutter a cstr)
  : ∃ clbs' csub albs' asub,
      stepStarTrace cstr clbs' csub ∧
      stepStarTrace astr albs' asub ∧
      MatchLTSInfTrace a csub asub ∧
      albs' ≠ [].
  Proof.
    specialize (mlit_cst_trace _ _ _ MAT) as CTR. apply LTL.unwrap_always in FST as ADV.
    apply LTL.eventually_first in ADV as (n & _ & ADV).
    specialize (ast_chunk_may_stt_effect _ _ _ n MAT) as [EFF | EFF].
    - destruct EFF as (clbs' & CST & MAT' & ?). specialize (ast_adv_effect _ _ _ MAT' ADV)
      as (clb & albs' & asub & CST' & AST & MAT'' & ?).
      exists (clbs' @@ clb), (tl (Str_nth_tl n cstr)), albs', asub.
      split; [eapply sst_trans; eauto | split; [assumption | split]]; eauto.
    - destruct EFF as (? & ? & ? & ? & ? & ? & ? & ? & ?). do 4 eexists; eauto.
  Qed.

  Lemma mlit_ast_steps'
    a cstr astr
    (MAT : MatchLTSInfTrace a cstr astr)
    (FST : finitely_stutter a cstr)
  : ∀ n, ∃ clbs' csub albs' asub,
      stepStarTrace cstr clbs' csub ∧
      stepStarTrace astr albs' asub ∧
      MatchLTSInfTrace a csub asub ∧
      n ≤ length albs'.
  Proof.
    intros n. induction n.
    - do 4 eexists. split; [constructor | split]; [constructor | split];
      [apply MAT | done].
    - destruct IHn as (clbs' & cstr' & albs' & astr' & CSST & ASST & MAT' & LN).
      assert (FST': finitely_stutter a cstr'). { eapply LTL.infoften_substream with (sup := cstr);
       [eapply sst_substream, CSST | apply FST]. }
      specialize (mlit_ast_steps _ _ _ MAT' FST') as STPS.
      destruct STPS as (clbs'' & cstr'' & albs'' & astr'' & CSST' & ASST' & MAT'' & LN').
      exists (clbs' ++ clbs''), cstr'', (albs' ++ albs''), astr''.
      split; [| split; [| split]].
      + eapply sst_trans; [apply CSST | apply CSST'].
      + eapply sst_trans; [apply ASST | apply ASST'].
      + apply MAT''.
      + destruct albs''; [contradiction | rewrite length_app; simpl; lia].
  Qed.

  Lemma mlit_ast_substream
    a cstr astr asub
    (MAT : MatchLTSInfTrace a cstr astr)
    (SUB : LTL.substream astr asub)
    (FST : finitely_stutter a cstr)
  : ∃ asub' csub,
      MatchLTSInfTrace a csub asub' ∧
      LTL.substream cstr csub ∧
      LTL.substream asub asub'.
  Proof.
    specialize (mlit_ast_trace _ _ _ MAT FST) as ATR.
    destruct (substream_sst ATR SUB) as [albs' SST].
    specialize (mlit_ast_steps' a cstr astr MAT FST (length albs')) as STPS.
    destruct STPS as (clbs' & cstr' & albs'' & astr' & CSST & ASST & MAT' & LN).
    exists astr', cstr'. split; [apply MAT' | split].
    - eapply sst_substream, CSST.
    - specialize (sst_trunc SST ASST LN) as SST'. eapply sst_substream, SST'.
  Qed.

  Lemma mlit_always_implies_lower
    `(MAT : MatchLTSInfTrace a cstr astr)
    `(AAL : LTL.always AP astr)
    `(REL : ∀ cstr' astr', LTSStRel a (hd cstr').1 (hd cstr').2 (hd astr').1 (hd astr').2 → AP astr' → CP cstr')
  : LTL.always CP cstr.
  Proof.
    apply LTL.always_contra. intros CONT. apply LTL.eventually_exists in CONT as (csub & CSUB & CP').
    eapply mlit_cst_substream in CSUB as (asub & MAT' & ASUB). 2: { apply MAT. }
    pinversion MAT'; subst. apply MatchLTSTrace_LTSStRel in CUR.
    apply (LTL.always_substream _ _ _ ASUB), LTL.unwrap_always in AAL.
    specialize (REL _ _ CUR AAL). contradiction.
  Qed.

  (* Single concrete-step extension of a carried MatchLTSTrace.  Reuses
     `lts_refine_step` (available since the section context is
     `LTSRefInitStep`) and the `mchLTSTrSnoc` constructor.  This is the
     per-step engine the coinductive builder below relies on. *)
  Local Lemma lts_step_extend
    a clbs cst albs ast clb cst'
    (MCH : MatchLTSTrace a clbs cst albs ast)
    (STP : cst ~[ clb ]~> cst')
    (COND' : LTSCond a (clbs @@ clb) cst')
  : ∃ albs' ast',
      ast ~[ albs' ]~>* ast' ∧
      MatchLTSTrace a (clbs @@ clb) cst' (albs ++ albs') ast'.
  Proof.
    apply MatchLTSTrace_lreachable in MCH as RCH. destruct RCH as [RCHC RCHA].
    apply MatchLTSTrace_LTSStRel in MCH as STR.
    eapply lts_refine_step in STR as HH; try eassumption.
    specialize (HH _ _ STP COND').
    destruct HH as (albs' & ast' & STPS_A & LBR & STR').
    exists albs', ast'. split; [assumption |].
    econstructor; eassumption.
  Qed.

  (* Prepend a finite list of trace points before a stream. *)
  Fixpoint prepend {X} (l : list X) (s : Stream X) : Stream X :=
    match l with
    | [] => s
    | x :: xs => Cons x (prepend xs s)
    end.

  Lemma prepend_app {X} (l1 l2 : list X) (s : Stream X)
  : prepend (l1 ++ l2) s = prepend l1 (prepend l2 s).
  Proof. induction l1; [reflexivity | simpl; by rewrite IHl1]. Qed.

  (* Expand an abstract chunk `ast ~[albs']~>* ast'` (starting at abstract
     history `h`) into the `length albs'` stream points
       (h, ast), (h@@l0, a1), ..., (h++albs'\last, a_{k-1})
     (the current point plus the strict intermediates, EXCLUDING the final
     state ast').  Prepending them before any `rest` whose head is the
     final point (h++albs', ast') yields a `stepStarTrace` of `albs'`
     reaching `rest`.  Built via `lstepStar_cons` + choice so the points
     are a concrete (data) object usable by the stream builder.  The empty
     chunk yields the empty list (no new points; astr does not advance). *)
  Lemma expand_block
    (h : list ALb) (ast : ASt) (albs' : list ALb) (ast' : ASt)
    (STPS : ast ~[ albs' ]~>* ast')
  : ∃ pts : list (list ALb * ASt),
      length pts = length albs' ∧
      (albs' ≠ [] → pts = (h, ast) :: tail pts) ∧
      ∀ rest : Stream (list ALb * ASt),
        (hd rest).1 = h ++ albs' →
        (hd rest).2 = ast' →
        stepStarTrace (prepend pts rest) albs' rest.
  Proof.
    generalize dependent ast. generalize dependent h.
    induction albs' as [| lb albs'' IH]; intros h ast STPS.
    - exists []. split; [reflexivity | split; [intros C; contradiction |]].
      intros rest HD1 HD2. inversion STPS; subst. simpl. constructor.
    - apply lstepStar_cons in STPS as (asti & STP1 & STPS2).
      specialize (IH (h @@ lb) asti STPS2) as (pts & LEN & SHP & HH).
      exists ((h, ast) :: pts). split; [simpl; by rewrite LEN |].
      split; [intros _; reflexivity |].
      intros rest HD1 HD2. simpl.
      eapply prefLbsCons with (preStr := prepend pts rest).
      + destruct (decide (albs'' = [])) as [E | NE].
        * subst albs''. apply length_zero_iff_nil in LEN. subst pts.
          simpl. split; [exact HD1 |].
          rewrite HD2. inversion STPS2; subst. apply STP1.
        * rewrite (SHP NE). simpl. split; [reflexivity | apply STP1].
      + apply HH; [| assumption]. rewrite HD1. by rewrite <- app_assoc.
  Qed.

  (* Deterministic (proof-irrelevant, via Hilbert's `Ax.epsilon`) choices used
     to build the abstract stream.  `Ax.epsilon i P` depends only on the
     predicate `P`, so the resulting abstract stream `inf_astr` below is a
     pure function of the concrete data `(cs, albs, ast)` — this is what
     makes the per-step "stutter equality" (`inf_astr` ignores a leading
     stuttering concrete step) provable. *)

  (* The abstract chunk emitted for the FIRST step of `cs`, carried abstract
     state `(albs, ast)`.  Its defining property (existence from
     `lts_step_extend`) is that it makes the carried MatchLTSTrace advance to
     the next concrete point. *)
  Definition pick_chunk a (cs : Stream (list CLb * CSt))
    (albs : list ALb) (ast : ASt) : list ALb * ASt :=
    Ax.epsilon (inhabits ([], ast)) (λ p,
      ast ~[ p.1 ]~>* p.2 ∧
      MatchLTSTrace a (hd (tl cs)).1 (hd (tl cs)).2 (albs ++ p.1) p.2).

  (* The `length (chunk).1` stream points realizing that chunk as a
     `stepStarTrace` segment (from `expand_block`); empty iff the chunk is
     empty (a stutter). *)
  Definition pick_pts a (cs : Stream (list CLb * CSt))
    (albs : list ALb) (ast : ASt) : list (list ALb * ASt) :=
    Ax.epsilon (inhabits []) (λ pts,
      length pts = length (pick_chunk a cs albs ast).1 ∧
      ((pick_chunk a cs albs ast).1 ≠ [] → pts = (albs, ast) :: tail pts) ∧
      ∀ rest : Stream (list ALb * ASt),
        (hd rest).1 = albs ++ (pick_chunk a cs albs ast).1 →
        (hd rest).2 = (pick_chunk a cs albs ast).2 →
        stepStarTrace (prepend pts rest) (pick_chunk a cs albs ast).1 rest).

  (* `adv … n`: the abstract layer advances (non-empty chunk) at concrete
     distance `n`, with the carried abstract state UNCHANGED (stutters do not
     change it).  `least_adv` is the least such `n` (arbitrary nat if the
     layer stutters forever — then every chunk, hence `pick_pts`, is empty,
     and `inf_astr` falls into the constant branch regardless). *)
  Definition adv a (cs : Stream (list CLb * CSt))
    (albs : list ALb) (ast : ASt) (n : nat) : Prop :=
    (pick_chunk a (Str_nth_tl n cs) albs ast).1 ≠ [].

  Definition least_adv a (cs : Stream (list CLb * CSt))
    (albs : list ALb) (ast : ASt) : nat :=
    Ax.epsilon (inhabits 0) (λ n,
      adv a cs albs ast n ∧ ∀ m, m < n → ¬ adv a cs albs ast m).

  (* The abstract stream, emitting one point per corecursive call so the
     recursive call sits *directly* under `Cons` (guardedness).  `pending`
     carries the not-yet-emitted points of the current block; when it runs
     out, the next block is computed: skip the leading stutter run (to
     `Str_nth_tl (least_adv …) cs`) and emit that advancing chunk's points.
     `pick_pts … = []` (no further advance) yields the constant stream. *)
  CoFixpoint emit_block a (pending : list (list ALb * ASt))
    (cs : Stream (list CLb * CSt)) (albs : list ALb) (ast : ASt)
    : Stream (list ALb * ASt) :=
    match pending with
    | p :: ps => Cons p (emit_block a ps cs albs ast)
    | [] =>
        let csn := Str_nth_tl (least_adv a cs albs ast) cs in
        match pick_pts a csn albs ast with
        | [] => Streams.const (albs, ast)
        | q :: qs =>
            Cons q (emit_block a qs (tl csn)
              (albs ++ (pick_chunk a csn albs ast).1)
              (pick_chunk a csn albs ast).2)
        end
    end.

  Definition inf_astr a (cs : Stream (list CLb * CSt))
    (albs : list ALb) (ast : ASt) : Stream (list ALb * ASt) :=
    emit_block a [] cs albs ast.

  (* The carried-match invariant maintained along the concrete trace: at
     concrete stream `cs`, the abstract state `(albs, ast)` matches. *)
  Definition inv a (cs : Stream (list CLb * CSt))
    (albs : list ALb) (ast : ASt) : Prop :=
    trace cs ∧
    LTL.always (λ csub, LTSCond a (hd csub).1 (hd csub).2) cs ∧
    MatchLTSTrace a (hd cs).1 (hd cs).2 albs ast.

  (* The chunk's defining property exists whenever the invariant holds. *)
  Local Lemma pick_chunk_exists a cs albs ast
    (INV : inv a cs albs ast)
  : ∃ p : list ALb * ASt,
      ast ~[ p.1 ]~>* p.2 ∧
      MatchLTSTrace a (hd (tl cs)).1 (hd (tl cs)).2 (albs ++ p.1) p.2.
  Proof.
    destruct INV as (TR & CO & MCH). destruct TR as [_ ADJ].
    apply LTL.unwrap_always in ADJ as STP. simpl in STP.
    destruct STP as (clb & HEQ & STP).
    apply (LTL.always_substream _ cs (tl cs) (LTL.substream_tl cs)) in CO.
    apply LTL.unwrap_always in CO as COND'. simpl in COND'.
    eapply lts_step_extend in MCH as HH; [| apply STP | rewrite <- HEQ; apply COND'].
    destruct HH as (albs' & ast' & STPS & MCH'). exists (albs', ast'). simpl.
    split; [apply STPS |]. rewrite HEQ. apply MCH'.
  Qed.

  Local Lemma pick_chunk_spec a cs albs ast
    (INV : inv a cs albs ast)
  : ast ~[ (pick_chunk a cs albs ast).1 ]~>* (pick_chunk a cs albs ast).2 ∧
    MatchLTSTrace a (hd (tl cs)).1 (hd (tl cs)).2
      (albs ++ (pick_chunk a cs albs ast).1) (pick_chunk a cs albs ast).2.
  Proof.
    unfold pick_chunk.
    apply (Ax.epsilon_spec (inhabits ([], ast))
      (λ p, ast ~[ p.1 ]~>* p.2 ∧
            MatchLTSTrace a (hd (tl cs)).1 (hd (tl cs)).2 (albs ++ p.1) p.2)).
    by apply pick_chunk_exists.
  Qed.

  Local Lemma pick_pts_spec a cs albs ast
    (INV : inv a cs albs ast)
  : length (pick_pts a cs albs ast) = length (pick_chunk a cs albs ast).1 ∧
    ((pick_chunk a cs albs ast).1 ≠ [] →
       pick_pts a cs albs ast = (albs, ast) :: tail (pick_pts a cs albs ast)) ∧
    ∀ rest : Stream (list ALb * ASt),
      (hd rest).1 = albs ++ (pick_chunk a cs albs ast).1 →
      (hd rest).2 = (pick_chunk a cs albs ast).2 →
      stepStarTrace (prepend (pick_pts a cs albs ast) rest)
        (pick_chunk a cs albs ast).1 rest.
  Proof.
    unfold pick_pts.
    apply (Ax.epsilon_spec (inhabits [])
      (λ pts, length pts = length (pick_chunk a cs albs ast).1 ∧
        ((pick_chunk a cs albs ast).1 ≠ [] → pts = (albs, ast) :: tail pts) ∧
        ∀ rest, (hd rest).1 = albs ++ (pick_chunk a cs albs ast).1 →
          (hd rest).2 = (pick_chunk a cs albs ast).2 →
          stepStarTrace (prepend pts rest) (pick_chunk a cs albs ast).1 rest)).
    destruct (pick_chunk_spec a cs albs ast INV) as [STPS _].
    destruct (expand_block albs ast (pick_chunk a cs albs ast).1
                (pick_chunk a cs albs ast).2 STPS) as (pts & LEN & SHP & HH).
    exists pts. split; [apply LEN | split; [apply SHP | apply HH]].
  Qed.

  Local Lemma adv_dec a cs albs ast n : adv a cs albs ast n ∨ ¬ adv a cs albs ast n.
  Proof. unfold adv. destruct (decide ((pick_chunk a (Str_nth_tl n cs) albs ast).1 = [])); auto. Qed.

  (* When the abstract layer advances somewhere, `least_adv` is the FIRST
     such distance.  (`Ax.epsilon` is fed the least-element predicate, whose
     satisfiability comes from `dec_inh_nat_subset_has_unique_least_element`.) *)
  Local Lemma least_adv_spec a cs albs ast
    (EX : ∃ n, adv a cs albs ast n)
  : adv a cs albs ast (least_adv a cs albs ast) ∧
    ∀ m, m < least_adv a cs albs ast → ¬ adv a cs albs ast m.
  Proof.
    unfold least_adv.
    apply (Ax.epsilon_spec (inhabits 0)
      (λ n, adv a cs albs ast n ∧ ∀ m, m < n → ¬ adv a cs albs ast m)).
    destruct (dec_inh_nat_subset_has_unique_least_element
                (adv a cs albs ast) (adv_dec a cs albs ast) EX) as (y & (PY & LE) & _).
    exists y. split; [exact PY |]. intros m LT CONT. specialize (LE m CONT). lia.
  Qed.

  (* The invariant survives an immediate stutter step. *)
  Local Lemma inv_stutter_tl a cs albs ast
    (INV : inv a cs albs ast)
    (EMP : (pick_chunk a cs albs ast).1 = [])
  : inv a (tl cs) albs ast.
  Proof.
    destruct (pick_chunk_spec a cs albs ast INV) as [STPS MCH].
    rewrite EMP in STPS, MCH. inversion STPS; subst.
    rewrite app_nil_r in MCH. destruct INV as (TR & CO & _).
    split; [apply trace_tl, TR | split; [| apply MCH]].
    eapply (LTL.always_substream _ cs (tl cs) (LTL.substream_tl cs)), CO.
  Qed.

  (* The invariant survives a whole stutter run (the first `n` chunks empty). *)
  Local Lemma inv_skip a cs albs ast n
    (INV : inv a cs albs ast)
    (STT : ∀ m, m < n → (pick_chunk a (Str_nth_tl m cs) albs ast).1 = [])
  : inv a (Str_nth_tl n cs) albs ast.
  Proof.
    induction n; [apply INV |].
    assert (INVn : inv a (Str_nth_tl n cs) albs ast).
    { apply IHn. intros m LT. apply STT. lia. }
    replace (Str_nth_tl (S n) cs) with (tl (Str_nth_tl n cs))
      by (rewrite tl_nth_tl; reflexivity).
    eapply inv_stutter_tl; [apply INVn |]. apply STT. lia.
  Qed.

  (* An empty chunk gives no points (independently of the invariant — needed
     for the no-advance/constant case). *)
  Local Lemma pick_pts_empty a cs albs ast
    (EMP : (pick_chunk a cs albs ast).1 = [])
  : pick_pts a cs albs ast = [].
  Proof.
    apply length_zero_iff_nil.
    assert (HL : length (pick_pts a cs albs ast)
                 = length (pick_chunk a cs albs ast).1).
    { unfold pick_pts.
      apply (Ax.epsilon_spec (inhabits [])
        (λ pts, length pts = length (pick_chunk a cs albs ast).1 ∧
          ((pick_chunk a cs albs ast).1 ≠ [] → pts = (albs, ast) :: tail pts) ∧
          ∀ rest, (hd rest).1 = albs ++ (pick_chunk a cs albs ast).1 →
            (hd rest).2 = (pick_chunk a cs albs ast).2 →
            stepStarTrace (prepend pts rest) (pick_chunk a cs albs ast).1 rest)).
      exists []. rewrite EMP. split; [reflexivity | split; [done |]].
      intros rest _ _. simpl. constructor. }
    rewrite HL, EMP. reflexivity.
  Qed.

  (* The carried point heads the abstract stream. *)
  Local Lemma inf_astr_hd a cs albs ast
    (INV : inv a cs albs ast)
  : hd (inf_astr a cs albs ast) = (albs, ast).
  Proof.
    unfold inf_astr. rewrite (unfold_Stream (emit_block a [] cs albs ast)).
    cbn [emit_block]. set (csn := Str_nth_tl (least_adv a cs albs ast) cs).
    destruct (Ax.excluded_middle_informative (∃ n, adv a cs albs ast n)) as [EX | NEX].
    - destruct (least_adv_spec a cs albs ast EX) as [ADV LST].
      assert (INVn : inv a csn albs ast).
      { apply inv_skip; [apply INV |]. intros m LT.
        specialize (LST m LT). unfold adv in LST. by apply Ax.NNPP in LST. }
      destruct (pick_pts_spec a csn albs ast INVn) as (LEN & SHP & _).
      unfold adv in ADV. fold csn in ADV. rewrite (SHP ADV). reflexivity.
    - assert (EMP : (pick_chunk a csn albs ast).1 = []).
      { apply Ax.NNPP. intros C. apply NEX. exists (least_adv a cs albs ast). apply C. }
      rewrite (pick_pts_empty a csn albs ast EMP). reflexivity.
  Qed.

  (* `emit_block` just flushes `pending` before continuing as the fresh
     stream from `(cs, albs, ast)`. *)
  Local Lemma emit_block_prepend a pending cs albs ast
  : emit_block a pending cs albs ast
    = prepend pending (emit_block a [] cs albs ast).
  Proof.
    induction pending as [| p ps IH]; [reflexivity |].
    rewrite (unfold_Stream (emit_block a (p :: ps) cs albs ast)).
    cbn [emit_block]. simpl. by rewrite IH.
  Qed.

  (* The first advancing position is the same from `cs` and from `tl cs`,
     when the first step is a stutter and the layer advances eventually. *)
  Local Lemma csn_stutter a cs albs ast
    (EMP : (pick_chunk a cs albs ast).1 = [])
    (EX : ∃ n, adv a cs albs ast n)
  : Str_nth_tl (least_adv a cs albs ast) cs
    = Str_nth_tl (least_adv a (tl cs) albs ast) (tl cs).
  Proof.
    assert (EMP0 : ¬ adv a cs albs ast 0).
    { unfold adv. cbn [Str_nth_tl]. rewrite EMP. intros C; by apply C. }
    assert (SHIFT : ∀ m, adv a (tl cs) albs ast m ↔ adv a cs albs ast (S m)).
    { intros m. unfold adv. cbn [Str_nth_tl]. reflexivity. }
    assert (EX' : ∃ n, adv a (tl cs) albs ast n).
    { destruct EX as [n Hn]. destruct n; [contradiction |].
      exists n. by apply SHIFT. }
    destruct (least_adv_spec a cs albs ast EX) as [ADVL LSTL].
    destruct (least_adv_spec a (tl cs) albs ast EX') as [ADVL' LSTL'].
    set (L := least_adv a cs albs ast) in *.
    set (L' := least_adv a (tl cs) albs ast) in *.
    assert (Lpos : L ≠ 0). { intros C. apply EMP0. by rewrite <- C. }
    assert (E1 : L' ≤ L - 1).
    { apply Nat.nlt_ge. intros LT. eapply LSTL'; [apply LT |].
      apply SHIFT. replace (S (L - 1)) with L by lia. apply ADVL. }
    assert (E2 : L ≤ S L').
    { apply Nat.nlt_ge. intros LT. eapply LSTL; [apply LT |]. by apply SHIFT. }
    assert (LEQ : L = S L') by lia. rewrite LEQ. cbn [Str_nth_tl]. reflexivity.
  Qed.

  (* No future advance ⇒ the abstract stream is constant. *)
  Local Lemma inf_astr_noadv a cs albs ast
    (NEX : ¬ ∃ n, adv a cs albs ast n)
  : inf_astr a cs albs ast = Streams.const (albs, ast).
  Proof.
    unfold inf_astr. rewrite (unfold_Stream (emit_block a [] cs albs ast)).
    cbn [emit_block].
    assert (EMPn : (pick_chunk a (Str_nth_tl (least_adv a cs albs ast) cs)
                      albs ast).1 = []).
    { apply Ax.NNPP. intros C. apply NEX. eauto. }
    rewrite (pick_pts_empty a _ albs ast EMPn).
    rewrite (unfold_Stream (Streams.const (albs, ast))). reflexivity.
  Qed.

  Local Lemma noadv_tl a cs albs ast
    (NEX : ¬ ∃ n, adv a cs albs ast n)
  : ¬ ∃ n, adv a (tl cs) albs ast n.
  Proof.
    intros [n Hn]. apply NEX. exists (S n). unfold adv in *.
    cbn [Str_nth_tl]. exact Hn.
  Qed.

  (* One-concrete-step unfolding of the abstract stream.

     - An immediate STUTTER (empty chunk) leaves the abstract stream
       unchanged (it advances only with the next non-empty chunk, which is
       at the same stream position whether measured from `cs` or `tl cs`).
     - An immediate ADVANCE prepends exactly this chunk's points before the
       stream resumed from the post-chunk config at `tl cs`. *)
  Local Lemma inf_astr_step a cs albs ast
    (INV : inv a cs albs ast)
  : ((pick_chunk a cs albs ast).1 = [] ∧
       inf_astr a cs albs ast = inf_astr a (tl cs) albs ast)
  ∨ ((pick_chunk a cs albs ast).1 ≠ [] ∧
       inf_astr a cs albs ast
       = prepend (pick_pts a cs albs ast)
           (inf_astr a (tl cs)
              (albs ++ (pick_chunk a cs albs ast).1)
              (pick_chunk a cs albs ast).2)).
  Proof.
    destruct (decide ((pick_chunk a cs albs ast).1 = [])) as [EMP | NE].
    - left. split; [exact EMP |].
      destruct (Ax.excluded_middle_informative (∃ n, adv a cs albs ast n)) as [EX | NEX].
      + (* both sides flush their (equal) first advancing block *)
        unfold inf_astr.
        rewrite (unfold_Stream (emit_block a [] cs albs ast)).
        rewrite (unfold_Stream (emit_block a [] (tl cs) albs ast)).
        cbn [emit_block].
        rewrite (csn_stutter a cs albs ast EMP EX). reflexivity.
      + (* infinite stutter from both: constant stream *)
        rewrite (inf_astr_noadv a cs albs ast NEX).
        rewrite (inf_astr_noadv a (tl cs) albs ast (noadv_tl a cs albs ast NEX)).
        reflexivity.
    - right. split; [exact NE |].
      (* immediate advance: least_adv = 0 *)
      assert (EX : ∃ n, adv a cs albs ast n).
      { exists 0. unfold adv. cbn [Str_nth_tl]. exact NE. }
      destruct (least_adv_spec a cs albs ast EX) as [_ LST].
      assert (L0 : least_adv a cs albs ast = 0).
      { destruct (least_adv a cs albs ast) eqn:E; [reflexivity |].
        exfalso. eapply (LST 0); [lia |]. unfold adv. cbn [Str_nth_tl]. exact NE. }
      destruct (pick_pts_spec a cs albs ast INV) as (LEN & _ & _).
      unfold inf_astr.
      rewrite (unfold_Stream (emit_block a [] cs albs ast)). cbn [emit_block].
      rewrite L0. cbn [Str_nth_tl].
      destruct (pick_pts a cs albs ast) as [| q qs] eqn:EP.
      { exfalso. simpl in LEN.
        symmetry in LEN. apply length_zero_iff_nil in LEN. by apply NE. }
      simpl. by rewrite emit_block_prepend.
  Qed.

  (* Package the trace's next adjacency as a one-label `stepStarTrace`. *)
  Local Lemma trace_one_step_sst a cs albs ast
    (INV : inv a cs albs ast)
  : ∃ clb, stepStarTrace cs [clb] (tl cs).
  Proof.
    destruct INV as ([_ ADJ] & _). apply LTL.unwrap_always in ADJ as STP.
    simpl in STP. destruct STP as (clb & HEQ & STP). exists clb.
    destruct cs as [hc tc]. simpl in *.
    eapply prefLbsCons; [split; eassumption | constructor].
  Qed.

  (* The carried-match invariant survives a non-empty (advancing) chunk. *)
  Local Lemma inv_adv_tl a cs albs ast
    (INV : inv a cs albs ast)
  : inv a (tl cs) (albs ++ (pick_chunk a cs albs ast).1) (pick_chunk a cs albs ast).2.
  Proof.
    destruct (pick_chunk_spec a cs albs ast INV) as [_ MCH].
    destruct INV as (TR & CO & _). split; [apply trace_tl, TR | split; [| apply MCH]].
    eapply (LTL.always_substream _ cs (tl cs) (LTL.substream_tl cs)), CO.
  Qed.

  (* `inf_astr` realizes the infinite-trace refinement: by paco3
     coinduction, peeling one concrete step at a time.  A stutter step
     keeps the same abstract stream (empty abstract chunk); an advancing
     step consumes exactly `inf_astr`'s leading block. *)
  Local Lemma inf_astr_correct a cs albs ast
    (INV : inv a cs albs ast)
  : MatchLTSInfTrace a cs (inf_astr a cs albs ast).
  Proof.
    revert cs albs ast INV. pcofix CIH. intros cs albs ast INV. pfold.
    destruct (trace_one_step_sst a cs albs ast INV) as [clb CST].
    assert (CUR : MatchLTSTrace a (hd cs).1 (hd cs).2
                    (hd (inf_astr a cs albs ast)).1 (hd (inf_astr a cs albs ast)).2).
    { rewrite (inf_astr_hd a cs albs ast INV). simpl. by destruct INV as (_ & _ & ?). }
    destruct (inf_astr_step a cs albs ast INV) as [(EMP & EQ) | (NE & EQ)].
    - (* stutter *)
      eapply mchLTSStrGenCstr with (clb' := clb) (albs' := [])
        (csub := tl cs) (asub := inf_astr a cs albs ast).
      + apply CUR.
      + apply CST.
      + constructor.
      + right. rewrite EQ. apply CIH. eapply inv_stutter_tl; eassumption.
    - (* advance *)
      eapply mchLTSStrGenCstr with (clb' := clb)
        (albs' := (pick_chunk a cs albs ast).1)
        (csub := tl cs)
        (asub := inf_astr a (tl cs)
                   (albs ++ (pick_chunk a cs albs ast).1)
                   (pick_chunk a cs albs ast).2).
      + apply CUR.
      + apply CST.
      + rewrite EQ.
        destruct (pick_pts_spec a cs albs ast INV) as (_ & _ & SST).
        apply SST.
        * rewrite (inf_astr_hd a (tl cs) _ _ (inv_adv_tl a cs albs ast INV)).
          reflexivity.
        * rewrite (inf_astr_hd a (tl cs) _ _ (inv_adv_tl a cs albs ast INV)).
          reflexivity.
      + right. apply CIH. apply inv_adv_tl, INV.
  Qed.

  (* ------------------------------------------------------------------
     Infinite-trace refinement CONSTRUCTOR.

     The companion to `mlit_always_implies_lower`: that lemma *consumes* a
     MatchLTSInfTrace (pushing abstract `always`-facts down to the
     concrete trace); this one *produces* one.  Given the finite
     refinement (LTSRef, in context) and an infinite concrete trace, every
     concrete execution has a matching abstract stream.

     This is the single piece of liveness-refinement infrastructure the
     convergence bridge (protocols/proofs/.../Fairness.v) needs and that
     LTSRefInitStep / LTSRef do not yet provide.

     `finitely_stutter` is deliberately NOT concluded here: non-Zeno-ness
     of the abstract layer is an application-level fact (it follows from
     the concrete system taking infinitely many abstract-advancing steps),
     so it is supplied separately by callers. *)
  Lemma lts_ref_inf_trace
    a (cstr : Stream (list CLb * CSt))
    (CTR : trace cstr)
    (COND : LTL.always (λ csub, LTSCond a (hd csub).1 (hd csub).2) cstr)
  : ∃ astr, MatchLTSInfTrace a cstr astr.
  Proof.
    (* Base point: `lts_refines` matches the reachable prefix `hd cstr`;
       then `inf_astr_correct` extends it coinductively over the trace. *)
    pose proof CTR as [RCH ADJ].
    apply LTL.unwrap_always in COND as COND0. simpl in COND0.
    edestruct (lts_refines (LTSRef := @LTSRefInitStep_LTSRef _ _ _ _ _ _ _ RIS)
                 a RCH COND0)
      as (albs0 & ast0 & MCH0).
    exists (inf_astr a cstr albs0 ast0).
    apply inf_astr_correct. split; [apply CTR | split; [apply COND | apply MCH0]].
  Qed.

End REFINE_PROPS.
