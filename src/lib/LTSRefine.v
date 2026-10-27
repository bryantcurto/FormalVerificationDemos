Set Implicit Arguments.

From refinement.lib Require Export
     Prelude
     TransSystem.

Section LTS_REFINE.

  Context (CSt ASt : Type) {CLb ALb : Type}.
  Context {A : Type}.

  Class LTSRefRel `{LTSParams CSt CLb,LTSParams ASt ALb} : Type := mkLTSRefRel {
    (* Do the states (and traces producing the states) correspond? *)
    LTSStRel (a : A) : list CLb -> CSt -> list ALb -> ASt -> Prop;
    (* Do the labels correspond? *)
    LTSLbRel (a : A) (clbs : list CLb) (cst : CSt) (albs : list ALb) (ast : ASt)
    : CLb -> list ALb -> Prop;
    (* Restrict the executions under inspection to those satisfying condition at each step.
       TODO: Remove this eventually. It is only used to system-view to client-view refinement, but
       there is a better approach to prove that refinement. When there's time, come up with a
       better approach to analizing restricted executions. *)
    LTSCond (a : A) : list CLb -> CSt -> Prop;
  }.

  Context {LTSPC : LTSParams CSt CLb} {LTSPA : LTSParams ASt ALb}.

  Section REF_INIT_STEP.

    Context `{REFR : LTSRefRel}.

    Definition LTSRefineInit : Prop :=
      ∀ (cst : CSt)
        (CON_INIT : init cst)
        `(COND : LTSCond a [] cst),
        ∃ (ast : ASt),
          init ast /\
          LTSStRel a [] cst [] ast.

    Definition LTSRefineStep : Prop :=
      ∀ (cst : CSt) (ast : ASt)
        `(CON_RCH : lreachable clbs cst)
        `(ABS_RCH : lreachable albs ast)
        `(ST_REL : LTSStRel a clbs cst albs ast)
        `(CON_STP : cst ~[ clb ]~> cst')
        `(COND' : LTSCond a (clbs @@ clb) cst'),
        ∃ albs' ast',
          ast ~[ albs' ]~>* ast' /\
          LTSLbRel a clbs cst albs ast clb albs' /\
          LTSStRel a (clbs @@ clb) cst' (albs ++ albs') ast'.

    Definition LTSStepCond : Prop :=
      ∀ (cst : CSt)
        `(CON_RCH : lreachable clbs cst)
        `(CON_STP : cst ~[ clb ]~> cst')
        `(COND' : LTSCond a (clbs @@ clb) cst'),
        LTSCond a clbs cst.

  End REF_INIT_STEP.

  Class LTSRefStep : Type := {
    ltsRefStepRel :: LTSRefRel;
    lts_refine_step : LTSRefineStep;
  }.

  Class LTSRefInitStep : Type := {
    ltsRefInitStep :: LTSRefStep;
    lts_refine_init : LTSRefineInit;
    lts_step_cond : LTSStepCond;
  }.

  Section REF.

    Context `{REFR : LTSRefRel}.

    Inductive MatchLTSTrace : A -> list CLb -> CSt -> list ALb -> ASt -> Prop :=
    | mchLTSTrNil
        `(STR : LTSStRel a [] cst [] ast)
        (RCHC : init cst)
        (RCHA : init ast)
      : MatchLTSTrace a [] cst [] ast
    | mchLTSTrSnoc
        `(MCH : MatchLTSTrace a clbs cst albs ast)
        `(STP_C : cst ~[ clb ]~> cst')
        `(STPS_A : ast ~[ albs' ]~>* ast')
        (LBR : LTSLbRel a clbs cst albs ast clb albs')
        (STR : LTSStRel a (clbs @@ clb) cst' (albs ++ albs') ast')
      : MatchLTSTrace a (clbs @@ clb) cst' (albs ++ albs') ast'.

    Inductive MatchLTSSubTrace
    : A -> list CLb -> CSt -> list ALb -> ASt ->
           list CLb -> CSt -> list ALb -> ASt -> Prop :=
    | mchLTSSbTrNil
        `(STR : LTSStRel a iclbs cst ialbs ast)
        (RCHC : lreachable iclbs cst)
        (RCHA : lreachable ialbs ast)
      : MatchLTSSubTrace a iclbs cst ialbs ast [] cst [] ast
    | mchLTSSbTrSnoc
        `(MCH : MatchLTSSubTrace a iclbs icst ialbs iast clbs cst albs ast)
        `(STP_C : cst ~[ clb' ]~> cst')
        `(STPS_A : ast ~[ albs' ]~>* ast')
        (LBR : LTSLbRel a (iclbs ++ clbs) cst (ialbs ++ albs) ast clb' albs')
        (STR : LTSStRel a (iclbs ++ clbs @@ clb') cst' (ialbs ++ albs ++ albs') ast')
      : MatchLTSSubTrace a iclbs icst ialbs iast (clbs @@ clb') cst' (albs ++ albs') ast'.

    Definition LTSRefines : Prop :=
      ∀ clbs cst a
        (RCH : lreachable clbs cst)
        (COND : LTSCond a clbs cst),
        ∃ albs ast,
          MatchLTSTrace a clbs cst albs ast.

  End REF.

  Class LTSRef : Type := mkLTSRef {
    ltsRefRel :: LTSRefRel;
    lts_refines : LTSRefines;
  }.

  Section REF_REL_LEMMAS.

    Context `{REFR : LTSRefRel}.

    Lemma MatchLTSTrace_lreachable
      `(MCH : MatchLTSTrace a clbs cst albs ast)
    : lreachable clbs cst /\
      lreachable albs ast.
    Proof.
      induction MCH; subst.
      - split; econstructor; eassumption || econstructor.
      - destruct IHMCH as [IH1 IH2].
        inversion IH1; inversion IH2; subst. split; econstructor;
        try eapply lstepStar_snoc_1; try eapply lstepStar_app_1; eassumption.
    Qed.

    Lemma MatchLTSTrace_LTSStRel
      `(MCH : MatchLTSTrace a clbs cst albs ast)
    : LTSStRel a clbs cst albs ast.
    Proof. inversion MCH; eassumption. Qed.

    Lemma MatchLTSSubTrace_lreachable
      `(SMCH : MatchLTSSubTrace a iclbs icst ialbs iast clbs cst albs ast)
    : lreachable (iclbs ++ clbs) cst /\
      lreachable (ialbs ++ albs) ast.
    Proof.
      induction SMCH.
      - rewrite !app_nil_r in *; split; eassumption.
      - destruct IHSMCH; split; try eassumption; rewrite app_assoc;
        eapply lreachable_snoc_1 || eapply lreachable_app_1; eassumption.
    Qed.

    Lemma MatchLTSSubTrace_lreachable'
      `(SMCH : MatchLTSSubTrace a iclbs icst ialbs iast clbs cst albs ast)
    : lreachable iclbs icst /\
      lreachable ialbs iast.
    Proof.
      induction SMCH; eassumption || (split; eassumption).
    Qed.

    Lemma MatchLTSSubTrace_LTSStRel
      `(SMCH : MatchLTSSubTrace a iclbs icst ialbs iast clbs cst albs ast)
    : LTSStRel a (iclbs ++ clbs) cst (ialbs ++ albs) ast.
    Proof.
      inversion SMCH; subst; rewrite ?app_nil_r; eassumption.
    Qed.

    Lemma MatchLTSSubTrace_LTSStRel'
      `(SMCH : MatchLTSSubTrace a iclbs icst ialbs iast clbs cst albs ast)
    : LTSStRel a iclbs icst ialbs iast.
    Proof.
      induction SMCH; subst; eassumption.
    Qed.

  End REF_REL_LEMMAS.

  #[global] Instance LTSRefInitStep_LTSRef `{LTSRefInitStep} : LTSRef.
  Proof.
    econstructor. intros ? **. induction RCH using lreachable_snoc_ind.
    - apply lts_refine_init in COND as HH; try eassumption. destruct HH as (? & ? & ?).
      eexists [], _. constructor; eassumption.
    - eapply lts_step_cond in COND as COND'; try eassumption.
      specialize (IHRCH1 COND') as (? & ? & MCH).
      eapply MatchLTSTrace_lreachable in MCH as HH; destruct HH as (? & ?).
      apply MatchLTSTrace_LTSStRel in MCH as ST_REL.
      eapply lts_refine_step in COND as HH; try eassumption; destruct HH as (? & ? & ? & ? & ?).
      repeat eexists. econstructor; eassumption.
  Defined.

  Section STEP_LEMMAS.

    Context `{LTSRefInitStep}.

    Lemma lts_refine_steps
      (cst : CSt) (ast : ASt)
      `(CON_RCH : lreachable clbs cst)
      `(ABS_RCH : lreachable albs ast)
      `(ST_REL : LTSStRel a clbs cst albs ast)
      `(CON_STP : cst ~[ clbs' ]~>* cst')
      `(COND' : LTSCond a (clbs ++ clbs') cst')
    : ∃ albs' ast',
        ast ~[ albs' ]~>* ast' /\
        MatchLTSSubTrace a clbs cst albs ast clbs' cst' albs' ast'.
    Proof.
      induction CON_STP using lstepStar_snoc_ind.
      - rewrite app_nil_r in *.
        eexists [], _. split; econstructor; eassumption.
      - rewrite app_assoc in COND'; eapply lts_step_cond in COND' as COND;
        try eapply lreachable_app_1; try eassumption.
        specialize (IHCON_STP COND) as (? & ? & ? & MCH).
        eapply MatchLTSSubTrace_lreachable in MCH as HH; destruct HH as (? & ?);
        eapply MatchLTSSubTrace_LTSStRel in MCH as ?.
        eapply lts_refine_step in STP as HH; try eassumption.
        specialize (HH COND') as (? & ? & ? & ? & ?).
        eexists (_ ++ _),_; split; [ eapply lstepStar_app_1; eassumption |].
        econstructor; rewrite <-!app_assoc in *; eassumption.
    Qed.

  End STEP_LEMMAS.

  Section REF_LEMMAS.

    Context `{REF : LTSRef}.

    Lemma MatchLTSTrace_merge
      `(MCH : MatchLTSTrace a clbs cst albs ast)
      `(SMCH : MatchLTSSubTrace a clbs cst albs ast clbs' cst' albs' ast')
    : MatchLTSTrace a (clbs ++ clbs') cst' (albs ++ albs') ast'.
    Proof.
      induction SMCH.
      - rewrite !app_nil_r; eassumption.
      - specialize (IHSMCH MCH).
        rewrite !app_assoc; econstructor; rewrite <-?app_assoc; eassumption.
    Qed.

    Lemma trace_con_lookup_abs
      (cst : CSt) (ast : ASt)
      `(MCH : MatchLTSTrace a clbs cst albs ast)
      `(LUC : clbs !! i = Some lb)
    : exists lbs j cst1 ast1,
        sublist_lookup j (length lbs) albs = Some lbs /\
        LTSLbRel a (take i clbs) cst1 (take j albs) ast1 lb lbs /\
        MatchLTSTrace a (take i clbs) cst1 (take j albs) ast1 /\
        cst1 ~[ drop i clbs ]~>* cst /\
        ast1 ~[ drop j albs ]~>* ast.
    Proof.
      revert i lb LUC. induction MCH; try congruence; try subst reach; intros.
      - (* base case: *) rewrite lookup_nil in LUC; congruence.
      - (* ind case: *)
        apply lookup_snoc_Some in LUC as [[? LUC] | [? ?]].
        + (* lb is in clbs: use ind hyp *)
          eapply IHMCH in LUC as HH0. destruct HH0 as (? & ? & ? & ? & LU_SL & ? & ? & ? & ?).
          apply lookup_lt_Some in LUC as ?. apply sublist_lookup_Some' in LU_SL as HH;
          destruct HH as (_ & HH).
          eassert (_ <= length albs) by (etransitivity; eapply Nat.le_add_r || eassumption).
          repeat eexists; try eassumption.
          * eapply sublist_lookup_app_Some; eassumption.
          * erewrite !take_app_le by lia; eassumption.
          * erewrite !take_app_le by lia; eassumption.
          * rewrite drop_app_le,lstepStar_snoc by lia. repeat eexists; eassumption.
          * rewrite drop_app_le,lstepStar_app by lia. repeat eexists; eassumption.
        + (* lb is now label appended to clbs: *)
          subst. repeat eexists; try eassumption.
          * rewrite sublist_lookup_app_r,Nat.sub_diag,sublist_lookup_all by reflexivity; reflexivity.
          * rewrite !take_app_length by reflexivity. eassumption.
          * rewrite !take_app_length by reflexivity. eassumption.
          * rewrite drop_app_length by reflexivity. econstructor; eassumption || constructor.
          * rewrite drop_app_length by reflexivity. eassumption.
    Qed.
    #[global] Arguments trace_con_lookup_abs {_ _ _ _ _} (_) [_ _] (_).

    Lemma trace_con_lookup_abs_prev
      (cst : CSt) (ast : ASt)
      `(LUC : clbs !! i = Some lb)
      `(LUA : sublist_lookup j (length lbs) albs = Some lbs)
      `(LBR : LTSLbRel a (take i clbs) cst (take j albs) ast lb lbs)
      `(MCH : MatchLTSTrace a (take i clbs) cst (take j albs) ast)
      `(LT : i1 < i)
      `(LUC1 : clbs !! i1 = Some lb1)
    : exists cst1 ast1 j1 lbs1,
        MatchLTSTrace a (take i1 clbs) cst1 (take j1 albs) ast1 /\
        sublist_lookup j1 (length lbs1) albs = Some lbs1 /\
        LTSLbRel a (take i1 clbs) cst1 (take j1 albs) ast1 lb1 lbs1 /\
        cst1 ~[ take (i - i1) (drop i1 clbs) ]~>* cst /\
        ast1 ~[ take (j - j1) (drop j1 albs) ]~>* ast /\
        j1 + length lbs1 <= j.
    Proof.
      erewrite <- lookup_take_lt in LUC1 by eassumption.
      eapply trace_con_lookup_abs in LUC1 as HH; try eassumption.
      destruct HH as (? & ? & ? & ? & LUA2 & LBR2 & MCH2 & STPS1 & STPS2).
      rewrite !take_take in MCH2,LBR2. rewrite min_l in MCH2,LBR2 by lia.
      apply sublist_lookup_Some' in LUA2 as HH. destruct HH as (_ & LE).
      match type of LE with ?a + ?b <= length (take ?c ?lbs) =>
        pose proof (firstn_le_length c lbs); assert (a <= c) by lia end.
      rewrite min_l in MCH2,LBR2 by lia. rewrite skipn_firstn_comm in STPS1,STPS2.
      eapply sublist_lookup_app_Some in LUA2; erewrite take_drop in LUA2.
      repeat (eexists || split); try eassumption.
      etransitivity; eassumption.
    Qed.
    #[global]
    Arguments trace_con_lookup_abs_prev {_ _ _ _ _} (_) [_ _ _] (_) [_] (_ _) [_] (_) [_] (_).

    Lemma trace_con_lookup_abs_2
      (cst : CSt) (ast : ASt)
      `(MCH : MatchLTSTrace a clbs cst albs ast)
      `(LT : i1 < i2)
      `(LUC1 : clbs !! i1 = Some lb1)
      `(LUC2 : clbs !! i2 = Some lb2)
    : exists cst1 cst2 ast1 ast2 j1 j2 lbs1 lbs2,
        MatchLTSTrace a (take i1 clbs) cst1 (take j1 albs) ast1 /\
        sublist_lookup j1 (length lbs1) albs = Some lbs1 /\
        LTSLbRel a (take i1 clbs) cst1 (take j1 albs) ast1 lb1 lbs1 /\
        cst1 ~[ take (i2 - i1) (drop i1 clbs) ]~>* cst2 /\
        ast1 ~[ take (j2 - j1) (drop j1 albs) ]~>* ast2 /\
        j1 + length lbs1 <= j2 /\
        MatchLTSTrace a (take i2 clbs) cst2 (take j2 albs) ast2 /\
        sublist_lookup j2 (length lbs2) albs = Some lbs2 /\
        LTSLbRel a (take i2 clbs) cst2 (take j2 albs) ast2 lb2 lbs2 /\
        cst2 ~[ drop i2 clbs ]~>* cst /\
        ast2 ~[ drop j2 albs ]~>* ast.
    Proof.
      eapply trace_con_lookup_abs in LUC2 as HH; try eassumption.
      destr_all HH.
      eapply trace_con_lookup_abs_prev in LT as HH; try eassumption.
      destr_all HH.
      repeat (eexists || split); eassumption.
    Qed.
    #[global] Arguments trace_con_lookup_abs_2 {_ _ _ _ _} (_) [_ _] (_) {_} (_) {_} (_).

    Lemma trace_abs_lookup_con
      (cst : CSt) (ast : ASt)
      `(MCH : MatchLTSTrace a clbs cst albs ast)
      `(LUA : albs !! j = Some alb)
    : ∃ albs1 albs2 i clb cst1 ast1,
        sublist_lookup (j - length albs1) (length albs1 + length albs2 + 1) albs = Some (albs1 ++ alb :: albs2) ∧
        clbs !! i = Some clb ∧
        LTSLbRel a (take i clbs) cst1 (take (j - length albs1) albs) ast1 clb (albs1 ++ alb :: albs2) ∧
        MatchLTSTrace a (take i clbs) cst1 (take (j - length albs1) albs) ast1 ∧
        cst1 ~[ drop i clbs ]~>* cst ∧
        ast1 ~[ drop (j - length albs1) albs ]~>* ast ∧
        length albs1 ≤ j.
    Proof.
      revert j alb LUA; induction MCH; intros.
      - naive_solver.
      - eapply lookup_app_Some in LUA as [LUA | (? & LUA)].
        + specialize (IHMCH _ _ LUA) as (? & ? & ? & ? & ? & ? & ALU & CLU & ? & ? & ? & ? & LEN).
          eapply sublist_lookup_Some' in ALU as HH; destruct HH as (? & ?);
          eapply lookup_lt_Some in CLU as ?.
          do 6 eexists; repeat split.
          * rewrite sublist_lookup_app_l; eassumption.
          * rewrite !lookup_app_l; eassumption.
          * rewrite !take_app_le by lia; eassumption.
          * rewrite !take_app_le by lia; eassumption.
          * rewrite !drop_app_le by lia; eapply lstepStar_snoc_1; eassumption.
          * rewrite !drop_app_le by lia; eapply lstepStar_app_1; eassumption.
          * exact LEN.
        + eapply list_elem_of_split_length in LUA as (? & ? & ? & EL); subst.
          assert (∀ a b, b <= a -> a - (a - b) = b) as EL' by lia.
          do 6 eexists; repeat split.
          * erewrite <-EL,EL' at 1 by lia; rewrite sublist_lookup_drop_app.
            eapply sublist_lookup_all. rewrite length_app; cbn; lia.
          * rewrite lookup_app_r,Nat.sub_diag; reflexivity.
          * rewrite take_app_le,firstn_all,<-EL,EL',take_app_le,firstn_all by lia.
            eassumption.
          * rewrite <-EL,EL',!take_app_le,!firstn_all by lia.
            eassumption.
          * rewrite drop_app_le,drop_all by lia.
            eapply lstepStar_snoc_1; eassumption || econstructor.
          * rewrite <-EL,EL',drop_app_le,drop_all by lia.
            eapply lstepStar_app_1; eassumption || econstructor.
          * lia.
    Qed.
    #[global] Arguments trace_abs_lookup_con {_ _ _ _ _} (_) [_] {_} (_).

    Lemma trace_abs_lookup_con_prev
      `(LUA2 : albs !! i2 = Some alb2)
      `(SLU2 : sublist_lookup (i2 - length albs21) (length albs21 + length albs22 + 1) albs = Some (albs21 ++ alb2 :: albs22))
      `(LUC2 : clbs !! j2 = Some clb2)
      `(LBR2 : LTSLbRel a (take j2 clbs) cst2 (take (i2 - length albs21) albs) ast2 clb2 (albs21 ++ alb2 :: albs22))
      `(MCH2 : MatchLTSTrace a (take j2 clbs) cst2 (take (i2 - length albs21) albs) ast2)
      `(LT : i1 < i2)
      `(LUA1 : albs !! i1 = Some alb1)
    : ∃ albs11 albs12 j1 clb1 cst1 ast1,
        MatchLTSTrace a (take j1 clbs) cst1 (take (i1 - length albs11) albs) ast1 ∧
        sublist_lookup (i1 - length albs11) (length albs11 + length albs12 + 1) albs = Some (albs11 ++ alb1 :: albs12) ∧
        clbs !! j1 = Some clb1 ∧
        LTSLbRel a (take j1 clbs) cst1 (take (i1 - length albs11) albs) ast1 clb1 (albs11 ++ alb1 :: albs12) ∧
        ast1 ~[ take ((i2 - length albs21) - (i1 - length albs11)) (drop (i1 - length albs11) albs) ]~>* ast2 ∧
        cst1 ~[ take (j2 - j1) (drop j1 clbs) ]~>* cst2 ∧
        j1 ≤ j2 ∧
        (j1 = j2 → length albs11 < length albs21).
    Proof.
      destruct (decide (i1 < i2 - length albs21)) as [LT2 | GE].
      - (* i1 lies in an earlier abstract block *)
        assert (take (i2 - length albs21) albs !! i1 = Some alb1) as LUA1'
          by (rewrite lookup_take_lt by lia; exact LUA1).
        eapply trace_abs_lookup_con in LUA1' as HH; try exact MCH2.
        destruct HH as (albs11 & albs12 & j1 & clb1 & cst1 & ast1 &
                        SLU1 & LUC1 & LBR1 & MCH1 & STPSc & STPSa & LEN1).
        apply lookup_take_Some in LUC1 as [LUC1' LTj].
        apply lookup_lt_Some in LUA2 as LTi2.
        pose proof SLU1 as SLU1c.
        apply sublist_lookup_Some' in SLU1c as [_ LE].
        rewrite length_take_le in LE by lia.
        rewrite !take_take in MCH1, LBR1.
        rewrite (Nat.min_l j1 j2) in MCH1, LBR1 by lia.
        rewrite (Nat.min_l (i1 - length albs11) (i2 - length albs21)) in MCH1, LBR1 by lia.
        rewrite skipn_firstn_comm in STPSc, STPSa.
        exists albs11, albs12, j1, clb1, cst1, ast1.
        repeat split.
        + exact MCH1.
        + rewrite <- (take_drop (i2 - length albs21) albs).
          apply sublist_lookup_app_Some. exact SLU1.
        + exact LUC1'.
        + exact LBR1.
        + exact STPSa.
        + exact STPSc.
        + lia.
        + intros; lia.
      - (* i1 lies in the same abstract block as i2 *)
        assert (i2 - length albs21 ≤ i1) as GE' by lia.
        remember (i1 - (i2 - length albs21)) as p eqn:Hp.
        assert (p < length albs21) as PLT by lia.
        assert (albs21 !! p = Some alb1) as LU21.
        { eapply sublist_lookup_lookup_Some_2 in SLU2 as HH; [| exact LUA1 |].
          - rewrite lookup_app_l in HH by lia. rewrite <- Hp in HH. exact HH.
          - split; lia. }
        pose proof (take_drop_middle albs21 p alb1 LU21) as SPLIT.
        assert (length (take p albs21) = p) as LENp by (rewrite length_take_le; lia).
        assert (i1 - length (take p albs21) = i2 - length albs21) as EQ by lia.
        exists (take p albs21), (drop (S p) albs21 ++ alb2 :: albs22),
               j2, clb2, cst2, ast2.
        repeat split.
        + rewrite EQ. exact MCH2.
        + rewrite EQ. rewrite app_comm_cons, app_assoc, SPLIT.
          replace (length (take p albs21) + length (drop (S p) albs21 ++ alb2 :: albs22) + 1)
            with (length albs21 + length albs22 + 1).
          * exact SLU2.
          * rewrite LENp, !length_app, length_drop. cbn [length]. lia.
        + exact LUC2.
        + rewrite EQ. rewrite app_comm_cons, app_assoc, SPLIT. exact LBR2.
        + rewrite EQ, Nat.sub_diag. constructor.
        + rewrite Nat.sub_diag. constructor.
        + lia.
        + intros _; lia.
    Qed.

    Lemma trace_abs_lookup_con_2
      (cst : CSt) (ast : ASt)
      `(MCH : MatchLTSTrace a clbs cst albs ast)
      `(LT : i1 < i2)
      `(LUA1 : albs !! i1 = Some alb1)
      `(LUA2 : albs !! i2 = Some alb2)
    : ∃ j1 j2 clb1 clb2 albs11 albs12 albs21 albs22 ast1 ast2 cst1 cst2,
        MatchLTSTrace a (take j1 clbs) cst1 (take (i1 - length albs11) albs) ast1 ∧
        sublist_lookup (i1 - length albs11) (length albs11 + length albs12 + 1) albs = Some (albs11 ++ alb1 :: albs12) ∧
        clbs !! j1 = Some clb1 ∧
        LTSLbRel a (take j1 clbs) cst1 (take (i1 - length albs11) albs) ast1 clb1 (albs11 ++ alb1 :: albs12) ∧
        ast1 ~[ take ((i2 - length albs21) - (i1 - length albs11)) (drop (i1 - length albs11) albs) ]~>* ast2 ∧
        cst1 ~[ take (j2 - j1) (drop j1 clbs) ]~>* cst2 ∧
        j1 ≤ j2 ∧
        MatchLTSTrace a (take j2 clbs) cst2 (take (i2 - length albs21) albs) ast2 ∧
        sublist_lookup (i2 - length albs21) (length albs21 + length albs22 + 1) albs = Some (albs21 ++ alb2 :: albs22) ∧
        clbs !! j2 = Some clb2 ∧
        LTSLbRel a (take j2 clbs) cst2 (take (i2 - length albs21) albs) ast2 clb2 (albs21 ++ alb2 :: albs22) ∧
        (j1 = j2 → length albs11 < length albs21) ∧
        cst2 ~[ drop j2 clbs ]~>* cst /\
        ast2 ~[ drop (i2 - length albs21) albs ]~>* ast.
    Proof.
      eapply trace_abs_lookup_con in LUA2 as HH; try eassumption. destr_all HH.
      eapply trace_abs_lookup_con_prev in LT as HH; try eassumption. destr_all HH.
      repeat (eexists || split); eassumption.
    Qed.

  End REF_LEMMAS.

End LTS_REFINE.

Arguments LTSRefineInit (_ _) {_ _ _ _ _ _}.
Arguments LTSRefineStep (_ _) {_ _ _ _ _ _}.
Arguments LTSStepCond (_ _) {_ _ _ _ _ _}.
Arguments LTSRefStep (_ _) {_ _ _ _ _}.
Arguments LTSRefInitStep (_ _) {_ _ _ _ _}.
Arguments LTSRefRel (_ _) {_ _ _ _ _}.
Arguments LTSRef (_ _) {_ _ _ _ _}.
Arguments LTSRefines (_ _) {_ _ _ _ _ _}.
