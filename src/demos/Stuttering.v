From refinement.lib Require Import
     Prelude
     TransSystem
     LTSRefine.

(** * Example #2: Stuttering

    A specification hour clock, and an implementation hour-minute clock whose
    minute steps are internal (τ) steps.
    Based on https://lamport.azurewebsites.net/pubs/state-machine.pdf *)

Definition nextHr (h : nat) : nat :=
  if decide (h = 12) then 1 else S h.

Definition nextHrMin (h m : nat) : nat * nat :=
  if decide (m = 59) then (nextHr h, 0) else (h, S m).

(** ** Specification: hour clock *)
Module Spec.

  Record St : Type := mkSt {
    hr : nat;
  }.

  (* Init = S = {1..12} *)
  Definition Init (st : St) : Prop :=
    1 ≤ hr st ≤ 12.

  Inductive Step (st : St) (u : unit) (st' : St) : Prop :=
  | step
      (ST' : st'.(hr) = nextHr st.(hr)).

  #[global] Instance LTS : LTSParams St unit :=
    mkLTSParams (mkTSCom Init) Step.

  Lemma inv_ge_1 lbs (st : St)
    (RCH : lreachable lbs st)
  : 1 ≤ st.(hr).
  Proof.
    induction RCH using lreachable_snoc_ind.
    - repeat red in INIT.
      destruct INIT as [H1 H2].
      apply H1.
    - inversion STEP. rewrite ST'.
      unfold nextHr. destruct (decide (st.(hr) = 12)).
      + reflexivity.
      + lia.
  Qed.

  Lemma inv_le_12 lbs (st : St)
    (RCH : lreachable lbs st)
  : st.(hr) ≤ 12.
  Proof.
    (* TODO *)
  Admitted.

End Spec.

(** ** Implementation: hour-minute clock *)
Module Impl.

  Record St : Type := mkSt {
    hr : nat;
    min : nat;
  }.

  (* Init = S = {1..12} × {0..59} *)
  Definition Init (st : St) : Prop :=
    1 ≤ hr st ≤ 12 ∧ min st ≤ 59.

  Inductive Step (st : St) (u : unit) (st' : St) : Prop :=
  | step
      (ST' : (st'.(hr), st'.(min)) = nextHrMin st.(hr) st.(min)).

  #[global] Instance LTS : LTSParams St unit :=
    mkLTSParams (mkTSCom Init) Step.

  Lemma inv_min_ge_0 lbs (st : St)
    (RCH : lreachable lbs st)
  : 0 ≤ st.(min).
  Proof.
    (* TODO *)
  Admitted.

  Lemma inv_min_le_59 lbs (st : St)
    (RCH : lreachable lbs st)
  : st.(min) ≤ 59.
  Proof.
    (* TODO *)
  Admitted.

End Impl.

#[global] Instance Stutter_LTSRefRel
: LTSRefRel Impl.St Spec.St (A:=unit) := {|
  LTSStRel := λ _ _ ist _ sst, (* Refinement Relation *)
    sst.(Spec.hr) = ist.(Impl.hr);
  LTSLbRel := λ _ _ _ _ _ _ _, True; (* given; ignore *)
  LTSCond := λ _ _ _, True; (* given; ignore *)
|}.

Lemma Stutter_lts_refine_init : LTSRefineInit Impl.St Spec.St.
Proof.
Admitted.

Lemma Stutter_ltsRefInitStep : LTSRefineStep Impl.St Spec.St.
Proof.
Admitted.

#[global] Instance Stutter_LTSRefInitStep
: LTSRefInitStep Impl.St Spec.St (A:=unit) := {|
  ltsRefInitStep := {|
    ltsRefStepRel := Stutter_LTSRefRel;
    lts_refine_step := Stutter_ltsRefInitStep
  |};
  lts_refine_init := Stutter_lts_refine_init;
  lts_step_cond := ltac:(intros ?**; exact I);
|}.
