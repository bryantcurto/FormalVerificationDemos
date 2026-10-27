From refinement.lib Require Import
     Prelude
     TransSystem
     LTSRefine.

(** * Example #2: Stuttering

    A specification hour clock, and an implementation hour-minute clock whose
    minute steps are internal (τ) steps. *)

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

End Impl.

#[global] Instance Stutter_LTSRefRel : LTSRefRel Impl.St Spec.St (A:=unit).
(* := {|
  LTSStRel := (* TODO *)
  LTSLbRel := λ _ _ _ _ _ _ _, True; (* given *)
  LTSCond := λ _ _ _, True; (* given *)
|}. *)
Admitted.

#[global] Instance Stutter_LTSRefInitStep : LTSRefInitStep Impl.St Spec.St (A:=unit).
Proof.
(* TODO *)
Admitted.
