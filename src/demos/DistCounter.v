From refinement.lib Require Import
     Prelude
     TransSystem
     LTSRefine.

(** * Example #12: Distributed counter

    A specification counter, and an implementation replicated counter in
    which each node holds a set of increment IDs. *)

(** ** Specification: counter *)
Module Spec.

  Record St : Type := mkSt {
    count : nat;
  }.

  Variant Lb : Type :=
  | Inc (n : nat).

  Definition Init (st : St) : Prop :=
    count st = 0.

  Inductive Step (st : St) : Lb → St → Prop :=
  | stepInc st'
      (COUNT : st'.(count) = S st.(count))
    : Step st (Inc st.(count)) st'.

  #[global] Instance LTS : LTSParams St Lb :=
    mkLTSParams (mkTSCom Init) Step.

End Spec.

(** ** Implementation: replicated counter *)
Module Impl.

  (* Node ↦ increment IDs. A finite map is finitely supported by construction;
     a node absent from the map holds ∅. *)
  Record St : Type := mkSt {
    nodes : gmap nat (gset nat);
  }.

  (* The increment IDs held by node [i]. *)
  Definition nodeIds (nds : gmap nat (gset nat)) (i : nat) : gset nat :=
    default ∅ (nds !! i).

  (* Every increment ID in the system. *)
  Definition allIds (nds : gmap nat (gset nat)) : gset nat :=
    map_fold (λ _ v a, v ∪ a) ∅ nds.

  (* σ[i ↦ σ(i) ∪ X] *)
  Definition addIds (nds : gmap nat (gset nat)) (i : nat) (X : gset nat) : gmap nat (gset nat) :=
    <[i := nodeIds nds i ∪ X]> nds.

  (* The [Inc] label reports the system-wide count after the step. It is an
     observer's view, not something node [i] computes. *)
  Variant Lb : Type :=
  | Inc (n : nat)
  | Tau.

  Definition Init (st : St) : Prop :=
    nodes st = ∅.

  Inductive Step (st : St) : Lb → St → Prop :=
  | stepInc x i st'
      (FRESH : x ∉ allIds st.(nodes))
      (NODES : st'.(nodes) = addIds st.(nodes) i {[x]})
    : Step st (Inc (size (allIds st.(nodes)))) st'
  | stepTau j X i st'
      (SSE : X ⊆ nodeIds st.(nodes) j)
      (NODES : st'.(nodes) = addIds st.(nodes) i X)
    : Step st Tau st'.

  #[global] Instance LTS : LTSParams St Lb :=
    mkLTSParams (mkTSCom Init) Step.

End Impl.

#[global] Instance DistCounter_LTSRefRel : LTSRefRel Impl.St Spec.St (A:=unit).
(* := {|
  LTSStRel := (* TODO *)
  LTSLbRel := (* TODO *)
  LTSCond := λ _ _ _, True; (* given *)
|}. *)
Admitted.

#[global] Instance DistCounter_LTSRefInitStep : LTSRefInitStep Impl.St Spec.St (A:=unit).
Proof.
(* TODO *)
Admitted.
