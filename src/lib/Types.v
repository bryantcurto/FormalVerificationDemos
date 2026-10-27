Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Import
     Base.

Class NodeId : Type := mkNodeId {
  NId : Type;
  NId_eq_dec :: EqDecision NId;
  NId_countable :: Countable NId;
}.

Class Parallel A : Type := parallel : A -> A -> Prop.
Global Hint Mode Parallel ! : typeclass_instances.
Global Instance : Params (@parallel) 2 := {}.
Infix "∥" := parallel (at level 70).

Class Order A : Type := ord : A -> A -> Prop.
Global Hint Mode Order ! : typeclass_instances.
Global Instance : Params (@ord) 2 := {}.
Infix "≺" := ord (at level 70).

Class Independent A : Type := indep : A -> A -> Prop.
Global Hint Mode Independent ! : typeclass_instances.
Global Instance : Params (@indep) 2 := {}.
Infix "#" := indep (at level 70).

Class Everything (A : Type) := evthg : A.
#[global] Hint Mode Everything ! : typeclass_instances.
Notation "'𝔼'" := evthg.

Class Something (A : Type) {B : Type} : Type := smthg : A -> B.
#[global] Hint Mode Something ! ! : typeclass_instances.

(* Variant of typeclass Elements that returns gset A rather than list A *)
Class ElemSet (A : Type) `{Countable A} (C : Type) : Type :=
  elemset : C -> gset A.
#[global] Arguments ElemSet (_) {_ _} (_).

Definition Prop_to_Set (P : Prop) : Set := P.
