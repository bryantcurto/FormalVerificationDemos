Set Implicit Arguments.

From refinement.lib Require Import
     Base Tactics Logic.

#[global] Instance sig_EqDecision {A : Type} `{EqDecision A} {P : A → Prop} : EqDecision ({ x : A | P x }).
Proof.
  repeat red; intros [x px] [y py]. destruct (decide (x = y)) as [->|].
  - left. rewrite (proof_irrelevance _ px py). reflexivity.
  - right. intros C. injection C. intros. contradiction.
Qed.
