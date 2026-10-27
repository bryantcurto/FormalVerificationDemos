Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Import
     Base Tactics.

Section REFLECT.

  Lemma reflect_iff'
    `(REF : reflect P b)
  : ¬ P <-> b = false.
  Proof.
    split; intros HH; inversion REF; subst;
    reflexivity || contradiction || congruence.
  Qed.

End REFLECT.
