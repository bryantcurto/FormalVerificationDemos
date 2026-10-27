Set Implicit Arguments.

From refinement.lib Require Import
     Base Tactics.

Section OPTION.

  Lemma union_None_l
    {A : Type}
    (my : option A)
  : None ∪ my = my.
  Proof. destruct my; reflexivity. Qed.

End OPTION.

