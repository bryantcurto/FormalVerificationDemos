Set Implicit Arguments.

From refinement Require Export Base.

From stdpp Require Export fin.

Section FIN.

  #[local] Definition fin_n_ne_0 {n : nat} (f : fin n) : n ≠ 0 := ltac:(destruct n; [inv f | lia]).

  Definition addWrap {n : nat} (f : fin n) (a : nat) :=
    nat_to_fin (Nat.mod_upper_bound (f + a) n (fin_n_ne_0 f)).

  Definition addWrap_spec {n : nat} (f : fin n) (a : nat)
  : (addWrap f a : nat) = (f + a) `mod` n := fin_to_nat_to_fin _ _ _.

End FIN.
