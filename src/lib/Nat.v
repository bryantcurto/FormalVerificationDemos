From refinement.lib Require Import
     Base.

#[global] Opaque Nat.ltb.

Module Nat.

  Export Nat.

  Lemma ltb_leb_incl n m
  : ltb n m = true ->
    leb n m = true.
  Proof.
    rewrite <-(reflect_iff _ _ (ltb_spec0 _ _)).
    rewrite <-(reflect_iff _ _ (leb_spec0 _ _)).
    eapply lt_le_incl.
  Qed.

  (** Bits at or above position [n] are false for values below [2^n]. *)
  Lemma testbit_above a n m
  : a < 2 ^ n ->
    n <= m ->
    testbit a m = false.
  Proof.
    intros Ha Hm.
    destruct (eq_dec a 0) as [-> | Ha0].
    - apply bits_0.
    - apply bits_above_log2.
      enough (log2 a < n) by lia.
      eapply log2_lt_pow2; lia.
  Qed.

  (** Masking [lor (shiftl a n) b] with [ones n] discards the high
      part and keeps only the masked low part. *)
  Lemma land_ones_lor_shiftl a b n
  : land (lor (shiftl a n) b) (ones n) = land b (ones n).
  Proof.
    apply bits_inj; intro m.
    rewrite !land_spec, lor_spec.
    destruct (lt_ge_cases m n) as [Hlt | Hge].
    - rewrite shiftl_spec_low, ones_spec_low by exact Hlt.
      reflexivity.
    - rewrite ones_spec_high, !andb_false_r by exact Hge.
      reflexivity.
  Qed.

  (** Right-shifting by [n] undoes [lor (shiftl a n) b] when [b < 2^n]. *)
  Lemma shiftr_lor_shiftl a b n
  : b < 2 ^ n ->
    shiftr (lor (shiftl a n) b) n = a.
  Proof.
    intro Hb.
    apply bits_inj; intro m.
    rewrite shiftr_spec, lor_spec, shiftl_spec_high by lia.
    rewrite (testbit_above _ _ _ Hb), orb_false_r by lia.
    f_equal. lia.
  Qed.

  (** Masking with [ones n] is the identity for values below [2^n]. *)
  Lemma land_ones' a n
  : a < 2 ^ n ->
    land a (ones n) = a.
  Proof.
    intro Ha.
    apply bits_inj; intro m.
    rewrite land_spec.
    destruct (lt_ge_cases m n) as [Hlt | Hge].
    - rewrite ones_spec_low by exact Hlt.
      apply andb_true_r.
    - rewrite ones_spec_high by exact Hge.
      rewrite andb_false_r. symmetry.
      eapply testbit_above; eassumption.
  Qed.

  Lemma fun_add_1_r : (λ n, n + 1) = S.
  Proof.
    apply Ax.functional_extensionality; exact Nat.add_1_r.
  Qed.

  Lemma strict_mono_fun_inj n m
    (f : nat → nat)
    (MONO : ∀ a b, a < b → f a < f b ∨ f b < f a)
    (EQ : f n = f m)
  : n = m.
  Proof.
    destruct (lt_eq_lt_dec n m) as [[ORD | EQ'] | ORD].
    1,3: specialize (MONO _ _ ORD) as []; exfalso; lia.
    { exact EQ'. }
  Qed.

End Nat.
