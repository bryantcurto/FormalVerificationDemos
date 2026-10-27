Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Import
     Base Tactics.

Lemma StrictOrder_Antisymmetric
  {A : Type}
  (R : relation A)
  (SO : StrictOrder R)
: Antisymmetric _ eq R.
Proof.
  inversion SO. intros ? ? R1 R2; exfalso.
  assert (R x x) by (etransitivity;eassumption).
  eapply StrictOrder_Irreflexive; eassumption.
Qed.

Section RELATIONS.

  #[global] Instance RelDecision_Fun
    {A B C D : Type}
    (fa : A -> C) (fb : B -> D)
    (R : C -> D -> Prop) {RD : RelDecision R}
  : RelDecision (λ a b, R (fa a) (fb b)).
  Proof. red; typeclasses eauto. Qed.

  #[global] Instance Is_true_RelDecision {A B : Type} (f : A → B → bool)
  : RelDecision (λ x y, (Is_true (f x y))).
  Proof. intros x y. destruct (f x y); cbn; typeclasses eauto. Qed.

  #[global] Instance StrictOrder_AntiSymm `{R : relation A,!StrictOrder R} : AntiSymm eq R.
  Proof.
    intros ? **; exfalso.
    assert (R x x) by (etransitivity;eassumption).
    eapply irreflexivity; eassumption || typeclasses eauto.
  Qed.

  (* Fix issue with typeclass resolution *)
  #[global] Instance subrelation_eq_impl : subrelation eq impl.
  Proof. eapply eq_subrelation,impl_Reflexive. Qed.

  #[global] Instance subrelation_eq_flip_impl : subrelation eq (flip impl).
  Proof. eapply eq_subrelation,flip_Reflexive. Qed.

  #[global] Instance Reflexive_fst {A : Type} (R : relation A) `{Reflexive _ R}
  : ∀ B, Reflexive (λ x y : A * B, R x.1 y.1).
  Proof. intros ** ? **; reflexivity. Qed.

  #[global] Instance Symmetric_fst {A : Type} (R : relation A) `{Symmetric _ R}
  : ∀ B, Symmetric (λ x y : A * B, R x.1 y.1).
  Proof. intros ** ? **; symmetry; assumption. Qed.

  #[global] Instance Transitive_fst {A : Type} (R : relation A) `{Transitive _ R}
  : ∀ B, Transitive (λ x y : A * B, R x.1 y.1).
  Proof. intros ** ? **; etransitivity; eassumption. Qed.

  #[global] Instance Equivalence_fst {A : Type} (R : relation A) `{Equivalence _ R}
  : ∀ B, Equivalence (λ x y : A * B, R x.1 y.1).
  Proof. intros **; constructor; typeclasses eauto. Qed.

  #[global] Instance Irreflexive_fst {A : Type} (R : relation A) `{Irreflexive _ R}
  : ∀ B, Irreflexive (λ x y : A * B, R x.1 y.1).
  Proof. intros ?[x y]. red; cbn in *. revert x. change (Reflexive (complement R)). typeclasses eauto. Qed.

  #[global] Instance StrictOrder_fst {A : Type} (R : relation A) `{StrictOrder _ R}
  : ∀ B, StrictOrder (λ x y : A * B, R x.1 y.1).
  Proof. intros **; constructor; typeclasses eauto. Qed.

  #[global] Instance Reflexive_snd {B : Type} (R : relation B) `{Reflexive _ R}
  : ∀ A, Reflexive (λ x y : A * B, R x.2 y.2).
  Proof. intros ** ? **; reflexivity. Qed.

  #[global] Instance Symmetric_snd {B : Type} (R : relation B) `{Symmetric _ R}
  : ∀ A, Symmetric (λ x y : A * B, R x.2 y.2).
  Proof. intros ** ? **; symmetry; assumption. Qed.

  #[global] Instance Transitive_snd {B : Type} (R : relation B) `{Transitive _ R}
  : ∀ A, Transitive (λ x y : A * B, R x.2 y.2).
  Proof. intros ** ? **; etransitivity; eassumption. Qed.

  #[global] Instance Equivalence_snd {B : Type} (R : relation B) `{Equivalence _ R}
  : ∀ A, Equivalence (λ x y : A * B, R x.2 y.2).
  Proof. intros **; constructor; typeclasses eauto. Qed.

  #[global] Instance Irreflexive_snd {B : Type} (R : relation B) `{Irreflexive _ R}
  : ∀ A, Irreflexive (λ x y : A * B, R x.2 y.2).
  Proof.
    intros ?[x y]. red; cbn in *. revert y. change (Reflexive (complement R)). typeclasses eauto.
  Qed.

  #[global] Instance StrictOrder_snd {B : Type} (R : relation B) `{StrictOrder _ R}
  : ∀ A, StrictOrder (λ x y : A * B, R x.2 y.2).
  Proof. intros **; constructor; typeclasses eauto. Qed.

End RELATIONS.
