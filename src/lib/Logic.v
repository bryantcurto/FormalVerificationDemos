Set Implicit Arguments.

From refinement.lib Require Import
     Base Tactics.

Lemma impl_inv
  (A B : Prop)
  (I : A -> B)
  (NB : ~B)
: ~A.
Proof. intro; apply NB,I; assumption. Qed.

Lemma disj_shortcircuit
  (P Q : Prop) `{Decision P}
  (ANT : P \/ Q)
: (P \/ (~P /\ Q)).
Proof.
  destruct ANT as [|];
  destruct (decide P) as [|].
  - left. assumption.
  - contradiction.
  - left. assumption.
  - right. split; assumption.
Qed.

(* TODO : this proof is probably somewhere in the stdlib *)
Lemma exists_disj
  {A : Type}
  {P Q : A -> Prop}
  (ANT : exists a, P a \/ Q a)
: (exists a, P a) \/ (exists a, Q a).
Proof.
  destruct ANT as [? []]; [ left | right ]; eexists; eassumption.
Qed.

Lemma exists_disj_2
  (A B : Type)
  (P Q : A -> B -> Prop)
  (ANT : exists a b, P a b \/ Q a b)
: (exists a b, P a b) \/ (exists a b, Q a b).
Proof.
  destruct ANT as [? D]. apply exists_disj in D as [];
  [ left | right ]; eexists; eassumption.
Qed.
