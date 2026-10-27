Set Implicit Arguments.
Set Primitive Projections.

From stdpp Require Export
     prelude gmap.

From refinement.lib Require Export
     Axioms.

Notation "l @@ v" := (l ++ [v]) (at level 5).
Notation "<[ k ++:= l ]> m" := (alter (λ l', l' ++ l) k m) (at level 5).
Notation "<[ k @@:= v ]> m" := (alter (λ l, l @@ v) k m) (at level 5).
Notation "<[ k ∪:= s ]> m" := (alter (λ s', s ∪ s') k m) (at level 5).
Notation "<[ k ∖:= s ]> m" := (alter (λ s', s' ∖ s) k m) (at level 5).

(* Allows typeclass resolution to determine equality. *)
Hint Constructors eq : typeclass_instances.

(* Encountered some issues where these wouldn't simplify *)
#[global] Arguments reverse_coercion /.
#[global] Transparent reverse_coercion.
