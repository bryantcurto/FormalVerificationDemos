(* =====================================================================
   Axioms.v  —  the development's entire axiomatic trusted base.

   This is the ONLY file that requires Coq's axiom-carrying modules.  The
   classical principles are NOT re-exported: they are reachable only as
   [Ax.classic], [Ax.epsilon], … so that

       grep -rn "Ax\.\(classic\|NNPP\|epsilon\|excluded_middle\|constructive\)" src

   bounds every appeal to excluded middle or choice.  `Print Assumptions` on
   a top-level theorem can be read against the short list here.

   What each entry costs, as reported by `Print Assumptions`:

     Ax.classic, Ax.NNPP
       Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
       Needed because the LTL operators are infinitary: [always] is
       coinductive and [eventually] inductive over an infinite stream, so
       neither is decidable, and the duality [neg_always] is Markov's
       Principle even for decidable predicates.  Prefer the derived LTL
       lemmas (e.g. [LTL.eventually_or_always_not]) over [Ax.classic].

     Ax.epsilon, Ax.epsilon_spec, Ax.excluded_middle_informative,
     Ax.constructive_indefinite_description
       + ClassicalEpsilon.constructive_indefinite_description
       Needed only by LTLRefine.v, to build an abstract stream corecursively
       out of the Prop-existential that the refinement interface yields.

     Ax.proof_irrelevance
       proof_irrelevance : ∀ (P : Prop) (p1 p2 : P), p1 = p2
       Used to identify two proofs of a side condition carried inside a
       label/state (see lib/Tactics.v's [uniq_proof]).

     Ax.functional_extensionality
       functional_extensionality_dep
       Used for pointwise equalities between functions.

   The four protocol-layer liveness theorems (ev_convergence,
   rwdep_convergence, ev_availability, rwdep_availability) depend on the
   first two entries only.
   ===================================================================== *)

(* Excluded middle and choice are required WITHOUT [Export]: the only way to
   reach them is through [Ax] below, so their use sites are greppable. *)
From Stdlib Require Import
     Logic.Classical_Prop
     Logic.ClassicalEpsilon
     Logic.IndefiniteDescription.

(* Proof irrelevance and functional extensionality are re-exported, because
   Coq's own tactics reach for their consequences implicitly ([eq_rect_eq] for
   dependent inversion, [eta_expansion_dep] for eta on dependent functions);
   hiding them would mean fighting the tactic ecosystem.  Explicit appeals are
   still written [Ax.proof_irrelevance] / [Ax.functional_extensionality] so
   that they, at least, stay greppable. *)
From Stdlib Require Export
     ProofIrrelevance
     Logic.FunctionalExtensionality.

Module Ax.

  (** Excluded middle. *)
  Notation classic := Classical_Prop.classic.
  Notation NNPP := Classical_Prop.NNPP.

  (** Choice: escaping a [Prop]-existential into [Type]. *)
  Notation constructive_indefinite_description :=
    ClassicalEpsilon.constructive_indefinite_description.
  Notation excluded_middle_informative :=
    ClassicalEpsilon.excluded_middle_informative.
  (* [epsilon i P] depends only on the predicate [P], never on a proof
     term; that determinism is what makes the corecursive stream
     construction in LTLRefine.v a function of its input. *)
  Notation epsilon := ClassicalEpsilon.epsilon.
  Notation epsilon_spec := ClassicalEpsilon.epsilon_spec.

  (** Proof irrelevance and functional extensionality. *)
  Notation proof_irrelevance := ProofIrrelevance.proof_irrelevance.
  Notation functional_extensionality :=
    FunctionalExtensionality.functional_extensionality.
  Notation functional_extensionality_dep :=
    FunctionalExtensionality.functional_extensionality_dep.
  Notation eta_expansion_dep := FunctionalExtensionality.eta_expansion_dep.

  (** Derived principles, so that proofs can name the reasoning step they
      make instead of appealing to excluded middle directly. *)

  (* Contraposition in the classical direction (the constructive one needs no
     axiom).  Lets a proof discharge [¬ P → Q] by exhibiting a witness for [P]
     from [¬ Q]. *)
  (* stated in ASCII: this file predates the stdpp notation scope *)
  Lemma contrapositive {P Q : Prop} (H : ~ Q -> P) : ~ P -> Q.
  Proof. intro NP. apply NNPP. intro NQ. exact (NP (H NQ)). Qed.

End Ax.
