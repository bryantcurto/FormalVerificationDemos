Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Import
     Base.

(* "Clean" subst, which substitutes newer terms in the context with older terms. *)
Ltac csubst :=
  repeat
    match goal with [old : ?A,new : ?A |- _] =>
      match goal with
      | [_ : old = new |- _] => subst new
      | [_ : new = old |- _] => subst new end end;
  subst.

Ltac econtradiction t :=
  match goal with
  | [H : _ |- _] =>
    eapply t in H;
    contradiction
  end.

Ltac assumpt := assumption || (symmetry; assumption).
Ltac eassumpt := eassumption || (symmetry; eassumption).

(* Lock hypotheses' values to prevent tactics matching them. *)
Definition _LOCK {A K} (key: K) (x : A) := x.
Arguments _LOCK {_ _ _}.

Ltac _lock H k :=
  lazymatch type of H with
  | ?T => change T with (_LOCK (key := k) T) in H
  end.
Tactic Notation "lock" hyp(H) "with" constr(key) := _lock H key.
Tactic Notation "lock" hyp(H) := lock H with 0.

Ltac _lock_val v k :=
  let nm := fresh "LOCKED" in
  let H := fresh "Hlock" in
  remember v as nm eqn:H;
  lock H with k.
Tactic Notation "lock_val" uconstr(v) "with" constr(key) := _lock_val v key.
Tactic Notation "lock_val" uconstr(v) := lock_val v with 0.

Tactic Notation "unlock" hyp(H) "with" constr(key) :=
  lazymatch type of H with @_LOCK _ _ key _ => unfold _LOCK in H end.
Tactic Notation "unlock" hyp(H) :=
  lazymatch type of H with _LOCK _ => unfold _LOCK in H end.
Tactic Notation "unlock" "*" "with" constr(key) :=
  repeat match goal with H: @_LOCK _ _ key _ |- _ => unfold _LOCK in H end.
Tactic Notation "unlock" "*" := unfold _LOCK in *.

Section LockTests.
  Goal forall (P Q: Prop), P -> Q -> P /\ Q.
  Proof.
    intros * HP HQ.
    lock HP; lock HQ with 1.
    Fail unlock HQ with 0.
    Fail match goal with H: P |- _ => idtac end.
    unlock HP with 0.
    unlock HQ.
    lock HP; lock HQ with nat.
    unlock * with nat.
    unlock *.
    auto.
  Qed.
End LockTests.

(* Lock hypotheses after rewriting to avoid infinite loops. *)
(*
Inductive _REWRITE_LOCK.
Ltac rewrite_if :=
  repeat match goal with
         | |- context[match ?b with | _ => _ end] =>
           match goal with
           | H: b = _ |- _ => rewrite H; lock H with _REWRITE_LOCK
           | H: _ = b |- _ => rewrite <- H; lock H with _REWRITE_LOCK
           end
         end; unlock * with _REWRITE_LOCK.
*)

(* Destruct one match case in H and try to solve with tac. *)
Ltac case1 H tac :=
  let H' := fresh H "_case" in
  lazymatch type of H with
  | context[match ?b with _ => _ end] => destruct b eqn:H'; try tac
  end.

Ltac case1' H tac :=
  let H' := fresh H "_case" in
  let rec inner := fun c =>
      match c with (_ ?c') => inner c' | _ => c end in
  lazymatch type of H with
  | context[match ?b with _ => _ end] =>
    let b' := inner b in
    destruct b' eqn:H'; simpl in H; try tac
  end.

(* Repeatedly destruct match cases in H and try to solve with tac. *)
Tactic Notation "cases" hyp(H) "by" tactic3(tac) :=
  repeat case1 H tac.
Tactic Notation "cases" hyp(H) :=
  cases H by discriminate.
Tactic Notation "cases" "*" "by" tactic3(tac) :=
  repeat match goal with
         | H: _ |- _ => progress cases H by tac
         end.
Tactic Notation "cases" "*" :=
  repeat match goal with
         | H: _ |- _ => progress cases H
         end.

Tactic Notation "cases'" hyp(H) "by" tactic3(tac) :=
  repeat case1' H tac.
Tactic Notation "cases'" hyp(H) :=
  cases' H by discriminate.
Tactic Notation "cases'" "*" "by" tactic3(tac) :=
  repeat match goal with
         | H: _ |- _ => progress cases' H by tac
         end.
Tactic Notation "cases'" "*" :=
  repeat match goal with
         | H: _ |- _ => progress cases' H
         end.

(* Destruct match cases in H and solve with tac until it would leave more than one goal. *)
Tactic Notation "cases" "-branch" hyp(H) "by" tactic3(tac) :=
  repeat (solve [case1 H tac] || (case1 H tac; [])).
Tactic Notation "cases" "-branch" hyp(H) :=
  cases -branch H by easy.
Tactic Notation "cases" "-branch" "*" "by" tactic3(tac) :=
  repeat match goal with
         | H: _ |- _ => progress cases -branch H by tac
         end.
Tactic Notation "cases" "-branch" "*" :=
  repeat match goal with
         | H: _ |- _ => progress cases -branch H
         end.

(* Destruct one match case in the goal and try to solve with tac. *)
Ltac case_goal tac :=
  let H' := fresh "goal_case" in
  lazymatch goal with
  | |- context[match ?b with _ => _ end] => destruct b eqn:H'; try tac
  end.

(* Repeatedly destruct match cases in the goal and try to solve with tac. *)
Tactic Notation "cases" "in" "goal" "by" tactic3(tac) :=
  repeat case_goal tac.
Tactic Notation "cases" "in" "goal" :=
  cases in goal by discriminate.

(* Split conjunction and existentials in the goal. *)
Ltac split_conj :=
  repeat match goal with
         | |- _ /\ _ => split
         end.
Ltac split_ex :=
  repeat match goal with
         | |- exists _, _ => esplit
         end.
Ltac split_all := repeat (split_conj || split_ex).

(* Destruct conjunction and existentials in hypotheses. *)
Ltac _destr_all H and ex and_tac ex_tac :=
  let Hl := fresh H "_l" in
  let Hr := fresh H "_r" in
  lazymatch type of H with
  | _ /\ _ =>
    lazymatch and with
    | true => destruct H as (Hl & Hr); try and_tac Hl; try and_tac Hr
    | _ => idtac
    end
  | exists _, _ =>
    lazymatch ex with
    | true => destruct H as (? & H); try ex_tac H
    | _ => idtac
    end
  end.
Ltac destr_conj H := _destr_all H true false destr_conj idtac.
Ltac destr_ex H := _destr_all H false true idtac destr_ex.
Ltac destr_all H := _destr_all H true true destr_all destr_all.
Tactic Notation "destr_conj" "*" :=
  repeat match goal with
         | H: _ /\ _ |- _ => destr_conj H
         end.
Tactic Notation "destr_ex" "*" :=
  repeat match goal with
         | H: exists _, _ |- _ => destr_ex H
         end.
Tactic Notation "destr_all" "*" :=
  repeat (destr_conj * || destr_ex *).

Ltac auto_eqdec :=
  repeat red; intros [] []; solve
  [ (* solve cases with mismatching constructors *)
    right; intros ?; congruence
  | repeat
    ( match goal with [H1 : ?T, H2 : ?T |- _] =>
        match type of T with
        | Set =>
          destruct (decide (H1 = H2));
          [ subst H2
          | right; let C := fresh in intros C; injection C as ?; contradiction ]
        | Type =>
          destruct (decide (H1 = H2));
          [ subst H2
          | right; let C := fresh in intros C; injection C as ?; contradiction ]
        | Prop =>
          pose proof (Ax.proof_irrelevance _ H1 H2); subst H2
        end end);
        left; reflexivity ].

(* TODO : do better *)
Ltac aggressive_rewrite_l2r n H a :=
  rewrite ?H in *;
  first
  [ guard n = 0(*; idtac "> > > aggression=0" *)
  | (* idtac "> > > aggression≠0 -" n; *)
    repeat (
      (*idtac "> > > trying to rewrite" H;*)
      match goal with
      | [H' : _ |- _ ] =>
        (*idtac "> > > > match on" H';*)
        tryif (constr_eq H H') then
          (*idtac "> > > > > fail:" H "and" H' "same type";*)
          fail
        else
          setoid_rewrite H in H'(*; idtac "> > > > > setoid rewrite" H "in" H'*)
      | [ |- _ ] =>
        (*idtac "> > > > match on goal";*)
          setoid_rewrite H(*; idtac "> > > > > setoid rewrite" H "in goal"*)
      end) ].

Ltac aggressive_rewrite_r2l n H b :=
  rewrite <-?H in *;
  first
  [ guard n = 0(*; idtac "> > > aggression=0" *)
  | (* idtac "> > > aggression≠0 -" n; *)
    repeat (
      (*idtac "> > trying to rewrite <-" H;*)
      match goal with
      | [H' : _ |- _ ] =>
        (*idtac "> > > > match on" H';*)
        tryif (constr_eq H H') then
          (*idtac "> > > > > fail:" H "and" H' "same type";*)
          fail
        else
          setoid_rewrite <-H in H'(*; idtac "> > > > > setoid rewrite <-" H "in" H'*)
      | [ |- _ ] =>
        setoid_rewrite <-H(*; idtac "> > > > > setoid rewrite <-" H "in goal"*)
      end) ].

Ltac is_equiv eq :=
  let H := fresh in
  assert (Equivalence eq) as H by typeclasses eauto;
  clear H.

(* Normalize context and goal using equivalence H with agression level n.
   Given equivalence H, use heristics to pick a direction and rewrite in that direction in each
   hypothesis and conclusion. If n = 0, use tactic `rewrite`. Otherwise, if n ≠ 0, also use
   tactic `setoid_rewrite`. *)
Ltac eq_norm rewrite_l2r rewrite_r2l H n :=
  let is_desirable a :=
    match a with
    | ?a' _ _ _ _ _ _ _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ _ _ _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ _ _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ _ => first [ is_constructor a' ]
    | ?a' _ _ => first [ is_constructor a' ]
    | ?a' _ => first [ is_constructor a' ]
    | ?a' => first [ is_constructor a' ]
    end
  in
  let is_undesirable a :=
    first [ is_proj a ]
  in
  (* identify H as defining an equivalence between terms *)
  match type of H with
  | ?rel ?a ?b =>
    is_equiv rel;
    (*idtac "is_equiv" rel "for" H;*)
    (* rewrite giving preference for left to right *)
    first
    [ (* avoid recursive equivalences *)
      match b with
      | context [a] =>
        (*idtac "> b contains a: rewriting" H "r2l";*)
        rewrite_r2l n H b
      | _ => fail
      end
    | match a with
      | context [b] =>
        (*idtac "> a contains b: rewriting" H "l2r";*)
        rewrite_l2r n H a
      | _ => fail
      end
    (* immediately simplify variables *)
    | is_var a; (*idtac "> a var: rewriting" H "l2r";*) rewrite_l2r n H a
    | is_var b; (*idtac "> b var: rewriting" H "r2l";*) rewrite_r2l n H b
    | (* rewrite from a to b if b seems more desirable *)
      first
      [ is_undesirable a(*; idtac "> a undesirable: rewriting" H "l2r"*)
      | is_desirable b(*; idtac "> b desirable: rewriting" H "l2r"*) ];
      rewrite_l2r n H a
    | (* rewrite from b to a if a seems more desirable *)
      first
      [ is_undesirable b(*; idtac "> b undesirable: rewriting" H "r2l"*)
      | is_desirable a(*; idtac "> a desirable: rewriting" H "r2l"*) ];
      rewrite_r2l n H b
    | (* default to rewriting right *)
      (*idtac "> default: rewriting" H "l2r";*)
      rewrite_l2r n H a ]
  end.

(* Perform eq_norm for each hypothesis on the goal. *)
Tactic Notation "eq_norm" "with" integer(n) :=
  repeat (
    repeat
      match goal with
      | [H : ?eq _ _ |- _] =>
        eq_norm aggressive_rewrite_l2r aggressive_rewrite_r2l H n; lock H
      end;
    repeat
      match goal with
      | [H : _LOCK _ |- _] =>
        unlock H
      end).

Tactic Notation "eq_norm" hyp(H) "with" integer(n) :=
  eq_norm aggressive_rewrite_l2r aggressive_rewrite_r2l H n.

Tactic Notation "eq_norm" hyp(H) :=
  eq_norm H with 0.

Tactic Notation "eq_norm" :=
  eq_norm with 0.

(* Break hypotheses in the form `<[ k := v ]> m !! k' = v'` into cases: k=k' and k≠k'. *)
Ltac case_map_update_lookup_hyp_aux H :=
  match type of H with
  (* cases for insert *)
  | context [ lookup ?id (insert ?id _ _) ] =>
    rewrite ?lookup_insert_eq in *; simplify_eq;
    try solve [contradiction]
  | context [ lookup ?id1 (insert ?id0 _ _) ] =>
    destruct (decide (id0 = id1)) as [Heq | Hne];
    [ try subst id0; try subst id1; try rewrite Heq in *;
      rewrite ?lookup_insert_eq in *; simplify_eq
    | rewrite ?lookup_insert_ne in * by assumption ];
    try solve [contradiction]
  | context [ lookup ?id1 (fmap _ (insert ?id0 _ _)) ] =>
    rewrite fmap_insert in H; case_map_update_lookup_hyp_aux H
  (* cases for partial_alter *)
  | context [ lookup ?id (partial_alter _ ?id _) ] =>
    rewrite ?lookup_partial_alter_eq in *; simplify_eq;
    try solve [contradiction]
  | context [ lookup ?id1 (partial_alter _ ?id0 _) ] =>
    destruct (decide (id0 = id1)) as [Heq | Hne];
    [ first [ is_var id0; rewrite Heq in *
            | is_var id1; rewrite <- Heq in *
            | rewrite Heq in * ];
      rewrite ?lookup_partial_alter_eq in *; simplify_eq
    | rewrite ?lookup_partial_alter_ne in * by assumption ];
    try solve [contradiction]
(*
  | lookup_total ?id1 (insert ?id0 _ _) =>
  | alter _ ?id1 (insert ?id0 _ _) =>
*)
  end.

Tactic Notation "case_map_update_lookup" "in" hyp(H) :=
  case_map_update_lookup_hyp_aux H.

Ltac case_map_update_lookup_aux :=
  match goal with
  (* cases for insert *)
  | |- context [ lookup ?id (insert ?id _ _) ] =>
    rewrite ?lookup_insert_eq in *; simplify_eq;
    try solve [contradiction]
  | |- context [ lookup ?id1 (insert ?id0 _ _) ] =>
    destruct (decide (id0 = id1)) as [Heq | Hne];
    [ try subst id0; try subst id1; try rewrite Heq in *;
      rewrite ?lookup_insert_eq in *; simplify_eq
    | rewrite ?lookup_insert_ne in * by assumption ];
    try solve [contradiction]
  | |- context [ lookup ?id1 (fmap _ (insert ?id0 _ _)) ] =>
    rewrite fmap_insert; case_map_update_lookup_aux
  (* cases for partial_alter *)
  | |- context [ lookup ?id (partial_alter _ ?id _) ] =>
    rewrite ?lookup_partial_alter_eq in *; simplify_eq;
    try solve [contradiction]
  | |- context [ lookup ?id1 (partial_alter _ ?id0 _) ] =>
    destruct (decide (id0 = id1)) as [Heq | Hne];
    [ first [ is_var id0; rewrite Heq in *
            | is_var id1; rewrite <- Heq in *
            | rewrite Heq in * ];
      rewrite ?lookup_partial_alter_eq in *; simplify_eq
    | rewrite ?lookup_partial_alter_ne in * by assumption ];
    try solve [contradiction]
(*
  | lookup_total ?id1 (insert ?id0 _ _) =>
  | alter _ ?id1 (insert ?id0 _ _) =>
*)
  end.

Tactic Notation "case_map_update_lookup" := case_map_update_lookup_aux.


Ltac simpl_natb_base H :=
  match type of H with
  | eq (A:=bool) ?l ?r =>
    first
    [ is_constructor l; is_constructor r; inversion H
    | is_constructor l; symmetry in H; simpl_natb_base H ]
  | context [~ (Is_true _)] => rewrite <-negb_True in H; simpl_natb_base H
  | context [Is_true _] => rewrite Is_true_true in H; simpl_natb_base H
  | context [_ =? _ = true] => rewrite Nat.eqb_eq in H
  | context [_ =? _ = false] => rewrite Nat.eqb_neq in H
  | context [_ && _ = true] =>
    rewrite andb_true_iff in H;
    match type of H with _ = true ∧ _ = true =>
      let Hl := fresh H "_l" in let Hr := fresh H "_r" in
      destruct H as [Hl Hr]; simpl_natb_base Hl; simpl_natb_base Hr
    end
  | context [_ && _ = false] =>
    rewrite andb_false_iff in H;
    match type of H with _ = false ∨ _ = false =>
      destruct H as [H | H]; [> simpl_natb_base H ..]
    end
  | context [_ || _ = true] =>
    rewrite orb_true_iff in H;
    match type of H with _ = true ∨ _ = true =>
      destruct H as [H | H]; [> simpl_natb_base H ..]
    end
  | context [_ || _ = false] =>
    rewrite orb_false_iff in H;
    match type of H with _ = false ∧ _ = false =>
      let Hl := fresh H "_l" in let Hr := fresh H "_r" in
      destruct H as [Hl Hr]; simpl_natb_base Hl; simpl_natb_base Hr
    end
  | context [_ <? _ = true] => rewrite Nat.ltb_lt in H
  | context [_ <=? _ = true] => rewrite Nat.leb_le in H
  | context [_ <? _ = false] => rewrite Nat.ltb_ge in H
  | context [_ <=? _ = false] => rewrite Nat.leb_gt in H
  | _ => idtac
  end.

Ltac simpl_natb_goal :=
  match goal with
  | |- eq (A:=bool) ?l ?r =>
    first
    [ is_constructor l; is_constructor r; naive_solver
    | is_constructor l; symmetry; simpl_natb_goal ]
  | |- context [~ (Is_true _)] => rewrite <-negb_True; simpl_natb_goal
  | |- context [Is_true _] => rewrite Is_true_true; simpl_natb_goal
  | |- context [_ =? _ = true] => rewrite Nat.eqb_eq
  | |- context [_ =? _ = false] => rewrite Nat.eqb_neq
  | |- context [_ && _ = true] =>
    rewrite andb_true_iff;
    match goal with |- _ = true ∧ _ = true => split; simpl_natb_goal end
  | |- context [_ && _ = false] =>
    rewrite andb_false_iff;
    match goal with |- _ = false ∨ _ = false =>
      (left; simpl_natb_goal) + (right; simpl_natb_goal)
    end
  | |- context [_ || _ = true] =>
    rewrite orb_true_iff;
    match goal with |- _ = true ∨ _ = true =>
      (left; simpl_natb_goal) + (right; simpl_natb_goal)
    end
  | |- context [_ || _ = false] =>
    rewrite orb_false_iff;
    match goal with |- _ = true ∨ _ = true => split; simpl_natb_goal end
  | |- context [_ <? _ = true] => rewrite Nat.ltb_lt
  | |- context [_ <=? _ = true] => rewrite Nat.leb_le
  | |- context [_ <? _ = false] => rewrite Nat.ltb_ge
  | |- context [_ <=? _ = false] => rewrite Nat.leb_gt
  | _ => idtac
  end.

Tactic Notation "simpl_natb" "in" hyp(H) := simpl_natb_base H.

Tactic Notation "simpl_natb" := simpl_natb_goal.

Tactic Notation "simpl_natb" "in" "*" :=
  repeat match goal with
  | [H : _ |- _] => progress simpl_natb in H
  end; simpl_natb.
