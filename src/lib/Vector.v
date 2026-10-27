Set Implicit Arguments.
Set Primitive Projections.

From refinement.lib Require Export Base Tactics Fin.

From stdpp Require Export vector.

(* Dependent case analysis on a non-empty [fin]: a [Fin.t (S n')] is either
   [F1] or an [FS].  Transparent ([Defined]) so it reduces in later proofs. *)
Lemma fin_caseS {n' : nat} {phi : Fin.t (S n') -> Type}
  (phiFZ : phi ( @Fin.F1 n'))
  (phiFS : forall i' : Fin.t n', phi ( @Fin.FS n' i'))
  : forall i, phi i.
Proof.
  intros i; revert phi phiFZ phiFS.
  exact (
    match i as i in Fin.t n return (match n as m return Fin.t m -> Type with O => fun _ => unit | S m' => fun i => forall phi' : Fin.t (S m') -> Type, phi' ( @Fin.F1 m') -> (forall i' : Fin.t m', phi' ( @Fin.FS m' i')) -> phi' i end) i with
    | @Fin.F1 n' => fun phi : Fin.t (S n') -> Type => fun phiFZ : phi ( @Fin.F1 n') => fun phiFS : forall i' : Fin.t n', phi ( @Fin.FS n' i') => phiFZ
    | @Fin.FS n' i' => fun phi : Fin.t (S n') -> Type => fun phiFS : phi ( @Fin.F1 n') => fun phiFS : forall i' : Fin.t n', phi ( @Fin.FS n' i') => phiFS i'
    end
  ).
Defined.

(* Dependent case analysis on a non-empty [vec]: every [vec A (S n')] is a
   [vcons].  Transparent ([Defined]) so it reduces in later proofs. *)
Lemma vec_caseS {A : Type} {n' : nat} (phi : vec A (S n') -> Type)
  (phi_cons : forall t', forall ts', phi (@vcons A t' n' ts'))
  : forall ts, phi ts.
Proof.
  intros ts. revert phi phi_cons.
  exact (
    match ts as ts in vec _ n return (match n as n return vec A n -> Type with O => fun _ => unit | S n' => fun ts => forall phi : vec A (S n') -> Type, (forall t' : A, forall ts' : vec A n', phi ( @vcons A t' n' ts')) -> phi ts end) ts with
    | @vnil _ => tt
    | @vcons _ t' n' ts' => fun phi => fun phi_S => phi_S t' ts'
    end
  ).
Defined.

(* Corresponds to imap function *)
Fixpoint vimap {A B : Type} {n : nat} (f : fin n -> A -> B) (v : vec A n) : vec B n.
Proof.
(* Logically equivalent to:
  match v with
  | [# ] => [# ]
  | @vcons _ a n' v' => (f 0 a) ::: imap (f ∘ S) v'
  end*)
  destruct v as [| a n' v'].
  - exact vnil.
  - exact ((f 0%fin a) ::: (vimap _ _ _ (λ i, f (FS i)) v')).
Defined.

Lemma vimap_cons
  {A B : Type} {n} (x : A) (v : vec A n) (f : fin (S n) → A → B)
: vimap f (x ::: v) = (f 0%fin x) ::: vimap (λ i, f (FS i)) v.
Proof. reflexivity. Qed.

Lemma vimap_app
  {A B : Type} {m} (v1 : vec A m) {n} (v2 : vec A n) (f : fin (m + n) → A → B)
: vimap f (v1 +++ v2) = vimap (λ i, f (Fin.L _ i)) v1 +++ vimap (λ i, f (Fin.R _ i)) v2.
Proof.
  revert n v2 f. induction v1; intros; cbn in *.
  - rewrite (Ax.eta_expansion_dep f); reflexivity.
  - f_equal; apply IHv1.
Qed.

Lemma vlookup_imap
  {A B : Type} {n} i (a : vec A n) (f : fin n → A → B)
: (vimap f a) !!! i = f i (a !!! i).
Proof.
  induction a; inv_fin i; cbn in *;
  [ reflexivity | intros i; apply IHa ].
Qed.


(* Corresponds to alter function *)
Definition valter {A : Type} {n : nat} f i v : vec A n :=
  vinsert i (f (v !!! i)) v.

Lemma vlookup_alter
  {A : Type} n i (a : vec A n) f
: (valter f i a) !!! i = f (a !!! i).
Proof.
  unfold valter; apply vlookup_insert.
Qed.

Lemma vlookup_alter_ne
  n A i j
  (NEQ : i ≠ j)
  (a : vec n A) f
: (valter f i a) !!! j = a !!! j.
Proof.
  unfold valter. apply vlookup_insert_ne. assumption.
Qed.

(* Corresponds to foldl *)
Fixpoint vfoldl {A B : Type} {n : nat} (f : A → B → A) (a : A) (v : vec B n) :=
  match v with
  | [# ] => a
  | x ::: v' => vfoldl f (f a x) v'
  end.

(* Corresponds to ifoldl *)
Fixpoint vifoldl {A B : Type} {n : nat} (f : A → fin n → B → A) (a : A) (v : vec B n) : A :=
  match v in vec _ n2 return n2 = n → A with
  | [# ] => λ _, a
  | x ::: v' => λ EQ,
      vifoldl (λ a i, f a (eq_rec _ _ (FS i) _ EQ)) (f a (eq_rec _ _ Fin.F1 _ EQ) x) v'
  end eq_refl.

Lemma vifoldl_fmap {A B C : Type} {n : nat} (f : A → fin n → B → A) (g : C → B) (a : A)
  (v : vec C n)
: vifoldl f a (vmap g v) = vifoldl (λ a i c, f a i (g c)) a v.
Proof. revert f a. induction v as [|x k v' IH]; intros f a; cbn; auto. Qed.

Lemma vifoldl_app {A B : Type} {n1 n2 : nat} (f : A → fin (n1 + n2) → B → A)
    (a : A) (v : vec B n1) (w : vec B n2)
: vifoldl f a (v +++ w) =
  vifoldl (λ a i b, f a (Fin.R n1 i) b)
    (vifoldl (λ a i b, f a (Fin.L n2 i) b) a v) w.
Proof.
  revert f a. induction v as [|x k v' IH]; intros f a; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma vifoldl_snoc {A B : Type} {n : nat} (f : A → fin (n + 1) → B → A) (a : A) (v : vec B n) (x : B)
: vifoldl f a (v +++ [# x]) =
  f (vifoldl (λ a i b, f a (Fin.L 1 i) b) a v) (Fin.R n 0%fin) x.
Proof. rewrite vifoldl_app. reflexivity. Qed.

(* Corresponds to ifoldluntil *)
Fixpoint vifoldluntil {A B : Type} {n : nat} (f : A → fin n → B → A * bool) (a : A) (v : vec B n) : A * bool :=
  match v in vec _ n2 return n2 = n → A * bool with
  | [# ] => λ _, (a, true)
  | x ::: v' => λ EQ,
      let '(a', cont) := f a (eq_rec _ _ Fin.F1 _ EQ) x in
      if cont then vifoldluntil (λ a i, f a (eq_rec _ _ (FS i) _ EQ)) a' v' else (a', cont)
  end eq_refl.

(* Step functions that agree on the elements of the vector give the same fold. *)
Lemma vifoldluntil_ext {A B : Type} {n : nat} (f g : A → fin n → B → A * bool) (a : A)
  (v : vec B n) (EXT : ∀ a i, f a i (v !!! i) = g a i (v !!! i))
: vifoldluntil f a v = vifoldluntil g a v.
Proof.
  revert f g a EXT. induction v as [|x k v' IH]; intros f g a EXT; cbn; [reflexivity |].
  rewrite (EXT a 0%fin : f a 0%fin x = g a 0%fin x). destruct (g a 0%fin x) as [a' []]; [| done].
  apply IH. intros. apply EXT.
Qed.

Lemma vifoldluntil_fmap {A B C : Type} {n : nat} (f : A → fin n → B → A * bool) (g : C → B)
  (a : A) (v : vec C n)
: vifoldluntil f a (vmap g v) = vifoldluntil (λ a i c, f a i (g c)) a v.
Proof.
  revert f a. induction v as [|x k v' IH]; intros f a; cbn; [reflexivity |].
  destruct (f a 0%fin (g x)) as [a' []]; [apply IH | reflexivity].
Qed.

Lemma vifoldluntil_app {A B : Type} {n1 n2 : nat} (f : A → fin (n1 + n2) → B → A * bool)
  (a : A) (v : vec B n1) (w : vec B n2)
: vifoldluntil f a (v +++ w) =
  let '(a', cont) := vifoldluntil (λ a i b, f a (Fin.L n2 i) b) a v in
  if cont then vifoldluntil (λ a i b, f a (Fin.R n1 i) b) a' w else (a', false).
Proof.
  revert f a. induction v as [|x k v' IH]; intros f a; cbn; [reflexivity |].
  destruct (f a 0%fin x) as [a' []] eqn:E; setoid_rewrite E; [apply IH | reflexivity].
Qed.

Lemma vifoldluntil_snoc {A B : Type} {n : nat} (f : A → fin (n + 1) → B → A * bool) (a : A)
  (v : vec B n) (x : B)
: vifoldluntil f a (v +++ [# x]) =
  let '(a', cont) := vifoldluntil (λ a i b, f a (Fin.L 1 i) b) a v in
  if cont then f a' (Fin.R n 0%fin) x else (a', false).
Proof.
  rewrite vifoldluntil_app. destruct (vifoldluntil _ a v) as [a' []]; [| reflexivity].
  cbn. destruct (f a' (Fin.R n 0%fin) x) as [a'' []]; reflexivity.
Qed.

(* For a "stationary" step function, which leaves the accumulator unchanged whenever it continues,
   the fold either continues past every element, or stops at the first element whose step stops. *)
Lemma vifoldluntil_stationary {A B : Type} {n : nat} (f : A → fin n → B → A * bool)
  (STAT : ∀ a j x, (f a j x).2 = true → (f a j x).1 = a)
  (a : A) (v : vec B n)
: match vifoldluntil f a v with
  | (a', true) => a' = a ∧ ∀ j, (f a j (v !!! j)).2 = true
  | (a', false) =>
    ∃ j : fin n,
      (∀ k : fin n, k < j → (f a k (v !!! k)).2 = true) ∧ f a j (v !!! j) = (a', false)
  end.
Proof.
  revert f STAT. induction v as [|x m v IH]; intros f STAT; [split; [done | intros j; inv_fin j] |].
  cbn. destruct (f a 0%fin x) as [a1 []] eqn:F.
  - assert (a1 = a) as -> by (pose proof (STAT a 0%fin x) as S; rewrite F in S; by apply S).
    specialize (IH (λ a i, f a (FS i)) (λ a j x, STAT a (FS j) x)).
    destruct (vifoldluntil _ a v) as [a' []].
    + destruct IH as [-> IH]. split; [done |]. intros j; inv_fin j; [cbn; by rewrite F | apply IH].
    + destruct IH as (j & PRE & FJ). exists (FS j). split; [| done].
      intros k; inv_fin k; [cbn; by rewrite F |]. intros k LT. apply PRE. cbn in LT. lia.
  - exists 0%fin. split; [intros k LT; cbn in LT; lia | done].
Qed.
