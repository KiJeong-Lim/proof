Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.

Module AuxiliaryPalatina.

Import ListNotations.

Section Utilities.

Definition case_eq {A : Type} : forall x : A, forall y : A, forall phi : forall x0 : A, x0 = y -> Type, phi y eq_refl -> forall H : x = y, phi x H :=
  fun x : A =>
  fun y : A =>
  fun phi : forall x0 : A, x0 = y -> Type =>
  fun phi_y : phi y eq_refl =>
  fun H : eq x y =>
  match H as H0 in eq _ y0 return forall phi0 : forall x0 : A, x0 = y0 -> Type, phi0 y0 eq_refl -> phi0 x H0 with
  | eq_refl =>
    fun phi0 : forall x0 : A, x0 = x -> Type =>
    fun phi_y0 : phi0 x eq_refl =>
    phi_y0
  end phi phi_y
.

Lemma div_mod_uniqueness :
  forall a : nat,
  forall b : nat,
  forall q : nat,
  forall r : nat,
  a = b * q + r ->
  r < b ->
  a / b = q /\ a mod b = r.
Proof with try (lia || now (firstorder; eauto)).
  assert (H : forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
  { intros x y; constructor.
    - intros H.
      induction H...
      destruct IHle as [z H0].
      exists (S z)...
    - intros H.
      destruct H as [z H]...
  }
  intros a b q r H1 H2.
  assert (H0 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
  assert (H3 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
  assert (H4 : ~ q > a / b).
  { intros H4.
    enough (H5 : exists z : nat, q = S (a / b + z))...
    destruct H5 as [z H5].
    enough (b * q + r >= b * S (a / b) + r)...
  }
  assert (H5 : ~ q < a / b).
  { intros H5.
    enough (H6 : exists z : nat, a / b = S (q + z))...
    destruct H6 as [z H6].
    enough (b * q + a mod b >= b * S (a / b) + a mod b)...
  }
  enough (q = a / b)...
Qed.

Definition first_nat : (nat -> bool) -> nat -> nat :=
  fun p : nat -> bool =>
  fix first_nat_fix (n : nat) {struct n} : nat :=
  match n with
  | 0 => 0
  | S n' => if p (first_nat_fix n') then first_nat_fix n' else n
  end
.

Theorem well_ordering_principle : 
  forall p : nat -> bool,
  forall n : nat,
  p n = true ->
  let m : nat := first_nat p n in
  p m = true /\ (forall i : nat, p i = true -> i >= m).
Proof with eauto. (* This proof has been improved by JunYoung Clare Jang. *)
  intros p n H3 m.
  assert (forall x : nat, p x = true -> p (first_nat p x) = true).
  { induction x...
    simpl.
    destruct (p (first_nat p x)) eqn:H0...
  }
  split...
  intros i H4.
  enough (forall x : nat, first_nat p x <= x).
  enough (forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
  enough (forall x : nat, forall y : nat, p y = true -> first_nat p x <= y)...
  - intros x y H2.
    destruct (Compare_dec.le_lt_dec x y).
    + eapply Nat.le_trans...
    + replace (first_nat p x) with (first_nat p y)...
  - intros x H1 y H2.
    induction H2; simpl.
    + rewrite H1...
    + rewrite <- IHle, H1...
  - induction x...
    simpl.
    destruct (p (first_nat p x)) eqn: H0...
Qed.

Fixpoint sum_from_0_to (n : nat) {struct n} : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_from_0_to n'
  end
.

Proposition sum_from_0_to_is :
  forall n : nat,
  2 * sum_from_0_to n = n * (S n).
Proof with lia.
  induction n; simpl in *...
Qed.

Fixpoint cantor_pairing (n : nat) {struct n} : nat * nat :=
  match n with
  | 0 => (0, 0)
  | S n' =>
    match cantor_pairing n' with
    | (0, y) => (S y, 0)
    | (S x, y) => (x, S y)
    end
  end
.

Lemma cantor_pairing_is_surjective :
  forall x : nat,
  forall y : nat,
  (x, y) = cantor_pairing (sum_from_0_to (x + y) + y).
Proof with (lia || eauto).
  enough (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y))...
  induction z.
  - intros y x H.
    assert (H0 : x = 0)...
    assert (H1 : y = 0)...
    subst...
  - induction y.
    + intros x H.
      assert (H0 : x = S z)...
      subst.
      simpl.
      destruct (cantor_pairing (z + sum_from_0_to z + 0)) eqn: H0.
      assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
      rewrite Nat.add_0_r, Nat.add_comm in H0.
      rewrite H0 in H1.
      inversion H1; subst...
    + intros x H.
      enough (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)).
      { assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by now simpl...
        simpl.
        rewrite H1, <- H0...
      }
      apply (IHy (S x))...
Qed.

Lemma cantor_pairing_is_injective :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) ->
  n = sum_from_0_to (x + y) + y.
Proof with (lia || eauto).
  induction n; simpl.
  - intros x y H.
    inversion H; subst...
  - intros x y H.
    destruct (cantor_pairing n) as [x' y'] eqn: H0.
    destruct x'; (inversion H; subst).
    + repeat (rewrite Nat.add_0_r).
      simpl.
      rewrite (IHn 0 y' eq_refl), Nat.add_0_l...
    + rewrite (IHn (S x) y' eq_refl).
      assert (H1 : forall x' : nat, S x' + y' = x' + S y')...
      repeat (rewrite H1)...
Qed.

Corollary cantor_pairing_is :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
Proof with eauto using cantor_pairing_is_injective, cantor_pairing_is_surjective.
  split...
  intros H.
  subst...
Qed.

Definition S_0 {A : Type} : forall n : nat, S n = 0 -> A :=
  fun n : nat =>
  fun H0 : S n = 0 =>
  let H1 : 0 = S n := @eq_ind nat (S n) (fun x : nat => x = S n) eq_refl 0 H0 in
  let H2 : False := @eq_ind nat 0 (fun x : nat => if Nat.eqb x 0 then True else False) I (S n) H1 in
  False_rect A H2
.

Definition S_S : forall n1 : nat, forall n2 : nat, S n1 = S n2 -> n1 = n2 :=
  fun n1 : nat =>
  fun n2 : nat =>
  fun H0 : S n1 = S n2 =>
  @eq_ind nat (S n1) (fun x : nat => n1 = pred x) eq_refl (S n2) H0
.

Inductive FinSet : nat -> Set :=
| FZ : forall n : nat, FinSet (S n) 
| FS : forall n : nat, FinSet n -> FinSet (S n)
.

Definition FinSet_case0 {P : FinSet 0 -> Type} : forall i : FinSet 0, P i :=
  fun i : FinSet 0 =>
  match i as i0 in FinSet Sn return Sn = 0 -> P i with
  | FZ n => S_0 n
  | FS n i' => S_0 n
  end eq_refl
.

Definition FinSet_caseS {n : nat} {P : FinSet (S n) -> Type} : P (FZ n) -> (forall i' : FinSet n, P (FS n i')) -> (forall i : FinSet (S n), P i) :=
  fun PZ : P (FZ n) =>
  fun PS : forall i' : FinSet n, P (FS n i') =>
  fun i : FinSet (S n) =>
  match i as i0 in FinSet Sn0 return (match Sn0 as Sn1 return FinSet Sn1 -> Type with 0 => FinSet_case0 | S n0 => fun i1 : FinSet (S n0) => forall P0 : FinSet (S n0) -> Type, P0 (FZ n0) -> (forall i' : FinSet n0, P0 (FS n0 i')) -> P0 i1 end) i0 with
  | FZ n0 => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PZ0
  | FS n0 i' => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PS0 i'
  end P PZ PS
.

Definition FinSet_rectS {P : forall n : nat, FinSet n -> Type} : (forall n : nat, P (S n) (FZ n)) -> (forall n : nat, forall i' : FinSet n, P n i' -> P (S n) (FS n i')) -> (forall n : nat, forall i : FinSet (S n), P (S n) i) :=
  fun PZ : forall n : nat, P (S n) (FZ n) =>
  fun PS : forall n : nat, forall i' : FinSet n, P n i' -> P (S n) (FS n i') =>
  fix FinSet_rectS_fix (n : nat) (i : FinSet (S n)) {struct i} : P (S n) i :=
  match i as i0 in FinSet Sn0 return P Sn0 i0 with
  | FZ n0 => PZ n0
  | FS n0 i' =>
    match n0 as n1 return forall i0' : FinSet n1, P (S n1) (FS n1 i0') with
    | 0 => fun i0' : FinSet 0 => @FinSet_case0 (fun i1 : FinSet 0 => P 1 (FS 0 i1)) i0'
    | S n0' => fun i0' : FinSet (S n0') => PS (S n0') i0' (FinSet_rectS_fix n0' i0')
    end i'
  end
.

Lemma forallb_true_iff {A : Type} {p : A -> bool} (xs : list A) :
  forallb p xs = true <-> forall x : A, In x xs -> p x = true.
Proof with try now firstorder.
  induction xs; simpl...
  rewrite andb_true_iff.
  split...
  intros H0 x H1.
  destruct H0; destruct H1...
  rewrite H1 in H...
Qed.

Definition fold_right_max_0 : list nat -> nat :=
  fold_right max 0
.

Lemma fold_right_max_0_in :
  forall ns : list nat,
  forall n : nat,
  In n ns ->
  fold_right_max_0 ns >= n.
Proof with (lia || eauto).
  unfold fold_right_max_0.
  induction ns as [| n' ns]; simpl...
  intros n H.
  destruct H...
  enough (fold_right max 0 ns >= n)...
Qed.

Lemma fold_right_max_0_app :
  forall ns1 : list nat,
  forall ns2 : list nat,
  fold_right_max_0 (ns1 ++ ns2) = max (fold_right_max_0 ns1) (fold_right_max_0 ns2).
Proof with (lia || eauto).
  unfold fold_right_max_0.
  induction ns1 as [| n1 ns1]; simpl... 
  intros n.
  rewrite IHns1...
Qed.

Lemma property1_of_fold_right_max_0 (Phi : nat -> Prop) (Phi_dec : forall i : nat, {Phi i} + {~ Phi i}) :
  forall ns : list nat,
  (forall i : nat, Phi i -> In i ns) ->
  forall n : nat,
  Phi n ->
  fold_right max 0 ns >= n.
Proof with (lia || eauto).
  induction ns; simpl.
  - intros H n H0.
    contradiction (H n).
  - intros H n H0.
    destruct (Compare_dec.le_lt_dec n a)...
    enough (fold_right max 0 ns >= n)...
    destruct (Phi_dec n).
    + destruct (H n p)...
      enough (forall ks : list nat, forall k : nat, In k ks -> fold_right max 0 ks >= k) by firstorder.
      induction ks; simpl...
      intros k H2.
      destruct H2...
      enough (fold_right Init.Nat.max 0 ks >= k)...
    + apply IHns...
      intros.
      destruct (H i H1)...
      subst.
      contradiction.
Qed.

Lemma property2_of_fold_right_max_0 :
  forall ns : list nat,
  forall n : nat,
  fold_right max 0 ns > n <-> (exists i : nat, In i ns /\ i > n).
Proof with (lia || eauto).
  induction ns; simpl.
  - split...
    now firstorder.
  - intros n.
    destruct (Compare_dec.le_lt_dec a (fold_right Init.Nat.max 0 ns)); split...
    + intros H.
      assert (H0 : fold_right Init.Nat.max 0 ns > n)...
      destruct (proj1 (IHns n) H0) as [i].
      now firstorder.
    + intros H.
      destruct H as [i].
      destruct H.
      destruct H.
      * subst...
      * enough (fold_right max 0 ns > n)...
        apply IHns...
    + intros H.
      exists a...
    + intros H.
      destruct H as [i].
      destruct H.
      destruct H.
      * subst...
      * enough (fold_right Init.Nat.max 0 ns > n)...
        apply IHns...
Qed.

Lemma property3_of_fold_right_max_0 :
  forall ns1 : list nat,
  forall ns2 : list nat,
  fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
Proof.
  apply fold_right_max_0_app.
Qed.

Lemma property4_of_fold_right_max_0 :
  forall ns : list nat,
  forall n : nat,
  In n ns ->
  fold_right max 0 ns >= n.
Proof with (lia || eauto).
  induction ns; simpl...
  intros n H.
  destruct H...
  enough (fold_right max 0 ns >= n)...
Qed.

Lemma property5_of_fold_right_max_0 :
  forall ns1 : list nat,
  forall ns2 : list nat,
  (forall n : nat, In n ns1 -> In n ns2) ->
  fold_right max 0 ns1 <= fold_right max 0 ns2.
Proof with (lia || eauto).
  induction ns1; simpl...
  intros ns2 H.
  destruct (Compare_dec.le_lt_dec a (fold_right max 0 ns1)).
  - enough (fold_right max 0 ns1 <= fold_right max 0 ns2)...
  - enough (a <= fold_right max 0 ns2)...
    apply property4_of_fold_right_max_0...
Qed.

Lemma fold_right_max_0_ext :
  forall ns1 : list nat,
  forall ns2 : list nat,
  (forall n : nat, In n ns1 <-> In n ns2) ->
  fold_right max 0 ns1 = fold_right max 0 ns2.
Proof with try now firstorder.
  intros.
  enough (fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
  split; apply property5_of_fold_right_max_0...
Qed.

End Utilities.

#[global] Create HintDb naive_set_theory.

Definition Ensemble (A : Type) : Type :=
  A -> Prop
.

Definition member {A : Type} : A -> Ensemble A -> Prop :=
  fun x : A => fun xs : Ensemble A => xs x
.

#[global] Hint Unfold member : naive_set_theory.

Definition isSubsetOf {A : Type} : Ensemble A -> Ensemble A -> Prop :=
  fun xs1 : Ensemble A => fun xs2 : Ensemble A => forall x : A, member x xs1 -> member x xs2
.

#[global] Hint Unfold isSubsetOf : naive_set_theory.

Inductive full {A : Type} : Ensemble A :=
| In_full {x : A} : member x full
.

#[global] Hint Constructors full : naive_set_theory.

Inductive empty {A : Type} : Ensemble A :=
.

#[global] Hint Constructors empty : naive_set_theory.

Inductive singleton {A : Type} : A -> Ensemble A :=
| In_singleton {x : A} : member x (singleton x)
.

#[global] Hint Constructors singleton : naive_set_theory.

Inductive unions {A : Type} : Ensemble (Ensemble A) -> Ensemble A :=
| In_unions {x : A} {xss : Ensemble (Ensemble A)} : forall xs : Ensemble A, member x xs -> member xs xss -> member x (unions xss)
.

#[global] Hint Constructors unions : naive_set_theory.

Inductive union {A : Type} : Ensemble A -> Ensemble A -> Ensemble A :=
| Inl_union {x : A} {xs1 : Ensemble A} {xs2 : Ensemble A} : member x xs1 -> member x (union xs1 xs2)
| Inr_union {x : A} {xs1 : Ensemble A} {xs2 : Ensemble A} : member x xs2 -> member x (union xs1 xs2)
.

#[global] Hint Constructors union : naive_set_theory.

Inductive intersection {A : Type} : Ensemble A -> Ensemble A -> Ensemble A :=
| In_intersection {x : A} {xs1 : Ensemble A} {xs2 : Ensemble A} : member x xs1 -> member x xs2 -> member x (intersection xs1 xs2)
.

#[global] Hint Constructors intersection : naive_set_theory.

Inductive image {A : Type} {B : Type} : (A -> B) -> Ensemble A -> Ensemble B :=
| In_image {xs : Ensemble A} : forall x : A, forall f : A -> B, member x xs -> member (f x) (image f xs)
.

#[global] Hint Constructors image : naive_set_theory.

Inductive inverse_image {A : Type} {B : Type} : (A -> B) -> Ensemble B -> Ensemble A :=
| In_inverse_image {f : A -> B} {ys : Ensemble B} : forall x : A, member (f x) ys -> member x (inverse_image f ys)
.

#[global] Hint Constructors inverse_image : naive_set_theory.

Definition NonEmpty {A : Type} : Ensemble A -> Prop :=
  fun xs : Ensemble A => exists x : A, member x xs
.

#[global] Hint Unfold NonEmpty : naive_set_theory.

End AuxiliaryPalatina.

Module DomainTheory.

Import ListNotations.

Import AuxiliaryPalatina.

#[global] Create HintDb domain_theory_hints.

Class TopologicalSpace (X : Set) : Type :=
  { is_open_set : Ensemble X -> Prop
  ; open_set_for_full :
    is_open_set full
  ; open_set_for_unions :
    forall xss : Ensemble (Ensemble X),
    (forall xs : Ensemble X, member xs xss -> is_open_set xs) ->
    is_open_set (unions xss)
  ; open_set_for_intersection :
    forall xs1 : Ensemble X,
    forall xs2 : Ensemble X,
    is_open_set xs1 ->
    is_open_set xs2 ->
    is_open_set (intersection xs1 xs2)
  }
.

#[global] Hint Resolve open_set_for_full : domain_theory_hints.

#[global] Hint Resolve open_set_for_unions : domain_theory_hints.

#[global] Hint Resolve open_set_for_intersection : domain_theory_hints.

Definition is_continuous_map {X : Set} {Y : Set} `{X_is_topology : TopologicalSpace X} `{Y_is_topology : TopologicalSpace Y} : (X -> Y) -> Prop :=
  fun f : X -> Y => forall ys : Ensemble Y, is_open_set ys -> is_open_set (inverse_image f ys)
.

#[global] Hint Unfold is_continuous_map : domain_theory_hints.

Class Poset_minor (X : Set) : Type :=
  { eql : X -> X -> Prop
  ; leq : X -> X -> Prop
  ; requriesEquivalence :> Equivalence eql
  ; requiresPreOrder :> PreOrder leq
  ; requiresPartialOrder :> PartialOrder eql leq
  }
.

Local Notation "x =-= y" := (eql x y) (at level 70, no associativity) : type_scope.

Class Poset (Y : Set) : Type :=
  { requiresPoset_minor :> Poset_minor Y
  ; substitutablity {X : Set} {requiresPoset_minor : Poset_minor X} : forall x1 : X, forall x2 : X, x1 =-= x2 -> forall f : X -> Y, f x1 =-= f x2
  }
.

#[global] Hint Resolve substitutablity : domain_theory_hints.

Lemma leq_refl1 {D : Set} `{D_is_poset_minor : Poset_minor D} :
  forall x1 : D,
  forall x2 : D,
  x1 =-= x2 ->
  leq x1 x2.
Proof with eauto.
  intros.
  apply partial_order_equivalence in H.
  destruct H...
Qed.

#[global] Hint Resolve leq_refl1 : domain_theory_hints.

Lemma leq_refl2 {D : Set} `{D_is_poset_minor : Poset D} :
  forall x1 : D,
  forall x2 : D,
  x1 =-= x2 ->
  leq x2 x1.
Proof with eauto.
  intros.
  apply partial_order_equivalence in H.
  destruct H...
Qed.

#[global] Hint Resolve leq_refl2 : domain_theory_hints.

Lemma leq_asym {D : Set} `{D_is_poset_minor : Poset_minor D} :
  forall x1 : D,
  forall x2 : D,
  leq x1 x2 ->
  leq x2 x1 ->
  x1 =-= x2.
Proof with eauto.
  intros.
  apply antisymmetry...
Qed.

#[global] Hint Resolve leq_asym : domain_theory_hints.

Lemma leq_trans {D : Set} `{D_is_poset_minor : Poset_minor D} :
  forall x1 : D,
  forall x2 : D,
  forall x3 : D,
  leq x1 x2 ->
  leq x2 x3 ->
  leq x1 x3.
Proof.
  intros.
  apply (transitivity (R:=leq) H H0).
Qed.

#[global] Hint Resolve leq_trans : domain_theory_hints.

Definition directed {D : Set} `{D_is_poset : Poset D} : Ensemble D -> Prop :=
  fun X : Ensemble D => NonEmpty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ leq x1 x3 /\ leq x2 x3)
.

#[global] Hint Unfold directed : domain_theory_hints.

Definition is_supremum {D : Set} `{D_is_poset : Poset D} : D -> Ensemble D -> Prop :=
  fun sup_xs : D => fun xs : Ensemble D => forall x : D, leq sup_xs x <-> (forall x0 : D, member x0 xs -> leq x0 x)
.

#[global] Hint Unfold is_supremum : domain_theory_hints.

Lemma supremum_unique {D : Set} `{D_is_poset_minor : Poset D} :
  forall X : Ensemble D,
  forall x1 : D,
  forall x2 : D,
  is_supremum x1 X ->
  is_supremum x2 X <-> x1 =-= x2.
Proof with eauto with *.
  intros X x1 x2 H1.
  split; intros H2.
  - apply leq_asym.
    + apply H1.
      intros x H.
      apply H2...
    + apply H2.
      intros x H.
      apply H1...
  - intros x.
    split.
    + intros H3 x' H4.
      apply H1...
    + intros H4.
      apply (leq_trans x2 x1 x)...
      apply H1...
Qed.

#[global] Hint Resolve supremum_unique : domain_theory_hints.

Lemma supremum_ext {D : Set} `{D_is_poset_minor : Poset D} :
  forall X1 : Ensemble D,
  forall X2 : Ensemble D,
  isSubsetOf X1 X2 ->
  isSubsetOf X2 X1 ->
  forall x1 : D,
  forall x2 : D,
  is_supremum x1 X1 ->
  is_supremum x2 X2 <-> x1 =-= x2.
Proof with eauto with *.
  intros X1 X2 H H0 x1 x2 H1.
  split; intros H2.
  - apply leq_asym.
    + apply H1.
      intros x H3.
      apply H2...
    + apply H2.
      intros x H3.
      apply H1...
  - intros x.
    split.
    + intros H3 x' H4.
      apply H1...
    + intros H4.
      apply (leq_trans x2 x1 x)...
      apply H1...
Qed.

#[global] Hint Resolve supremum_ext : domain_theory_hints.

Class CompletePartialOrder (D : Set) `{requiresPoset : Poset D} : Type :=
  { bottom : D
  ; bottom_least :
    forall x : D,
    leq bottom x
  ; supremum_exists :
    forall xs : Ensemble D,
    directed xs ->
    {sup_xs : D | is_supremum sup_xs xs}
  }
.

#[global] Hint Resolve bottom_least : domain_theory_hints.

#[global] Hint Resolve supremum_exists : domain_theory_hints.

Class CompleteLattice (D : Set) `{requiresPoset : Poset D} : Type :=
  { supremum_always_exists :
    forall xs : Ensemble D,
    {sup_xs : D | is_supremum sup_xs xs}
  }
.

#[global] Hint Resolve supremum_always_exists : domain_theory_hints.

Global Program Instance each_complete_lattice_is_a_cpo (D : Set) `{D_is_poset : Poset D} (requiresCompleteLattice : CompleteLattice D) : CompletePartialOrder D :=
  { bottom := supremum_always_exists empty
  }
.

Next Obligation with eauto with naive_set_theory.
  assert (H := proj2_sig (supremum_always_exists empty)).
  simpl in H.
  apply H.
  intros.
  inversion H0.
Qed.

Next Obligation with eauto with naive_set_theory.
  apply supremum_always_exists.
Qed.

Global Program Instance scott_topology (D : Set) `{D_is_poset : Poset D} (requiresCompletePartialOrder : CompletePartialOrder D) : TopologicalSpace D :=
  { is_open_set := fun O : Ensemble D => (forall x : D, forall y : D, member x O -> leq x y -> member y O) /\ (forall X : Ensemble D, directed X -> forall sup_X : D, is_supremum sup_X X -> member sup_X O -> NonEmpty (intersection X O))
  }
.

Next Obligation with eauto with *.
  split...
  intros.
  destruct H.
  destruct H.
  exists x...
Qed.

Next Obligation with eauto with *.
  split.
  - intros.
    destruct H0.
    apply (In_unions xs)...
    apply (proj1 (H xs H2) x y)...
  - intros.
    inversion H0; subst.
    inversion H2; subst. 
    destruct (proj2 (H xs H6) X H0 sup_X H1 H5) as [x].
    inversion H7; subst.
    exists x...
Qed.

Next Obligation with eauto with *.
  split.
  - intros.
    destruct H3...
  - intros.
    inversion H5; subst.
    destruct (H2 X H3 sup_X H4 H6) as [x1].
    destruct (H1 X H3 sup_X H4 H7) as [x2].
    inversion H3; subst.
    inversion H8; inversion H9; subst.
    destruct (H11 x1 H12 x2 H17) as [x].
    destruct H14.
    destruct H15.
    exists x...
Qed.

Definition U_x {D : Set} `{D_is_cpo : CompletePartialOrder D} : D -> Ensemble D :=
  fun x : D => fun z : D => ~ leq z x
.

Lemma U_x_is_open {D : Set} `{D_is_cpo : CompletePartialOrder D} :
  forall x : D,
  is_open_set (U_x x).
Proof with eauto with *.
  intros x.
  enough ( claim1 :
    forall y : D,
    forall z : D,
    member y (U_x x) ->
    leq y z ->
    member z (U_x x)
  ).
  { split...
    intros.
    inversion H; subst...
    assert (claim2 : ~ (forall x0 : D, leq x0 x \/ ~ member x0 X)).
    { intros H4.
      contradiction H1.
      unfold is_supremum in H0.
      apply (proj2 (H0 x)).
      intros x0 H5.
      destruct (H4 x0)...
      contradiction.
    }
    apply not_all_ex_not in claim2.
    destruct claim2 as [x1].
    exists x1.
    apply not_or_and in H4.
    destruct H4.
    apply NNPP in H5.
    constructor...
  }
  unfold U_x, member.
  intros y z H H0 H1.
  contradiction H.
  apply (transitivity (R:=leq) H0 H1).
Qed.

Definition characterization_of_continuous_map_on_cpos {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} : (D -> D') -> Prop :=
  fun f : D -> D' =>
  forall X : Ensemble D,
  directed X ->
  let Y : Ensemble D' := image f X in
  exists sup_X : D, exists sup_Y : D', is_supremum sup_X X /\ is_supremum sup_Y Y /\ f sup_X =-= sup_Y
.

Lemma continuous_maps_on_cpos_are_always_monotonic {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall f : D -> D',
  is_continuous_map f ->
  forall x1 : D,
  forall x2 : D,
  leq x1 x2 ->
  leq (f x1) (f x2).
Proof with eauto with *.
  intros f H x1 x2 H0.
  apply NNPP.
  intros H1.
  assert (H2 : member (f x1) (U_x (f x2))) by now unfold U_x.
  assert (H3 : member x1 (inverse_image f (U_x (f x2)))) by now constructor.
  assert (H4 : is_open_set (inverse_image f (U_x (f x2)))) by now apply H, U_x_is_open.
  assert (H5 : member x2 (inverse_image f (U_x (f x2)))) by now apply (proj1 H4 x1 x2).
  enough (H6 : member (f x2) (U_x (f x2)))...
  inversion H5...
Qed.

Lemma property1_of_Scott_topology {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall f : D -> D',
  is_continuous_map f ->
  forall X : Ensemble D,
  directed X ->
  directed (image f X).
Proof with eauto with *.
  intros f H X H0.
  destruct H0 as [H0 H1].
  assert (H2 : forall x1 : D, forall x2 : D, leq x1 x2 -> leq (f x1) (f x2)) by now apply continuous_maps_on_cpos_are_always_monotonic.
  split.
  - destruct H0 as [x0]...
  - intros y1 H3 y2 H4.
    inversion H3; inversion H4; subst.
    rename x into x1, x0 into x2.
    destruct (H1 x1 H5 x2 H9) as [x3].
    exists (f x3).
    destruct H6.
    destruct H7.
    repeat split...
Qed.

Lemma property2_of_Scott_topology {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall f : D -> D',
  is_continuous_map f ->
  forall X : Ensemble D,
  directed X ->
  forall sup_X : D,
  is_supremum sup_X X ->
  directed (image f X) ->
  {sup_Y : D' | is_supremum sup_Y (image f X) /\ f sup_X =-= sup_Y}.
Proof with eauto with *.
  intros f H X H0 sup_X H1 H2.
  set (Y := image f X).
  assert (H3 : forall x1 : D, forall x2 : D, leq x1 x2 -> leq (f x1) (f x2)) by now apply continuous_maps_on_cpos_are_always_monotonic.
  destruct (supremum_exists Y H2) as [sup_Y H4].
  exists sup_Y.
  assert (claim1 : leq sup_Y (f sup_X)).
  { apply H4.
    intros y H5.
    inversion H5; subst.
    apply H3, H1...
  }
  assert (claim2 : leq (f sup_X) sup_Y).
  { apply NNPP.
    intros H5.
    assert (H6 : member (f sup_X) (U_x sup_Y)) by now unfold U_x.
    assert (H7 : member sup_X (inverse_image f (U_x sup_Y))) by now constructor.
    assert (H8 : is_open_set (inverse_image f (U_x sup_Y))) by now apply H, U_x_is_open.
    destruct H8.
    destruct (H9 X H0 sup_X H1 H7) as [x1].
    inversion H10; subst.
    inversion H12; subst.
    contradiction H13.
    apply H4...
  }
  split...
Qed.

Theorem the_main_reason_for_introducing_the_Scott_topology {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall f : D -> D',
  is_continuous_map f <-> characterization_of_continuous_map_on_cpos f.
Proof with eauto with *.
  assert (claim1 : forall f : D -> D', is_continuous_map f -> forall x1 : D, forall x2 : D, leq x1 x2 -> leq (f x1) (f x2)) by apply continuous_maps_on_cpos_are_always_monotonic.
  unfold characterization_of_continuous_map_on_cpos; split; intros H.
  - intros X H0.
    inversion H0; subst.
    set (Y := image f X).
    assert (H3 : directed Y) by now apply property1_of_Scott_topology.
    destruct (supremum_exists X H0) as [sup_X H4].
    exists sup_X.
    destruct (property2_of_Scott_topology f H X H0 sup_X H4 H3) as [sup_Y H5].
    exists sup_Y...
  - assert (claim2 : forall x1 : D, forall x2 : D, leq x1 x2 -> leq (f x1) (f x2)).
    { intros x1 x2 H0.
      set (X := union (singleton x1) (singleton x2)).
      set (Y := image f X).
      assert (H1 : is_supremum x2 X).
      { intros x.
        split.
        - intros H1 x' H2.
          inversion H2; inversion H3; subst...
        - intros H1.
          apply H1...
      }
      assert (H2 : directed X).
      { split.
        - exists x1...
        - intros x1' H2 x2' H3.
          exists x2.
          repeat split...
          + inversion H2; (inversion H4; subst)...
          + inversion H3; (inversion H4; subst)... 
      }
      destruct (H X H2) as [sup_X H3].
      destruct H3 as [sup_Y H3].
      destruct H3.
      destruct H4.
      assert (H6 : sup_X =-= x2) by now apply (supremum_unique X).
      assert (H7 : sup_Y =-= f x2).
      { apply (supremum_unique Y)...
        intros y.
        split...
        intros H7 y' H8.
        apply (leq_trans y' (f x2) y)...
        apply H4...
      }
      apply H4...
    }
    intros O H0.
    split.
    + intros x1 x2 H1 H2.
      inversion H1; subst.
      constructor.
      apply (proj1 H0 (f x1) (f x2))...
    + intros X H1 sup_X H2 H3.
      destruct (H X H1) as [sup_X' H4].
      destruct H4 as [sup_Y H4].
      destruct H4.
      destruct H5.
      assert (sup_X =-= sup_X') by now apply (supremum_unique X).
      assert (H8 : member (f sup_X) O).
      { inversion H3; subst...
      }
      assert (H9 : directed (image f X)).
      { destruct H1.
        split.
        - destruct H1 as [x1].
          exists (f x1)...
        - intros y1 H10 y2 H11.
          inversion H10; subst.
          inversion H11; subst.
          rename x into x1, x0 into x2.
          destruct (H9 x1 H12 x2 H13) as [x3].
          destruct H14.
          destruct H15.
          exists (f x3).
          repeat split...
      }
      assert (H10 : NonEmpty (intersection (image f X) O)).
      { apply (proj2 H0 (image f X) H9 (f sup_X))...
        intros y.
        split.
        - intros.
          apply H5...
          apply (leq_trans sup_Y (f sup_X) y)...
        - intros.
          apply (leq_trans (f sup_X) sup_Y y)...
          apply H5...
      }
      destruct H10 as [y1].
      inversion H10; subst.
      inversion H11; subst.
      exists x...
Qed.

Global Program Instance direct_product_of_two_poset_minor {D : Set} {D' : Set} `{D_is_poset_minor : Poset_minor D} `{D'_is_poset_minor : Poset_minor D'} : Poset_minor (D * D') :=
  { eql := fun d1 : D * D' => fun d2 : D * D' => eql (fst d1) (fst d2) /\ eql (snd d1) (snd d2)
  ; leq := fun d1 : D * D' => fun d2 : D * D' => leq (fst d1) (fst d2) /\ leq (snd d1) (snd d2)
  }
.

Next Obligation with eauto with *.
  repeat split...
  destruct H...
  destruct H...
  destruct H, H0.
  apply (transitivity H H0).
  destruct H, H0.
  apply (transitivity H1 H2).
Qed.

Next Obligation with eauto with *.
  repeat split...
  destruct H, H0...
  destruct H, H0...
Qed.

Next Obligation with eauto with *.
  repeat split...
  destruct H...
  destruct H...
  destruct H...
  destruct H...
  destruct H.
  destruct H0, H...
  destruct H.
  destruct H0, H...
Qed.

Global Program Instance direct_product_of_two_poset {D : Set} {D' : Set} `{D_is_poset : Poset D} `{D'_is_poset : Poset D'} : Poset (D * D') :=
  {}
.

Next Obligation with eauto with *.
  constructor.
  apply (substitutablity x1 x2 H (fun x : X => fst (f x))).
  apply (substitutablity x1 x2 H (fun x : X => snd (f x))).
Qed.

Inductive getFsts {D : Set} {D' : Set} : Ensemble (D * D') -> Ensemble D :=
| In_getFsts {ps : Ensemble (D * D')} :
  forall x : D,
  forall x' : D',
  member (x, x') ps ->
  member x (getFsts ps)
.

#[global] Hint Constructors getFsts : domain_theory_hints.

Inductive getSnds {D : Set} {D' : Set} : Ensemble (D * D') -> Ensemble D' :=
| In_getSnds {ps : Ensemble (D * D')} :
  forall x : D,
  forall x' : D',
  member (x, x') ps ->
  member x' (getSnds ps)
.

#[global] Hint Constructors getSnds : domain_theory_hints.

Program Instance direct_product_of_two_cpos {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} : CompletePartialOrder (D * D') :=
  { bottom := (bottom, bottom)
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Next Obligation with eauto with *.
  assert (H0 : directed (getFsts xs)).
  { destruct H.
    split.
    - destruct H.
      exists (fst x).
      apply (In_getFsts (fst x) (snd x)).
      rewrite <- surjective_pairing...
    - intros x1 H1 x2 H2.
      inversion H1; subst.
      rename x' into y1.
      inversion H2; subst.
      rename x' into y2.
      destruct (H0 (x1, y1) H3 (x2, y2) H4) as [p].
      destruct p as [x3 y3].
      exists x3.
      destruct H5.
      destruct H6.
      repeat split...
      + apply H6.
      + apply H7. 
  }
  assert (H1 : directed (getSnds xs)).
  { destruct H.
    split.
    - destruct H.
      exists (snd x).
      apply (In_getSnds (fst x) (snd x)).
      rewrite <- surjective_pairing...
    - intros y1 H2 y2 H3.
      inversion H2; subst.
      rename x into x1.
      inversion H3; subst.
      rename x into x2.
      destruct (H1 (x1, y1) H4 (x2, y2) H5) as [p].
      destruct p as [x3 y3].
      exists y3.
      destruct H6.
      destruct H7.
      repeat split...
      + apply H7.
      + apply H8. 
  }
  destruct (supremum_exists (getFsts xs) H0) as [sup_fst_xs H2].
  destruct (supremum_exists (getSnds xs) H1) as [sup_snd_xs H3].
  exists (sup_fst_xs, sup_snd_xs).
  intros p.
  destruct p as [x y].
  split.
  - intros H4 p0 H5.
    destruct p0 as [x0 y0].
    split; [apply H2 | apply H3]...
    all: apply H4.
  - intros H4.
    split; [apply H2 | apply H3]...
    + intros x0 H5.
      inversion H5; subst.
      rename x' into y0.
      apply (H4 (x0, y0))...
    + intros y0 H5.
      inversion H5; subst.
      apply (H4 (x0, y0))...
Defined.

Lemma cartesian_supremum  {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall X : Ensemble (D * D'),
  directed X ->
  exists sup_X : D * D', is_supremum sup_X X /\ is_supremum (fst sup_X) (getFsts X) /\ is_supremum (snd sup_X) (getSnds X).
Proof with eauto with *.
  intros xs H.
  assert (H0 : directed (getFsts xs)).
  { destruct H.
    split.
    - destruct H.
      exists (fst x).
      apply (In_getFsts (fst x) (snd x)).
      rewrite <- surjective_pairing...
    - intros x1 H1 x2 H2.
      inversion H1; subst.
      rename x' into y1.
      inversion H2; subst.
      rename x' into y2.
      destruct (H0 (x1, y1) H3 (x2, y2) H4) as [p].
      destruct p as [x3 y3].
      exists x3.
      destruct H5.
      destruct H6.
      repeat split...
      + apply H6.
      + apply H7. 
  }
  assert (H1 : directed (getSnds xs)).
  { destruct H.
    split.
    - destruct H.
      exists (snd x).
      apply (In_getSnds (fst x) (snd x)).
      rewrite <- surjective_pairing...
    - intros y1 H2 y2 H3.
      inversion H2; subst.
      rename x into x1.
      inversion H3; subst.
      rename x into x2.
      destruct (H1 (x1, y1) H4 (x2, y2) H5) as [p].
      destruct p as [x3 y3].
      exists y3.
      destruct H6.
      destruct H7.
      repeat split...
      + apply H7.
      + apply H8. 
  }
  destruct (supremum_exists (getFsts xs) H0) as [sup_fst_xs H2].
  destruct (supremum_exists (getSnds xs) H1) as [sup_snd_xs H3].
  exists (sup_fst_xs, sup_snd_xs).
  simpl.
  split...
  intros p.
  destruct p as [x y].
  split.
  - intros H4 p0 H5.
    destruct p0 as [x0 y0].
    split; [apply H2 | apply H3]...
    all: apply H4.
  - intros H4.
    split; [apply H2 | apply H3]...
    + intros x0 H5.
      inversion H5; subst.
      rename x' into y0.
      apply (H4 (x0, y0))...
    + intros y0 H5.
      inversion H5; subst.
      apply (H4 (x0, y0))...
Qed.

Local Notation "D1 ~> D2" := ({f : D1 -> D2 | is_continuous_map f}) (at level 15, right associativity) : type_scope.

Lemma continuous_maps_are_continuous {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall f : D ~> D',
  is_continuous_map (proj1_sig f).
Proof.
  apply proj2_sig.
Qed.

#[global] Hint Resolve continuous_maps_are_continuous : domain_theory_hints.

Global Program Instance ContinuousMaps_is_Poset_minor {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} : Poset_minor (D ~> D') :=
  { eql := fun f1 : D ~> D' => fun f2 : D ~> D' => forall x : D, eql (proj1_sig f1 x) (proj1_sig f2 x)
  ; leq := fun f1 : D ~> D' => fun f2 : D ~> D' => forall x : D, leq (proj1_sig f1 x) (proj1_sig f2 x)
  }
.

Next Obligation with eauto with *.
  repeat split...
  intros f1 f2 f3 H1 H2 x.
  apply (transitivity (H1 x) (H2 x)).
Qed.

Next Obligation with eauto with *.
  repeat split...
Qed.

Next Obligation with eauto with *.
  intros f1 f2.
  repeat split...
  intros x.
  apply leq_refl2...
  intros H.
  destruct H...
Qed.

Global Program Instance ContinuousMaps_is_Poset {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} : Poset (D ~> D') :=
  {}
.

Next Obligation with eauto with *.
  apply (substitutablity x1 x2 H (fun x' : X => proj1_sig (f x') x)).
Qed.

Lemma sup_of_maps_on_cpos_is_well_defined {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall fs : Ensemble (D ~> D'),
  directed fs ->
  forall x : D,
  directed (image (fun f : D ~> D' => proj1_sig f x) fs).
Proof with eauto with *.
  intros fs H x.
  destruct H.
  split.
  - destruct H as [f0].
    exists (proj1_sig f0 x).
    apply (In_image f0)...
  - intros y1 H1 y2 H2.
    inversion H1; subst.
    inversion H2; subst.
    rename x0 into f1, x1 into f2.
    destruct (H0 f1 H3 f2 H4) as [f3].
    destruct H5 as [H5 [H6 H7]].
    exists (proj1_sig f3 x).
    repeat split...
    apply (In_image f3)...
Qed.

Lemma sup_of_continuous_maps_on_cpos_exists_if_their_set_is_directed {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall fs : Ensemble (D ~> D'),
  forall directed_fs : directed fs,
  let f : D -> D' := fun x : D => proj1_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_maps_on_cpos_is_well_defined fs directed_fs x)) in
  is_continuous_map f.
Proof with eauto with *.
  intros fs H f.
  apply the_main_reason_for_introducing_the_Scott_topology.
  intros X H0 Y.
  destruct (supremum_exists X H0) as [sup_X H1].
  exists sup_X, (f sup_X).
  enough (is_supremum (f sup_X) Y)...
  assert ( claim1 :
    forall f_i : D ~> D',
    member f_i fs ->
    is_supremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
  ).
  { intros f_i H2.
    assert (H3 : is_continuous_map (proj1_sig f_i)) by now apply (proj2_sig f_i).
    assert (H4 : characterization_of_continuous_map_on_cpos (proj1_sig f_i)) by now apply the_main_reason_for_introducing_the_Scott_topology.
    destruct (H4 X H0) as [sup_X' [sup_Y' [H5 [H6 H7]]]].
    assert (H8 : sup_X' =-= sup_X) by now apply (supremum_unique X).
    apply (supremum_unique (image (fun x : D => proj1_sig f_i x) X) sup_Y' (proj1_sig f_i sup_X))...
    symmetry.
    transitivity (proj1_sig f_i sup_X')...
  }
  assert (claim2 : is_supremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs)) by apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs) (sup_of_maps_on_cpos_is_well_defined fs H sup_X))).
  set (sup_f_i_X_i := fun y : D' => exists f_i : D ~> D', member f_i fs /\ is_supremum y (image (fun x : D => proj1_sig f_i x) X)).
  set (sup_x_X_f_i := fun y : D' => exists x : D, member x X /\ is_supremum y (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)).
  set (f_i_x := fun y : D' => exists f_i : D ~> D', exists x : D, member f_i fs /\ member x X /\ y =-= proj1_sig f_i x).
  assert (claim3 : is_supremum (f sup_X) sup_f_i_X_i).
  { intros y.
    split.
    - intros H2 y1 H3.
      destruct H3 as [f1 [H3 H4]].
      assert (H5 : is_supremum (proj1_sig f1 sup_X) (image (fun x : D => proj1_sig f1 x) X)) by now apply claim1.
      assert (H6 : y1 =-= proj1_sig f1 sup_X) by now apply (supremum_unique (image (fun x : D => proj1_sig f1 x) X)).
      apply (leq_trans y1 (proj1_sig f1 sup_X) y)...
      apply (leq_trans (proj1_sig f1 sup_X) (f sup_X) y)...
      apply claim2...
      apply (In_image f1)...
    - intros H2.
      apply claim2...
      intros y1 H3.
      apply H2.
      inversion H3; subst...
      rename x into f1.
      exists f1...
  }
  assert ( lemma1 :
    forall sup : D',
    is_supremum sup sup_f_i_X_i ->
    is_supremum sup f_i_x
  ).
  { intros sup H2 y.
    split.
    - intros H3 y1 H4.
      destruct H4 as [f1 [x1 [H4 [H5 H6]]]].
      enough (H7 : forall x : D, forall x' : D, leq x x' -> leq (proj1_sig f1 x) (proj1_sig f1 x')).
      { assert (H8 : leq (proj1_sig f1 x1) (proj1_sig f1 sup_X)) by now apply H7, H1.
        apply (leq_trans y1 sup y)...
        apply (leq_trans y1 (proj1_sig f1 x1) sup)...
        apply (leq_trans (proj1_sig f1 x1) (proj1_sig f1 sup_X) sup)...
        apply H2...
        exists f1...
      }
      apply continuous_maps_on_cpos_are_always_monotonic...
    - intros H3.
      apply H2.
      intros y1 [f1 [H4 H5]].
      apply H5.
      intros y' H6.
      inversion H6; subst.
      rename x into x1.
      apply H3.
      exists f1, x1...
  }
  assert ( lemma2 :
    forall sup : D',
    is_supremum sup f_i_x ->
    is_supremum sup sup_x_X_f_i
  ).
  { intros sup H2 y.
    split.
    - intros H3 y1 [x1 [H4 H5]].
      apply H5.
      intros x' H6.
      inversion H6; subst.
      rename x into f1.
      apply H2...
      exists f1, x1...
    - intros H3.
      apply H2.
      intros y1 [f1 [x1 [H4 [H5 H6]]]].
      apply (leq_trans y1 (proj1_sig f1 x1) y)...
      assert (H7 : is_supremum (f x1) (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs)) by apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs) (sup_of_maps_on_cpos_is_well_defined fs H x1))).
      assert (H8 : leq (proj1_sig f1 x1) (f x1)).
      { apply H7...
        apply (In_image f1)...
      }
      apply (leq_trans (proj1_sig f1 x1) (f x1) y)...
      apply H3...
      assert (H9 : is_supremum (f x1) (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs)) by apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs) (sup_of_maps_on_cpos_is_well_defined fs H x1))).
      exists x1...
  }
  enough (claim4 : is_supremum (f sup_X) sup_x_X_f_i).
  { intros y.
    split.  
    - intros H2 y1 H3.
      inversion H3; subst.
      rename x into x1.
      assert (H5 : is_supremum (f x1) (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs)) by apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs) (sup_of_maps_on_cpos_is_well_defined fs H x1))).
      apply claim4...
      exists x1...
    - intros H2.
      apply claim4...
      intros y1 [x1 [H3 H4]].
      assert (H5 : is_supremum (f x1) (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs)) by apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs) (sup_of_maps_on_cpos_is_well_defined fs H x1))).
      assert (H6 : y1 =-= f x1) by now apply (supremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x1) fs) y1 (f x1)).
      apply (leq_trans y1 (f x1) y)...
  }
  apply lemma2, lemma1...
Qed.

Definition supremum_of_continuous_maps {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  forall fs : Ensemble (D ~> D'),
  directed fs ->
  D ~> D'.
Proof with eauto with *.
  intros fs directed_fs.
  exists (fun x : D => proj1_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_maps_on_cpos_is_well_defined fs directed_fs x))).
  apply sup_of_continuous_maps_on_cpos_exists_if_their_set_is_directed...
Defined.

Definition bottom_of_continuous_maps {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} :
  D ~> D'.
Proof with eauto with *.
  exists (fun _ : D => bottom).
  intros Y [H H0].
  split.
  - intros x1 x2 H1 H2.
    inversion H1; subst...
  - intros X [[x0 H1] H2] sup_X H3 H4.
    exists x0.
    constructor...
    inversion H4; subst...
Defined.

Global Program Instance set_continuous_maps_on_cpos_is_cpo {D : Set} {D' : Set} `{D_is_cpo : CompletePartialOrder D} `{D'_is_cpo : CompletePartialOrder D'} : CompletePartialOrder (D ~> D') :=
  { bottom := bottom_of_continuous_maps
  }
.

Next Obligation with eauto with *.
  apply bottom_least...
Qed.

Next Obligation with eauto with *.
  rename xs into fs.
  exists (supremum_of_continuous_maps fs H).
  intros f.
  split.
  - intros H0 f0 H1 x.
    apply (leq_trans (proj1_sig f0 x) (proj1_sig (supremum_of_continuous_maps fs H) x) (proj1_sig f x))...
    assert (H2 : is_supremum (proj1_sig (supremum_of_continuous_maps fs H) x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by now apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_maps_on_cpos_is_well_defined fs H x))).
    apply H2...
    apply (In_image f0)...
  - intros H0 x.
    assert (H1 : is_supremum (proj1_sig (supremum_of_continuous_maps fs H) x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by now apply (proj2_sig (supremum_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_maps_on_cpos_is_well_defined fs H x))).
    apply H1...
    intros y H2.
    inversion H2; subst.
    rename x0 into f0.
    apply (H0 f0 H3 x).
Defined.

Lemma separately_continuous_iff {D1 : Set} {D2 : Set} {D3 : Set} `{D1_is_cpo : CompletePartialOrder D1} `{D2_is_cpo : CompletePartialOrder D2} `{D3_is_cpo : CompletePartialOrder D3} :
  forall f : D1 * D2 -> D3,
  is_continuous_map f <-> ((forall x1 : D1, is_continuous_map (fun x2 : D2 => f (x1, x2))) /\ (forall x2 : D2, is_continuous_map (fun x1 : D1 => f (x1, x2)))).
Proof with eauto with *.
  intros f.
  split.
  - intros H.
    split.
    + intros x1_0.
      apply the_main_reason_for_introducing_the_Scott_topology.
      intros X H0 Y.
      destruct (supremum_exists X H0) as [sup_X H1].
      set (sup_Y := f (x1_0, sup_X)).
      exists sup_X, sup_Y.
      enough (is_supremum (f (x1_0, sup_X)) Y)...
      set (x1_x2 := fun p : D1 * D2 => x1_0 = fst p /\ member (snd p) X).
      assert (H2 : is_supremum (x1_0, sup_X) x1_x2).
      { intros [x1 x2].
        split.
        - intros [H2 H3] [x1' x2'] [H4 H5].
          simpl in *.
          subst x1'.
          split...
          apply H1...
        - intros H3.
          simpl.
          split...
          + destruct H0 as [[x2_0 H4] H5].
            apply (H3 (x1_0, x2_0)).
            split...
          + apply H1...
            intros x2' H4.
            apply (H3 (x1_0, x2'))...
            split...
      }
      assert (H3 : characterization_of_continuous_map_on_cpos f) by now apply the_main_reason_for_introducing_the_Scott_topology.
      assert (H4 : directed x1_x2).
      { destruct H0 as [[x2_0 H0] H4].
        split.
        - exists (x1_0, x2_0).
          split...
        - intros [x1_1 x2_1] [H7 H5] [x1_2 x2_2] [H8 H6]...
          simpl in *.
          subst x1_1 x1_2.
          destruct (H4 x2_1 H5 x2_2 H6) as [x3_2 [H7 [H8 H9]]].
          exists (x1_0, x3_2).
          simpl.
          repeat split...
      }
      assert (H5 : is_supremum (f (x1_0, sup_X)) (image f x1_x2)).
      { destruct (H3 x1_x2 H4) as [[x1_0' sup_X'] [sup_Y' [H5 [H6 H7]]]].
        assert (H8 : (x1_0, sup_X) =-= (x1_0', sup_X')) by now apply (supremum_unique x1_x2).
        assert (H9 : sup_Y =-= sup_Y').
        { transitivity (f (x1_0', sup_X'))...
        }
        apply (supremum_unique (image f x1_x2) _ _ H6)...
      }
      assert (H6 : isSubsetOf (image f x1_x2) Y).
      { intros y H6.
        inversion H6; subst.
        destruct H7 as [H7 H8].
        destruct x as [x1 x2].
        simpl in *.
        subst x1.
        apply (In_image x2)...
      }
      assert (H7 : isSubsetOf Y (image f x1_x2)).
      { intros y H7.
        inversion H7; subst.
        rename x into x2.
        apply (In_image (x1_0, x2))...
        split...
      }
      apply (supremum_ext (image f x1_x2) Y H6 H7 _ _ H5)...
    + intros x2_0.
      apply the_main_reason_for_introducing_the_Scott_topology.
      intros X H0 Y.
      destruct (supremum_exists X H0) as [sup_X H1].
      set (sup_Y := f (sup_X, x2_0)).
      exists sup_X, sup_Y.
      enough (is_supremum (f (sup_X, x2_0)) Y)...
      set (x1_x2 := fun p : D1 * D2 => x2_0 = snd p /\ member (fst p) X).
      assert (H2 : is_supremum (sup_X, x2_0) x1_x2).
      { intros [x1 x2].
        split.
        - intros [H2 H3] [x1' x2'] [H4 H5].
          simpl in *.
          subst x2'.
          split...
          apply H1...
        - intros H3.
          simpl.
          split...
          + apply H1...
            intros x1' H4.
            apply (H3 (x1', x2_0))...
            split...
          + destruct H0 as [[x1_0 H4] H5].
            apply (H3 (x1_0, x2_0)).
            split...
      }
      assert (H3 : characterization_of_continuous_map_on_cpos f) by now apply the_main_reason_for_introducing_the_Scott_topology.
      assert (H4 : directed x1_x2).
      { destruct H0 as [[x1_0 H0] H4].
        split.
        - exists (x1_0, x2_0).
          split...
        - intros [x1_1 x2_1] [H7 H5] [x1_2 x2_2] [H8 H6]...
          simpl in *.
          subst x2_1 x2_2.
          destruct (H4 x1_1 H5 x1_2 H6) as [x1_3 [H7 [H8 H9]]].
          exists (x1_3, x2_0).
          simpl.
          repeat split...
      }
      assert (H5 : is_supremum (f (sup_X, x2_0)) (image f x1_x2)).
      { destruct (H3 x1_x2 H4) as [[sup_X' x2_0'] [sup_Y' [H5 [H6 H7]]]].
        assert (H8 : (sup_X, x2_0) =-= (sup_X', x2_0')) by now apply (supremum_unique x1_x2).
        assert (H9 : sup_Y =-= sup_Y').
        { transitivity (f (sup_X', x2_0'))...
        }
        apply (supremum_unique (image f x1_x2) _ _ H6)...
      }
      assert (H6 : isSubsetOf (image f x1_x2) Y).
      { intros y H6.
        inversion H6; subst.
        destruct H7 as [H7 H8].
        destruct x as [x1 x2].
        simpl in *.
        subst x2.
        apply (In_image x1)...
      }
      assert (H7 : isSubsetOf Y (image f x1_x2)).
      { intros y H7.
        inversion H7; subst.
        rename x into x1.
        apply (In_image (x1, x2_0))...
        split...
      }
      apply (supremum_ext (image f x1_x2) Y H6 H7 _ _ H5)...
  - intros [H H0].
    apply the_main_reason_for_introducing_the_Scott_topology.
    intros X H1 Y.
    destruct (cartesian_supremum X H1) as [[sup_X1 sup_X2] [H2 [H3 H4]]].
    set (X1 := getFsts X).
    set (X2 := getSnds X).
    set (sup_Y := f (sup_X1, sup_X2)).
    exists (sup_X1, sup_X2), sup_Y.
    simpl in *.
    enough (is_supremum sup_Y Y)...
    assert (H5 : forall x1 : D1, characterization_of_continuous_map_on_cpos (fun x2 : D2 => f (x1, x2))).
    { intros x1.
      apply the_main_reason_for_introducing_the_Scott_topology...
    }
    assert (H6 : forall x2 : D2, characterization_of_continuous_map_on_cpos (fun x1 : D1 => f (x1, x2))).
    { intros x2.
      apply the_main_reason_for_introducing_the_Scott_topology...
    }
    assert (H7 : directed X2).
    { destruct H1 as [[[x1_0 x2_0] H1] H7].
      split.
      - exists x2_0...
      - intros x2_1 H8 x2_2 H9.
        inversion H8; subst.
        rename x into x1_1.
        inversion H9; subst.
        rename x into x1_2.
        destruct (H7 (x1_1, x2_1) H10 (x1_2, x2_2) H11) as [[x3_1 x3_2] [H12 [[H13 H14] [H15 H16]]]].
        exists x3_2.
        simpl in *...
    }
    set (sup_X1_x2 := fun p : D1 * D2 => member (snd p) X2 /\ fst p = sup_X1).
    assert (H8 : is_supremum (f (sup_X1, sup_X2)) (image f sup_X1_x2)).
    { destruct (H5 sup_X1 X2 H7) as [sup_X2' [sup_Y' [H8 [H9 H10]]]].
      assert (H11 : sup_X2 =-= sup_X2') by now apply (supremum_unique X2).
      assert (H12 : sup_Y =-= sup_Y').
      { transitivity (f (sup_X1, sup_X2'))...
      }
      assert (H13 : isSubsetOf (image (fun x2 : D2 => f (sup_X1, x2)) X2) (image f sup_X1_x2)).
      { intros y H13.
        inversion H13; subst.
        rename x into x2.
        apply (In_image (sup_X1, x2)).
        split...
      }
      assert (H14 : isSubsetOf (image f sup_X1_x2) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
      { intros y H14.
        inversion H14; subst.
        destruct H15 as [H15 H16].
        destruct x as [x1 x2].
        simpl in *.
        subst x1.
        apply (In_image x2)...
      }
      apply (supremum_ext _ _ H13 H14 sup_Y' (f (sup_X1, sup_X2)))...
    }
    set (sup_X1_f_x1_x2 := fun y : D3 => exists x2 : D2, member x2 X2 /\ is_supremum y (image (fun x1 : D1 => f (x1, x2)) X1)).
    assert (H9 : directed X1).
    { destruct H1 as [[[x1_0 x2_0] H1] H9].
      split.
      - exists x1_0...
      - intros x1_1 H10 x1_2 H11.
        inversion H10; subst.
        rename x' into x2_1.
        inversion H11; subst.
        rename x' into x2_2.
        destruct (H9 (x1_1, x2_1) H12 (x1_2, x2_2) H13) as [[x3_1 x3_2] [H14 [[H15 H16] [H17 H18]]]].
        exists x3_1.
        simpl in *...
    }
    assert ( claim1 :
      forall x2 : D2,
      member x2 X2 ->
      is_supremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)
    ).
    { intros x2 H10.
      destruct (H6 x2 X1 H9) as [sup_X_ [sup_Y_ [H11 [H12 H13]]]].
      assert (H14 : sup_X_ =-= sup_X1) by now apply (supremum_unique X1).
      assert (H15 : sup_Y_ =-= f (sup_X1, x2)).
      { transitivity (f (sup_X_, x2))...
        apply (substitutablity _ _ H14 (fun x' : D1 => f (x', x2)))...
      }
      apply (supremum_unique (image (fun x1 : D1 => f (x1, x2)) X1) sup_Y_ (f (sup_X1, x2)) H12)...
    }
    assert (H10 : is_supremum (f (sup_X1, sup_X2)) sup_X1_f_x1_x2).
    { intros y.
      split.
      - intros H10 y' [x2 [H11 H12]].
        assert (H13 := claim1 x2 H11).
        assert (y' =-= f (sup_X1, x2)) by now apply (supremum_unique (image (fun x1 : D1 => f (x1, x2)) X1)).
        transitivity (f (sup_X1, x2))...
        transitivity (f (sup_X1, sup_X2))...
        apply (continuous_maps_on_cpos_are_always_monotonic (fun x2 : D2 => f (sup_X1, x2)))...
        apply H4...
      - intros H10.
        apply H8...
        intros y' H11.
        inversion H11; subst.
        destruct x as [x1 x2].
        destruct H12 as [H12 H13].
        simpl in *.
        subst x1.
        apply H10...
        exists x2...
    }
    set (x1_x2 := fun p : D1 * D2 => member (fst p) X1 /\ member (snd p) X2).
    assert (H11 : is_supremum (f (sup_X1, sup_X2)) (image f x1_x2)).
    { intros y.
      split.
      - intros H11 y' H12.
        inversion H12; subst.
        destruct x as [x1 x2].
        destruct H13 as [H13 H14].
        simpl in *.
        transitivity (f (sup_X1, x2))...
        + apply (continuous_maps_on_cpos_are_always_monotonic (fun x1' : D1 => f (x1', x2)))...
          apply H3...
        + apply H10...
          exists x2...
      - intros H11.
        apply NNPP.
        intros H12.
        assert (H13 : member (f (sup_X1, sup_X2)) (U_x y)) by now (unfold U_x).
        assert (H14 : is_open_set (U_x y)) by now apply U_x_is_open.
        destruct (H sup_X1 (U_x y) H14) as [H15 H16].
        assert (H17 : member sup_X2 (inverse_image (fun x2 : D2 => f (sup_X1, x2)) (U_x y))) by now constructor.
        destruct (H16 X2 H7 sup_X2 H4 H17) as [x2 H18].
        inversion H18; subst.
        inversion H20; subst.
        contradiction H21.
        assert (H22 := claim1 x2 H19).
        apply H22.
        intros y' H23.
        apply H11.
        inversion H23; subst.
        constructor.
        split...
    }
    intros y.
    split.
    + intros H12 y' H13.
      apply H11...
      inversion H13; subst.
      destruct x as [x1 x2].
      repeat econstructor...
    + intros H12.
      apply H11.
      intros y' H13.
      inversion H13; subst.
      destruct x as [x1_1 x2_2].
      destruct H14 as [H14 H15].
      simpl in *.
      inversion H14; subst.
      inversion H15; subst.
      rename x' into x2_1, x into x1_2.
      inversion H1.
      destruct (H19 (x1_1, x2_1) H16 (x1_2, x2_2) H17) as [[x3_1 x3_2] [H20 [[H21 H22] [H23 H24]]]].
      transitivity (f (x3_1, x3_2))...
      simpl in H21, H22, H23, H24.
      transitivity (f (x1_1, x3_2)).
      * apply (continuous_maps_on_cpos_are_always_monotonic (fun x2' : D2 => f (x1_1, x2')))...
      * apply (continuous_maps_on_cpos_are_always_monotonic (fun x1' : D1 => f (x1', x3_2)))...
Qed.

End DomainTheory.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.

Global Create HintDb my_hints.

Module MyUtilities.

  Definition case_eq {A : Type} : forall x : A, forall y : A, forall phi : forall x0 : A, x0 = y -> Type, phi y eq_refl -> forall H : x = y, phi x H :=
    fun x : A =>
    fun y : A =>
    fun phi : forall x0 : A, x0 = y -> Type =>
    fun phi_y : phi y eq_refl =>
    fun H : eq x y =>
    match H as H0 in eq _ y0 return forall phi0 : forall x0 : A, x0 = y0 -> Type, phi0 y0 eq_refl -> phi0 x H0 with
    | eq_refl =>
      fun phi0 : forall x0 : A, x0 = x -> Type =>
      fun phi_y0 : phi0 x eq_refl =>
      phi_y0
    end phi phi_y
  .

  Lemma div_mod_uniqueness :
    forall a : nat,
    forall b : nat,
    forall q : nat,
    forall r : nat,
    a = b * q + r ->
    r < b ->
    a / b = q /\ a mod b = r.
  Proof with try (lia || now (firstorder; eauto)).
    assert (H : forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
    { intros x y; constructor.
      - intros H.
        induction H...
        destruct IHle as [z H0].
        exists (S z)...
      - intros H.
        destruct H as [z H]...
    }
    intros a b q r H1 H2.
    assert (H0 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (H3 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
    assert (H4 : ~ q > a / b).
    { intros H4.
      enough (H5 : exists z : nat, q = S (a / b + z))...
      destruct H5 as [z H5].
      enough (b * q + r >= b * S (a / b) + r)...
    }
    assert (H5 : ~ q < a / b).
    { intros H5.
      enough (H6 : exists z : nat, a / b = S (q + z))...
      destruct H6 as [z H6].
      enough (b * q + a mod b >= b * S (a / b) + a mod b)...
    }
    enough (q = a / b)...
  Qed.

  Definition first_nat : (nat -> bool) -> nat -> nat :=
    fun p : nat -> bool =>
    fix first_nat_fix (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
    | S n' => if p (first_nat_fix n') then first_nat_fix n' else n
    end
  .

  Theorem well_ordering_principle : 
    forall p : nat -> bool,
    forall n : nat,
    p n = true ->
    let m : nat := first_nat p n in
    p m = true /\ (forall i : nat, p i = true -> i >= m).
  Proof with eauto. (* This proof has been improved by JunYoung Clare Jang. *)
    intros p n H3 m.
    assert (forall x : nat, p x = true -> p (first_nat p x) = true).
    { induction x...
      simpl.
      destruct (p (first_nat p x)) eqn:H0...
    }
    split...
    intros i H4.
    enough (forall x : nat, first_nat p x <= x).
    enough (forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
    enough (forall x : nat, forall y : nat, p y = true -> first_nat p x <= y)...
    - intros x y H2.
      destruct (Compare_dec.le_lt_dec x y).
      + eapply Nat.le_trans...
      + replace (first_nat p x) with (first_nat p y)...
    - intros x H1 y H2.
      induction H2; simpl.
      + rewrite H1...
      + rewrite <- IHle, H1...
    - induction x...
      simpl.
      destruct (p (first_nat p x)) eqn: H0...
  Qed.

  Fixpoint sum_from_0_to (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
    | S n' => n + sum_from_0_to n'
    end
  .

  Proposition sum_from_0_to_is :
    forall n : nat,
    2 * sum_from_0_to n = n * (S n).
  Proof with lia.
    induction n; simpl in *...
  Qed.

  Fixpoint cantor_pairing (n : nat) {struct n} : nat * nat :=
    match n with
    | 0 => (0, 0)
    | S n' =>
      match cantor_pairing n' with
      | (0, y) => (S y, 0)
      | (S x, y) => (x, S y)
      end
    end
  .

  Lemma cantor_pairing_is_surjective :
    forall x : nat,
    forall y : nat,
    (x, y) = cantor_pairing (sum_from_0_to (x + y) + y).
  Proof with (lia || eauto).
    enough (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y))...
    induction z.
    - intros y x H.
      assert (H0 : x = 0)...
      assert (H1 : y = 0)...
      subst...
    - induction y.
      + intros x H.
        assert (H0 : x = S z)...
        subst.
        simpl.
        destruct (cantor_pairing (z + sum_from_0_to z + 0)) eqn: H0.
        assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
        rewrite Nat.add_0_r, Nat.add_comm in H0.
        rewrite H0 in H1.
        inversion H1; subst...
      + intros x H.
        enough (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)).
        { assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by now simpl...
          simpl.
          rewrite H1, <- H0...
        }
        apply (IHy (S x))...
  Qed.

  Lemma cantor_pairing_is_injective :
    forall n : nat,
    forall x : nat,
    forall y : nat,
    cantor_pairing n = (x, y) ->
    n = sum_from_0_to (x + y) + y.
  Proof with (lia || eauto).
    induction n; simpl.
    - intros x y H.
      inversion H; subst...
    - intros x y H.
      destruct (cantor_pairing n) as [x' y'] eqn: H0.
      destruct x'; (inversion H; subst).
      + repeat (rewrite Nat.add_0_r).
        simpl.
        rewrite (IHn 0 y' eq_refl), Nat.add_0_l...
      + rewrite (IHn (S x) y' eq_refl).
        assert (H1 : forall x' : nat, S x' + y' = x' + S y')...
        repeat (rewrite H1)...
  Qed.

  Corollary cantor_pairing_is :
    forall n : nat,
    forall x : nat,
    forall y : nat,
    cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
  Proof with eauto using cantor_pairing_is_injective, cantor_pairing_is_surjective.
    split...
    intros H.
    subst...
  Qed.

  Definition S_0 {A : Type} : forall n : nat, S n = 0 -> A :=
    fun n : nat =>
    fun H0 : S n = 0 =>
    let H1 : 0 = S n := @eq_ind nat (S n) (fun x : nat => x = S n) eq_refl 0 H0 in
    let H2 : False := @eq_ind nat 0 (fun x : nat => if Nat.eqb x 0 then True else False) I (S n) H1 in
    False_rect A H2
  .

  Definition S_S : forall n1 : nat, forall n2 : nat, S n1 = S n2 -> n1 = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun H0 : S n1 = S n2 =>
    @eq_ind nat (S n1) (fun x : nat => n1 = pred x) eq_refl (S n2) H0
  .

  Inductive FinSet : nat -> Set :=
  | FZ : forall n : nat, FinSet (S n) 
  | FS : forall n : nat, FinSet n -> FinSet (S n)
  .

  Definition FinSet_case0 {P : FinSet 0 -> Type} : forall i : FinSet 0, P i :=
    fun i : FinSet 0 =>
    match i as i0 in FinSet Sn return Sn = 0 -> P i with
    | FZ n => S_0 n
    | FS n i' => S_0 n
    end eq_refl
  .

  Definition FinSet_caseS {n : nat} {P : FinSet (S n) -> Type} : P (FZ n) -> (forall i' : FinSet n, P (FS n i')) -> (forall i : FinSet (S n), P i) :=
    fun PZ : P (FZ n) =>
    fun PS : forall i' : FinSet n, P (FS n i') =>
    fun i : FinSet (S n) =>
    match i as i0 in FinSet Sn0 return (match Sn0 as Sn1 return FinSet Sn1 -> Type with 0 => FinSet_case0 | S n0 => fun i1 : FinSet (S n0) => forall P0 : FinSet (S n0) -> Type, P0 (FZ n0) -> (forall i' : FinSet n0, P0 (FS n0 i')) -> P0 i1 end) i0 with
    | FZ n0 => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PZ0
    | FS n0 i' => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PS0 i'
    end P PZ PS
  .

  Definition FinSet_rectS {P : forall n : nat, FinSet n -> Type} : (forall n : nat, P (S n) (FZ n)) -> (forall n : nat, forall i' : FinSet n, P n i' -> P (S n) (FS n i')) -> (forall n : nat, forall i : FinSet (S n), P (S n) i) :=
    fun PZ : forall n : nat, P (S n) (FZ n) =>
    fun PS : forall n : nat, forall i' : FinSet n, P n i' -> P (S n) (FS n i') =>
    fix FinSet_rectS_fix (n : nat) (i : FinSet (S n)) {struct i} : P (S n) i :=
    match i as i0 in FinSet Sn0 return P Sn0 i0 with
    | FZ n0 => PZ n0
    | FS n0 i' =>
      match n0 as n1 return forall i0' : FinSet n1, P (S n1) (FS n1 i0') with
      | 0 => fun i0' : FinSet 0 => @FinSet_case0 (fun i1 : FinSet 0 => P 1 (FS 0 i1)) i0'
      | S n0' => fun i0' : FinSet (S n0') => PS (S n0') i0' (FinSet_rectS_fix n0' i0')
      end i'
    end
  .


  Lemma forallb_true_iff {A : Type} {p : A -> bool} (xs : list A) :
    forallb p xs = true <-> forall x : A, In x xs -> p x = true.
  Proof with try now firstorder.
    induction xs; simpl...
    rewrite andb_true_iff.
    split...
    intros H0 x H1.
    destruct H0; destruct H1...
    rewrite H1 in H...
  Qed.

  Definition fold_right_max_0 : list nat -> nat :=
    fold_right max 0
  .

  Lemma fold_right_max_0_in :
    forall ns : list nat,
    forall n : nat,
    In n ns ->
    fold_right_max_0 ns >= n.
  Proof with (lia || eauto).
    unfold fold_right_max_0.
    induction ns as [| n' ns]; simpl...
    intros n H.
    destruct H...
    enough (fold_right max 0 ns >= n)...
  Qed.

  Lemma fold_right_max_0_app :
    forall ns1 : list nat,
    forall ns2 : list nat,
    fold_right_max_0 (ns1 ++ ns2) = max (fold_right_max_0 ns1) (fold_right_max_0 ns2).
  Proof with (lia || eauto).
    unfold fold_right_max_0.
    induction ns1 as [| n1 ns1]; simpl... 
    intros n.
    rewrite IHns1...
  Qed.

  Lemma property1_of_fold_right_max_0 (Phi : nat -> Prop) (Phi_dec : forall i : nat, {Phi i} + {~ Phi i}) :
    forall ns : list nat,
    (forall i : nat, Phi i -> In i ns) ->
    forall n : nat,
    Phi n ->
    fold_right max 0 ns >= n.
  Proof with (lia || eauto).
    induction ns; simpl.
    - intros H n H0.
      contradiction (H n).
    - intros H n H0.
      destruct (Compare_dec.le_lt_dec n a)...
      enough (fold_right max 0 ns >= n)...
      destruct (Phi_dec n).
      + destruct (H n p)...
        enough (forall ks : list nat, forall k : nat, In k ks -> fold_right max 0 ks >= k) by firstorder.
        induction ks; simpl...
        intros k H2.
        destruct H2...
        enough (fold_right Init.Nat.max 0 ks >= k)...
      + apply IHns...
        intros.
        destruct (H i H1)...
        subst.
        contradiction.
  Qed.

  Lemma property2_of_fold_right_max_0 :
    forall ns : list nat,
    forall n : nat,
    fold_right max 0 ns > n <-> (exists i : nat, In i ns /\ i > n).
  Proof with (lia || eauto).
    induction ns; simpl.
    - split...
      now firstorder.
    - intros n.
      destruct (Compare_dec.le_lt_dec a (fold_right Init.Nat.max 0 ns)); split...
      + intros H.
        assert (H0 : fold_right Init.Nat.max 0 ns > n)...
        destruct (proj1 (IHns n) H0) as [i].
        now firstorder.
      + intros H.
        destruct H as [i].
        destruct H.
        destruct H.
        * subst...
        * enough (fold_right max 0 ns > n)...
          apply IHns...
      + intros H.
        exists a...
      + intros H.
        destruct H as [i].
        destruct H.
        destruct H.
        * subst...
        * enough (fold_right Init.Nat.max 0 ns > n)...
          apply IHns...
  Qed.

  Lemma property3_of_fold_right_max_0 :
    forall ns1 : list nat,
    forall ns2 : list nat,
    fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
  Proof.
    apply fold_right_max_0_app.
  Qed.

  Lemma property4_of_fold_right_max_0 :
    forall ns : list nat,
    forall n : nat,
    In n ns ->
    fold_right max 0 ns >= n.
  Proof with (lia || eauto).
    induction ns; simpl...
    intros n H.
    destruct H...
    enough (fold_right max 0 ns >= n)...
  Qed.

  Lemma property5_of_fold_right_max_0 :
    forall ns1 : list nat,
    forall ns2 : list nat,
    (forall n : nat, In n ns1 -> In n ns2) ->
    fold_right max 0 ns1 <= fold_right max 0 ns2.
  Proof with (lia || eauto).
    induction ns1; simpl...
    intros ns2 H.
    destruct (Compare_dec.le_lt_dec a (fold_right max 0 ns1)).
    - enough (fold_right max 0 ns1 <= fold_right max 0 ns2)...
    - enough (a <= fold_right max 0 ns2)...
      apply property4_of_fold_right_max_0...
  Qed.

  Lemma fold_right_max_0_ext :
    forall ns1 : list nat,
    forall ns2 : list nat,
    (forall n : nat, In n ns1 <-> In n ns2) ->
    fold_right max 0 ns1 = fold_right max 0 ns2.
  Proof with try now firstorder.
    intros.
    enough (fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
    split; apply property5_of_fold_right_max_0...
  Qed.

End MyUtilities.

Module MyStructures.

  Class isPoset (A : Type) : Type :=
    { leProp : A -> A -> Prop
    ; Poset_requiresPreOrder :> PreOrder leProp
    ; Poset_requiresPartialOrder :> PartialOrder (@eq A) leProp
    }
  .

  Global Hint Resolve Poset_requiresPreOrder : my_hints.

  Global Hint Resolve Poset_requiresPartialOrder : my_hints.

  Global Notation "x =< y" := (leProp x y) (at level 70, no associativity) : type_scope.

  Lemma Poset_refl {A : Type} `{A_isPoset : isPoset A} :
    forall x : A,
    x =< x.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_refl : my_hints.

  Lemma Poset_refl1 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 = x2 ->
    x1 =< x2.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl1 : my_hints.

  Lemma Poset_refl2 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 = x2 ->
    x2 =< x1.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl2 : my_hints.

  Lemma Poset_asym {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 =< x2 ->
    x2 =< x1 ->
    x1 = x2.
  Proof.
    intros x1 x2 H H0.
    apply Poset_requiresPartialOrder.
    split; [apply H | apply H0].
  Qed.

  Global Hint Resolve Poset_asym : my_hints.

  Lemma Poset_trans {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 =< x2 ->
    x2 =< x3 ->
    x1 =< x3.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_trans : my_hints.

  Global Program Instance nat_isPoset : isPoset nat :=
    { leProp := le
    }
  .

End MyStructures.

Module MyEnsemble.

  Import ListNotations.

  Import MyStructures.

  Definition ensemble : Type -> Type :=
    fun A : Type =>
    arrow A Prop
  .

  Definition member {A : Type} : A -> ensemble A -> Prop :=
    fun x : A =>
    fun xs : ensemble A =>
    xs x
  .

  Global Hint Unfold member : my_hints.

  Global Notation "x '\in' xs" := (member x xs) (at level 70, no associativity) : type_scope.

  Definition isSubsetOf {A : Type} : ensemble A -> ensemble A -> Prop :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    forall x : A,
    member x xs1 ->
    member x xs2
  .

  Global Hint Unfold isSubsetOf : my_hints.

  Global Notation "xs1 '\subseteq' xs2" := (isSubsetOf xs1 xs2) (at level 70, no associativity) : type_scope.

  Global Program Instance ensemble_isPoset {A : Type} : isPoset (ensemble A) :=
    { leProp := isSubsetOf
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with eauto with *.
    intros xs1 xs2.
    split.
    - repeat red.
      split.
      + subst...
      + red.
        subst...
    - intros [H H0].
      apply functional_extensionality.
      intros x.
      apply propositional_extensionality.
      split.
      + apply (H x).
      + apply (H0 x).
  Qed.

  Inductive finite {A : Type} : list A -> ensemble A :=
  | in_finite {x : A} :
    forall xs : list A,
    In x xs ->
    member x (finite xs)
  .

  Global Hint Constructors finite : my_hints.

  Definition empty {A : Type} : ensemble A :=
    finite []
  .

  Lemma in_empty_iff {A : Type} :
    forall x : A,
    member x empty <-> False.
  Proof with eauto with *.
    intros x.
    split...
    intros H.
    inversion H; subst...
  Qed.

  Global Hint Resolve in_empty_iff : my_hints.

  Definition singleton {A : Type} : A -> ensemble A :=
    fun x : A => finite [x]
  .

  Lemma in_singleton_iff {A : Type} :
    forall x : A,
    forall x1 : A,
    member x (singleton x1) <-> x1 = x.
  Proof with eauto with *.
    intros x x1.
    split.
    - intros H.
      inversion H; subst.
      destruct H0 as [H0 | []]...
    - intros H.
      subst...
  Qed.

  Global Hint Resolve in_singleton_iff : my_hints.

  Inductive unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
  | in_unions {x : A} :
    forall xs : ensemble A,
    forall xss : ensemble (ensemble A),
    member x xs ->
    member xs xss ->
    member x (unions xss)
  .

  Global Hint Constructors unions : my_hints.

  Definition union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    unions (finite [xs1; xs2])
  .

  Lemma in_union_iff {A : Type} :
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    forall x : A,
    member x (union xs1 xs2) <-> (member x xs1 \/ member x xs2).
  Proof with eauto with *.
    intros xs1 xs2 x.
    split.
    - intros H.
      inversion H; subst.
      inversion H1; subst.
      destruct H2 as [H2 | [H2 | []]]; subst...
    - intros [H | H]; [apply (in_unions xs1) | apply (in_unions xs2)]...
  Qed.

  Global Hint Resolve in_union_iff : my_hints.

  Inductive intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
  | in_intersection {x : A} :
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    member x xs1 ->
    member x xs2 ->
    member x (intersection xs1 xs2)
  .

  Global Hint Constructors intersection : my_hints.

  Inductive full {A : Type} : ensemble A :=
  | in_full {x : A} :
    member x full
  .

  Global Hint Constructors full : my_hints.

  Inductive image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
  | in_image {x : A} :
    forall f : A -> B,
    forall xs : ensemble A,
    member x xs ->
    member (f x) (image f xs)
  .

  Global Hint Constructors image : my_hints.

  Inductive preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
  | in_preimage {x : A} :
    forall f : A -> B,
    forall ys : ensemble B,
    member (f x) ys ->
    member x (preimage f ys)
  .

  Global Hint Constructors preimage : my_hints.

  Definition nonempty {A : Type} : ensemble A -> Prop :=
    fun xs : ensemble A =>
    exists x : A, member x xs
  .

  Global Hint Unfold nonempty : my_hints.

End MyEnsemble.

Module GeneralTopology.

Import ListNotations.

Import MyStructures.

Import MyEnsemble.

Class isTopologicalSpace (X : Type) : Type :=
  { isOpen : ensemble X -> Prop
  ; open_for_full :
    isOpen full
  ; open_for_unions :
    forall xss : ensemble (ensemble X),
    (forall xs : ensemble X, member xs xss -> isOpen xs) ->
    isOpen (unions xss)
  ; open_for_intersection :
    forall xs1 : ensemble X,
    forall xs2 : ensemble X,
    isOpen xs1 ->
    isOpen xs2 ->
    isOpen (intersection xs1 xs2)
  }
.

Global Hint Resolve open_for_full : my_hints.

Global Hint Resolve open_for_unions : my_hints.

Global Hint Resolve open_for_intersection : my_hints.

Definition isContinuousMap {X : Type} {Y : Type} `{X_isTopologicalSpace : isTopologicalSpace X} `{Y_isTopologicalSpace : isTopologicalSpace Y} : (X -> Y) -> Prop :=
  fun f : X -> Y =>
  forall ys : ensemble Y,
  isOpen ys ->
  isOpen (preimage f ys)
.

Global Hint Unfold isContinuousMap : my_hints.

End GeneralTopology.

Module DomainTheory.

  Import ListNotations.

  Import MyStructures.

  Import MyEnsemble.

  Import GeneralTopology.

  Definition isSupremum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    forall d : D,
    sup_X =< d <-> (forall x : D, member x X -> x =< d)
  .

  Global Hint Unfold isSupremum : my_hints.

  Lemma isSupremum_upperbound {D : Type} `{D_isPoset : isPoset D} :
    forall sup_X : D,
    forall X : ensemble D,
    isSupremum sup_X X ->
    forall x : D,
    member x X ->
    x =< sup_X.
  Proof with eauto with *.
    intros sup_X X H x H0.
    apply H...
  Qed.

  Global Hint Resolve isSupremum_upperbound : my_hints.

  Lemma isSupremum_isSubsetOf {D : Type} `{D_isPoset : isPoset D} :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    isSubsetOf X1 X2 ->
    forall sup_X1 : D,
    isSupremum sup_X1 X1 ->
    forall sup_X2 : D,
    isSupremum sup_X2 X2 ->
    sup_X1 =< sup_X2.
  Proof with eauto with *.
    intros X1 X2 H sup_X1 H0 sup_X2 H1.
    apply H0...
  Qed.

  Global Hint Resolve isSupremum_isSubsetOf : my_hints.

  Lemma isSupremum_ext {D : Type} `{D_isPoset : isPoset D} :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    (forall x : D, member x X1 <-> member x X2) ->
    forall sup_X1 : D,
    isSupremum sup_X1 X1 ->
    forall sup_X2 : D,
    isSupremum sup_X2 X2 <-> sup_X1 = sup_X2.
  Proof with eauto with *.
    intros X1 X2 H sup_X1 H0 sup_X2.
    assert (claim1 := fun x : D => fun H1 : member x X1 => proj1 (H x) H1).
    assert (claim2 := fun x : D => fun H1 : member x X2 => proj2 (H x) H1).
    split...
    intros H1.
    intros x.
    split.
    - intros H2 x' H3.
      apply H0...
    - intros H2.
      enough (H3 : sup_X1 =< x) by apply (Poset_trans sup_X2 sup_X1 x (Poset_refl2 sup_X1 sup_X2 H1) H3).
      apply H0...
  Qed.

  Global Hint Resolve isSupremum_ext : my_hints.

  Lemma isSupremum_unique {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup1 : D,
    isSupremum sup1 X ->
    forall sup2 : D,
    isSupremum sup2 X <-> sup1 = sup2.
  Proof with eauto with *.
    intros X sup1 H sup2...
  Qed.

  Global Hint Resolve isSupremum_unique : my_hints.

    Definition image_sup {D : Type} `{D_isPoset : isPoset D} : ensemble (ensemble D) -> ensemble D :=
      fun Xs : ensemble (ensemble D) =>
      fun sup_X : D =>
      exists X : ensemble D, member X Xs /\ isSupremum sup_X X
    .

  Global Hint Unfold image_sup : my_hints.

  Lemma sup_image_sup_isGreaterThan {D : Type} `{D_isPoset : isPoset D} :
    forall Xs : ensemble (ensemble D),
    forall sup : D,
    isSupremum sup (image_sup Xs) ->
    forall X : ensemble D,
    member X Xs ->
    forall sup_X : D,
    isSupremum sup_X X ->
    sup_X =< sup.
  Proof with eauto with *.
    intros Xs sup H X H0 sup_X H1.
    apply H...
  Qed.

  Global Hint Resolve sup_image_sup_isGreaterThan : my_hints.

  Lemma isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs {D : Type} `{D_isPoset : isPoset D} :
    forall Xs : ensemble (ensemble D),
    (forall X : ensemble D, member X Xs -> exists sup_X : D, isSupremum sup_X X) ->
    forall sup : D,
    isSupremum sup (unions Xs) <-> isSupremum sup (image_sup Xs).
  Proof with eauto with *.
    intros Xs H sup.
    split.
    - intros H0 x.
      split.
      + intros H1 x' [X [H2 H3]].
        apply H3...
      + intros H1.
        apply H0.
        intros x' H2.
        inversion H2; subst.
        destruct (H xs H4) as [sup_xs H5].
        apply H5...
        apply H1...
    - intros H0 x.
      split.
      + intros H1 x' H2.
        inversion H2; subst.
        destruct (H xs H4) as [sup_xs H5].
        apply H5...
      + intros H1.
        apply H0.
        intros x' [X [H2 H3]].
        apply H3...
  Qed.

  Class isCompleteLattice (D : Type) : Type :=
    { CompleteLattice_requiresPoset :> isPoset D
    ; supremum_always_exists :
      forall X : ensemble D,
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Global Hint Resolve supremum_always_exists : my_hints.

  Lemma unions_isSupremum {A : Type} :
    forall Xs : ensemble (ensemble A),
    isSupremum (unions Xs) Xs.
  Proof with eauto with *.
    intros Xs X.
    split.
    - intros H xs H0.
      transitivity (unions Xs)...
      intros x H1.
      apply (in_unions xs)...
    - intros H x H0.
      inversion H0; subst.
      apply (H xs)...
  Qed.

  Global Instance ensemble_isCompleteLattice {A : Type} : isCompleteLattice (ensemble A) :=
    { CompleteLattice_requiresPoset := ensemble_isPoset
    ; supremum_always_exists :=
      fun Xs : ensemble (ensemble A) =>
      exist _ (unions Xs) (unions_isSupremum Xs)
    }
  .

  Definition isDirected {D : Type} `{D_isPoset : isPoset D} : ensemble D -> Prop :=
    fun X : ensemble D =>
    nonempty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ x1 =< x3 /\ x2 =< x3)
  .

  Global Hint Unfold isDirected : my_hints.

  Class isCompletePartialOrder (D : Type) : Type :=
    { CompletePartialOrder_requiresPoset :> isPoset D
    ; bottom_exists : {min_D : D | forall x : D, min_D =< x}
    ; square_up_exists :
      forall X : ensemble D,
      isDirected X ->
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Global Program Instance CompleteLattice_isCompletePartialOrder {D : Type} (D_requiresCompleteLattice : isCompleteLattice D) : isCompletePartialOrder D :=
    { CompletePartialOrder_requiresPoset := CompleteLattice_requiresPoset
    }
  .

  Next Obligation.
    destruct (supremum_always_exists empty) as [min_D H].
    exists min_D.
    intros x.
    apply H.
    intros x' H0.
    inversion H0; subst.
    inversion H1.
  Defined.

  Next Obligation.
    apply supremum_always_exists.
  Defined.

  Global Program Instance ScottTopology_isTopologicalSpace {D : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) : isTopologicalSpace D :=
    { isOpen :=
      fun O : ensemble D =>
      (forall x : D, forall y : D, member x O -> x =< y -> member y O) /\ (forall X : ensemble D, isDirected X -> forall sup_X : D, isSupremum sup_X X -> member sup_X O -> nonempty (intersection X O))
    }
  .

  Next Obligation with eauto with *.
    split...
    intros.
    destruct H as [[x H] H2]...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros.
      destruct H0.
      apply (in_unions xs)...
      apply (proj1 (H xs H2) x y)...
    - intros.
      inversion H0; subst.
      inversion H2; subst.
      destruct (proj2 (H xs H6) X H0 sup_X H1 H5) as [x H7].
      inversion H7; subst...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros.
      destruct H3...
    - intros.
      inversion H5; subst.
      destruct (H2 X H3 sup_X H4 H6) as [x1 H8].
      destruct (H1 X H3 sup_X H4 H7) as [x2 H9].
      inversion H3; subst.
      inversion H8; inversion H9; subst.
      destruct (H11 x1 H12 x2 H17) as [x [H14 [H15 H16]]].
      exists x...
  Qed.

  Definition U {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} : D -> ensemble D :=
    fun x : D =>
    fun z : D =>
    ~ z =< x
  .

  Global Hint Unfold U : my_hints.

  Lemma U_x_isOpen {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} :
    forall x : D,
    isOpen (U x).
  Proof with eauto with *.
    intros x.
    assert ( claim1 :
      forall y : D,
      forall z : D,
      member y (U x) ->
      y =< z ->
      member z (U x)
    ).
    { intros y z H H0 H1.
      contradiction H...
    }
    split...
    intros X H sup_X H0 H1.
    inversion H; subst.
    assert (claim2 : ~ (forall x0 : D, x0 =< x \/ ~ member x0 X)).
    { intros H4.
      contradiction H1.
      apply (proj2 (H0 x)).
      intros x0 H5.
      destruct (H4 x0); [apply H6 | contradiction].
    }
    apply not_all_ex_not in claim2.
    destruct claim2 as [x1 H4].
    exists x1.
    apply not_or_and in H4.
    destruct H4 as [H4 H5].
    apply NNPP in H5...
  Qed.

  Definition characterization_of_ContinuousMap_on_cpos {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D -> D') -> Prop :=
    fun f : D -> D' =>
    forall X : ensemble D,
    isDirected X ->
    let Y : ensemble D' := image f X in
    exists sup_X : D, exists sup_Y : D', isSupremum sup_X X /\ isSupremum sup_Y Y /\ f sup_X = sup_Y
  .

  Lemma ContinuousMaps_on_cpos_are_always_monotonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall x1 : D,
    forall x2 : D,
    x1 =< x2 ->
    f x1 =< f x2.
  Proof with eauto with *.
    intros f H x1 x2 H0.
    apply NNPP.
    intros H1.
    assert (H2 : member (f x1) (U (f x2))) by now unfold U.
    assert (H3 : member x1 (preimage f (U (f x2)))) by now constructor.
    assert (H4 : isOpen (preimage f (U (f x2)))) by now apply H, U_x_isOpen.
    assert (H5 : member x2 (preimage f (U (f x2)))) by now apply (proj1 H4 x1 x2).
    enough (H6 : member (f x2) (U (f x2)))...
    inversion H5...
  Qed.

  Lemma ContinuousMaps_preservesDirected {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    isDirected (image f X).
  Proof with eauto with *.
    intros f H X H0.
    destruct H0 as [H0 H1].
    assert (H2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMaps_on_cpos_are_always_monotonic.
    split.
    - destruct H0 as [x0 H0]...
    - intros y1 H3 y2 H4.
      inversion H3; inversion H4; subst.
      rename x into x1, x0 into x2.
      destruct (H1 x1 H5 x2 H9) as [x3 [H6 [H7 H8]]].
      exists (f x3).
      repeat split...
  Qed.

  Lemma ContinuousMaps_preservesSupremum {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    isDirected (image f X) ->
    {sup_Y : D' | isSupremum sup_Y (image f X) /\ f sup_X = sup_Y}.
  Proof with eauto with *.
    intros f H X H0 sup_X H1 H2.
    set (Y := image f X).
    assert (H3 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMaps_on_cpos_are_always_monotonic.
    destruct (square_up_exists Y H2) as [sup_Y H4].
    exists sup_Y.
    assert (claim1 : sup_Y =< f sup_X).
    { apply H4.
      intros y H5.
      inversion H5; subst.
      apply H3, H1...
    }
    assert (claim2 : f sup_X =< sup_Y).
    { apply NNPP.
      intros H5.
      assert (H6 : member (f sup_X) (U sup_Y)) by now unfold U.
      assert (H7 : member sup_X (preimage f (U sup_Y))) by now constructor.
      assert (H8 : isOpen (preimage f (U sup_Y))) by now apply H, U_x_isOpen.
      destruct H8.
      destruct (H9 X H0 sup_X H1 H7) as [x1 H10].
      inversion H10; subst.
      inversion H12; subst.
      contradiction H13...
    }
    split...
  Qed.

  Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f <-> characterization_of_ContinuousMap_on_cpos f.
  Proof with eauto with *.
    assert (claim1 : forall f : D -> D', isContinuousMap f -> forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by apply ContinuousMaps_on_cpos_are_always_monotonic.
    split.
    - intros H X H0.
      inversion H0; subst.
      set (Y := image f X).
      assert (H3 : isDirected Y) by now apply ContinuousMaps_preservesDirected.
      destruct (square_up_exists X H0) as [sup_X H4].
      exists sup_X.
      destruct (ContinuousMaps_preservesSupremum f H X H0 sup_X H4 H3) as [sup_Y H5].
      exists sup_Y...
    - intros H.
      assert (claim2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2).
      { intros x1 x2 H0.
        set (X := finite [x1; x2]).
        set (Y := image f X).
        assert (H1 : isSupremum x2 X).
        { intros x.
          split.
          - intros H1 x' H2.
            inversion H2; subst.
            destruct H3 as [H3 | [H3 | []]]...
          - intros H1...
        }
        assert (H2 : isDirected X).
        { split.
          - exists x1...
          - intros x1' H2 x2' H3.
            exists x2.
            enough (x1' =< x2 /\ x2' =< x2)...
        }
        destruct (H X H2) as [sup_X H3].
        destruct H3 as [sup_Y [H3 [H4 H5]]].
        assert (H6 : sup_X = x2) by now apply (isSupremum_unique X).
        subst...
      }
      intros O H0.
      split.
      + intros x1 x2 H1 H2.
        inversion H1; subst.
        constructor.
        apply (proj1 H0 (f x1) (f x2))...
      + intros X H1 sup_X H2 H3.
        destruct (H X H1) as [sup_X' [sup_Y [H4 [H5 H6]]]].
        assert (H7 : sup_X = sup_X') by now apply (isSupremum_unique X).
        subst sup_X' sup_Y.
        assert (H8 : member (f sup_X) O) by now inversion H3; subst.
        assert (H9 : isDirected (image f X)).
        { destruct H1 as [[x1_0 H1] H6].
          split.
          - exists (f x1_0)...
          - intros y1 H10 y2 H11.
            inversion H10; subst.
            inversion H11; subst.
            rename x into x1, x0 into x2.
            destruct (H6 x1 H7 x2 H9) as [x3 [H12 [H13 H14]]].
            exists (f x3).
            repeat split...
        }
        assert (H10 : nonempty (intersection (image f X) O)).
        { apply (proj2 H0 (image f X) H9 (f sup_X))...
        }
        destruct H10 as [y1 H10].
        inversion H10; subst.
        inversion H6; subst.
        exists x...
  Qed.

  Local Program Instance DirectProductOfTwoPosets_isPoset {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isPoset (D * D') :=
    { leProp :=
      fun p1 : (D * D') =>
      fun p2 : (D * D') =>
      fst p1 =< fst p2 /\ snd p1 =< snd p2
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros [x1 y1]...
    - intros [x1 y1] [x2 y2] [x3 y3] [H H0] [H1 H2]...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros H.
      subst.
      repeat red.
      repeat split...
    - intros [[H H0] [H1 H2]].
      apply injective_projections...
  Qed.

  Inductive getFsts {D : Type} {D' : Type} : ensemble (D * D') -> ensemble D :=
  | in_getFsts {ps : ensemble (D * D')} :
    forall x : D,
    forall x' : D',
    member (x, x') ps ->
    member x (getFsts ps)
  .

  Global Hint Constructors getFsts : domain_theory_hints.

  Inductive getSnds {D : Type} {D' : Type} : ensemble (D * D') -> ensemble D' :=
  | in_getSnds {ps : ensemble (D * D')} :
    forall x : D,
    forall x' : D',
    member (x, x') ps ->
    member x' (getSnds ps)
  .

  Global Hint Constructors getSnds : domain_theory_hints.

  Local Program Instance DirectProductOfTwoCompletePartialOrders_isCompletePartialOrder {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isCompletePartialOrder (D * D') :=
    { CompletePartialOrder_requiresPoset := DirectProductOfTwoPosets_isPoset (@CompletePartialOrder_requiresPoset D D_requiresCompletePartialOrder) (@CompletePartialOrder_requiresPoset D' D'_requiresCompletePartialOrder)
    }
  .

  Next Obligation.
    destruct (@bottom_exists D D_requiresCompletePartialOrder) as [bot_D H].
    destruct (@bottom_exists D' D'_requiresCompletePartialOrder) as [bot_D' H0].
    exists (bot_D, bot_D').
    intros [d d'].
    split; [apply H | apply H0].
  Defined.

  Next Obligation.
    assert (claim1 : isDirected (getFsts X)).
    { destruct H as [H H0].
      split.
      - destruct H as [[d0 d0'] H].
        exists d0.
        apply (in_getFsts d0 d0' H).
      - intros d1 H1 d2 H2.
        inversion H1; subst.
        inversion H2; subst.
        rename x' into d1', x'0 into d2'.
        destruct (H0 (d1, d1') H3 (d2, d2') H4) as [[d3 d3'] [H5 [[H6 H7] [H8 H9]]]].
        exists d3.
        split.
        + apply (in_getFsts d3 d3' H5).
        + split; [apply H6 | apply H8].
    }
    assert (claim2 : isDirected (getSnds X)).
    { destruct H as [H H0].
      split.
      - destruct H as [[d0 d0'] H].
        exists d0'.
        apply (in_getSnds d0 d0' H).
      - intros d1' H1 d2' H2.
        inversion H1; subst.
        inversion H2; subst.
        rename x into d1, x0 into d2.
        destruct (H0 (d1, d1') H3 (d2, d2') H4) as [[d3 d3'] [H5 [[H6 H7] [H8 H9]]]].
        exists d3'.
        split.
        + apply (in_getSnds d3 d3' H5).
        + split; [apply H7 | apply H9].
    }
    destruct (@square_up_exists D D_requiresCompletePartialOrder (getFsts X) claim1) as [sup_X1 H0].
    destruct (@square_up_exists D' D'_requiresCompletePartialOrder (getSnds X) claim2) as [sup_X2 H1].
    exists (sup_X1, sup_X2).
    intros [d d'].
    split.
    - intros H2 [x x'] H3.
      split.
      + apply H0.
        * apply (proj1 H2).
        * apply (in_getFsts x x' H3).
      + apply H1.
        * apply (proj2 H2).
        * apply (in_getSnds x x' H3).
    - intros H2.
      split.
      + apply H0.
        intros x H3.
        inversion H3; subst.
        apply (proj1 (H2 (x, x') H4)).
      + apply H1.
        intros x' H3.
        inversion H3; subst.
        apply (proj2 (H2 (x, x') H4)).
  Defined.

  Local Notation "D1 ~> D2" := ({f : D1 -> D2 | isContinuousMap f}) (at level 70, no associativity) : type_scope.

  Definition ContinuousMap_is_continuous {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : forall f : D ~> D', isContinuousMap (proj1_sig f) :=
    fun f : D ~> D' => proj2_sig f
  .

  Global Hint Resolve ContinuousMap_is_continuous : my_hints.

  Lemma squigarrows_are_the_same_iff {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f1 : D ~> D',
    forall f2 : D ~> D',
    (forall x : D, proj1_sig f1 x = proj1_sig f2 x) ->
    f1 = f2.
  Proof with eauto.
    intros f1 f2 H.
    enough (claim1 : proj1_sig f1 = proj1_sig f2) by apply (eq_sig f1 f2 claim1), proof_irrelevance.
    apply functional_extensionality...
  Qed.

  Global Hint Resolve squigarrows_are_the_same_iff : my_hints.

  Local Program Instance squigarrow_isPoset {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isPoset (D ~> D') :=
    { leProp :=
      fun f1 : D ~> D' =>
      fun f2 : D ~> D' =>
      forall x : D,
      proj1_sig f1 x =< proj1_sig f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros H.
      subst.
      split; intros x...
    - intros [H H0]...
  Qed.

  Lemma sup_of_squigarrow_is_well_defined {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall fs : ensemble (D ~> D'),
    isDirected fs ->
    forall x : D,
    isDirected (image (fun f : D ~> D' => proj1_sig f x) fs).
  Proof with eauto with *.
    intros fs [H H0] x.
    split.
    - destruct H as [f0].
      exists (proj1_sig f0 x).
      apply (in_image (fun f : D ~> D' => proj1_sig f x))...
    - intros y1 H1 y2 H2.
      inversion H1; subst.
      inversion H2; subst.
      rename x0 into f1, x1 into f2.
      destruct (H0 f1 H3 f2 H4) as [f3 [H5 [H6 H7]]].
      exists (proj1_sig f3 x).
      repeat split...
      apply (in_image (fun f : D ~> D' => proj1_sig f x))...
  Qed.

  Lemma sup_of_set_of_squigarrows_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall fs : ensemble (D ~> D'),
    forall fs_isDirected : isDirected fs,
    let f : D -> D' := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs fs_isDirected x)) in
    isContinuousMap f.
  Proof with eauto with *.
    intros fs H f.
    apply the_main_reason_for_introducing_ScottTopology.
    intros X H0 Y.
    destruct (square_up_exists X H0) as [sup_X H1].
    exists sup_X, (f sup_X).
    assert ( claim1 :
      forall f_i : D ~> D',
      member f_i fs ->
      isSupremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
    ).
    { intros f_i H2.
      assert (H3 : isContinuousMap (proj1_sig f_i))...
      assert (H4 : characterization_of_ContinuousMap_on_cpos (proj1_sig f_i)) by now apply the_main_reason_for_introducing_ScottTopology.
      destruct (H4 X H0) as [sup_X' [sup_Y' [H5 [H6 H7]]]].
      assert (H8 : sup_X' = sup_X) by now apply (isSupremum_unique X).
      subst...
    }
    assert (claim2 : isSupremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs) (sup_of_squigarrow_is_well_defined fs H sup_X))).
    assert (claim3 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs.
      - intros ys H2.
        inversion H2; subst.
        rename x into f_i.
        exists (proj1_sig f_i sup_X)...
      - intros y.
        split.
        + intros H2 y' [ys [H3 H4]].
          inversion H3; subst.
          rename x into f_i.
          assert (H6 := claim1 f_i H5).
          assert (H7 : y' = proj1_sig f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X)).
          transitivity (proj1_sig f_i sup_X)...
          apply claim2...
          apply (in_image (fun f_i0 : D ~> D' => proj1_sig f_i0 sup_X))...
        + intros H2.
          apply claim2.
          intros y' H3.
          inversion H3; subst.
          rename x into f_i.
          apply H2.
          exists (image (fun x : D => proj1_sig f_i x) X).
          split...
          apply (in_image (fun f_i0 : D ~> D' => image (fun x : D => proj1_sig f_i0 x) X))...
    }
    assert (claim4 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
    { enough (H2 : forall x' : D', member x' (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs)) <-> member x' (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))) by now apply (proj2 (isSupremum_ext _ _ H2 _ claim3 _) eq_refl).
      intros y.
      split.
      - intros H2.
        inversion H2; subst.
        rename xs into ys.
        inversion H4; subst.
        rename x into f_i.
        inversion H3; subst.
        apply (in_unions (image (fun f_i' : D ~> D' => proj1_sig f_i' x) fs)).
        + apply (in_image (fun f_i' : D ~> D' => proj1_sig f_i' x))...
        + apply (in_image (fun x0 : D => image (fun f_i0 : D ~> D' => proj1_sig f_i0 x0) fs))...
      - intros H2.
        inversion H2; subst.
        rename xs into ys.
        inversion H4; subst.
        inversion H3; subst.
        rename x0 into f_i.
        apply (in_unions (image (fun x' : D => proj1_sig f_i x') X)).
        + apply (in_image (fun x' : D => proj1_sig f_i x'))...
        + apply (in_image (fun f_i0 : D ~> D' => image (fun x0 : D => proj1_sig f_i0 x0) X))...
    }
    assert (claim5 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
      intros ys H2.
      inversion H2; subst.
      exists (f x).
      intros y.
      split.
      - intros H4 y' H5.
        inversion H5; subst.
        rename x0 into f_i.
        apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x)))...
      - intros H4.
        assert (H5 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
        apply H5...
    }
    assert (claim6 : isSupremum (f sup_X) (image f X)).
    { intros y.
      split.
      - intros H2 y' H3.
        inversion H3; subst.
        apply claim5...
        exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs).
        split.
        + apply (in_image (fun x0 : D => image (fun f_i : D ~> D' => proj1_sig f_i x0) fs))...
        + apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
      - intros H2.
        apply claim5.
        intros y' [ys [H3 H4]].
        inversion H3; subst.
        assert (H6 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
        assert (H7 : y' = f x) by now apply (isSupremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)).
        transitivity (f x)...
    }
    split...
  Qed.

  Local Program Instance squigarrow_isCompletePartialOrder {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isCompletePartialOrder (D ~> D') :=
    { CompletePartialOrder_requiresPoset := squigarrow_isPoset D_requiresCompletePartialOrder D'_requiresCompletePartialOrder
    }
  .

  Next Obligation.
    set (bot := fun _ : D => proj1_sig bottom_exists).
    assert (claim1 : isContinuousMap bot).
    { intros Y [H H0].
      split.
      - intros x1 x2 H1 H2.
        inversion H1; subst.
        apply (in_preimage bot).
        apply (H (bot x1) (bot x2) H3 (Poset_refl (proj1_sig bottom_exists))).
      - intros X [[x_0 H1] H2] sup_X H3 H4.
        inversion H4; subst.
        exists x_0.
        constructor.
        + apply H1.
        + apply (in_preimage bot).
          apply (H (bot sup_X) (bot x_0) H5).
          apply Poset_refl.
    }
    exists (exist _ bot claim1).
    simpl.
    intros f x.
    apply (proj2_sig bottom_exists).
  Defined.

  Next Obligation.
    rename X into fs, H into fs_isDirected.
    set (sup_fs := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs fs_isDirected x))).
    exists (exist _ sup_fs (sup_of_set_of_squigarrows_exists_if_it_is_directed fs fs_isDirected)).
    assert (claim1 : forall x : D, isSupremum (sup_fs x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (fun x : D => proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs fs_isDirected x))).
    intros f.
    simpl.
    split.
    - intros H f' H0 x.
      apply (claim1 x).
      + apply H.
      + apply (in_image (fun f_i : D ~> D' => proj1_sig f_i x)).  
        apply H0.
    - intros H x.
      apply (claim1 x).
      intros f' H0.
      inversion H0; subst.
      rename x0 into f'.
      apply (H f').
      apply H1.
  Defined.

  Lemma separately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isCompletePartialOrder : isCompletePartialOrder D1} `{D2_isCompletePartialOrder : isCompletePartialOrder D2} `{D3_isCompletePartialOrder : isCompletePartialOrder D3} :
    forall f : D1 * D2 -> D3,
    ((forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2))) /\ (forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)))) <-> isContinuousMap f.
  Proof with eauto with *.
    intros f.
    split.
    - intros [H H0].
      apply the_main_reason_for_introducing_ScottTopology.
      intros X H1 Y.
      destruct (square_up_exists X H1) as [[sup_X1 sup_X2] H2].
      set (X1 := getFsts X).
      set (X2 := getSnds X).
      exists (sup_X1, sup_X2), (f (sup_X1, sup_X2)).
      assert (claim1 : isDirected X1).
      { destruct H1 as [[[x1_0 x2_0] H1] H3].
        split.
        - exists x1_0.
          apply (in_getFsts x1_0 x2_0)...
        - intros x1_1 H4 x1_2 H5.
          inversion H4; subst.
          inversion H5; subst.
          rename x' into x2_1, x'0 into x2_2.
          destruct (H3 (x1_1, x2_1) H6 (x1_2, x2_2) H7) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
          exists x3_1.
          split...
          apply (in_getFsts x3_1 x3_2)...
      }
      assert (claim2 : isDirected X2).
      { destruct H1 as [[[x1_0 x2_0] H1] H3].
        split.
        - exists x2_0.
          apply (in_getSnds x1_0 x2_0)...
        - intros x2_1 H4 x2_2 H5.
          inversion H4; subst.
          inversion H5; subst.
          rename x into x1_1, x0 into x1_2.
          destruct (H3 (x1_1, x2_1) H6 (x1_2, x2_2) H7) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
          exists x3_2.
          split...
          apply (in_getSnds x3_1 x3_2)...
      }
      assert ( claim3 :
        forall x1 : D1,
        exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremum sup_X2_x1 X2 /\ isSupremum sup_f_X2_x1 (image (fun x2 : D2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) = sup_f_X2_x1
      ).
      { intros x1.
        apply (the_main_reason_for_introducing_ScottTopology (fun x2 : D2 => f (x1, x2)))...
      }
      assert ( claim4 :
        forall x2 : D2,
        exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremum sup_X1_x2 X1 /\ isSupremum sup_f_X1_x2 (image (fun x1 : D1 => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) = sup_f_X1_x2
      ).
      { intros x2.
        apply (the_main_reason_for_introducing_ScottTopology (fun x1 : D1 => f (x1, x2)))...
      }
      assert (XXX : isSupremum sup_X1 X1 /\ isSupremum sup_X2 X2).
      { destruct (square_up_exists X1 claim1) as [sup_X1' H3].
        destruct (square_up_exists X2 claim2) as [sup_X2' H4].
        assert (H5 : isSupremum (sup_X1', sup_X2') X).
        { intros [x1 x2].
          split.
          - intros [H5 H6] [x1' x2'] H7.
            simpl in *.
            split.
            + apply H3...
              apply (in_getFsts x1' x2')...
            + apply H4...
              apply (in_getSnds x1' x2')...
          - intros H5.
            split.
            + apply H3.
              intros x1' H6.
              inversion H6; subst.
              rename x' into x2'.
              apply (proj1 (H5 (x1', x2') H7)).
            + apply H4.
              intros x2' H6.
              inversion H6; subst.
              rename x into x1'.
              apply (proj2 (H5 (x1', x2') H7)).
          }
        assert (H6 : (sup_X1, sup_X2) = (sup_X1', sup_X2')) by now apply (isSupremum_unique X).
        inversion H6; subst.
        simpl in *.
        split...
      }
      destruct XXX as [claim5 claim6].
      assert (claim7 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
      { destruct (claim3 sup_X1) as [sup_X2_x1 [sup_f_X1_x2 [H3 [H4 H5]]]].
        assert (H6 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2) <-> sup_f_X1_x2 = f (sup_X1, sup_X2)) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder)).
        apply H6.
        transitivity (f (sup_X1, sup_X2_x1)).
        - symmetry...
        - enough (H7 : sup_X2_x1 = sup_X2) by congruence.
          apply (isSupremum_unique X2)...
      }
      assert ( claim8 :
        forall x2 : D2,
        member x2 X2 ->
        isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)
      ).
      { intros x2 H3.
        destruct (claim4 x2) as [sup_X1' [sup_f_X1_x2' [H4 [H5 H6]]]].
        assert (H7 : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1) <-> sup_f_X1_x2' = f (sup_X1, x2)) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder)).
        apply H7.
        transitivity (f (sup_X1', x2)).
        - symmetry...
        - enough (H8 : sup_X1' = sup_X1) by congruence.
          apply (isSupremum_unique X1)...
      }
      assert (claim9 : isSupremum (f (sup_X1, sup_X2)) (image_sup (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
      { intros y.
        split.
        - intros H3 y' [ys [H4 H5]].
          inversion H4; subst.
          rename x into x2.
          assert (H7 : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)) by now apply claim8.
          assert (H8 : y' = (f (sup_X1, x2))) by now apply (isSupremum_unique (image (fun x1 : D1 => f (x1, x2)) X1)).
          assert (H9 : f (sup_X1, x2) =< f (sup_X1, sup_X2)).
          { apply (ContinuousMaps_on_cpos_are_always_monotonic (fun x2' : D2 => f (sup_X1, x2')) (H sup_X1)).
            apply claim6...
          }
          transitivity (f (sup_X1, x2))...
        - intros H7.
          apply claim7.
          intros y' H8.
          inversion H8; subst.
          rename x into x2.
          apply H7...
          exists (image (fun x1 : D1 => f (x1, x2)) X1).
          split.
          + apply (in_image (fun x0 : D2 => image (fun x1 : D1 => f (x1, x0)) X1))...
          + apply claim8...
      }
      assert (claim10 : isSupremum (f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
      { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
        intros ys H3.
        inversion H3; subst.
        rename x into x2.
        exists (f (sup_X1, x2))...
      }
      assert (claim11 : isSupremum (f (sup_X1, sup_X2)) (image f X)).
      { intros y.
        split.
        - intros H3 y' H4.
          inversion H4; subst.
          apply claim10.
          + apply H3.
          + destruct x as [x1 x2].
            apply (in_unions (image (fun x1' : D1 => f (x1', x2)) X1)).
            * apply (in_image (fun x1' : D1 => f (x1', x2))).
              apply (in_getFsts x1 x2)...
            * apply (in_image (fun x0 : D2 => image (fun x3 : D1 => f (x3, x0)) X1)).
              apply (in_getSnds x1 x2)...
        - intros H3.
          apply claim10.
          intros y' H4.
          inversion H4; subst.
          rename xs into ys.
          inversion H6; subst.
          rename x into x2_2.
          inversion H5; subst.
          rename x into x1_1.
          inversion H8; subst.
          rename x' into x2_1.
          inversion H7; subst.
          rename x into x1_2.
          destruct H1 as [H1 H11].
          destruct (H11 (x1_1, x2_1) H9 (x1_2, x2_2) H10) as [[x3_1 x3_2] [H12 [[H13 H14] [H15 H16]]]].
          simpl in *.
          assert (H17 : f (x1_1, x2_2) =< f (x3_1, x3_2)).
          { transitivity (f (x1_1, x3_2)).
            - apply (ContinuousMaps_on_cpos_are_always_monotonic (fun x2 : D2 => f (x1_1, x2)))...
            - apply (ContinuousMaps_on_cpos_are_always_monotonic (fun x1 : D1 => f (x1, x3_2)))...
          }
          transitivity (f (x3_1, x3_2))...
      }
      split...
    - intros H.
      split.
      + intros x1.
        apply (the_main_reason_for_introducing_ScottTopology (fun x2 : D2 => f (x1, x2))).
        intros X2 H0 Y.
        destruct (square_up_exists X2 H0) as [sup_X2 H1].
        set (X := image (fun x2 : D2 => (x1, x2)) X2).
        assert (claim1 : isDirected X).
        { destruct H0 as [[x2_0 H0] H2].
          split.
          - exists (x1, x2_0).
            apply (in_image (fun x2 : D2 => (x1, x2)))...
          - intros [x1_1 x2_1] H3 [x1_2 x2_2] H4.
            inversion H3; subst x1_1; subst.
            inversion H4; subst x1_2; subst.
            rename H8 into H5, H9 into H6.
            destruct (H2 x2_1 H5 x2_2 H6) as [x3_2 [H7 [H8 H9]]].
            exists (x1, x3_2).
            repeat split...
        }
        destruct (square_up_exists X claim1) as [sup_X H2].
        exists sup_X2, (f sup_X).
        assert (claim2 : (x1, sup_X2) = sup_X).
        { apply (isSupremum_unique X)...
          intros [x_1 x_2].
          split.
          - intros [H3 H4] [x_1' x_2'] H5.
            inversion H5; subst x_1'; subst.
            simpl.
            split...
          - intros H3.
            simpl.
            split.
            + destruct H0 as [[x2_0 H0] H4].
              apply (H3 (x1, x2_0))...
            + apply H1.
              intros x_2' H4.
              apply (H3 (x1, x_2'))...
        }
        assert (claim3 : f (x1, sup_X2) = f sup_X) by congruence.
        assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' = sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
        destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
        assert (claim4 : isSupremum (f sup_X) Y).
        { assert (H6 : isSupremum (f sup_X) (image f X) <-> sup_Y' = f sup_X) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) (image f X)).
          assert (H7 : isSupremum (f sup_X) (image f X)).
          { apply H6.
            transitivity (f sup_X').
            - symmetry...
            - enough (H7 : sup_X' = sup_X) by congruence.
              apply (isSupremum_unique X)...
          }
          assert (H8 : forall y : D3, member y (image f X) <-> member y Y).
          { intros y.
            split.
            - intros H8.
              inversion H8; subst.
              inversion H9; subst.
              rename x0 into x2.
              apply (in_image (fun x2 : D2 => f (x1, x2)))...
            - intros H8.
              inversion H8; subst.
              rename x into x2.
              apply (in_image f)...
          }
          apply (proj2 (@isSupremum_ext D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) _ _ H8 _ H7 _) eq_refl).
        }
        split...
      + intros x2.
        apply (the_main_reason_for_introducing_ScottTopology (fun x1 : D1 => f (x1, x2))).
        intros X1 H0 Y.
        destruct (square_up_exists X1 H0) as [sup_X1 H1].
        set (X := image (fun x1 : D1 => (x1, x2)) X1).
        assert (YYY : forall x1 : D1, member x1 X1 -> member (x1, x2) X).
        { intros x1 H2.
          apply (in_image (fun x1 : D1 => (x1, x2))), H2.
        }
        assert (claim1 : isDirected X).
        { destruct H0 as [[x1_0 H0] H2].
          split.
          - exists (x1_0, x2).
            apply (in_image (fun x1 : D1 => (x1, x2)))...
          - intros [x1_1 x2_1] H3 [x1_2 x2_2] H4.
            inversion H3; subst x2_1; subst.
            inversion H4; subst x2_2; subst.
            rename H8 into H5, H9 into H6.
            destruct (H2 x1_1 H5 x1_2 H6) as [x3_1 [H7 [H8 H9]]].
            exists (x3_1, x2).
            repeat split...
        }
        destruct (square_up_exists X claim1) as [sup_X H2].
        exists sup_X1, (f sup_X).
        assert (claim2 : (sup_X1, x2) = sup_X).
        { apply (isSupremum_unique X)...
          intros [x_1 x_2].
          split.
          - intros [H3 H4] [x_1' x_2'] H5.
            inversion H5; subst x_1'; subst.
            simpl.
            split...
          - intros H3.
            simpl.
            split.
            + apply H1.
              intros x_1' H4.
              apply (H3 (x_1', x2))...
            + destruct H0 as [[x1_0 H0] H4].
              apply (H3 (x1_0, x2))...
        }
        assert (claim3 : f (sup_X1, x2) = f sup_X) by congruence.
        assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' = sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
        destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
        assert (claim4 : isSupremum (f sup_X) Y).
        { assert (H6 : isSupremum (f sup_X) (image f X) <-> sup_Y' = f sup_X) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) (image f X)).
          assert (H7 : isSupremum (f sup_X) (image f X)).
          { apply H6.
            transitivity (f sup_X').
            - symmetry...
            - enough (H7 : sup_X' = sup_X) by congruence.
              apply (isSupremum_unique X)...
          }
          assert (H8 : forall y : D3, member y (image f X) <-> member y Y).
          { intros y.
            split.
            - intros H8.
              inversion H8; subst.
              inversion H9; subst.
              rename x0 into x1.
              apply (in_image (fun x1 : D1 => f (x1, x2)))...
            - intros H8.
              inversion H8; subst.
              rename x into x1.
              apply (in_image f)...
          }
          apply (proj2 (@isSupremum_ext D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) _ _ H8 _ H7 _) eq_refl).
        }
        split...
  Qed.

End DomainTheory.

Module UntypedLamdbdaCalculus.

  Import ListNotations.

  Import MyUtilities.

  Import MyStructures.

  Import MyEnsemble.

  Import GeneralTopology.

  Import DomainTheory.

  Definition ivar : Set :=
    nat
  .

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    apply Nat.eq_dec.
  Defined.

  Inductive tm : Set :=
  | tmVar : forall x : ivar, tm
  | tmApp : forall P1 : tm, forall P2 : tm, tm
  | tmLam : forall y : ivar, forall Q : tm, tm
  .

  Definition tm_eq_dec :
    forall M1 : tm,
    forall M2 : tm,
    {M1 = M2} + {M1 <> M2}.
  Proof with try ((left; congruence) || (right; congruence)).
    induction M1; destruct M2...
    - destruct (ivar_eq_dec x x0)...
    - destruct (IHM1_1 M2_1); destruct (IHM1_2 M2_2)...
    - destruct (ivar_eq_dec y y0); destruct (IHM1 M2)...
  Defined.

  Fixpoint getRank (M : tm) {struct M} : nat :=
    match M with
    | tmVar x => 0
    | tmApp P1 P2 => S (max (getRank P1) (getRank P2))
    | tmLam y Q => S (getRank Q)
    end
  .

  Inductive subtm : tm -> tm -> Set :=
  | subtmRefl : forall M : tm, subtm M M
  | subtmAppL : forall M : tm, forall P1 : tm, forall P2 : tm, subtm M P1 -> subtm M (tmApp P1 P2)
  | subtmAppR : forall M : tm, forall P1 : tm, forall P2 : tm, subtm M P2 -> subtm M (tmApp P1 P2)
  | subtmLAbs : forall M : tm, forall y : ivar, forall Q : tm, subtm M Q -> subtm M (tmLam y Q)
  .

  Global Hint Constructors tm : my_hints.

  Lemma subtm_getRank :
    forall M : tm,
    forall N : tm,
    subtm M N ->
    getRank M <= getRank N.
  Proof with lia.
    intros M N X.
    induction X; simpl...
  Qed.

  Lemma subtm_and_same_rank_implies_same_term :
    forall M : tm,
    forall N : tm,
    subtm M N ->
    getRank M = getRank N ->
    M = N.
  Proof with lia.
    intros M N X.
    destruct X; intros.
    - reflexivity.
    - assert (H0 := subtm_getRank M P1 X).
      simpl in *...
    - assert (H0 := subtm_getRank M P2 X).
      simpl in *...
    - assert (H0 := subtm_getRank M Q X).
      simpl in *...
  Qed.

  Lemma subtm_refl :
    forall M1 : tm,
    subtm M1 M1.
  Proof.
    apply subtmRefl.
  Qed.

  Local Hint Resolve subtm_refl : core.

  Lemma subtm_asym :
    forall M1 : tm,
    forall M2 : tm,
    subtm M1 M2 ->
    subtm M2 M1 ->
    M1 = M2.
  Proof with eauto.
    intros.
    apply subtm_and_same_rank_implies_same_term...
    enough (getRank M1 <= getRank M2 /\ getRank M2 <= getRank M1) by lia.
    split; apply subtm_getRank...
  Qed.

  Local Hint Resolve subtm_asym : core.

  Lemma subtm_trans :
    forall M1 : tm,
    forall M2 : tm,
    forall M3 : tm,
    subtm M1 M2 ->
    subtm M2 M3 ->
    subtm M1 M3.
  Proof with eauto.
    enough (claim1 : forall L : tm, forall N : tm, forall M : tm, subtm N L -> subtm M N -> subtm M L)...
    induction L.
    all: intros; inversion H; subst...
    - constructor 2...
    - constructor 3...
    - constructor 4...
  Qed.

  Local Hint Resolve subtm_trans : core.

  Theorem strong_induction_on_tm (phi : tm -> Prop) :
    (forall M : tm, (forall N : tm, subtm N M -> N <> M -> phi N) -> phi M) ->
    forall M : tm,
    phi M.
  Proof with try now (firstorder; eauto).
    intros XXX.
    enough (claim1 : forall M : tm, forall L : tm, subtm L M -> phi L)...
    induction M.
    all: intros L H; apply XXX; intros N H0 H1; inversion H0; subst...
    all: inversion H; subst...
  Qed.

  Definition occurence_rect (XP : forall z : ivar, forall M : tm, subtm (tmVar z) M -> Type) :
    (forall x : ivar, XP x (tmVar x) (subtmRefl (tmVar x))) ->
    (forall x : ivar, forall P1 : tm, forall P2 : tm, forall X : subtm (tmVar x) P1, XP x P1 X -> XP x (tmApp P1 P2) (subtmAppL (tmVar x) P1 P2 X)) ->
    (forall x : ivar, forall P1 : tm, forall P2 : tm, forall X : subtm (tmVar x) P2, XP x P2 X -> XP x (tmApp P1 P2) (subtmAppR (tmVar x) P1 P2 X)) ->
    (forall x : ivar, forall y : ivar, forall Q : tm, forall X : subtm (tmVar x) Q, XP x Q X -> XP x (tmLam y Q) (subtmLAbs (tmVar x) y Q X)) ->
    (forall x : ivar, forall M : tm, forall X : subtm (tmVar x) M, XP x M X).
  Proof.
    intros XP_refl XP_appl XP_appr XP_labs z.
    assert ( XXX :
      forall N : tm,
      forall M : tm,
      forall X : subtm N M,
      forall H : N = tmVar z,
      XP z M (eq_rect N (fun N0 : tm => subtm N0 M) X (tmVar z) H)
    ).
    { assert ( XP_Refl :
        forall M0 : tm,
        forall H : M0 = tmVar z,
        XP z M0 (eq_rect M0 (fun N1 : tm => subtm N1 M0) (subtmRefl M0) (tmVar z) H)
      ).
      { intros M0.
        apply (case_eq M0 (tmVar z) (fun M1 : tm => fun H0 : M1 = tmVar z => XP z M1 (eq_rect M1 (fun N1 : tm => subtm N1 M1) (subtmRefl M1) (tmVar z) H0))).
        apply (XP_refl z).
      }
      assert ( XP_AppL :
        forall M0 : tm,
        forall P1 : tm,
        forall P2 : tm,
        forall H : M0 = tmVar z,
        forall X' : subtm M0 P1,
        (forall H' : M0 = tmVar z, XP z P1 (eq_rect M0 (fun N1 : tm => subtm N1 P1) X' (tmVar z) H')) ->
        XP z (tmApp P1 P2) (eq_rect M0 (fun N1 : tm => subtm N1 (tmApp P1 P2)) (subtmAppL M0 P1 P2 X') (tmVar z) H)
      ).
      { intros M0 P1 P2.
        apply (case_eq M0 (tmVar z) (fun M1 : tm => fun H0 : M1 = tmVar z => forall X' : subtm M1 P1, (forall H' : M1 = tmVar z, XP z P1 (eq_rect M1 (fun N1 : tm => subtm N1 P1) X' (tmVar z) H')) -> XP z (tmApp P1 P2) (eq_rect M1 (fun N1 : tm => subtm N1 (tmApp P1 P2)) (subtmAppL M1 P1 P2 X') (tmVar z) H0))).
        apply (fun X' : subtm (tmVar z) P1 => fun IHX' : forall H' : tmVar z = tmVar z, XP z P1 (eq_rect (tmVar z) (fun N1 : tm => subtm N1 P1) X' (tmVar z) H') => XP_appl z P1 P2 X' (IHX' eq_refl)).
      }
      assert ( XP_AppR :
        forall M0 : tm,
        forall P1 : tm,
        forall P2 : tm,
        forall H : M0 = tmVar z,
        forall X' : subtm M0 P2,
        (forall H' : M0 = tmVar z, XP z P2 (eq_rect M0 (fun N1 : tm => subtm N1 P2) X' (tmVar z) H')) ->
        XP z (tmApp P1 P2) (eq_rect M0 (fun N1 : tm => subtm N1 (tmApp P1 P2)) (subtmAppR M0 P1 P2 X') (tmVar z) H)
      ).
      { intros M0 P1 P2.
        apply (case_eq M0 (tmVar z) (fun M1 : tm => fun H0 : M1 = tmVar z => forall X' : subtm M1 P2, (forall H' : M1 = tmVar z, XP z P2 (eq_rect M1 (fun N1 : tm => subtm N1 P2) X' (tmVar z) H')) -> XP z (tmApp P1 P2) (eq_rect M1 (fun N1 : tm => subtm N1 (tmApp P1 P2)) (subtmAppR M1 P1 P2 X') (tmVar z) H0))).
        apply (fun X' : subtm (tmVar z) P2 => fun IHX' : forall H' : tmVar z = tmVar z, XP z P2 (eq_rect (tmVar z) (fun N1 : tm => subtm N1 P2) X' (tmVar z) H') => XP_appr z P1 P2 X' (IHX' eq_refl)).
      }
      assert ( XP_LAbs :
        forall M0 : tm,
        forall y : ivar,
        forall Q : tm,
        forall H : M0 = tmVar z,
        forall X' : subtm M0 Q,
        (forall H' : M0 = tmVar z, XP z Q (eq_rect M0 (fun N1 : tm => subtm N1 Q) X' (tmVar z) H')) ->
        XP z (tmLam y Q) (eq_rect M0 (fun N1 : tm => subtm N1 (tmLam y Q)) (subtmLAbs M0 y Q X') (tmVar z) H)
      ).
      { intros M0 y Q.
        apply (case_eq M0 (tmVar z) (fun M1 : tm => fun H0 : M1 = tmVar z => forall X' : subtm M1 Q, (forall H' : M1 = tmVar z, XP z Q (eq_rect M1 (fun N1 : tm => subtm N1 Q) X' (tmVar z) H')) -> XP z (tmLam y Q) (eq_rect M1 (fun N1 : tm => subtm N1 (tmLam y Q)) (subtmLAbs M1 y Q X') (tmVar z) H0))).
        apply (fun X' : subtm (tmVar z) Q => fun IHX' : forall H' : tmVar z = tmVar z, XP z Q (eq_rect (tmVar z) (fun N1 : tm => subtm N1 Q) X' (tmVar z) H') => XP_labs z y Q X' (IHX' eq_refl)).
      }
      apply (
        fix occurence_rect_fix (N : tm) (M : tm) (X : subtm N M) {struct X} : forall H : N = tmVar z, XP z M (eq_rect N (fun N1 : tm => subtm N1 M) X (tmVar z) H) :=
        match X as X0 in subtm N0 M0 return forall H : N0 = tmVar z, XP z M0 (eq_rect N0 (fun N1 : tm => subtm N1 M0) X0 (tmVar z) H) with
        | subtmRefl M0 =>
          fun H : M0 = tmVar z =>
          XP_Refl M0 H 
        | subtmAppL M0 P1 P2 X' =>
          fun H : M0 = tmVar z =>
          XP_AppL M0 P1 P2 H X' (occurence_rect_fix M0 P1 X')
        | subtmAppR M0 P1 P2 X' =>
          fun H : M0 = tmVar z =>
          XP_AppR M0 P1 P2 H X' (occurence_rect_fix M0 P2 X')
        | subtmLAbs M0 y Q X' =>
          fun H : M0 = tmVar z =>
          XP_LAbs M0 y Q H X' (occurence_rect_fix M0 Q X')
        end
      ).
    }
    apply (
      fun M : tm =>
      fun X : subtm (tmVar z) M =>
      XXX (tmVar z) M X eq_refl
    ).
  Defined.

  Fixpoint getFVs (M : tm) : list ivar :=
    match M with
    | tmVar x => [x]
    | tmApp P1 P2 => getFVs P1 ++ getFVs P2
    | tmLam y Q => remove ivar_eq_dec y (getFVs Q)
    end
  .

  Fixpoint isFreeIn (z : ivar) (M : tm) {struct M} : bool :=
    match M with
    | tmVar x => Nat.eqb x z
    | tmApp P1 P2 => isFreeIn z P1 || isFreeIn z P2
    | tmLam y Q => isFreeIn z Q && negb (Nat.eqb z y)
    end
  .

  Lemma getFVs_isFreeIn (M : tm) :
    forall z : ivar,
    In z (getFVs M) <-> isFreeIn z M = true.
  Proof with try now firstorder.
    induction M; simpl; intros z.
    - rewrite Nat.eqb_eq...
    - rewrite orb_true_iff, in_app_iff...
    - rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq.
      split; intros H.
      + apply in_remove in H...
      + apply in_in_remove...
  Qed.

  Definition substitution : Set :=
    ivar -> tm
  .

  Definition nil_subtitution : substitution :=
    tmVar
  .

  Definition cons_substitution : ivar -> tm -> substitution -> substitution :=
    fun x : ivar => fun M : tm => fun sigma : substitution => fun y : ivar => if ivar_eq_dec x y then M else sigma y
  .

  Fixpoint mk_substitution (sigma : list (ivar * tm)) {struct sigma} : substitution :=
    match sigma with
    | [] => nil_subtitution
    | (x, M) :: sigma' => cons_substitution x M (mk_substitution sigma')
    end
  .

  Definition get_max_ivar : tm -> ivar :=
    fun M : tm => fold_right_max_0 (getFVs M)
  .

  Lemma get_max_ivar_lt (M : tm) :
    forall x : ivar,
    get_max_ivar M < x ->
    isFreeIn x M = false.
  Proof with lia.
    intros x.
    enough (get_max_ivar M < x -> ~ In x (getFVs M)) by now rewrite getFVs_isFreeIn, not_true_iff_false in H.
    assert (H1 : In x (getFVs M) -> fold_right_max_0 (getFVs M) >= x) by apply fold_right_max_0_in.
    enough (fold_right_max_0 (getFVs M) >= x -> fold_right_max_0 (getFVs M) < x -> False) by now eauto...
  Qed.

  Definition isFreshIn_substitution : ivar -> substitution -> tm -> bool :=
    fun x : ivar => fun sigma : substitution => fun M : tm => forallb (fun z : ivar => negb (isFreeIn x (sigma z))) (getFVs M)
  .

  Definition chi : substitution -> tm -> ivar :=
    fun sigma : substitution => fun M : tm => S (fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)))
  .

  Theorem main_property_of_chi :
    forall M : tm,
    forall sigma : substitution,
    isFreshIn_substitution (chi sigma M) sigma M = true.
  Proof with try now firstorder.
    assert ( claim1 :
      forall sigma : substitution,
      forall M : tm,
      forall x : ivar,
      isFreeIn x M = true ->
      isFreeIn (chi sigma M) (sigma x) = false
    ).
    { intros sigma M x H.
      enough (get_max_ivar (sigma x) < chi sigma M) by now apply get_max_ivar_lt.
      unfold chi, fold_right_max_0.
      enough (fold_right max 0 (map (fun z : ivar => get_max_ivar (sigma z)) (getFVs M)) >= get_max_ivar (sigma x)) by lia.
      rewrite <- getFVs_isFreeIn in H.
      apply fold_right_max_0_in, in_map_iff...
    }
    unfold isFreshIn_substitution.
    intros M sigma.
    apply forallb_true_iff.
    intros x H.
    apply negb_true_iff, claim1, getFVs_isFreeIn...
  Qed.

  Lemma chi_nil : 
    forall M : tm,
    isFreeIn (chi nil_subtitution M) M = false.
  Proof with try now firstorder.
    intros M.
    assert (H : isFreshIn_substitution (chi nil_subtitution M) nil_subtitution M = true) by apply main_property_of_chi.
    unfold isFreshIn_substitution in H.
    rewrite forallb_true_iff in H.
    simpl in H.
    apply not_true_iff_false.
    intros H0.
    assert (H1 : negb (chi nil_subtitution M =? chi nil_subtitution M) = true) by now apply H, getFVs_isFreeIn.
    rewrite negb_true_iff, Nat.eqb_neq in H1...
  Qed.

  Fixpoint run_substitution_on_tm (sigma : substitution) (M : tm) {struct M} : tm :=
    match M with
    | tmVar x => sigma x
    | tmApp P1 P2 => tmApp (run_substitution_on_tm sigma P1) (run_substitution_on_tm sigma P2)
    | tmLam y Q =>
      let z : ivar := chi sigma M in
      tmLam z (run_substitution_on_tm (cons_substitution y (tmVar z) sigma) Q)
    end
  .

  Theorem main_property_isFreshIn_substitution :
    forall M : tm,
    forall z : ivar,
    forall sigma : substitution,
    isFreshIn_substitution z sigma M = true <-> isFreeIn z (run_substitution_on_tm sigma M) = false.
  Proof with try now firstorder.
    induction M; simpl.
    - intros z sigma.
      unfold isFreshIn_substitution.
      simpl.
      rewrite andb_true_iff, negb_true_iff...
    - intros z sigma.
      rewrite orb_false_iff.
      unfold isFreshIn_substitution.
      simpl.
      rewrite forallb_app, andb_true_iff...
    - intros z sigma.
      rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq.
      unfold isFreshIn_substitution.
      simpl.
      rewrite forallb_true_iff.
      split; intros H.
      + destruct (ivar_eq_dec z (chi sigma (tmLam y M)))...
        left.
        apply IHM.
        unfold isFreshIn_substitution.
        rewrite forallb_true_iff.
        intros x H0.
        unfold cons_substitution.
        destruct (ivar_eq_dec y x).
        * unfold isFreeIn.
          apply negb_true_iff, Nat.eqb_neq...
        * apply H, in_in_remove...
      + intros x H0.
        apply in_remove in H0.
        destruct H0.
        destruct H.
        * assert (H2 : isFreshIn_substitution z (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) M = true) by now apply IHM.
          unfold isFreshIn_substitution in H2.
          rewrite forallb_true_iff in H2.
          assert (H3 := H2 x H0).
          unfold cons_substitution in H3.
          destruct (ivar_eq_dec y x)...
        * assert (H2 : isFreshIn_substitution z sigma (tmLam y M) = true).
          { rewrite H.
            apply main_property_of_chi...
          }
          unfold isFreshIn_substitution in H2.
          rewrite forallb_true_iff in H2.
          apply H2.
          rewrite getFVs_isFreeIn.
          simpl.
          rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq, <- getFVs_isFreeIn...
  Qed.

  Definition equiv_substitution_wrt : substitution -> substitution -> tm -> Prop :=
    fun sigma1 : substitution => fun sigma2 : substitution => fun M : tm => forall x : ivar, isFreeIn x M = true -> sigma1 x = sigma2 x
  .

  Lemma property1_of_equiv_substitution_wrt :
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    (forall x : ivar, sigma1 x = sigma2 x) ->
    forall M : tm,
    equiv_substitution_wrt sigma1 sigma2 M.
  Proof with try now firstorder.
    unfold equiv_substitution_wrt...
  Qed.

  Lemma chi_equiv_substitution_wrt :
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    forall M : tm,
    equiv_substitution_wrt sigma1 sigma2 M ->
    chi sigma1 M = chi sigma2 M.
  Proof with reflexivity.
    unfold chi.
    intros sigma1 sigma2 M H.
    enough (H0 : (map (fun x : ivar => get_max_ivar (sigma1 x)) (getFVs M)) = (map (fun x : ivar => get_max_ivar (sigma2 x)) (getFVs M))) by congruence.
    apply map_ext_in.
    intros x H0.
    rewrite (H x (proj1 (getFVs_isFreeIn M x) H0))...
  Qed.

  Theorem main_property_of_equiv_substitution_wrt :
    forall M : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    equiv_substitution_wrt sigma1 sigma2 M ->
    run_substitution_on_tm sigma1 M = run_substitution_on_tm sigma2 M.
  Proof with try now firstorder.
    induction M.
    - intros sigma1 sigma2 H.
      apply H.
      simpl.
      rewrite Nat.eqb_eq...
    - intros sigma1 sigma2 H.
      assert (H1 : equiv_substitution_wrt sigma1 sigma2 M1).
      { intros x H0.
        apply H.
        simpl.
        rewrite orb_true_iff...
      }
      assert (H2 : equiv_substitution_wrt sigma1 sigma2 M2).
      { intros x H0.
        apply H.
        simpl.
        rewrite orb_true_iff...
      }
      simpl.
      rewrite (IHM1 sigma1 sigma2 H1), (IHM2 sigma1 sigma2 H2)...
    - intros sigma1 sigma2 H.
      simpl.
      assert (H0 : equiv_substitution_wrt (cons_substitution y (tmVar (chi sigma1 (tmLam y M))) sigma1) (cons_substitution y (tmVar (chi sigma2 (tmLam y M))) sigma2) M).
      { intros x H0.
        unfold cons_substitution.
        destruct (ivar_eq_dec y x).
        - rewrite (chi_equiv_substitution_wrt sigma1 sigma2 (tmLam y M) H)...
        - apply H.
          simpl.
          rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
      }
      assert (H1 : chi sigma1 (tmLam y M) = chi sigma2 (tmLam y M)) by now apply chi_equiv_substitution_wrt.
      rewrite (IHM (cons_substitution y (tmVar (chi sigma1 (tmLam y M))) sigma1) (cons_substitution y (tmVar (chi sigma2 (tmLam y M))) sigma2) H0), H1...
  Qed.

  Lemma trivial_substitution :
    forall x : ivar,
    forall M : tm,
    run_substitution_on_tm (cons_substitution x (tmVar x) nil_subtitution) M = run_substitution_on_tm nil_subtitution M.
  Proof with try now firstorder.
    unfold cons_substitution.
    intros x M.
    apply main_property_of_equiv_substitution_wrt.
    intros y H.
    destruct (ivar_eq_dec x y)...
  Qed.

  Definition compose_substitution : substitution -> substitution -> substitution :=
    fun sigma1 : substitution => fun sigma2 : substitution => fun x : ivar => run_substitution_on_tm sigma1 (sigma2 x)
  .

  Lemma distri_compose_cons :
    forall M : tm,
    forall N : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    forall x : ivar,
    forall y : ivar,
    isFreshIn_substitution y sigma1 (tmLam x M) = true ->
    forall z : ivar,
    isFreeIn z M = true ->
    cons_substitution x N (compose_substitution sigma2 sigma1) z = compose_substitution (cons_substitution y N sigma2) (cons_substitution x (tmVar y) sigma1) z.
  Proof with try now firstorder.
    intros M N sigma1 sigma2 x y H z H0.
    unfold cons_substitution, compose_substitution.
    destruct (ivar_eq_dec x z).
    - simpl.
      destruct (ivar_eq_dec y y)...
    - unfold isFreshIn_substitution in H.
      rewrite forallb_true_iff in H.
      assert (H1 : isFreeIn y (sigma1 z) = false).
      { apply negb_true_iff, H, getFVs_isFreeIn.
        simpl.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
      }
      assert ( claim1 :
        forall u : ivar,
        isFreeIn u (sigma1 z) = true ->
        cons_substitution y N sigma2 u = sigma2 u
      ).
      { unfold cons_substitution.
        intros u H2.
        destruct (ivar_eq_dec y u)...
        subst.
        rewrite H1 in H2...
      }
      apply main_property_of_equiv_substitution_wrt...
  Qed.

  Corollary distri_compose_cons_for_chi :
    forall M : tm,
    forall N : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    forall x : ivar,
    let y : ivar := chi sigma1 (tmLam x M) in
    forall z : ivar,
    isFreeIn z M = true ->
    cons_substitution x N (compose_substitution sigma2 sigma1) z = compose_substitution (cons_substitution y N sigma2) (cons_substitution x (tmVar y) sigma1) z.
  Proof with eauto using distri_compose_cons, main_property_of_chi.
    intros M N sigma1 sigma2 x y z H...
  Qed.

  Definition FreeIn_wrt : ivar -> substitution -> tm -> Prop :=
    fun x : ivar => fun sigma : substitution => fun M : tm => exists y : ivar, isFreeIn y M = true /\ isFreeIn x (sigma y) = true
  .

  Theorem isFreeIn_wrt_true_iff (M : tm) :
    forall z : ivar,
    forall sigma : substitution,
    isFreeIn z (run_substitution_on_tm sigma M) = true <-> FreeIn_wrt z sigma M.
  Proof with try now firstorder.
    unfold FreeIn_wrt.
    induction M; simpl.
    - intros z sigma.
      split; intros H.
      + exists x.
        rewrite Nat.eqb_eq...
      + destruct H as [y H].
        rewrite Nat.eqb_eq in H.
        destruct H.
        subst...
    - intros z sigma.
      rewrite orb_true_iff.
      split; intros H.
      + destruct H; [enough (H0 : exists y : ivar, isFreeIn y M1 = true /\ isFreeIn z (sigma y) = true) | enough (H0 : exists y : ivar, isFreeIn y M2 = true /\ isFreeIn z (sigma y) = true)]...
        all: destruct H0 as [y]; exists y; rewrite orb_true_iff...
      + destruct H as [y].
        rewrite orb_true_iff in H...
    - intros x sigma.
      rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq.
      split; intros H.
      + destruct H.
        assert (H1 := proj1 (IHM x (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma)) H).
        destruct H1 as [w].
        destruct H1.
        set (z := chi sigma (tmLam y M)).
        fold z in H, H0, H2.
        destruct (ivar_eq_dec y w).
        * subst.
          unfold cons_substitution in H2.
          destruct (ivar_eq_dec w w)...
          unfold isFreeIn in H2.
          rewrite Nat.eqb_eq in H2...
        * exists w.
          rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq.
          unfold cons_substitution in H2.
          destruct (ivar_eq_dec y w)...
      + rename y into z.
        destruct H as [y].
        destruct H.
        set (w := chi sigma (tmLam z M)).
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H.
        destruct (ivar_eq_dec w x).
        * subst.
          assert (isFreshIn_substitution w sigma (tmLam z M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_substitution in H1.
          rewrite forallb_true_iff in H1.
          enough (H2 : isFreeIn w (sigma y) = false) by now rewrite H0 in H2.
          apply negb_true_iff, H1, getFVs_isFreeIn.
          simpl.
          rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
        * split...
          apply IHM.
          exists y.
          split...
          unfold cons_substitution.
          destruct (ivar_eq_dec z y)...
  Qed.

  Lemma chi_ext :
    forall sigma : substitution,
    forall sigma' : substitution,
    forall M : tm,
    forall M' : tm,
    (forall z : ivar, FreeIn_wrt z sigma M <-> FreeIn_wrt z sigma' M') ->
    chi sigma M = chi sigma' M'.
  Proof with try now firstorder.
    unfold chi, FreeIn_wrt.
    intros.
    enough (fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)) = fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma' x)) (getFVs M'))) by lia.
    assert ( claim1 :
      forall z : ivar,
      In z (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) <-> In z (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))
    ).
    { intros z.
      repeat (rewrite in_flat_map).
      split; intros.
      all: destruct H0 as [x]; rewrite getFVs_isFreeIn in H0.
      1: assert (H1 : exists y : ivar, isFreeIn y M' = true /\ isFreeIn z (sigma' y) = true).
      3: assert (H1 : exists y : ivar, isFreeIn y M = true /\ isFreeIn z (sigma y) = true).
      1, 3: apply H; exists x...
      1, 2: rewrite getFVs_isFreeIn in H0...
      all: destruct H1 as [y]; exists y; repeat (rewrite getFVs_isFreeIn)...
    }
    assert (H0 : fold_right_max_0 (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) = fold_right_max_0 (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))) by now apply fold_right_max_0_ext.
    unfold get_max_ivar.
    enough (H1 : forall xs : list ivar, forall f : ivar -> list ivar, fold_right_max_0 (map (fun x : ivar => fold_right_max_0 (f x)) xs) = fold_right_max_0 (flat_map f xs)) by now repeat (rewrite H1).
    induction xs; simpl; intros f...
    rewrite fold_right_max_0_app...
  Qed.

  Theorem main_property_of_compose_substitution :
    forall M : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    run_substitution_on_tm sigma2 (run_substitution_on_tm sigma1 M) = run_substitution_on_tm (compose_substitution sigma2 sigma1) M.
  Proof with try now firstorder.
    induction M; simpl.
    - intros sigma1 sigma2...
    - intros sigma1 sigma2.
      rewrite IHM1, IHM2...
    - intros sigma1 sigma2.
      enough (lemma : chi sigma2 (run_substitution_on_tm sigma1 (tmLam y M)) = chi (compose_substitution sigma2 sigma1) (tmLam y M)).
      { set (x := chi sigma1 (tmLam y M)).
        set (x' := chi sigma2 (tmLam x (run_substitution_on_tm (cons_substitution y (tmVar x) sigma1) M))).
        set (z := chi (compose_substitution sigma2 sigma1) (tmLam y M)).
        assert (H := IHM (cons_substitution y (tmVar x) sigma1) (cons_substitution x (tmVar x') sigma2)).
        rewrite H.
        assert (H0 : run_substitution_on_tm (compose_substitution (cons_substitution x (tmVar x') sigma2) (cons_substitution y (tmVar x) sigma1)) M = run_substitution_on_tm (cons_substitution y (tmVar x') (compose_substitution sigma2 sigma1)) M).
        { apply main_property_of_equiv_substitution_wrt.
          intros u H0.
          assert (H1 := distri_compose_cons_for_chi M (tmVar x') sigma1 sigma2 y).
          simpl in H1.
          rewrite (H1 u H0)...
        }
        rewrite H0.
        replace x' with z...
      }
      rename y into x.
      set (y := chi sigma1 (tmLam x M)).
      assert ( claim1 :
        forall y' : ivar,
        (exists x' : ivar, isFreeIn x' (tmLam y (run_substitution_on_tm (cons_substitution x (tmVar y) sigma1) M)) = true /\ isFreeIn y' (sigma2 x') = true) ->
        (exists u : ivar, isFreeIn u (tmLam x M) = true /\ isFreeIn y' (compose_substitution sigma2 sigma1 u) = true)
      ).
      { intros y' H.
        destruct H as [x'].
        destruct H.
        simpl in H.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H.
        destruct H.
        assert (H2 := proj1 (isFreeIn_wrt_true_iff M x' (cons_substitution x (tmVar y) sigma1)) H).
        destruct H2 as [u].
        destruct H2.
        unfold cons_substitution in H3.
        destruct (ivar_eq_dec x u).
        - unfold isFreeIn in H3.
          rewrite Nat.eqb_eq in H3...
        - exists u.
          split.
          + simpl.
            rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
          + apply (proj2 (isFreeIn_wrt_true_iff (sigma1 u) y' sigma2))...
      }
      assert ( claim2 :
        forall y' : ivar,
        (exists x' : ivar, isFreeIn x' (tmLam x M) = true /\ isFreeIn y' (compose_substitution sigma2 sigma1 x') = true) ->
        (exists u : ivar, isFreeIn u (tmLam y (run_substitution_on_tm (cons_substitution x (tmVar y) sigma1) M)) = true /\ isFreeIn y' (sigma2 u) = true)
      ).
      { intros y' H.
        destruct H as [x'].
        destruct H.
        simpl in H.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H.
        destruct H.
        assert (H2 := proj1 (isFreeIn_wrt_true_iff (sigma1 x') y' sigma2) H0).
        destruct H2 as [u].
        destruct H2.
        assert (H4 : isFreeIn u (run_substitution_on_tm (cons_substitution x (tmVar y) sigma1) M) = true).
        { apply isFreeIn_wrt_true_iff.
          exists x'.
          split...
          unfold cons_substitution.
          destruct (ivar_eq_dec x x')...
        }
        exists u.
        split...
        simpl.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq.
        split...
        intros H5.
        subst.
        enough (H6 : isFreeIn y (sigma1 x') = false) by now rewrite H2 in H6.
        assert (H5 := main_property_of_chi (tmLam x M) sigma1).
        unfold isFreshIn_substitution in H5.
        rewrite forallb_true_iff in H5.
        apply negb_true_iff, H5.
        rewrite getFVs_isFreeIn.
        simpl.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
      }
      apply chi_ext...
  Qed.

  Corollary compose_one :
    forall M : tm,
    forall N : tm,
    forall sigma : substitution,
    forall x : ivar,
    run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) sigma) M = run_substitution_on_tm sigma (run_substitution_on_tm (cons_substitution x N nil_subtitution) M).
  Proof with try now firstorder.
    intros M N sigma x.
    replace (run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) sigma) M) with (run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) (compose_substitution sigma nil_subtitution)) M).
    replace (run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) (compose_substitution sigma nil_subtitution)) M) with (run_substitution_on_tm (compose_substitution sigma (cons_substitution x N nil_subtitution)) M).
    rewrite main_property_of_compose_substitution...
    all: apply main_property_of_equiv_substitution_wrt; apply property1_of_equiv_substitution_wrt; unfold compose_substitution, cons_substitution, nil_subtitution; intros z; destruct (ivar_eq_dec x z)...
  Qed.

  Theorem main_property_of_cons_substitution :
    forall x : ivar,
    forall z : ivar,
    forall M : tm,
    forall N : tm,
    forall sigma : substitution,
    isFreeIn z (tmLam x M) = false ->
    run_substitution_on_tm (cons_substitution x N sigma) M = run_substitution_on_tm (cons_substitution z N sigma) (run_substitution_on_tm (cons_substitution x (tmVar z) nil_subtitution) M).
  Proof with try now firstorder.
    intros.
    rewrite (main_property_of_compose_substitution M (cons_substitution x (tmVar z) nil_subtitution) (cons_substitution z N sigma)).
    apply main_property_of_equiv_substitution_wrt.
    intros w H0.
    unfold cons_substitution, nil_subtitution, compose_substitution.
    destruct (ivar_eq_dec x w); simpl.
    - destruct (ivar_eq_dec z z)...
    - destruct (ivar_eq_dec z w)...
      simpl in H.
      subst.
      rewrite H0 in H.
      simpl in H.
      rewrite negb_false_iff, Nat.eqb_eq in H.
      contradiction n...
  Qed.

  Class isPreLambdaStructure (D : Type) : Type :=
    { runApp : D -> (D -> D)
    ; runLam : (D -> D) -> D
    }
  .

  Lemma runApp_ext {D : Type} `{D_isPreLambdaStructure : isPreLambdaStructure D} :
    forall v1 : D,
    forall v2 : D,
    forall v1' : D,
    forall v2' : D,
    v1 = v1' ->
    v2 = v2' ->
    runApp v1 v2 = runApp v1' v2'.
  Proof.
    congruence.
  Qed.

  Global Hint Resolve runApp_ext : my_hints.

  Lemma runLam_ext {D : Type} `{D_isPreLambdaStructure : isPreLambdaStructure D} :
    forall vv : D -> D,
    forall vv' : D -> D,
    (forall v0 : D, vv v0 = vv' v0) ->
    runLam vv = runLam vv'.
  Proof.
    intros vv vv' H.
    apply functional_extensionality in H.
    congruence.
  Qed.

  Global Hint Resolve runLam_ext : my_hints.

  Definition eval_tm {D : Type} `{D_is_model : isPreLambdaStructure D} : (ivar -> D) -> tm -> D :=
    fix eval_tm_fix (E : ivar -> D) (M : tm) {struct M} : D :=
    match M with
    | tmVar x => E x
    | tmApp P1 P2 => runApp (eval_tm_fix E P1) (eval_tm_fix E P2)
    | tmLam y Q => runLam (fun v : D => eval_tm_fix (fun z : ivar => if ivar_eq_dec y z then v else E z) Q)
    end
  .

  Lemma eval_tm_ext {D : Type} `{D_is_model : isPreLambdaStructure D} :
    forall M : tm,
    forall E1 : ivar -> D,
    forall E2 : ivar -> D,
    (forall z : ivar, isFreeIn z M = true -> E1 z = E2 z) ->
    eval_tm E1 M = eval_tm E2 M.
  Proof with try now eauto with *.
    induction M; simpl.
    - intros E1 E2 H.
      apply H.
      rewrite Nat.eqb_eq...
    - intros E1 E2 H.
      rewrite (IHM1 E1 E2), (IHM2 E1 E2)...
    - intros E1 E2 H.
      enough (XXX : (fun v : D => eval_tm (fun z : ivar => if ivar_eq_dec y z then v else E1 z) M) = (fun v : D => eval_tm (fun z : ivar => if ivar_eq_dec y z then v else E2 z) M)) by congruence.
      apply functional_extensionality.
      intros v.
      apply (IHM (fun z : ivar => if ivar_eq_dec y z then v else E1 z) (fun z : ivar => if ivar_eq_dec y z then v else E2 z))...
      intros z H0.
      destruct (ivar_eq_dec y z)...
      apply H.
      rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
  Qed.

  Theorem run_substitution_on_tm_preserves_eval_tm {D : Type} `{D_is_model : isPreLambdaStructure D} :
    forall M : tm,
    forall sigma : substitution,
    forall E : ivar -> D,
    eval_tm (fun z : ivar => eval_tm E (sigma z)) M = eval_tm E (run_substitution_on_tm sigma M).
  Proof with try now eauto with *.
    induction M.
    - intros sigma E...
    - intros sigma E.
      simpl...
    - intros sigma E.
      enough (claim1 : forall v : D, eval_tm (fun z : ivar => if ivar_eq_dec y z then v else eval_tm E (sigma z)) M = eval_tm (fun z : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z then v else E z) (run_substitution_on_tm (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) M)) by now apply runLam_ext.
      intros v.
      assert (H := IHM (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) (fun z : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z then v else E z)).
      symmetry in H.
      symmetry.
      transitivity (eval_tm (fun z : ivar => eval_tm (fun z0 : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z0 then v else E z0) (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma z)) M)...
      apply eval_tm_ext.
      intros z H0.
      unfold cons_substitution.
      destruct (ivar_eq_dec y z).
      + unfold eval_tm.
        destruct (ivar_eq_dec (chi sigma (tmLam y M)) (chi sigma (tmLam y M)))...
      + apply eval_tm_ext.
        intros z' H1.
        destruct (ivar_eq_dec (chi sigma (tmLam y M)) z')...
        subst.
        assert (H2 : isFreshIn_substitution (chi sigma (tmLam y M)) sigma (tmLam y M) = true) by now apply main_property_of_chi.
        unfold isFreshIn_substitution in H2.
        rewrite forallb_true_iff in H2.
        enough (H3 : isFreeIn (chi sigma (tmLam y M)) (sigma z) = false) by now rewrite H3 in H1.
        apply negb_true_iff, H2, getFVs_isFreeIn.
        simpl.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
  Qed.

  Class isLambdaStructure (Dom : Type) : Type :=
    { requiresPreLambdaStructure :> isPreLambdaStructure Dom
    ; respect_beta : forall vv : Dom -> Dom, forall v0 : Dom, runApp (runLam vv) v0 = vv v0
    ; respect_eta : forall v : Dom, runLam (runApp v) = v
    }
  .

  Global Hint Resolve respect_beta : semantics_of_ulc.

  Global Hint Resolve respect_eta : semantics_of_ulc.

End UntypedLamdbdaCalculus.
