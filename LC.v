From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.

Module AuxiliaryPalatina.

Import ListNotations.

Lemma div_mod_uniqueness :
  forall a : nat,
  forall b : nat,
  forall q : nat,
  forall r : nat,
  a = b * q + r ->
  r < b ->
  a / b = q /\ a mod b = r.
Proof with lia.
  assert (forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
  { intros x y; constructor.
    - intros H; induction H.
      + exists 0...
      + destruct IHle as [z H0]; exists (S z)...
    - intros H; destruct H as [z H]...
  }
  intros a b q r H1 H2.
  assert (H0 : a = b * (a / b) + (a mod b)). { apply (Nat.div_mod a b)... }
  assert (H3 : 0 <= a mod b < b). { apply (Nat.mod_bound_pos a b)... }
  assert (H4 : ~ q > a / b).
  { intros H4.
    assert (H5 : exists z : nat, q = S (a / b + z)). { apply (H q (a / b))... }
    destruct H5 as [z H5].
    cut (b * q + r >= b * S (a / b) + r)...
  }
  assert (H5 : ~ q < a / b).
  { intros H5.
    assert (H6 : exists z : nat, a / b = S (q + z)). { apply (H (a / b) q)... }
    destruct H6 as [z H6].
    cut (b * q + a mod b >= b * S (a / b) + a mod b)...
  }
  cut (q = a / b)...
Qed.

Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => if p (first_nat p n') then first_nat p n' else n
  end
.

Theorem well_ordering_principle : 
  forall p : nat -> bool,
  forall n : nat,
  p n = true ->
  let m := first_nat p n in
  p m = true /\ (forall i : nat, p i = true -> i >= m).
Proof with eauto. (* improved by Clare Jang *)
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
    + rewrite <- IHle.
      rewrite H1...
  - induction x...
    simpl.
    destruct (p (first_nat p x)) eqn: H0...
Qed.

Fixpoint sum_from_0_to (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_from_0_to n'
  end
.

Theorem sum_from_0_to_is :
  forall n : nat,
  2 * sum_from_0_to n = n * (S n).
Proof with lia.
  induction n; simpl in *...
Qed.

Fixpoint cantor_pairing (n : nat) : nat * nat :=
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
  cut (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y))...
  induction z.
  - intros y x H.
    assert (H0 : x = 0)...
    assert (H1 : y = 0)...
    subst...
  - induction y.
    + intros x H.
      assert (H0 : x = S z)... subst. simpl.
      destruct (cantor_pairing (z + sum_from_0_to z + 0)) eqn: H0.
      assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
      rewrite Nat.add_0_r in H0. rewrite Nat.add_comm in H0. rewrite H0 in H1.
      inversion H1; subst...
    + intros x H.
      assert (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)). { apply (IHy (S x))... }
      assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y). { simpl... }
      simpl. rewrite H1. rewrite <- H0...
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
    inversion H. subst...
  - intros x y H.
    destruct (cantor_pairing n) as [x' y'] eqn: H0.
    destruct x'; (inversion H; subst).
    + repeat (rewrite Nat.add_0_r).
      simpl.
      rewrite (IHn 0 y' eq_refl).
      rewrite Nat.add_0_l...
    + rewrite (IHn (S x) y' eq_refl).
      assert (H1 : forall x' : nat, S x' + y' = x' + S y')...
      repeat (rewrite H1)...
Qed.

Theorem cantor_pairing_is :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
Proof.
  intros n x y; split; [apply (cantor_pairing_is_injective n x y) | intros; subst; eauto using (cantor_pairing_is_surjective x y)].
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

Definition FinSet_0 {P : FinSet 0 -> Type} : forall i : FinSet 0, P i :=
  fun i : FinSet 0 =>
  match i as i0 in FinSet Sn return Sn = 0 -> P i with
  | FZ n => S_0 n
  | FS n i' => S_0 n
  end eq_refl
.

Definition FinSet_S {n : nat} {P : FinSet (S n) -> Type} : P (FZ n) -> (forall i' : FinSet n, P (FS n i')) -> forall i : FinSet (S n), P i :=
  fun PZ : P (FZ n) =>
  fun PS : forall i' : FinSet n, P (FS n i') =>
  fun i : FinSet (S n) =>
  match i as i0 in FinSet n0 return (match n0 as n1 return FinSet n1 -> Type with 0 => FinSet_0 | S n0' => fun i1 : FinSet (S n0') => forall P : FinSet (S n0') -> Type, P (FZ n0') -> (forall i' : FinSet n0', P (FS n0' i')) -> P i1 end) i0 with
  | FZ n0 => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PZ0
  | FS n0 i' => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PS0 i'
  end P PZ PS
.

End AuxiliaryPalatina.
