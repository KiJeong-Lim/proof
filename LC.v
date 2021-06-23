Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

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
  assert (H : forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
  { intros x y; constructor.
    - intros H; induction H.
      + exists 0...
      + destruct IHle as [z H0]; exists (S z)...
    - intros H; destruct H as [z H]...
  }
  intros a b q r H1 H2.
  assert (H0 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
  assert (H3 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
  assert (H4 : ~ q > a / b).
  { intros H4.
    enough (H5 : exists z : nat, q = S (a / b + z)).
    { destruct H5 as [z H5].
      enough (b * q + r >= b * S (a / b) + r)...
    }
    apply (H q (a / b))...
  }
  assert (H5 : ~ q < a / b).
  { intros H5.
    enough (H6 : exists z : nat, a / b = S (q + z)).
    { destruct H6 as [z H6].
      enough (b * q + a mod b >= b * S (a / b) + a mod b)...
    }
    apply (H (a / b) q)...
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
  let m := first_nat p n in
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

Theorem sum_from_0_to_is :
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
    firstorder.
  - intros n.
    destruct (Compare_dec.le_lt_dec a (fold_right Init.Nat.max 0 ns)); split...
    + intros H.
      assert (H0 : fold_right Init.Nat.max 0 ns > n)...
      destruct (proj1 (IHns n) H0) as [i].
      firstorder.
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

End AuxiliaryPalatina.

Module UntypedLamdbdaCalculus.

Import ListNotations.

Import AuxiliaryPalatina.

Section SyntaxOfLambdaCalculus.

Definition ivar : Set :=
  nat
.

Definition ivar_eq_dec : forall x : ivar, forall y : ivar, {x = y} + {x <> y} :=
  Nat.eq_dec
.

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

Proposition property1_of_equiv_substitution_wrt :
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
Proof with eauto using main_property_of_chi.
  intros M N sigma1 sigma2 x y z H0.
  apply (distri_compose_cons M N sigma1 sigma2 x y)...
Qed.

Definition isFreeIn_wrt : ivar -> substitution -> tm -> Prop :=
  fun x : ivar => fun sigma : substitution => fun M : tm => exists y : ivar, isFreeIn y M = true /\ isFreeIn x (sigma y) = true
.

Theorem isFreeIn_wrt_true_iff (M : tm) :
  forall z : ivar,
  forall sigma : substitution,
  isFreeIn z (run_substitution_on_tm sigma M) = true <-> isFreeIn_wrt z sigma M.
Proof with try now firstorder.
  unfold isFreeIn_wrt.
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
  (forall z : ivar, isFreeIn_wrt z sigma M <-> isFreeIn_wrt z sigma' M') ->
  chi sigma M = chi sigma' M'.
Proof with try now firstorder.
  unfold chi, isFreeIn_wrt.
  intros.
  enough (fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)) = fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma' x)) (getFVs M'))) by lia.
  assert ( claim1 :
    forall z : ivar,
    In z (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) <-> In z (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))
  ).
  { intros z.
    repeat (rewrite in_flat_map).
    split; intros.
    - destruct H0 as [x].
      rewrite getFVs_isFreeIn in H0.
      assert (H1 : exists y : ivar, isFreeIn y M' = true /\ isFreeIn z (sigma' y) = true).
      { apply H.
        exists x...
        rewrite getFVs_isFreeIn in H0...
      }
      destruct H1 as [y].
      exists y.
      repeat (rewrite getFVs_isFreeIn)...
    - destruct H0 as [x].
      rewrite getFVs_isFreeIn in H0.
      assert (H1 : exists y : ivar, isFreeIn y M = true /\ isFreeIn z (sigma y) = true).
      { apply H.
        exists x...
        rewrite getFVs_isFreeIn in H0...
      }
      destruct H1 as [y].
      exists y.
      repeat (rewrite getFVs_isFreeIn)...
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

End SyntaxOfLambdaCalculus.

Section SemanticsOfLambdaCalculus.

Class isLambdaModel (Dom : Set) : Type :=
  { runApp : Dom -> Dom -> Dom
  ; runLam : (Dom -> Dom) -> Dom
  ; runLam_ext : forall vv1 : Dom -> Dom, forall vv2 : Dom -> Dom, (forall v : Dom, vv1 v = vv2 v) -> runLam vv1 = runLam vv2
  }
.

Variable D : Set.

Fixpoint eval_tm `{D_is_model : isLambdaModel D} (E : ivar -> D) (M : tm) {struct M} : D :=
  match M with
  | tmVar x => E x
  | tmApp P1 P2 => runApp (eval_tm E P1) (eval_tm E P2)
  | tmLam y Q => runLam (fun v : D => eval_tm (fun z : ivar => if ivar_eq_dec y z then v else E z) Q)
  end
.

Lemma eval_tm_ext `{D_is_model : isLambdaModel D} :
  forall M : tm,
  forall E1 : ivar -> D,
  forall E2 : ivar -> D,
  (forall z : ivar, isFreeIn z M = true -> E1 z = E2 z) ->
  eval_tm E1 M = eval_tm E2 M.
Proof with try now firstorder.
  induction M; simpl.
  - intros E1 E2 H.
    apply H.
    rewrite Nat.eqb_eq...
  - intros E1 E2 H.
    rewrite (IHM1 E1 E2), (IHM2 E1 E2)...
    all: intros z H0; apply H; rewrite orb_true_iff...
  - intros E1 E2 H.
    apply runLam_ext.
    intros v.
    rewrite (IHM (fun z : ivar => if ivar_eq_dec y z then v else E1 z) (fun z : ivar => if ivar_eq_dec y z then v else E2 z))...
    intros z H0.
    destruct (ivar_eq_dec y z)...
    apply H.
    rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
Qed.

Theorem run_substitution_on_tm_preserves_eval_tm `{D_is_model : isLambdaModel D} :
  forall M : tm,
  forall sigma : substitution,
  forall E : ivar -> D,
  eval_tm (fun z : ivar => eval_tm E (sigma z)) M = eval_tm E (run_substitution_on_tm sigma M).
Proof with try now firstorder.
  induction M.
  - intros sigma E...
  - intros sigma E.
    simpl.
    rewrite IHM1, IHM2...
  - intros sigma E.
    enough (claim1 : forall v : D, eval_tm (fun z : ivar => if ivar_eq_dec y z then v else eval_tm E (sigma z)) M = eval_tm (fun z : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z then v else E z) (run_substitution_on_tm (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) M)) by now apply runLam_ext.
    intros v.
    rewrite <- IHM.
    apply eval_tm_ext.
    intros z H.
    unfold cons_substitution.
    destruct (ivar_eq_dec y z).
    + unfold eval_tm.
      destruct (ivar_eq_dec (chi sigma (tmLam y M)) (chi sigma (tmLam y M)))...
    + apply eval_tm_ext.
      intros z' H0.
      destruct (ivar_eq_dec (chi sigma (tmLam y M)) z')...
      subst.
      assert (H1 : isFreshIn_substitution (chi sigma (tmLam y M)) sigma (tmLam y M) = true) by now apply main_property_of_chi.
      unfold isFreshIn_substitution in H1.
      rewrite forallb_true_iff in H1.
      enough (H2 : isFreeIn (chi sigma (tmLam y M)) (sigma z) = false) by now rewrite H2 in H0.
      apply negb_true_iff, H1, getFVs_isFreeIn.
      simpl.
      rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq...
Qed.

End SemanticsOfLambdaCalculus.

End UntypedLamdbdaCalculus.
