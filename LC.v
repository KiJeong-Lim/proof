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

Fixpoint first_nat (p : nat -> bool) (n : nat) {struct n} : nat :=
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
      simpl. rewrite H1, <- H0...
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
  intros n x y; split...
  intros H; subst...
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

Lemma forallb_true_iff {A : Type} {p : A -> bool} (xs : list A) :
  forallb p xs = true <-> forall x : A, In x xs -> p x = true.
Proof.
  induction xs; simpl.
  - firstorder.
  - rewrite andb_true_iff.
    firstorder.
    now rewrite H2 in H1.
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
  induction ns1 as [|n1 ns1]; simpl... 
  intros n.
  rewrite IHns1...
Qed.

End AuxiliaryPalatina.

Module UntypedLamdbdaCalculus.

Import ListNotations.

Import AuxiliaryPalatina.

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
Proof with firstorder.
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
  fun x : ivar =>
  fun M : tm =>
  fun sigma : substitution =>
  fun y : ivar =>
  if ivar_eq_dec x y
  then M
  else sigma y
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
Proof.
  intros x.
  enough (get_max_ivar M < x -> ~ In x (getFVs M)) by now rewrite getFVs_isFreeIn, not_true_iff_false in H.
  assert (H1 : In x (getFVs M) -> fold_right_max_0 (getFVs M) >= x) by apply fold_right_max_0_in.
  enough (fold_right_max_0 (getFVs M) >= x -> fold_right_max_0 (getFVs M) < x -> False) by now eauto.
  lia.
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
Proof with firstorder.
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
Proof with eauto.
  intros M.
  assert (H : isFreshIn_substitution (chi nil_subtitution M) nil_subtitution M = true) by apply main_property_of_chi.
  unfold isFreshIn_substitution in H.
  rewrite forallb_true_iff in H.
  simpl in H.
  apply not_true_iff_false.
  intros H0.
  assert (H1 : negb (chi nil_subtitution M =? chi nil_subtitution M) = true) by now apply H, getFVs_isFreeIn.
  rewrite negb_true_iff in H1.
  rewrite Nat.eqb_neq in H1.
  contradiction.
Qed.

Fixpoint run_substitution_on_tm (sigma : substitution) (M : tm) {struct M} : tm :=
  match M with
  | tmVar x => sigma x
  | tmApp P1 P2 => tmApp (run_substitution_on_tm sigma P1) (run_substitution_on_tm sigma P2)
  | tmLam y Q =>
    let z : ivar := chi sigma M in
    let sigma' : substitution := cons_substitution y (tmVar z) sigma in
    tmLam z (run_substitution_on_tm sigma' Q)
  end
.

Definition equiv_substitution_wrt : substitution -> substitution -> tm -> Prop :=
  fun sigma1 : substitution => fun sigma2 : substitution => fun M : tm => forall x : ivar, isFreeIn x M = true -> sigma1 x = sigma2 x
.

Lemma chi_equiv_substitution_wrt :
  forall M : tm,
  forall sigma1 : substitution,
  forall sigma2 : substitution,
  equiv_substitution_wrt sigma1 sigma2 M ->
  chi sigma1 M = chi sigma2 M.
Proof with reflexivity.
  unfold chi.
  intros M sigma1 sigma2 H.
  assert ((map (fun x : ivar => get_max_ivar (sigma1 x)) (getFVs M)) = (map (fun x : ivar => get_max_ivar (sigma2 x)) (getFVs M))).
  { apply map_ext_in.
    intros x H0.
    rewrite (H x (proj1 (getFVs_isFreeIn M x) H0))...
  }
  rewrite H0...
Qed.

Theorem main_property_of_equiv_substitution_wrt :
  forall M : tm,
  forall sigma1 : substitution,
  forall sigma2 : substitution,
  equiv_substitution_wrt sigma1 sigma2 M ->
  run_substitution_on_tm sigma1 M = run_substitution_on_tm sigma2 M.
Proof with firstorder.
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
      - rewrite (chi_equiv_substitution_wrt (tmLam y M) sigma1 sigma2 H)...
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
Proof with firstorder.
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
Proof with firstorder.
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
    assert (claim1 : forall u : ivar, isFreeIn u (sigma1 z) = true -> cons_substitution y N sigma2 u = sigma2 u).
    { unfold cons_substitution.
      intros u H2.
      destruct (ivar_eq_dec y u).
      - subst.
        rewrite H1 in H2.
        discriminate.
      - reflexivity.
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

End UntypedLamdbdaCalculus.
