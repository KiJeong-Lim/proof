Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export Lia.
Require Export Ensembles.

(*
  Constructive Completeness Proofs and Delimited Control
  - Danko Ilik
*)

Module Helper.

  Section Section1.
  
    Lemma div_mod_property :
      forall a : nat,
      forall b : nat,
      forall q : nat,
      forall r : nat,
      a = b * q + r ->
      r < b ->
      a / b = q /\ a mod b = r.
    Proof.
      assert (forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
        intros x y.
        constructor.
        intro.
        induction H.
        exists 0.
        lia.
        destruct IHle as [z H0].
        exists (S z).
        lia.
        intro.
        destruct H as [z H].
        lia.
      intros a b q r H1 H2.
      assert (a = b * (a / b) + (a mod b)).
        apply (Nat.div_mod a b).
        lia.
      assert (0 <= a mod b < b).
        apply (Nat.mod_bound_pos a b).
        lia.
        lia.
      assert (~ q > a / b).
        intro.
        assert (exists z : nat, q = S (a / b + z)).
          apply (H q (a / b)).
          lia.
        destruct H5 as [z H5].
        assert (b + r < a mod b).
          assert (b * q + r >= b * S (a / b) + r).
            lia.
          lia.
        lia.
      assert (~ q < a / b).
        intro.
        assert (exists z : nat, a / b = S (q + z)).
          apply (H (a / b) q).
          lia.
        destruct H6 as [z H6].
        assert (a mod b + r < b).
          assert (b * q + a mod b >= b * S (a / b) + a mod b).
            lia.
          lia.
        lia.
      assert (q = a / b).
        lia.
      assert (r = a mod b).
        lia.
      lia.
    Qed.
    
  End Section1.

  Section Section2.

    Fixpoint sum_from_0_to (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n + sum_from_0_to n'
      end
    .

    Proposition value_of_sum_from_0_to :
      forall n : nat,
      2 * sum_from_0_to n = n * (S n).
    Proof.
      intros n.
      induction n.
      - intuition.
      - simpl in *.
        lia.
    Qed.

    Fixpoint mapsLineToPlane (n : nat) : (nat * nat) :=
      match n with
      | 0 => (0, 0)
      | S n' =>
        let x := fst (mapsLineToPlane n') in
        let y := snd (mapsLineToPlane n') in
        match x with
        | 0 => (S y, 0)
        | S x' => (x', S y)
        end
      end
    .

    Proposition mapsLineToPlane_is_surjective:
      forall x y : nat,
      (x, y) = mapsLineToPlane (sum_from_0_to (x + y) + y).
    Proof.
      cut (
        forall z x y : nat,
        z = x + y ->
        (x, y) = mapsLineToPlane (sum_from_0_to z + y)
      ).
        intro.
        intros x y.
        apply (H (x + y) x y eq_refl).
      intros z.
      induction z.
      - intros x y.
        intro.
        assert (x = 0).
          lia.
        assert (y = 0).
          lia.
        subst.
        intuition.
      - cut (
          forall y x : nat,
          S z = x + y ->
          (x, y) = mapsLineToPlane (sum_from_0_to (S z) + y)
        ).
          intuition.
        intros y.
        induction y.
        * intros x.
          intro.
          assert (x = S z).
            lia.
          subst.
          simpl sum_from_0_to.
          simpl plus.
          assert ((0, z) = mapsLineToPlane (sum_from_0_to z + z)).
            apply (IHz 0 z).
            lia.
          assert ((0, z) = mapsLineToPlane (z + sum_from_0_to z + 0)).
            rewrite H0.
            assert (sum_from_0_to z + z = z + sum_from_0_to z + 0).
              lia.
            rewrite H1.
            tauto.
          simpl.
          rewrite <- H1.
          simpl.
          tauto.
        * intros x.
          intro.
          assert ((S x, y) = mapsLineToPlane (sum_from_0_to (S z) + y)).
            apply (IHy (S x)).
            lia.
          assert (mapsLineToPlane (z + sum_from_0_to z + S y) = mapsLineToPlane (sum_from_0_to (S z) + y)).
            assert (z + sum_from_0_to z + S y = sum_from_0_to (S z) + y).
              simpl.
              lia.
            rewrite H1.
            tauto.
          simpl.
          rewrite H1.
          rewrite <- H0.
          simpl.
          tauto.
    Qed.

    Proposition mapsLineToPlane_is_injective :
      forall n x y : nat,
      (x, y) = mapsLineToPlane n ->
      n = sum_from_0_to (x + y) + y.
    Proof.
      intros n.
      induction n.
      - intros x y.
        simpl.
        intro.
        assert (x = 0 /\ y = 0).
          apply (pair_equal_spec).
          apply H.
        destruct H0.
        subst.
        simpl.
        tauto.
      - cut (
          forall y x : nat,
          (x, y) = mapsLineToPlane (S n) ->
          S n = sum_from_0_to (x + y) + y
        ).
          intuition.
        intros y.
        destruct y.
        * intros x.
          intro.
          simpl in H.
          assert (mapsLineToPlane n = (fst (mapsLineToPlane n), snd (mapsLineToPlane n))).
            apply (surjective_pairing).
          destruct (fst (mapsLineToPlane n)). 
          + assert (x = S (snd (mapsLineToPlane n))).
              apply (proj1 (proj1 (pair_equal_spec _ _ 0 0) H)).
            subst.
            simpl.
            cut (n = snd (mapsLineToPlane n) + 0 + sum_from_0_to (snd (mapsLineToPlane n) + 0) + 0).
              lia.
            cut (n = sum_from_0_to (0 + snd (mapsLineToPlane n)) + snd (mapsLineToPlane n)).
              assert (snd (mapsLineToPlane n) + 0 = 0 + snd (mapsLineToPlane n)).
                lia.
              rewrite H1.
              lia.
            apply (IHn 0 (snd (mapsLineToPlane n))).
            rewrite <- H0.
            tauto.
          + assert (0 = S (snd (mapsLineToPlane n))).
              apply (proj2 (proj1 (pair_equal_spec x n0 _ _) H)).
            inversion H1.
        * intros x.
          intro.
          assert (x = fst (mapsLineToPlane (S n)) /\ S y = snd (mapsLineToPlane (S n))).
            apply pair_equal_spec.
            rewrite H.
            apply surjective_pairing.
          cut (n = sum_from_0_to (S x + y) + y).
            intro.
            assert (x + S y = S (x + y)).
              lia.
            rewrite H2.
            simpl in *.
            lia.
          apply (IHn (S x) y).
          assert (mapsLineToPlane n = (fst (mapsLineToPlane n), snd (mapsLineToPlane n))).
            apply (surjective_pairing).
          simpl in *.
          destruct (fst (mapsLineToPlane n)).
          + assert (S y = 0).
              destruct H0.
              simpl in H2.
              apply H2.
            inversion H2.
          + assert (x = n0 /\ y = snd (mapsLineToPlane n)).
              destruct H0.
              simpl in *.
              constructor.
              apply H0.
              inversion H2.
              tauto.
            destruct H2.
            rewrite <- H2 in *.
            rewrite H3 in *.
            rewrite <- H1.
            tauto.
    Qed.

  End Section2.

  Section Section3.
    
    Lemma Included_refl {A : Type} :
      forall xs : Ensemble A,
      Included A xs xs.
    Proof.
      intros xs.
      intros x.
      tauto.
    Qed.

    Lemma Included_Add {A : Type} :
      forall x : A,
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      Included A xs1 xs2 ->
      Included A (Add A xs1 x) (Add A xs2 x).
    Proof.
      intros x xs1 xs2.
      unfold Included.
      intro.
      intros x'.
      intro.
      destruct H0.
      - unfold Add.
        apply Union_introl.
        apply (H x0).
        apply H0.
      - unfold Add.
        apply Union_intror.
        apply H0.
    Qed.

  End Section3.

  Section Section4.
    
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
    Proof.
      intros p.
      assert (forall x : nat, p x = true -> p (first_nat p x) = true).
        intros x.
        induction x.
        tauto.
        simpl.
        cut (let b := p (first_nat p x) in p (S x) = true -> p (if b then first_nat p x else S x) = true).
          simpl.
          tauto.
        intros.
        assert (b = true \/ b = false).
          destruct b.
            tauto.
            tauto.
        destruct H0.
        rewrite H0.
        unfold b in H0.
        apply H0.
        rewrite H0.
        apply H.
      assert (forall x : nat, first_nat p x <= x).
        intros x.
        induction x.
          simpl.
          lia.
          simpl.
          cut (let b := p (first_nat p x) in (if b then first_nat p x else S x) <= S x).
            simpl.
            tauto.
          intros.
          assert (b = true \/ b = false).
            destruct b.
              tauto.
              tauto.
          destruct H0.
            rewrite H0.
            lia.
            rewrite H0.
            lia.
      assert (forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
        intros x.
        intro.
        intros y.
        intro.
        induction H2.
          simpl.
          rewrite H1.
          tauto.
          simpl.
          rewrite <- IHle.
          rewrite H1.
          tauto.
      assert (forall x : nat, forall y : nat, p y = true -> first_nat p x <= y).
        intros x.
        intros y.
        intro.
        assert (x <= y \/ x > y).
          lia.
        destruct H3.
        assert (first_nat p x <= x <= y).
          constructor.
          apply (H0 x).
          apply H3.
          lia.
        assert (p (first_nat p y) = true).
          apply (H y).
          assert (first_nat p x <= x).
            apply (H0 x).
            apply H2.
        assert (first_nat p y = first_nat p x).
          apply (H1 y).
          apply H4.
          lia.
          rewrite <- H5.
          apply (H0 y).
      intros n.
      intro.
      intros m.
      constructor.
      unfold m.
      apply (H n H3).
      intros i.
      intro.
      assert (first_nat p n <= i).
        apply (H2 n i H4).
      lia.
    Qed.

  End Section4.

End Helper.

Module PropositionalLogic.

  Import Helper.

  Section Syntax.

    Definition PVar : Set := 
      nat
    .

    Inductive Formula : Set :=
    | AtomF : forall i : PVar, Formula
    | ContradictionF : Formula
    | NegationF : forall p1 : Formula, Formula
    | ConjunctionF : forall p1 : Formula, forall p2 : Formula, Formula
    | DisjunctionF : forall p1 : Formula, forall p2 : Formula, Formula
    | ImplicationF : forall p1 : Formula, forall p2 : Formula, Formula
    | BiconditionalF : forall p1 : Formula, forall p2 : Formula, Formula
    .
    
    Proposition eq_Formula_dec :
      forall p1 p2 : Formula,
      {p1 = p2} + {p1 <> p2}.
    Proof.
      intros p1.
      induction p1.
      - intros p2.
        destruct p2.
        * destruct (Nat.eq_dec i i0).
          + intuition.
          + assert (AtomF i <> AtomF i0).
              intro.
              inversion H.
              intuition.
            intuition.
        * assert (AtomF i <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF i <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        induction p2.
        * assert (ContradictionF <> AtomF i).
            intro.
            inversion H.
          intuition.
        * intuition.
        * assert (ContradictionF <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (ContradictionF <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        destruct p2.
        * assert (NegationF p1 <> AtomF i).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * destruct (IHp1 p2).
            subst.
            tauto.
            assert (NegationF p1 <> NegationF p2).
              intro.
              inversion H.
              apply (n H1).
            intuition.
        * assert (NegationF p1 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (NegationF p1 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        destruct p2.
        * assert (ConjunctionF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          intuition.
        * assert (ConjunctionF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * assert (ConjunctionF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (ConjunctionF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (ConjunctionF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (ConjunctionF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (ConjunctionF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (ConjunctionF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        destruct p2.
        * assert (DisjunctionF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (DisjunctionF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (DisjunctionF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (DisjunctionF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (DisjunctionF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        induction p2.
        * assert (ImplicationF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (ImplicationF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (ImplicationF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (ImplicationF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (ImplicationF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        destruct p2.
        * assert (BiconditionalF p1_1 p1_2 <> AtomF i).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> ContradictionF).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> NegationF p2).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (BiconditionalF p1_1 p1_2 <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (BiconditionalF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (BiconditionalF p1_1 p1_2 <> BiconditionalF p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
    Qed.

    Fixpoint rankOfFormula (p : Formula) : nat :=
      match p with
      | AtomF i => 0
      | ContradictionF => 1
      | NegationF p1 => S (rankOfFormula p1)
      | ConjunctionF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      | DisjunctionF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      | ImplicationF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      | BiconditionalF p1 p2 => S (max (rankOfFormula p1) (rankOfFormula p2))
      end
    .
    
    Fixpoint enum_formula_aux (rank : nat) (seed0 : nat) : Formula :=
      match rank with
      | 0 =>
        let i := seed0 in
        AtomF i
      | S rank' =>
        let (seed1, piece1) := mapsLineToPlane seed0 in
        match piece1 with
        | 0 => ContradictionF
        | S 0 => NegationF (enum_formula_aux rank' seed1) 
        | S (S 0) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          ConjunctionF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S 0)) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          DisjunctionF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S (S 0))) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          ImplicationF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S (S (S 0)))) =>
          let (seed2, seed3) := mapsLineToPlane seed1 in
          BiconditionalF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
        | S (S (S (S (S (S i))))) => AtomF i
        end
      end
    .

    Lemma enum_formula_aux_property :
      forall p : Formula,
      forall rank : nat,
      rankOfFormula p <= rank ->
      exists seed : nat,
      enum_formula_aux rank seed = p.
    Proof.
      assert (
        forall x : nat,
        forall y : nat,
        forall z : nat,
        (y, z) = mapsLineToPlane x <-> x = sum_from_0_to (y + z) + z
      ).
        intros x y z.
        constructor.
        intro.
        apply mapsLineToPlane_is_injective.
        intuition.
        intro.
        subst.
        apply mapsLineToPlane_is_surjective.
      intros p.
      induction p.
      - intros r.
        simpl.
        intro.
        destruct r.
        * exists i.
          simpl.
          tauto.
        * assert (exists seed : nat, (0, S (S (S (S (S (S i)))))) = mapsLineToPlane seed).
          exists (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))).
          apply (proj2 (H (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))) 0 (S (S (S (S (S (S i))))))) eq_refl).
          destruct H1 as [seed H1].
          exists seed.
          simpl.
          rewrite <- H1.
          tauto.
      - intros r.
        simpl.
        intro.
        inversion H0.
          exists 0.
          simpl.
          tauto.
          exists 0.
          simpl.
          tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (rankOfFormula p).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert (rankOfFormula p <= rank).
          lia.
        subst.
        destruct (IHp rank H2) as [seed H1].
        exists (sum_from_0_to (seed + 1) + 1).
        assert ((seed, 1) = mapsLineToPlane (sum_from_0_to (seed + 1) + 1)).
          apply (H ((sum_from_0_to (seed + 1) + 1)) seed 1).
          intuition.
        simpl in *.
        rewrite <- H3.
        rewrite H1.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 2) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 2) + 2).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 2) + 2) (sum_from_0_to (seed2 + seed3) + seed3) 2)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 3) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 3) + 3).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 3) + 3) (sum_from_0_to (seed2 + seed3) + seed3) 3)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 4) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 4) + 4).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 4) + 4) (sum_from_0_to (seed2 + seed3) + seed3) 4)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
      - intros r.
        simpl.
        intro.
        assert (exists rank : nat, r = S rank).
          inversion H0.
          exists (Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)).
          tauto.
          exists m.
          tauto.
        destruct H1 as [rank H1].
        rewrite H1 in H0.
        assert ((Init.Nat.max (rankOfFormula p1) (rankOfFormula p2)) <= rank).
          lia.
        subst.
        destruct (IHp1 rank) as [seed2 H3].
          lia.
        destruct (IHp2 rank) as [seed3 H4].
          lia.
        assert (exists seed : nat, (sum_from_0_to (seed2 + seed3) + seed3, 5) = mapsLineToPlane seed).
          exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 5) + 5).
            apply (proj2 (H (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + 5) + 5) (sum_from_0_to (seed2 + seed3) + seed3) 5)).
            tauto.
        destruct H1 as [seed H1].
        exists (seed).
        simpl.
        rewrite <- H1.
        assert ((seed2, seed3) = mapsLineToPlane (sum_from_0_to (seed2 + seed3) + seed3)).
          apply (proj2 (H (sum_from_0_to (seed2 + seed3) + seed3) seed2 seed3)).
          tauto.
        rewrite <- H5.
        rewrite H3.
        rewrite H4.
        tauto.
    Qed.

    Definition enumerateFormula (n : nat) : Formula :=
      let (x, y) := mapsLineToPlane n in
      enum_formula_aux x y
    .

    Theorem Formula_is_enumerable : 
      forall p : Formula,
      exists n : nat, enumerateFormula n = p.
    Proof.
      intros p.
      assert (exists seed : nat, enum_formula_aux (rankOfFormula p) seed = p).
        apply (enum_formula_aux_property p (rankOfFormula p)).
        lia.
      destruct H as [seed H].
      exists (sum_from_0_to (rankOfFormula p + seed) + seed).
      assert ((rankOfFormula p, seed) = mapsLineToPlane (sum_from_0_to (rankOfFormula p + seed) + seed)).
        apply mapsLineToPlane_is_surjective.
      unfold enumerateFormula.
      rewrite <- H0.
      apply H.
    Qed.

  End Syntax.

  Section BooleanAlgebra.

    Class CountableBooleanAlgebra (B : Type) : Type :=
      { eqB : B -> B -> Prop
      ; trueB : B
      ; falseB : B
      ; andB : B -> B -> B
      ; enumB : nat -> B
      ; CBA_AXM_1 :
        forall b1 : B,
        eqB b1 b1
      ; CBA_AXM_2 :
        forall b1 : B,
        forall b2 : B,
        eqB b1 b2 ->
        eqB b2 b1
      ; CBA_AXM_3 :
        forall b1 : B,
        forall b2 : B,
        forall b3 : B,
        eqB b1 b2 ->
        eqB b2 b3 ->
        eqB b1 b3
      ; CBA_AXM_6 :
        forall b1 : B,
        forall b1' : B,
        forall b2 : B,
        forall b2' : B,
        eqB b1 b1' ->
        eqB b2 b2' ->
        eqB (andB b1 b2) (andB b1' b2')
      ; CBA_axm_1 :
        forall b1 : B,
        eqB (andB b1 b1) b1
      ; CBA_axm_3 :
        forall b1 : B,
        forall b2 : B,
        eqB (andB b1 b2) (andB b2 b1)
      ; CBA_axm_5 :
        forall b1 : B,
        forall b2 : B,
        forall b3 : B,
        eqB (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3)
      ; CBA_axm_9 :
        forall b1 : B,
        eqB (andB falseB b1) falseB
      ; CBA_axm_10 :
        forall b1 : B,
        eqB (andB trueB b1) b1
      ; CBA_axm_15 :
        forall b1 : B,
        exists n1 : nat, enumB n1 = b1
      }
    .

    Variable B : Type.

    Variable cba : CountableBooleanAlgebra B.

    Notation "b1 == b2" := (eqB b1 b2) (at level 80).

    Notation "b1 =< b2" := (eqB (andB b1 b2) b1) (at level 80).

    Lemma leq_CBA_refl :
      forall b1 : B,
      b1 =< b1.
    Proof.
      intros b1.
      apply CBA_axm_1.
    Qed.

    Lemma leq_CBA_refl' :
      forall b1 : B,
      forall b2 : B,
      b1 == b2 ->
      b1 =< b2.
    Proof.
      intros b1 b2.
      intro.
      assert (b2 == andB b1 b2).
        apply CBA_AXM_2.
        assert (andB b1 b2 == andB b2 b2).
          apply CBA_AXM_6.
        apply H.
        apply CBA_AXM_1.
        apply (CBA_AXM_3 _ _ _ H0).
        apply leq_CBA_refl.
      apply CBA_AXM_2.
      apply (CBA_AXM_3 _ _ _ H).
      apply H0.
    Qed.

    Lemma leq_CBA_asym :
      forall b1 : B,
      forall b2 : B,
      b1 =< b2 ->
      b2 =< b1 ->
      b1 == b2.
    Proof.
      intros b1 b2 H1 H2.
      assert (andB b1 b2 == andB b2 b1).
        apply CBA_axm_3.
      assert (andB b1 b2 == b1).
        apply H1.
      assert (andB b2 b1 == b2).
        apply H2.
      apply (CBA_AXM_3 b1 (andB b1 b2) b2).
      apply (CBA_AXM_2).
      apply H0.
      apply (CBA_AXM_3 (andB b1 b2) (andB b2 b1) b2 H H3).
    Qed.

    Lemma leq_CBA_trans :
      forall b1 : B,
      forall b2 : B,
      forall b3 : B,
      b1 =< b2 ->
      b2 =< b3 ->
      b1 =< b3.
    Proof.
      intros b1 b2 b3 H1 H2.
      assert (andB b1 (andB b2 b3) == andB (andB b1 b2) b3).
        apply CBA_axm_5.
      assert (andB (andB b1 b2) b3 == andB b1 b3).
        apply CBA_AXM_6.
        apply H1.
        apply CBA_AXM_1.
      assert (andB b1 (andB b2 b3) == andB b1 b3).
        apply (CBA_AXM_3 (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3) (andB b1 b3) H H0).
      assert (andB b1 (andB b2 b3) == andB b1 b2).
        apply CBA_AXM_6.
        apply CBA_AXM_1.
        apply H2.
      assert (andB b1 b3 == andB b1 b2).
        apply (CBA_AXM_3 (andB b1 b3) (andB b1 (andB b2 b3)) (andB b1 b2)).
        apply CBA_AXM_2.
        apply H3.
        apply H4.
      apply (CBA_AXM_3 (andB b1 b3) (andB b1 b2) b1).
      apply H5.
      apply H1.
    Qed.

    Lemma leq_CBA_and :
      forall b1 : B,
      forall b2 : B,
      forall b3 : B,
      forall b4 : B,
      b1 =< b3 ->
      b2 =< b4 ->
      andB b1 b2 =< andB b3 b4.
    Proof.
      intros b1 b2 b3 b4.
      intro.
      intro.
      assert (andB (andB b1 b2) (andB b3 b4) == andB (andB b1 b3) (andB b2 b4)).
        assert (andB (andB b1 b3) (andB b2 b4) == andB b1 (andB b3 (andB b2 b4))).
          apply CBA_AXM_2.
          apply CBA_axm_5.
        assert (andB b1 (andB b3 (andB b2 b4)) == andB b1 (andB (andB b3 b2) b4)).
          apply CBA_AXM_6.
          apply CBA_AXM_1.
          apply CBA_axm_5.
        assert (andB b1 (andB (andB b3 b2) b4) == andB b1 (andB (andB b2 b3) b4)).
          apply CBA_AXM_6.
          apply CBA_AXM_1.
          apply CBA_AXM_6.
          apply CBA_axm_3.
          apply CBA_AXM_1.
        assert (andB b1 (andB (andB b2 b3) b4) == andB b1 (andB (andB b2 b3) b4)).
          apply CBA_AXM_6.
          apply CBA_AXM_1.
          apply CBA_AXM_1.
        assert (andB b1 (andB (andB b2 b3) b4) == andB b1 (andB b2 (andB b3 b4))).
          apply CBA_AXM_6.
          apply CBA_AXM_1.
          apply CBA_AXM_2.
          apply CBA_axm_5.
        assert (andB b1 (andB b2 (andB b3 b4)) == andB (andB b1 b2) (andB b3 b4)).
          apply CBA_axm_5.
        apply CBA_AXM_2.
        apply (CBA_AXM_3 _ _ _ H1).
        apply (CBA_AXM_3 _ _ _ H2).
        apply (CBA_AXM_3 _ _ _ H3).
        apply (CBA_AXM_3 _ _ _ H4).
        apply (CBA_AXM_3 _ _ _ H5).
        apply (CBA_AXM_3 _ _ _ H6).
        apply CBA_AXM_1.
      assert (andB (andB b1 b3) (andB b2 b4) == andB b1 b2).
        apply CBA_AXM_6.
        apply H.
        apply H0.
      apply (CBA_AXM_3 _ _ _ H1).
      apply H2.
    Qed.

    Definition isFilter (filter : Ensemble B) :=
      (exists b1 : B, filter b1) /\ (forall b1 : B, forall b2 : B, filter b1 -> b1 =< b2 -> filter b2) /\ (forall b1 : B, forall b2 : B, forall b : B, filter b1 -> filter b2 -> b == andB b1 b2 -> filter b)
    .

    Lemma isFilter_refl' :
      forall bs1 : Ensemble B,
      isFilter bs1 ->
      forall bs2 : Ensemble B,
      Included B bs1 bs2 ->
      Included B bs2 bs1 ->
      isFilter bs2.
    Proof.
      intros bs1 H0 bs2 H1 H2.
      destruct H0.
      destruct H0.
      constructor.
      destruct H as [b1].
      exists b1.
      apply (H1 b1 H).
      constructor.
      intros b1 b2 H4 H5.
      apply (H1 b2).
      apply (H0 b1 b2).
      apply (H2 b1 H4).
      apply H5.
      intros b1 b2 b H4 H5 H6.
      apply (H1 b).
      apply (H3 b1 b2 b).
      apply (H2 b1 H4).
      apply (H2 b2 H5).
      apply H6.
    Qed.

    Inductive FiniteMeet : Ensemble B -> nat -> Ensemble B :=
    | FiniteMeetZ :
      forall b : B,
      forall bs : Ensemble B,
      b == trueB ->
      In B (FiniteMeet bs 0) b
    | FiniteMeetS :
      forall b : B,
      forall bs : Ensemble B,
      forall n : nat,
      forall b1 : B,
      forall b2 : B,
      In B bs b1 ->
      In B (FiniteMeet bs n) b2 ->
      b == andB b1 b2 ->
      In B (FiniteMeet bs (S n)) b
    .

    Lemma FiniteMeet_plus :
      forall bs : Ensemble B,
      forall n1 : nat,
      forall n2 : nat,
      forall b1 : B,
      forall b2 : B,
      In B (FiniteMeet bs n1) b1 ->
      In B (FiniteMeet bs n2) b2 ->
      exists b : B, In B (FiniteMeet bs (n1 + n2)) b /\ b == andB b1 b2.
    Proof.
      intros bs n1.
      induction n1.
      - intros n2 b1 b2 H1 H2.
        inversion H1.
        subst.
        assert (0 + n2 = n2).
          lia.
        rewrite H0.
        exists b2.
        constructor.
        apply H2.
        assert (andB b1 b2 == andB trueB b2).
          apply CBA_AXM_6.
          apply H.
          apply CBA_AXM_1.
        apply CBA_AXM_2.
        apply (CBA_AXM_3 _ _ _ H3).
        apply (CBA_axm_10).
      - intros n2 b1 b2 H1 H2.
        inversion H1.
        subst.
        assert (exists b' : B, In B (FiniteMeet bs (n1 + n2)) b' /\ b' == andB b3 b2).
          destruct (IHn1 n2 b3 b2 H3 H2) as [b'].
          destruct H.
          exists b'.
          constructor.
          apply H.
          apply H4.
        destruct H as [b'].
        exists (andB b1 b2).
        simpl.
        assert (andB (andB b1 b3) b2 == andB b1 (andB b3 b2)).
          assert (andB b1 (andB b3 b2) == andB (andB b1 b3) b2).
            apply CBA_axm_5.
          apply CBA_AXM_2.
          apply (CBA_axm_5).
        destruct H.
        constructor.
        apply (FiniteMeetS (andB b1 b2) bs (n1 + n2) b0 b').
        apply H0.
        apply H.
        assert (andB b1 b2 == andB (andB b0 b3) b2).
          apply CBA_AXM_6.
          apply H5.
          apply CBA_AXM_1.
        assert (andB (andB b0 b3) b2 == andB b0 (andB b3 b2)).
          apply CBA_AXM_2.
          apply CBA_axm_5.
        assert (andB b0 (andB b3 b2) == andB b0 b').
          apply CBA_AXM_6.
          apply CBA_AXM_1.
          apply CBA_AXM_2.
          apply H6.
        apply (CBA_AXM_3 _ _ _ H7).
        apply (CBA_AXM_3 _ _ _ H8).
        apply (CBA_AXM_3 _ _ _ H9).
        apply (CBA_AXM_1).
        apply CBA_AXM_1.
    Qed.

    Lemma FiniteMeet_subset :
      forall n : nat,
      forall bs1 : Ensemble B,
      forall bs2 : Ensemble B,
      Included B bs1 bs2 ->
      Included B (FiniteMeet bs1 n) (FiniteMeet bs2 n).
    Proof.
      intros n.
      induction n.
      - intros bs1 bs2 H.
        intros b H0.
        inversion H0.
        subst.
        apply (FiniteMeetZ b).
        apply H1.
      - intros bs1 bs2 H.
        intros b H0.
        inversion H0.
        subst.
        apply (FiniteMeetS b bs2 n b1 b2).
        apply (H b1 H2).
        apply (IHn bs1 bs2 H b2 H3).
        apply H5.
    Qed.

    Inductive Closure : Ensemble B -> Ensemble B :=
    | InClosure :
      forall bs : Ensemble B,
      forall b : B,
      forall n : nat,
      forall b1 : B,
      In B (FiniteMeet bs n) b1 ->
      b1 =< b ->
      In B (Closure bs) b
    .

    Definition inconsistent (bs1 : Ensemble B) : Prop :=
      In B bs1 falseB
    .

    Definition equiconsistent (bs1 : Ensemble B) (bs2 : Ensemble B) : Prop :=
      inconsistent bs1 <-> inconsistent bs2
    .

    Definition element_complete (bs1 : Ensemble B) (b2 : B) : Prop :=
      equiconsistent bs1 (Closure (Add B bs1 b2)) -> In B bs1 b2
    .

    Definition complete (bs1 : Ensemble B) : Prop :=
      forall b2 : B, element_complete bs1 b2
    .

    Lemma fact_1_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter (Closure bs).
    Proof.
      intros bs.
      constructor.
      exists trueB.
      apply (InClosure bs trueB 0 trueB).
      apply (FiniteMeetZ trueB).
      apply CBA_AXM_1.
      apply CBA_axm_10.
      constructor.
      intros b1 b2.
      intro.
      intro.
      inversion H.
      subst.
      apply (InClosure bs b2 n b0).
      apply H1.
      apply (leq_CBA_trans b0 b1 b2).
      apply H2.
      apply H0.
      intros b1 b2 b H1 H2 H3.
      inversion H1.
      subst.
      inversion H2.
      subst.
      destruct (FiniteMeet_plus bs n n0 b3 b4) as [b'].
      apply H.
      apply H4.
      destruct H6.
      apply (InClosure bs b (n + n0) b').
      apply H6.
      assert (andB b3 b4 =< andB b1 b2).
        apply (leq_CBA_and b3 b4 b1 b2).
        apply H0.
        apply H5.
      apply (CBA_AXM_3 (andB b' b) (andB (andB b3 b4) (andB b1 b2)) b').
      apply CBA_AXM_6.
      apply H7.
      apply H3.
      apply CBA_AXM_2.
      apply (CBA_AXM_3 _ _ _ H7).
      apply CBA_AXM_2.
      apply H8.
    Qed.

    Lemma fact_2_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall b : B,
      b == trueB ->
      In B bs b.
    Proof.
      intros bs.
      intro.
      intros b.
      intro HHH.
      destruct H.
      destruct H0.
      destruct H as [b1].
      apply (H0 b1).
      apply H.
      assert (andB b1 trueB == b1).
        assert (andB trueB b1 == b1).
          apply CBA_axm_10.
        assert (andB b1 trueB == andB trueB b1).
          apply CBA_axm_3.
        apply (CBA_AXM_3 _ _ _  H3 H2).
      assert (andB b1 b == andB b1 trueB).
        apply (CBA_AXM_6).
        apply CBA_AXM_1.
        apply HHH.
      apply (CBA_AXM_3 _ _ _ H3).
      apply H2.
    Qed.

    Lemma fact_3_of_1_2_8 :
      forall bs : Ensemble B,
      Included B bs (Closure bs).
    Proof.
      intros bs.
      intros b H0.
      apply (InClosure bs b 1 b).
      assert (andB b trueB == b).
        assert (andB b trueB == andB trueB b).
          apply CBA_axm_3.
        assert (andB trueB b == b).
          apply CBA_axm_10.
        apply (CBA_AXM_3 _ _ _ H).
        apply H1.
      apply (FiniteMeetS b bs 0 b trueB).
      apply H0.
      apply (FiniteMeetZ trueB bs).
      apply CBA_AXM_1.
      apply CBA_AXM_2.
      apply H.
      apply (leq_CBA_refl b).
    Qed.

    Lemma fact_4_of_1_2_8 :
      forall bs1 : Ensemble B,
      forall bs2 : Ensemble B,
      Included B bs1 bs2 ->
      Included B (Closure bs1) (Closure bs2).
    Proof.
      intros bs1 bs2 H.
      intros b H0.
      inversion H0.
      subst.
      assert (Included B (FiniteMeet bs1 n) (FiniteMeet bs2 n)).
        apply FiniteMeet_subset.
        apply H.
      apply (InClosure bs2 b n b1).
      apply (H3 b1 H1).
      apply H2.
    Qed.

    Lemma fact_5_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter bs ->
      Included B (Closure bs) bs.
    Proof.
      intros bs.
      intro.
      cut (
        forall n : nat,
        Included B (FiniteMeet bs n) bs
      ).
        intro.
        intros b H1.
        inversion H1.
        subst.
        destruct H.
        destruct H4.
        assert (Included B (FiniteMeet bs n) bs).
          apply (H0 n).
        apply (H4 b1 b).
        apply (H6 b1).
        apply H2.
        apply H3.
      intros n.
      induction n.
      - intros b H0.
        inversion H0.
        subst.
        apply fact_2_of_1_2_8.
        apply H.
        apply H1.
      - destruct H.
        destruct H0.
        intros b H2.
        inversion H2.
        subst.
        apply (H1 b1 b2).
        apply H4.
        apply (IHn b2 H5).
        apply H7.
    Qed.

    Lemma proposition_1_2_9 :
      forall bs : Ensemble B,
      forall b1 : B,
      forall b2 : B,
      isFilter bs ->
      b1 == b2 ->
      In B bs b1 ->
      In B bs b2.
    Proof.
      intros bs b1 b2 H0 H1 H2.
      assert (b1 =< b2).
        apply (leq_CBA_refl').
        apply H1.
      destruct H0.
      destruct H3.
      apply (H3 b1 b2).
      apply H2.
      apply H.
    Qed.

    Inductive Construction : Ensemble B -> nat -> Ensemble B :=
    | InConstruction :
      forall bs : Ensemble B,
      forall n : nat,
      forall b : B,
      equiconsistent bs (Closure (Add B bs (enumB n))) ->
      enumB n == b ->
      In B (Construction bs n) b
    .

    Fixpoint SequenceConstruction (bs : Ensemble B) (n : nat) : Ensemble B :=
      match n with
      | 0 => bs
      | S n' =>
        let bs' := SequenceConstruction bs n' in
        Closure (Union B bs' (Construction bs' n'))
      end
    .

    Lemma lemma_1_2_11 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n : nat,
      isFilter (SequenceConstruction bs n).
    Proof.
      intros bs H n.
      induction n.
      - simpl.
        apply H.
      - simpl.
        apply fact_1_of_1_2_8.
    Qed.

    Lemma lemma_1_2_12 :
      forall bs : Ensemble B,
      forall n1 : nat,
      forall n2 : nat,
      n1 <= n2 ->
      Included B (SequenceConstruction bs n1) (SequenceConstruction bs n2).
    Proof.
      intros bs n1 n2 H.
      induction H.
      - intros b H0.
        apply H0.
      - intros b H0.
        simpl.
        assert (In B (SequenceConstruction bs m) b).
          apply (IHle b H0).
        apply (fact_4_of_1_2_8 (SequenceConstruction bs m)).
        intros b0 H3.
        apply Union_introl.
        apply H3.
        apply fact_3_of_1_2_8.
        apply H1.
    Qed.

    Lemma lemma_1_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n : nat,
      equiconsistent bs (SequenceConstruction bs n).
    Proof.
      intros bs H n.
      induction n.
      - simpl.
        unfold equiconsistent.
        tauto.
      - constructor.
        * intro.
          assert (Included B (SequenceConstruction bs n) (SequenceConstruction bs (S n))).
          apply lemma_1_2_12.
          lia.
          destruct IHn.
          apply H1.
          apply H2.
          apply H0.
        * intro.
          inversion H0.
          subst.
          apply (proj2 IHn).
          assert (falseB == b1).
            assert (andB b1 falseB == andB falseB b1).
              apply CBA_axm_3.
            assert (andB falseB b1 == falseB).
              apply CBA_axm_9.
            apply (leq_CBA_asym).
            apply H4.
            apply H2.
          cut (
            forall l : nat,
            forall b : B,
            In B (FiniteMeet (Union B (SequenceConstruction bs n) (Construction (SequenceConstruction bs n) n)) l) b ->
            In B (SequenceConstruction bs n) b \/ equiconsistent (SequenceConstruction bs n) (Closure (Add B (SequenceConstruction bs n) (enumB n)))
          ).
            intro.
            destruct (H4 n0 b1 H1).
            apply (proposition_1_2_9 (SequenceConstruction bs n) b1 falseB).
            apply lemma_1_2_11.
            apply H.
            apply CBA_AXM_2.
            apply H3.
            apply H5.
            apply (proj2 H5).
            apply (InClosure (Add B (SequenceConstruction bs n) (enumB n)) falseB n0 b1).
            assert (
              forall i : nat,
              forall b : B,
              In B (FiniteMeet (Union B (SequenceConstruction bs n) (Construction (SequenceConstruction bs n) n)) i) b ->
              (FiniteMeet (Add B (SequenceConstruction bs n) (enumB n)) i) b
            ).
              induction i.
                intros b.
                intro.
                inversion H6.
                subst.
                apply (FiniteMeetZ b (Add B (SequenceConstruction bs n) (enumB n)) H7).
                intros b.
                intro.
                inversion H6.
                subst.
                inversion H8.
                subst.
                apply (FiniteMeetS b (Add B (SequenceConstruction bs n) (enumB n)) i b2 b3).
                apply Union_introl.
                apply H7.
                apply (IHi).
                apply H9.
                apply H11.
                subst.
                simpl.
                apply (FiniteMeetS b (Add B (SequenceConstruction bs n) (enumB n)) i (enumB n) b3).
                apply Union_intror.
                apply In_singleton.
                apply (IHi).
                apply H9.
                inversion H7.
                subst.
                assert (andB (enumB n) b3 == andB b2 b3).
                  apply CBA_AXM_6.
                  apply H12.
                  apply CBA_AXM_1.
                apply (CBA_AXM_3 _ _ _ H11).
                apply CBA_AXM_2.
                apply H13.
              apply (H6 n0 b1).
              apply H1.
              apply H2.
          intros l.
          induction l.
          + intros b.
            intro.
            inversion H4.
            subst.
            apply or_introl.
            apply fact_2_of_1_2_8.
            apply lemma_1_2_11.
            apply H.
            apply H5.
          + intros b.
            intro.
            inversion H4.
            subst.
            assert (isFilter (SequenceConstruction bs n)).
              apply lemma_1_2_11.
              apply H.
            destruct (IHl b3 H7).
            inversion H6.
            subst.
            apply or_introl.
            destruct H5.
            destruct H11.
            apply (H12 b2 b3 b).
            apply H10.
            apply H8.
            apply H9.
            subst.
            inversion H10.
            subst.
            apply or_intror.
            apply H11.
            apply or_intror.
            apply H8.
    Qed.

    Lemma lemma_2_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n1 : nat,
      forall n2 : nat,
      equiconsistent (SequenceConstruction bs n1) (SequenceConstruction bs n2).
    Proof.
      intros bs H n1 n2.
      assert (equiconsistent bs (SequenceConstruction bs n1)).
        apply lemma_1_of_1_2_13.
        apply H.
      assert (equiconsistent bs (SequenceConstruction bs n2)).
        apply lemma_1_of_1_2_13.
        apply H.
      unfold equiconsistent in *.
      tauto.
    Qed.

    Inductive InfiniteConstruction : Ensemble B -> Ensemble B :=
    | InInfiniteConstruction :
      forall bs : Ensemble B,
      forall n : nat,
      forall b : B,
      In B (SequenceConstruction bs n) b ->
      In B (InfiniteConstruction bs) b
    .

    Lemma lemma_3_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      Included B bs (InfiniteConstruction bs) /\ equiconsistent bs (InfiniteConstruction bs).
    Proof.
      intros bs H.
      constructor.
      intros b H0.
      apply (InInfiniteConstruction bs 0 b).
      simpl.
      apply H0.
      constructor.
      intro.
      apply (InInfiniteConstruction bs 0 falseB).
      simpl.
      apply H0.
      intro.
      inversion H0.
      subst.
      destruct (lemma_1_of_1_2_13 bs H n).
      tauto.
    Qed.

    Theorem theorem_1_2_14 :
      forall bs : Ensemble B,
      isFilter bs ->
      let bs' := InfiniteConstruction bs in
      isFilter bs' /\ equiconsistent bs bs' /\ complete bs'.
    Proof.
      intros bs H bs'.
      assert (Included B bs bs' /\ equiconsistent bs bs').
        apply lemma_3_of_1_2_13.
        apply H.
      destruct H0.
      constructor.
      constructor.
      destruct H.
      destruct H as [b1].
      exists b1.
      apply (H0 b1 H).
      constructor.
      intros b1 b2 H4 H5.
      inversion H4.
      subst.
      apply (InInfiniteConstruction bs n b2).
      destruct (lemma_1_2_11 bs H n).
      destruct H6.
      apply (H6 b1 b2).
      apply H2.
      apply H5.
      intros b1 b2 b H3 H4 H5.
      inversion H3.
      subst.
      inversion H4.
      subst.
      assert (n <= n0 \/ n0 <= n).
        lia.
      destruct H7.
      assert (Included B (SequenceConstruction bs n) (SequenceConstruction bs n0)).
        apply lemma_1_2_12.
        apply H7.
      apply (InInfiniteConstruction bs n0 b).
      apply (proposition_1_2_9 (SequenceConstruction bs n0) (andB b1 b2) b).
      apply lemma_1_2_11.
      apply H.
      apply CBA_AXM_2.
      apply H5.
      apply fact_5_of_1_2_8.
      apply lemma_1_2_11.
      apply H.
      apply (InClosure (SequenceConstruction bs n0) (andB b1 b2) 2 (andB b1 b2)).
      apply (FiniteMeetS (andB b1 b2) (SequenceConstruction bs n0) 1 b1 b2).
      apply (H8 b1 H2).
      apply (FiniteMeetS b2 (SequenceConstruction bs n0) 0 b2 trueB).
      apply H6.
      apply (FiniteMeetZ).
      apply CBA_AXM_1.
      apply CBA_AXM_2.
      assert (andB b2 trueB == andB trueB b2).
        apply CBA_axm_3.
      apply (CBA_AXM_3 _ _ _ H9).
      apply CBA_axm_10.
      apply CBA_AXM_1.
      apply leq_CBA_refl.
      assert (Included B (SequenceConstruction bs n0) (SequenceConstruction bs n)).
        apply lemma_1_2_12.
        apply H7.
      apply (InInfiniteConstruction bs n b).
      apply (proposition_1_2_9 (SequenceConstruction bs n) (andB b1 b2) b).
      apply lemma_1_2_11.
      apply H.
      apply CBA_AXM_2.
      apply H5.
      apply fact_5_of_1_2_8.
      apply lemma_1_2_11.
      apply H.
      apply (InClosure (SequenceConstruction bs n) (andB b1 b2) 2 (andB b1 b2)).
      apply (FiniteMeetS (andB b1 b2) (SequenceConstruction bs n) 1 b1 b2).
      apply H2.
      apply (FiniteMeetS b2 (SequenceConstruction bs n) 0 b2 trueB).
      apply (H8 b2 H6).
      apply (FiniteMeetZ).
      apply CBA_AXM_1.
      apply CBA_AXM_2.
      assert (andB b2 trueB == andB trueB b2).
        apply CBA_axm_3.
      apply (CBA_AXM_3 _ _ _ H9).
      apply CBA_axm_10.
      apply CBA_AXM_1.
      apply leq_CBA_refl.
      constructor.
      apply H1.
      unfold complete.
      intros b'.
      intro.
      destruct (CBA_axm_15 b') as [n'].
      assert (equiconsistent (SequenceConstruction bs n') (Closure (Add B (SequenceConstruction bs n') b'))).
        constructor.
        intro.
        apply fact_3_of_1_2_8.
        apply Union_introl.
        apply H4.
        intro.
        assert (inconsistent (Closure (Add B bs' b'))).
          apply (fact_4_of_1_2_8 (Add B (SequenceConstruction bs n') b') (Add B bs' b')).
          intros b.
          intro.
          inversion H5.
          subst.
          apply Union_introl.
          apply (InInfiniteConstruction bs n' b).
          apply H6.
          inversion H6.
          subst.
          apply Union_intror.
          apply In_singleton.
        apply H4.
      assert (equiconsistent (SequenceConstruction bs n') bs').
        assert (equiconsistent bs bs').
          apply lemma_3_of_1_2_13.
          apply H.
        assert (equiconsistent bs (SequenceConstruction bs n')).
          apply lemma_1_of_1_2_13.
          apply H.
        unfold equiconsistent in *.
        tauto.
      apply (proj2 H6).
      apply (proj2 H2).
      apply H5.
      assert (In B (SequenceConstruction bs (S n')) b').
        simpl.
        apply fact_3_of_1_2_8.
        apply Union_intror.
        apply (InConstruction).
        subst.
        apply H4.
        subst.
        apply CBA_AXM_1.
      apply (InInfiniteConstruction bs (S n') b').
      apply H5.
    Qed.

    Definition isUltraFilter (bs : Ensemble B) :=
      forall bs1 : Ensemble B, isFilter bs1 -> equiconsistent bs bs1 -> Included B bs bs1 -> Included B bs1 bs
    .

    Corollary corollary_1_2_16 :
      forall bs : Ensemble B,
      isFilter bs ->
      isUltraFilter (InfiniteConstruction bs).
    Proof.
      intros bs H.
      intros bs1 H0 H1 H2.
      intros b H3.
      assert (equiconsistent (InfiniteConstruction bs) (Closure (Add B (InfiniteConstruction bs) b))).
        constructor.
        intro.
        apply fact_3_of_1_2_8.
        apply Union_introl.
        apply H4.
        intro.
        assert (inconsistent (Closure bs1)).
          apply (fact_4_of_1_2_8 (Add B (InfiniteConstruction bs) b) bs1).
          intros b'.
          intro.
          inversion H5.
          subst.
          apply (H2 b' H6).
          inversion H6.
          subst.
          apply H3.
          apply H4.
        apply (proj2 H1).
        assert (Included B (Closure bs1) bs1).
          apply fact_5_of_1_2_8.
          apply H0.
        apply (H6 falseB H5).
      destruct (theorem_1_2_14 bs H).
      destruct H6.
      unfold complete in *.
      unfold element_complete in *.
      apply (H7 b).
      apply H4.
    Qed.

  End BooleanAlgebra.

  Section Semantics.

    Definition satisfies (structure : Formula -> Prop) (p : Formula) : Prop :=
      structure p
    .

    Definition preservesContradiction (structure : Formula -> Prop) : Prop :=
      satisfies structure ContradictionF <-> (False)
    .

    Definition preservesNegation (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, satisfies structure (NegationF p1) <-> (~ satisfies structure p1)
    .

    Definition preservesConjunction (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (ConjunctionF p1 p2) <-> (satisfies structure p1 /\ satisfies structure p2)
    .

    Definition preservesDisjunction (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (DisjunctionF p1 p2) <-> (satisfies structure p1 \/ satisfies structure p2)
    .

    Definition preservesImplication (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (ImplicationF p1 p2) <-> (satisfies structure p1 -> satisfies structure p2)
    .

    Definition preservesBiconditional (structure : Formula -> Prop) : Prop :=
      forall p1 : Formula, forall p2 : Formula, satisfies structure (BiconditionalF p1 p2) <-> (satisfies structure p1 <-> satisfies structure p2)
    .

    Definition isStructure (structure : Formula -> Prop) : Prop :=
      preservesContradiction structure /\ preservesNegation structure /\ preservesConjunction structure /\ preservesDisjunction structure /\ preservesImplication structure /\ preservesBiconditional structure /\ (forall p1 : Formula, satisfies structure (NegationF (NegationF p1)) -> satisfies structure p1)
    .

    Definition entails (hs : Ensemble Formula) (c : Formula) : Prop :=
      forall structure : Formula -> Prop, isStructure structure -> (forall h : Formula, In Formula hs h -> satisfies structure h) -> satisfies structure c 
    .

    Lemma extend_entails :
      forall hs1 : Ensemble Formula,
      forall c : Formula,
      entails hs1 c ->
      forall hs2 : Ensemble Formula,
      Included Formula hs1 hs2 ->
      entails hs2 c.
    Proof.
      intros hs1 c.
      intro.
      intros hs2.
      intro.
      intros structure.
      intro.
      intro.
      apply H.
      apply H1.
      intros h.
      intro.
      apply H2.
      apply H0.
      apply H3.
    Qed.

  End Semantics.

  Section InferenceRules.

    Inductive infers : Ensemble Formula -> Formula -> Prop :=
    | Assumption :
      forall hs : Ensemble Formula,
      forall h : Formula,
      In Formula hs h ->
      infers hs h
    | ContradictionI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      infers hs a ->
      infers hs (NegationF a) ->
      infers hs ContradictionF
    | ContradictionE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      infers hs ContradictionF ->
      infers hs a
    | NegationI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      infers (Add Formula hs a) ContradictionF ->
      infers hs (NegationF a)
    | NegationE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      infers (Add Formula hs (NegationF a)) ContradictionF ->
      infers hs a
    | ConjunctionI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs a ->
      infers hs b ->
      infers hs (ConjunctionF a b)
    | ConjunctionE1 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs (ConjunctionF a b) ->
      infers hs a
    | ConjunctionE2 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs (ConjunctionF a b) ->
      infers hs b
    | DisjunctionI1 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs a ->
      infers hs (DisjunctionF a b)
    | DisjunctionI2 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs b ->
      infers hs (DisjunctionF a b)
    | DisjunctionE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      forall c : Formula,
      infers hs (DisjunctionF a b) ->
      infers (Add Formula hs a) c ->
      infers (Add Formula hs b) c ->
      infers hs c
    | ImplicationI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers (Add Formula hs a) b ->
      infers hs (ImplicationF a b)
    | ImplicationE :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs (ImplicationF a b) ->
      infers hs a ->
      infers hs b
    | BiconditionalI :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers (Add Formula hs a) b ->
      infers (Add Formula hs b) a ->
      infers hs (BiconditionalF a b)
    | BiconditionalE1 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs (BiconditionalF a b) ->
      infers hs a ->
      infers hs b
    | BiconditionalE2 :
      forall hs : Ensemble Formula,
      forall a : Formula,
      forall b : Formula,
      infers hs (BiconditionalF a b) ->
      infers hs b ->
      infers hs a
    .

    Example exclusive_middle :
      forall p : Formula,
      infers (Empty_set Formula) (DisjunctionF p (NegationF p)).
    Proof.
      intros p.
      apply (NegationE (Empty_set Formula) (DisjunctionF p (NegationF p))).
      apply (ContradictionI (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) (DisjunctionF p (NegationF p))).
      apply (DisjunctionI2 (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) p (NegationF p)).
      apply (NegationI (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) p).
      apply (ContradictionI (Add Formula (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) p) (DisjunctionF p (NegationF p))).
      apply (DisjunctionI1 (Add Formula (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) p) p (NegationF p)).
      apply (Assumption (Add Formula (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) p) p).
      apply Union_intror.
      apply In_singleton.
      apply (Assumption (Add Formula (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) p) (NegationF (DisjunctionF p (NegationF p)))).
      apply Union_introl.
      apply Union_intror.
      apply In_singleton.
      apply (Assumption (Add Formula (Empty_set Formula) (NegationF (DisjunctionF p (NegationF p)))) (NegationF (DisjunctionF p (NegationF p)))).
      apply Union_intror.
      apply In_singleton.
    Qed.

    Lemma cut_property :
      forall hs : Ensemble Formula,
      forall p1 : Formula,
      forall p2 : Formula,
      infers hs p1 ->
      infers (Add Formula hs p1) p2 ->
      infers hs p2.
    Proof.
      intros hs p1 p2.
      intro.
      intro.
      assert (infers hs (ImplicationF p1 p2)).
        apply (ImplicationI hs p1 p2 H0).
      apply (ImplicationE hs p1 p2 H1 H).
    Qed.

  End InferenceRules.

  Section Soundness.

    Lemma extend_infers :
      forall hs1 : Ensemble Formula,
      forall c : Formula,
      infers hs1 c ->
      forall hs2 : Ensemble Formula,
      Included Formula hs1 hs2 ->
      infers hs2 c.
    Proof.
      intros hs1 c.
      intro.
      induction H.
      - intros hs2.
        intro.
        apply (Assumption hs2 h).
        apply (H0 h H).
      - intros hs2.
        intro.
        apply (ContradictionI hs2 a).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (ContradictionE hs2 a).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (NegationI hs2 a).
        apply (IHinfers (Add Formula hs2 a)).
        apply Included_Add.
        apply H0.
      - intros hs2.
        intro.
        apply (NegationE hs2 a).
        apply (IHinfers (Add Formula hs2 (NegationF a))).
        apply Included_Add.
        apply H0.
      - intros hs2.
        intro.
        apply (ConjunctionI hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (ConjunctionE1 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (ConjunctionE2 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (DisjunctionI1 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (DisjunctionI2 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (DisjunctionE hs2 a b c).
        apply (IHinfers1 hs2 H2).
        apply (IHinfers2 (Add Formula hs2 a)).
        apply Included_Add.
        apply H2.
        apply (IHinfers3 (Add Formula hs2 b)).
        apply Included_Add.
        apply H2.
      - intros hs2.
        intro.
        apply (ImplicationI hs2 a b).
        apply (IHinfers (Add Formula hs2 a)).
        apply Included_Add.
        apply H0.
      - intros hs2.
        intro.
        apply (ImplicationE hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (BiconditionalI hs2 a b).
        apply (IHinfers1 (Add Formula hs2 a)).
        apply Included_Add.
        apply H1.
        apply (IHinfers2 (Add Formula hs2 b)).
        apply Included_Add.
        apply H1.
      - intros hs2.
        intro.
        apply (BiconditionalE1 hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (BiconditionalE2 hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
    Qed.

    Lemma Assumption_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      In Formula hs a ->
      entails hs a.
    Proof.
      intros hs c H.
      apply (extend_entails (Singleton Formula c) c).
      intros v.
      intros.
      apply H1.
      apply In_singleton.
      intros h.
      intro.
      inversion H0.
      subst.
      apply H.
    Qed.

    Lemma ContradictionI_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      entails hs a ->
      entails hs (NegationF a) ->
      entails hs ContradictionF.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesNegation v).
        unfold isStructure in H1.
        intuition.
      assert (satisfies v a).
        apply (H v H1 H2).
      assert (satisfies v (NegationF a)).
        apply (H0 v H1 H2).
      contradiction (proj1 (H3 a)).
    Qed.

    Lemma ContradictionE_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      entails hs ContradictionF ->
      entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesContradiction v).
        unfold isStructure in H0.
        intuition.
      assert (satisfies v ContradictionF).
        apply (H v H0 H1).
      contradiction (proj1 H2).
    Qed.

    Lemma NegationI_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      entails (Add Formula hs a) ContradictionF ->
      entails hs (NegationF a).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesNegation v).
        unfold isStructure in H0.
        intuition.
      assert (preservesContradiction v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a)).
      intro.
      assert (satisfies v ContradictionF).
        apply (H v).
        apply H0.
        intros h.
        intro.
        inversion H5.
        subst.
        apply (H1 h H6).
        subst.
        inversion H6.
        subst.
        apply H4.
      contradiction (proj1 H3).
    Qed.

    Lemma NegationE_preserves :
      forall hs : Ensemble Formula,
      forall a : Formula,
      entails (Add Formula hs (NegationF a)) ContradictionF ->
      entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesNegation v).
        unfold isStructure in H0.
        intuition.
      assert (preservesContradiction v).
        unfold isStructure in H0.
        intuition.
      assert (forall p1 : Formula, satisfies v (NegationF (NegationF p1)) -> satisfies v p1).
        unfold isStructure in H0.
        intuition.
      apply (H4 a).
      apply (NegationI_preserves hs (NegationF a)).
      apply H.
      apply H0.
      apply H1.
    Qed.

    Lemma ConjunctionI_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs a ->
      entails hs b ->
      entails hs (ConjunctionF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesConjunction v).
        unfold isStructure in H1.
        intuition.
      apply (proj2 (H3 a b)).
      constructor.
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Lemma ConjunctionE1_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs (ConjunctionF a b) ->
      entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesConjunction v).
        unfold isStructure in H0.
        intuition.
      destruct (proj1 (H2 a b)).
        apply H.
        apply H0.
        apply H1.
      apply H3.
    Qed.

    Lemma ConjunctionE2_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs (ConjunctionF a b) ->
      entails hs b.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesConjunction v).
        unfold isStructure in H0.
        intuition.
      destruct (proj1 (H2 a b)).
        apply H.
        apply H0.
        apply H1.
      apply H4.
    Qed.

    Lemma DisjunctionI1_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs a ->
      entails hs (DisjunctionF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesDisjunction v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a b)).
      apply or_introl.
      apply H.
      apply H0.
      apply H1.
    Qed.

    Lemma DisjunctionI2_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs b ->
      entails hs (DisjunctionF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesDisjunction v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a b)).
      apply or_intror.
      apply H.
      apply H0.
      apply H1.
    Qed.

    Lemma DisjunctionE_preserves :
      forall hs : Ensemble Formula,
      forall a b c : Formula,
      entails hs (DisjunctionF a b) ->
      entails (Add Formula hs a) c ->
      entails (Add Formula hs b) c ->
      entails hs c.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesDisjunction v).
        unfold isStructure in H2.
        intuition.
      assert (satisfies v a \/ satisfies v b).
        apply (proj1 (H4 a b)).
        apply H.
        apply H2.
        apply H3.
      destruct H5.
      apply H0.
      apply H2.
      intros h.
      intro.
      inversion H6.
      subst.
      apply H3.
      apply H7.
      subst.
      inversion H7.
      subst.
      apply H5.
      apply H1.
      apply H2.
      intros h.
      intro.
      inversion H6.
      subst.
      apply H3.
      apply H7.
      subst.
      inversion H7.
      subst.
      apply H5.
    Qed.

    Lemma ImplicationI_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails (Add Formula hs a) b ->
      entails hs (ImplicationF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesImplication v).
        unfold isStructure in H0.
        intuition.
      apply (proj2 (H2 a b)).
      intro.
      apply H.
      apply H0.
      intros h.
      intro.
      inversion H4.
      subst.
      apply (H1 h).
      apply H5.
      inversion H5.
      subst.
      apply H3.
    Qed.

    Lemma ImplicationE_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs (ImplicationF a b) ->
      entails hs a ->
      entails hs b.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesImplication v).
        unfold isStructure in H1.
        intuition.
      apply (proj1 (H3 a b)).
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Lemma BiconditionalI_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails (Add Formula hs a) b ->
      entails (Add Formula hs b) a ->
      entails hs (BiconditionalF a b).
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesBiconditional v).
        unfold isStructure in H1.
        intuition.
      apply (proj2 (H3 a b)).
      constructor.
      intro.
      apply H.
      apply H1.
      intros h.
      intro.
      inversion H5.
      subst.
      apply (H2 h).
      apply H6.
      inversion H6.
      subst.
      apply H4.
      intro.
      apply H0.
      apply H1.
      intros h.
      intro.
      inversion H5.
      subst.
      apply (H2 h).
      apply H6.
      inversion H6.
      subst.
      apply H4.
    Qed.

    Lemma BiconditionalE1_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs (BiconditionalF a b) ->
      entails hs a ->
      entails hs b.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesBiconditional v).
        unfold isStructure in H1.
        intuition.
      apply (proj1 (H3 a b)).
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Lemma BiconditionalE2_preserves :
      forall hs : Ensemble Formula,
      forall a b : Formula,
      entails hs (BiconditionalF a b) ->
      entails hs b ->
      entails hs a.
    Proof.
      intros.
      intros v.
      intros.
      assert (preservesBiconditional v).
        unfold isStructure in H1.
        intuition.
      apply (proj1 (H3 a b)).
      apply H.
      apply H1.
      apply H2.
      apply H0.
      apply H1.
      apply H2.
    Qed.

    Theorem Soundness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      infers hs c ->
      entails hs c.
    Proof.
      intros hs c H.
      induction H.
      - apply (Assumption_preserves hs h H).
      - apply (ContradictionI_preserves hs a IHinfers1 IHinfers2).
      - apply (ContradictionE_preserves hs a IHinfers).
      - apply (NegationI_preserves hs a IHinfers).
      - apply (NegationE_preserves hs a IHinfers).
      - apply (ConjunctionI_preserves hs a b IHinfers1 IHinfers2).
      - apply (ConjunctionE1_preserves hs a b IHinfers).
      - apply (ConjunctionE2_preserves hs a b IHinfers).
      - apply (DisjunctionI1_preserves hs a b IHinfers).
      - apply (DisjunctionI2_preserves hs a b IHinfers).
      - apply (DisjunctionE_preserves hs a b c IHinfers1 IHinfers2 IHinfers3).
      - apply (ImplicationI_preserves hs a b IHinfers).
      - apply (ImplicationE_preserves hs a b IHinfers1 IHinfers2).
      - apply (BiconditionalI_preserves hs a b IHinfers1 IHinfers2).
      - apply (BiconditionalE1_preserves hs a b IHinfers1 IHinfers2).
      - apply (BiconditionalE2_preserves hs a b IHinfers1 IHinfers2).
    Qed.

  End Soundness.

  Section Completeness.

    Program Instance LindenbaumBooleanAlgebra : CountableBooleanAlgebra Formula :=
      { eqB := fun p1 : Formula => fun p2 : Formula => infers (Singleton Formula p1) p2 /\ infers (Singleton Formula p2) p1
      ; trueB := NegationF ContradictionF
      ; falseB := ContradictionF
      ; andB := ConjunctionF
      ; enumB := enumerateFormula
      }
    .
    Next Obligation.
      constructor.
      apply Assumption.
      apply In_singleton.
      apply Assumption.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply (cut_property (Singleton Formula b1) b2 b3).
      apply H.
      apply (extend_infers (Singleton Formula b2) b3 H0).
      intros b.
      intro.
      inversion H3.
      subst.
      apply Union_intror.
      apply In_singleton.
      apply (cut_property (Singleton Formula b3) b2 b1).
      apply H1.
      apply (extend_infers (Singleton Formula b2) b1 H2).
      intros b.
      intro.
      inversion H3.
      subst.
      apply Union_intror.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply (cut_property (Singleton Formula (ConjunctionF b1 b2)) b1).
      apply (ConjunctionE1 _ _ b2).
      apply Assumption.
      apply In_singleton.
      apply (extend_infers (Singleton Formula b1) b1' H).
      intros h.
      intro.
      inversion H3.
      subst.
      apply Union_intror.
      apply In_singleton.
      apply (cut_property (Singleton Formula (ConjunctionF b1 b2)) b2).
      apply (ConjunctionE2 _ b1 _).
      apply Assumption.
      apply In_singleton.
      apply (extend_infers (Singleton Formula b2) b2' H0).
      intros h.
      intro.
      inversion H3.
      subst.
      apply Union_intror.
      apply In_singleton.
      apply ConjunctionI.
      apply (cut_property (Singleton Formula (ConjunctionF b1' b2')) b1').
      apply (ConjunctionE1 _ _ b2').
      apply Assumption.
      apply In_singleton.
      apply (extend_infers (Singleton Formula b1') b1 H2).
      intros h.
      intro.
      inversion H3.
      subst.
      apply Union_intror.
      apply In_singleton.
      apply (cut_property (Singleton Formula (ConjunctionF b1' b2')) b2').
      apply (ConjunctionE2 _ b1' _).
      apply Assumption.
      apply In_singleton.
      apply (extend_infers (Singleton Formula b2') b2 H1).
      intros h.
      intro.
      inversion H3.
      subst.
      apply Union_intror.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply (ConjunctionE1 _ b1 b1).
      apply Assumption.
      apply In_singleton.
      apply ConjunctionI.
      apply Assumption.
      apply In_singleton.
      apply Assumption.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply (ConjunctionE2 _ b1 b2).
      apply Assumption.
      apply In_singleton.
      apply (ConjunctionE1 _ b1 b2).
      apply Assumption.
      apply In_singleton.
      apply ConjunctionI.
      apply (ConjunctionE2 _ b2 b1).
      apply Assumption.
      apply In_singleton.
      apply (ConjunctionE1 _ b2 b1).
      apply Assumption.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply ConjunctionI.
      apply ConjunctionI.
      apply (ConjunctionE1 _ b1 (ConjunctionF b2 b3)).
      apply Assumption.
      apply In_singleton.
      apply (ConjunctionE1 _ b2 b3).
      apply (ConjunctionE2 _ b1 (ConjunctionF b2 b3)).
      apply Assumption.
      apply In_singleton.
      apply (ConjunctionE2 _ b2 b3).
      apply (ConjunctionE2 _ b1 (ConjunctionF b2 b3)).
      apply Assumption.
      apply In_singleton.
      apply ConjunctionI.
      apply (ConjunctionE1 _ b1 b2).
      apply (ConjunctionE1 _ (ConjunctionF b1 b2) b3).
      apply Assumption.
      apply In_singleton.
      apply ConjunctionI.
      apply (ConjunctionE2 _ b1 b2).
      apply (ConjunctionE1 _ (ConjunctionF b1 b2) b3).
      apply Assumption.
      apply In_singleton.
      apply (ConjunctionE2 _ (ConjunctionF b1 b2) b3).
      apply Assumption.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply (ConjunctionE1 _ ContradictionF b1).
      apply Assumption.
      apply In_singleton.
      apply (ContradictionE _ (ConjunctionF ContradictionF b1)).
      apply Assumption.
      apply In_singleton.
    Qed.
    Next Obligation.
      constructor.
      apply (ConjunctionE2 _ (NegationF ContradictionF) b1).
      apply Assumption.
      apply In_singleton.
      apply ConjunctionI.
      apply NegationI.
      apply Assumption.
      apply Union_intror.
      apply In_singleton.
      apply Assumption.
      apply In_singleton.
    Qed.
    Next Obligation.
      apply (Formula_is_enumerable b1).
    Qed.

    Lemma infers_has_compactness :
      forall hs : Ensemble Formula,
      forall c : Formula,
      infers hs c ->
      exists hs' : Ensemble Formula, (forall h : Formula, In Formula hs' h \/ ~ In Formula hs' h) /\ Included Formula hs' hs /\ infers hs' c /\ (exists bound : nat, forall h : Formula, In Formula hs' h -> exists n : nat, enumerateFormula n = h /\ n < bound).
    Proof.
      intros hs c H.
      induction H.
      - exists (Singleton Formula h).
        constructor.
        intros p.
        destruct (eq_Formula_dec h p).
        apply or_introl.
        subst.
        apply In_singleton.
        apply or_intror.
        intro.
        subst.
        inversion H0.
        apply (n H1).
        constructor.
        intros p.
        intro.
        inversion H0.
        subst.
        apply H.
        constructor.
        apply (Assumption (Singleton Formula h) h).
        apply In_singleton.
        destruct (Formula_is_enumerable h) as [n H0].
        exists (S n).
        intros h0.
        intro.
        inversion H1.
        exists n.
        subst.
        constructor.
        tauto.
        lia.
      - destruct IHinfers1 as [hs1' H1].
        destruct IHinfers2 as [hs2' H2].
        destruct H1 as [HHH1].
        destruct H2 as [HHH2].
        exists (Union Formula hs1' hs2').
        constructor.
        intros h.
        destruct (HHH1 h).
        apply or_introl.
        apply Union_introl.
        apply H3.
        destruct (HHH2 h).
        apply or_introl.
        apply Union_intror.
        apply H4.
        apply or_intror.
        intro.
        inversion H5.
        subst.
        apply (H3 H6).
        subst.
        apply (H4 H6).
        destruct H1.
        destruct H3.
        destruct H2.
        destruct H5.
        constructor.
        intros p.
        intro.
        inversion H7.
        subst.
        apply (H1 p H8).
        subst.
        apply (H2 p H8).
        constructor.
        apply (ContradictionI (Union Formula hs1' hs2') a).
        apply (extend_infers hs1' a H3 (Union Formula hs1' hs2')).
        intros p.
        intro.
        apply Union_introl.
        apply H7.
        apply (extend_infers hs2' (NegationF a) H5 (Union Formula hs1' hs2')).
        intros p.
        intro.
        apply Union_intror.
        apply H7.
        destruct H4 as [bound1].
        destruct H6 as [bound2].
        exists (max bound1 bound2).
        intros p.
        intro.
        inversion H7.
        subst.
        destruct (H4 p H8) as [n].
        exists n.
        destruct H9.
        constructor.
        apply H9.
        lia.
        subst.
        destruct (H6 p H8) as [n].
        exists n.
        destruct H9.
        constructor.
        apply H9.
        lia.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists hs1.
        constructor.
        apply HHH1.
        constructor.
        apply H0.
        constructor.
        apply (ContradictionE hs1 a).
        apply H1.
        destruct H2 as [bound1].
        exists bound1.
        apply H2.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists (Subtract Formula hs1 a).
        constructor.
        intros h.
        destruct (eq_Formula_dec a h).
        apply or_intror.
        intro.
        inversion H3.
        subst.
        apply H5.
        apply In_singleton.
        destruct (HHH1 h).
        apply or_introl.
        constructor.
        apply H3.
        intro.
        inversion H4.
        apply (n H5).
        apply or_intror.
        intro.
        inversion H4.
        apply (H3 H5).
        assert (Included Formula (Subtract Formula hs1 a) hs).
          intros p.
          intro.
          inversion H3.
          assert (In Formula (Add Formula hs a) p).
            apply H0.
            apply H4.
          inversion H6.
          subst.
          apply H7.
          tauto.
        constructor.
        apply H3.
        assert (Included Formula hs1 (Add Formula (Subtract Formula hs1 a) a)).
          intros p.
          intro.
          destruct (eq_Formula_dec a p).
            subst.
            apply Union_intror.
            apply In_singleton.
            apply Union_introl.
            constructor.
            apply H4.
            intro.
            inversion H5.
            tauto.
        constructor.
        apply (NegationI (Subtract Formula hs1 a) a).
        apply (extend_infers hs1 ContradictionF H1 (Add Formula (Subtract Formula hs1 a) a) H4).
        destruct H2 as [bound1].
        exists bound1.
        intros h.
        intro.
        apply (H2 h).
        inversion H5.
        apply H6.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists (Subtract Formula hs1 (NegationF a)).
        constructor.
        intros h.
        destruct (eq_Formula_dec (NegationF a) h).
        apply or_intror.
        intro.
        inversion H3.
        subst.
        apply H5.
        apply In_singleton.
        destruct (HHH1 h).
        apply or_introl.
        constructor.
        apply H3.
        intro.
        inversion H4.
        apply (n H5).
        apply or_intror.
        intro.
        inversion H4.
        apply (H3 H5).
        assert (Included Formula (Subtract Formula hs1 (NegationF a)) hs).
          intros h.
          intro.
          inversion H3.
          assert (In Formula (Add Formula hs (NegationF a)) h).
            apply (H0 h H4).
          inversion H6.
          subst.
          apply H7.
          subst.
          contradiction H5.
        constructor.
        apply H3.
        assert (Included Formula hs1 (Add Formula (Subtract Formula hs1 (NegationF a)) (NegationF a))).
          intros p.
          intro.
          destruct (eq_Formula_dec (NegationF a) p).
            subst.
            apply Union_intror.
            apply In_singleton.
            apply Union_introl.
            constructor.
            apply H4.
            intro.
            inversion H5.
            tauto.
        constructor.
        apply (NegationE (Subtract Formula hs1 (NegationF a)) a).
        apply (extend_infers hs1 ContradictionF H1 (Add Formula (Subtract Formula hs1 (NegationF a)) (NegationF a)) H4).
        destruct H2 as [bound1].
        exists bound1.
        intros h.
        intro.
        apply (H2 h).
        inversion H5.
        apply H6.
      - destruct IHinfers1 as [hs1].
        destruct IHinfers2 as [hs2].
        destruct H1 as [HHH1].
        destruct H2 as [HHH2].
        destruct H1.
        destruct H3.
        destruct H2.
        destruct H5.
        exists (Union Formula hs1 hs2).
        constructor.
        intros h.
        destruct (HHH1 h).
        apply or_introl.
        apply Union_introl.
        apply H7.
        destruct (HHH2 h).
        apply or_introl.
        apply Union_intror.
        apply H8.
        apply or_intror.
        intro.
        inversion H9.
        subst.
        apply (H7 H10).
        subst.
        apply (H8 H10).
        assert (Included Formula hs1 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_introl.
          apply H7.
        assert (Included Formula hs2 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_intror.
          apply H8.
        constructor.
        intros p.
        intro.
        inversion H9.
        subst.
        apply (H1 p H10).
        subst.
        apply (H2 p H10).
        constructor.
        apply (ConjunctionI (Union Formula hs1 hs2) a b).
        apply (extend_infers hs1 a H3 (Union Formula hs1 hs2) H7).
        apply (extend_infers hs2 b H5 (Union Formula hs1 hs2) H8).
        destruct H4 as [bound1].
        destruct H6 as [bound2].
        exists (max bound1 bound2).
        intros h.
        intro.
        inversion H9.
        subst.
        destruct (H4 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
        subst.
        destruct (H6 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists hs1.
        constructor.
        apply HHH1.
        constructor.
        apply H0.
        constructor.
        apply (ConjunctionE1 hs1 a b H1).
        apply H2.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists hs1.
        constructor.
        apply HHH1.
        constructor.
        apply H0.
        constructor.
        apply (ConjunctionE2 hs1 a b H1).
        apply H2.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists hs1.
        constructor.
        apply HHH1.
        constructor.
        apply H0.
        constructor.
        apply (DisjunctionI1 hs1 a b H1).
        apply H2.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists hs1.
        constructor.
        apply HHH1.
        constructor.
        apply H0.
        constructor.
        apply (DisjunctionI2 hs1 a b H1).
        apply H2.
      - destruct IHinfers1 as [hs1].
        destruct IHinfers2 as [hs2].
        destruct IHinfers3 as [hs3].
        destruct H2 as [HHH1].
        destruct H3 as [HHH2].
        destruct H4 as [HHH3].
        destruct H2.
        destruct H5.
        destruct H3.
        destruct H7.
        destruct H4.
        destruct H9.
        exists (Union Formula hs1 (Union Formula (Subtract Formula hs2 a) (Subtract Formula hs3 b))).
        constructor.
        intros h.
        destruct (HHH1 h).
        apply or_introl.
        apply Union_introl.
        apply H11.
        destruct (HHH2 h).
        destruct (eq_Formula_dec a h).
        destruct (HHH3 h).
        destruct (eq_Formula_dec b h).
        apply or_intror.
        intro.
        inversion H14.
        subst.
        contradiction H11.
        subst.
        inversion H15.
        subst.
        inversion H16.
        apply H18.
        apply In_singleton.
        subst.
        inversion H16.
        apply H18.
        apply In_singleton.
        apply or_introl.
        apply Union_intror.
        apply Union_intror.
        constructor.
        apply H13.
        intro.
        contradiction n.
        inversion H14.
        tauto.
        apply or_intror.
        intro.
        inversion H14.
        subst.
        contradiction H11.
        subst.
        inversion H15.
        subst.
        inversion H16.
        contradiction H18.
        apply In_singleton.
        subst.
        inversion H16.
        contradiction H13.
        apply or_introl.
        apply Union_intror.
        apply Union_introl.
        constructor.
        apply H12.
        intro.
        inversion H13.
        contradiction n.
        destruct (HHH3 h).
        destruct (eq_Formula_dec b h).
        apply or_intror.
        intro.
        inversion H14.
        subst.
        contradiction H11.
        subst.
        inversion H15.
        subst.
        inversion H16.
        contradiction H12.
        subst.
        inversion H16.
        contradiction H18.
        apply In_singleton.
        apply or_introl.
        apply Union_intror.
        apply Union_intror.
        constructor.
        apply H13.
        intro.
        inversion H14.
        contradiction H15.
        apply or_intror.
        intro.
        inversion H14.
        contradiction H11.
        inversion H15.
        subst.
        inversion H17.
        contradiction H12.
        subst.
        inversion H17.
        contradiction H13.
        assert (Included Formula hs2 (Add Formula (Subtract Formula hs2 a) a)).
          intros p.
          intro.
          destruct (eq_Formula_dec a p).
          subst.
          apply Union_intror.
          apply In_singleton.
          apply Union_introl.
          constructor.
          apply H11.
          intro.
          inversion H12.
          tauto.
        assert (Included Formula hs3 (Add Formula (Subtract Formula hs3 b) b)).
          intros p.
          intro.
          destruct (eq_Formula_dec b p).
          subst.
          apply Union_intror.
          apply In_singleton.
          apply Union_introl.
          constructor.
          apply H12.
          intro.
          inversion H13.
          tauto.
        assert (Included Formula (Union Formula hs1 (Union Formula (Subtract Formula hs2 a) (Subtract Formula hs3 b))) hs).
          intros p.
          intro.
          inversion H13.
          subst.
          apply (H2 p H14).
          inversion H14.
          subst.
          inversion H16.
          assert (In Formula (Add Formula hs a) p).
            apply (H3 p H15).
          inversion H18.
          subst.
          apply H19.
          subst.
          tauto.
          subst.
          inversion H16.
          assert (In Formula (Add Formula hs b) p).
            apply (H4 p H15).
          inversion H18.
          subst.
          apply H19.
          subst.
          tauto.
        constructor.
        apply H13.
        constructor.
        apply (DisjunctionE (Union Formula hs1 (Union Formula (Subtract Formula hs2 a) (Subtract Formula hs3 b))) a b c).
        apply (extend_infers hs1 (DisjunctionF a b) H5).
        intros p.
        intro.
        apply Union_introl.
        apply H14.
        apply (extend_infers hs2 c H7).
        intros p.
        intro.
        destruct (eq_Formula_dec a p).
          subst.
          apply Union_intror.
          apply In_singleton.
          apply Union_introl.
          apply Union_intror.
          apply Union_introl.
          constructor.
          apply H14.
          intro.
          inversion H15.
          tauto.
        apply (extend_infers hs3 c H9).
        intros p.
        intro.
        destruct (eq_Formula_dec b p).
          subst.
          apply Union_intror.
          apply In_singleton.
          apply Union_introl.
          apply Union_intror.
          apply Union_intror.
          constructor.
          apply H14.
          intro.
          inversion H15.
          tauto.
        destruct H6 as [bound1].
        destruct H8 as [bound2].
        destruct H10 as [bound3].
        exists (max bound1 (max bound2 bound3)).
        intros h.
        intro.
        inversion H14.
        subst.
        destruct (H6 h H15) as [n].
        exists n.
        destruct H16.
        constructor.
        tauto.
        lia.
        inversion H15.
        subst.
        destruct (H8 h) as [n].
          destruct H17.
          apply H16.
        destruct H16.
        exists n.
        constructor.
        tauto.
        lia.
        subst.
        destruct (H10 h) as [n].
          destruct H17.
          apply H16.
        destruct H16.
        exists n.
        constructor.
        tauto.
        lia.
      - destruct IHinfers as [hs1].
        destruct H0 as [HHH1].
        destruct H0.
        destruct H1.
        exists (Subtract Formula hs1 a).
        constructor.
        intros h.
        destruct (HHH1 h).
        destruct (eq_Formula_dec a h).
        apply or_intror.
        intro.
        inversion H4.
        apply H6.
        subst.
        apply In_singleton.
        apply or_introl.
        constructor.
        apply H3.
        intro.
        inversion H4.
        apply (n H5).
        apply or_intror.
        intro.
        apply H3.
        inversion H4.
        apply H5.
        assert (Included Formula (Subtract Formula hs1 a) hs).
          intros p.
          intro.
          inversion H3.
          assert (In Formula (Add Formula hs a) p).
            apply H0.
            apply H4.
          inversion H6.
          subst.
          apply H7.
          tauto.
        constructor.
        apply H3.
        assert (Included Formula hs1 (Add Formula (Subtract Formula hs1 a) a)).
          intros p.
          intro.
          destruct (eq_Formula_dec a p).
            subst.
            apply Union_intror.
            apply In_singleton.
            apply Union_introl.
            constructor.
            apply H4.
            intro.
            inversion H5.
            tauto.
        constructor.
        apply (ImplicationI (Subtract Formula hs1 a) a).
        apply (extend_infers hs1 b H1 (Add Formula (Subtract Formula hs1 a) a) H4).
        destruct H2 as [bound1].
        exists bound1.
        intros h.
        intro.
        apply (H2 h).
        inversion H5.
        apply H6.
      - destruct IHinfers1 as [hs1].
        destruct IHinfers2 as [hs2].
        destruct H1 as [HHH1].
        destruct H2 as [HHH2].
        destruct H1.
        destruct H3.
        destruct H2.
        destruct H5.
        exists (Union Formula hs1 hs2).
        constructor.
        intros h.
        destruct (HHH1 h).
        apply or_introl.
        apply Union_introl.
        apply H7.
        destruct (HHH2 h).
        apply or_introl.
        apply Union_intror.
        apply H8.
        apply or_intror.
        intro.
        inversion H9.
        subst.
        contradiction H7.
        subst.
        contradiction H8.
        assert (Included Formula hs1 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_introl.
          apply H7.
        assert (Included Formula hs2 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_intror.
          apply H8.
        constructor.
        intros p.
        intro.
        inversion H9.
        subst.
        apply (H1 p H10).
        subst.
        apply (H2 p H10).
        constructor.
        apply (ImplicationE (Union Formula hs1 hs2) a b).
        apply (extend_infers hs1 (ImplicationF a b) H3 (Union Formula hs1 hs2) H7).
        apply (extend_infers hs2 a H5 (Union Formula hs1 hs2) H8).
        destruct H4 as [bound1].
        destruct H6 as [bound2].
        exists (max bound1 bound2).
        intros h.
        intro.
        inversion H9.
        subst.
        destruct (H4 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
        subst.
        destruct (H6 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
      - destruct IHinfers1 as [hs1].
        destruct IHinfers2 as [hs2].
        destruct H1 as [HHH1].
        destruct H2 as [HHH2].
        destruct H1.
        destruct H3.
        destruct H2.
        destruct H5.
        exists (Union Formula (Subtract Formula hs1 a) (Subtract Formula hs2 b)).
        constructor.
        intros h.
        destruct (HHH1 h).
        destruct (eq_Formula_dec a h).
        destruct (HHH2 h).
        destruct (eq_Formula_dec b h).
        subst.
        apply or_intror.
        intro.
        inversion H9.
        inversion H10.
        contradiction H13.
        apply In_singleton.
        inversion H10.
        contradiction H13.
        apply In_singleton.
        apply or_introl.
        apply Union_intror.
        constructor.
        apply H8.
        intro.
        inversion H9.
        contradiction n.
        apply or_intror.
        intro.
        inversion H9.
        subst.
        inversion H10.
        apply H12.
        apply In_singleton.
        subst.
        inversion H10.
        subst.
        contradiction H11.
        apply or_introl.
        apply Union_introl.
        constructor.
        apply H7.
        intro.
        inversion H8.
        contradiction n.
        destruct (HHH2 h).
        destruct (eq_Formula_dec b h).
        apply or_intror.
        intro.
        inversion H9.
        subst.
        inversion H10.
        contradiction H7.
        subst.
        inversion H10.
        apply H12.
        apply In_singleton.
        apply or_introl.
        apply Union_intror.
        constructor.
        apply H8.
        intro.
        inversion H9.
        contradiction n.
        apply or_intror.
        intro.
        inversion H9.
        subst.
        inversion H10.
        contradiction H7.
        subst.
        inversion H10.
        contradiction H8.
        assert (Included Formula hs1 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_introl.
          apply H7.
        assert (Included Formula hs2 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_intror.
          apply H8.
        constructor.
        intros p.
        intro.
        inversion H9.
        destruct (eq_Formula_dec a p).
        inversion H10.
        contradiction H13.
        rewrite e.
        apply In_singleton.
        subst.
        assert (In Formula (Add Formula hs a) p).
        apply (H1 p (proj1 H10)).
        inversion H11.
        apply H12.
        inversion H12.
        tauto.
        destruct (eq_Formula_dec b p).
        inversion H10.
        contradiction H13.
        rewrite e.
        apply In_singleton.
        subst.
        assert (In Formula (Add Formula hs b) p).
        apply (H2 p (proj1 H10)).
        inversion H11.
        apply H12. 
        inversion H12.
        tauto.
        constructor.
        apply (BiconditionalI (Union Formula (Subtract Formula hs1 a) (Subtract Formula hs2 b)) a b).
        apply (extend_infers hs1 b H3).
        intros p.
        intro.
        assert (In Formula (Add Formula hs a) p).
        apply (H1 p H9).
        destruct (eq_Formula_dec a p).
        apply Union_intror.
        rewrite e.
        apply In_singleton.
        apply Union_introl.
        apply Union_introl.
        constructor.
        apply H9.
        intro.
        apply n.
        inversion H11.
        tauto.
        apply (extend_infers hs2 a H5).
        intros p.
        intro.
        assert (In Formula (Add Formula hs b) p).
        apply (H2 p H9).
        destruct (eq_Formula_dec b p).
        apply Union_intror.
        rewrite e.
        apply In_singleton.
        apply Union_introl.
        apply Union_intror.
        constructor.
        apply H9.
        intro.
        apply n.
        inversion H11.
        tauto.
        destruct H4 as [bound1].
        destruct H6 as [bound2].
        exists (max bound1 bound2).
        intros h.
        intro.
        inversion H9.
        destruct (H4 h (proj1 H10)) as [n].
        destruct H12.
        exists n.
        constructor.
        tauto.
        lia.
        destruct (H6 h (proj1 H10)) as [n].
        destruct H12.
        exists n.
        constructor.
        tauto.
        lia.
      - destruct IHinfers1 as [hs1].
        destruct IHinfers2 as [hs2].
        destruct H1 as [HHH1].
        destruct H2 as [HHH2].
        destruct H1.
        destruct H3.
        destruct H2.
        destruct H5.
        exists (Union Formula hs1 hs2).
        constructor.
        intros h.
        destruct (HHH1 h).
        apply or_introl.
        apply Union_introl.
        apply H7.
        destruct (HHH2 h).
        apply or_introl.
        apply Union_intror.
        apply H8.
        apply or_intror.
        intro.
        inversion H9.
        subst.
        contradiction H7.
        contradiction H8.
        assert (Included Formula hs1 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_introl.
          apply H7.
        assert (Included Formula hs2 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_intror.
          apply H8.
        constructor.
        intros p.
        intro.
        inversion H9.
        subst.
        apply (H1 p H10).
        subst.
        apply (H2 p H10).
        constructor.
        apply (BiconditionalE1 (Union Formula hs1 hs2) a b).
        apply (extend_infers hs1 (BiconditionalF a b) H3 (Union Formula hs1 hs2) H7).
        apply (extend_infers hs2 a H5 (Union Formula hs1 hs2) H8).
        destruct H4 as [bound1].
        destruct H6 as [bound2].
        exists (max bound1 bound2).
        intros h.
        intro.
        inversion H9.
        subst.
        destruct (H4 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
        subst.
        destruct (H6 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
      - destruct IHinfers1 as [hs1].
        destruct IHinfers2 as [hs2].
        destruct H1 as [HHH1].
        destruct H2 as [HHH2].
        destruct H1.
        destruct H3.
        destruct H2.
        destruct H5.
        exists (Union Formula hs1 hs2).
        constructor.
        intros h.
        destruct (HHH1 h).
        apply or_introl.
        apply Union_introl.
        apply H7.
        destruct (HHH2 h).
        apply or_introl.
        apply Union_intror.
        apply H8.
        apply or_intror.
        intro.
        inversion H9.
        contradiction H7.
        contradiction H8.
        assert (Included Formula hs1 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_introl.
          apply H7.
        assert (Included Formula hs2 (Union Formula hs1 hs2)).
          intros p.
          intro.
          apply Union_intror.
          apply H8.
        constructor.
        intros p.
        intro.
        inversion H9.
        subst.
        apply (H1 p H10).
        subst.
        apply (H2 p H10).
        constructor.
        apply (BiconditionalE2 (Union Formula hs1 hs2) a b).
        apply (extend_infers hs1 (BiconditionalF a b) H3 (Union Formula hs1 hs2) H7).
        apply (extend_infers hs2 b H5 (Union Formula hs1 hs2) H8).
        destruct H4 as [bound1].
        destruct H6 as [bound2].
        exists (max bound1 bound2).
        intros h.
        intro.
        inversion H9.
        subst.
        destruct (H4 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
        subst.
        destruct (H6 h H10) as [n].
        exists n.
        destruct H11.
        constructor.
        tauto.
        lia.
    Qed.

    Inductive TH : Ensemble Formula -> Ensemble Formula :=
    | InTH :
      forall ps : Ensemble Formula,
      forall p : Formula,
      infers ps p ->
      In Formula (TH ps) p
    .
    
    Lemma lemma_1_3_8 :
      forall ps : Ensemble Formula,
      isFilter Formula LindenbaumBooleanAlgebra (TH ps).
    Proof.
      intros ps.
      constructor.
      exists (NegationF ContradictionF).
      apply InTH.
      apply NegationI.
      apply Assumption.
      apply Union_intror.
      apply In_singleton.
      constructor.
      intros b1 b2 H1 H2.
      inversion H1.
      subst.
      inversion H2.
      apply InTH.
      apply (ConjunctionE2 _ b1 b2).
      apply (cut_property ps b1 (ConjunctionF b1 b2)).
      apply H.
      apply (extend_infers (Singleton Formula b1) (andB b1 b2) H3).
      intros p.
      intro.
      inversion H4.
      subst.
      apply Union_intror.
      apply In_singleton.
      intros b1 b2 b H1 H2 H3.
      inversion H1.
      subst.
      inversion H2.
      subst.
      inversion H3.
      apply InTH.
      apply (cut_property ps (andB b1 b2) b).
      apply ConjunctionI.
      apply H.
      apply H0.
      apply (extend_infers (Singleton Formula (andB b1 b2)) b H5).
      intros p.
      intro.
      inversion H6.
      subst.
      apply Union_intror.
      apply In_singleton.
    Qed.

    Lemma TH_subseteq_Closure :
      forall ps : Ensemble Formula,
      Included Formula (TH ps) (Closure Formula LindenbaumBooleanAlgebra ps).
    Proof.
      cut (
        forall n : nat,
        forall hs : Ensemble Formula,
        forall c : Formula,
        infers hs c ->
        (forall h : Formula, In Formula hs h \/ ~ In Formula hs h) ->
        (forall h : Formula, In Formula hs h -> exists k : nat, enumerateFormula k = h /\ k < n) ->
        In Formula (FiniteMeet Formula LindenbaumBooleanAlgebra hs n) c
      ).
        intro HHH.
        intros ps.
        intros p.
        intro.
        inversion H.
        subst.
        destruct (infers_has_compactness ps p H0) as [hs].
        destruct H1.
        destruct H2.
        destruct H3.
        destruct H4 as [bound].
        assert (In Formula (Closure Formula LindenbaumBooleanAlgebra hs) p).
          apply (InClosure Formula LindenbaumBooleanAlgebra hs p bound p).
          apply (HHH bound hs p H3 H1 H4).
          apply CBA_axm_1.
        assert (Included Formula (Closure Formula LindenbaumBooleanAlgebra hs) (Closure Formula LindenbaumBooleanAlgebra ps)). 
          apply fact_4_of_1_2_8.
          apply H2.
        apply (H6 p H5).
      intros n.
      induction n.
      - intros hs c.
        intro.
        intro.
        intro.
        assert (Included Formula hs (Empty_set Formula)).
          intros h.
          intro.
          destruct (H1 h H2) as [k].
          destruct H3.
          lia.
        assert (infers (Empty_set Formula) c).
          apply (extend_infers hs c H).
          apply H2.
        apply FiniteMeetZ.
        constructor.
        apply NegationI.
        apply Assumption.
        apply Union_intror.
        apply In_singleton.
        apply (extend_infers (Empty_set Formula) c H3).
        intros h.
        intro.
        inversion H4.
      - intros hs c.
        intro.
        intro.
        intro.
        destruct (H0 (enumerateFormula n)).
        * assert (In Formula (FiniteMeet Formula LindenbaumBooleanAlgebra (Subtract Formula hs (enumerateFormula n)) n) (ImplicationF (enumerateFormula n) c)).
            apply IHn.
            apply ImplicationI.
            apply (extend_infers hs c H).
            intros h.
            intro.
            destruct (eq_Formula_dec (enumerateFormula n) h).
            subst.
            apply Union_intror.
            apply In_singleton.
            apply Union_introl.
            constructor.
            apply H3.
            intro.
            inversion H4.
            contradiction n0.
            intros h.
            destruct (eq_Formula_dec (enumerateFormula n) h).
            apply or_intror.
            intro.
            inversion H3.
            contradiction H5.
            subst.
            apply In_singleton.
            destruct (H0 h).
            apply or_introl.
            constructor.
            apply H3.
            intro.
            inversion H4.
            subst.
            tauto.
            apply or_intror.
            intro.
            inversion H4.
            contradiction H3.
            intros h.
            intro.
            inversion H3.
            destruct (H1 h H4) as [k].
            exists k.
            constructor.
            tauto.
            assert (k <> n).
              intro.
              destruct H6.
              subst.
              apply H5.
              apply In_singleton.
            lia.
          
    Qed.

    Definition Filter (ps : Ensemble Formula) (n : nat) : Ensemble Formula :=
      SequenceConstruction Formula LindenbaumBooleanAlgebra (TH ps) n
    .

    Definition CompleteFilter (ps : Ensemble Formula) : Ensemble Formula :=
      InfiniteConstruction Formula LindenbaumBooleanAlgebra (TH ps)
    .

    Fixpoint AxiomSet (ps : Ensemble Formula) (n : nat) : Ensemble Formula :=
      match n with
      | 0 => ps
      | S n' => Union Formula (AxiomSet ps n') (Construction Formula LindenbaumBooleanAlgebra (Filter ps n') n')
      end
    .

    Inductive FullAxiomSet : Ensemble Formula -> Ensemble Formula :=
    | InFullAxiomSet :
      forall ps : Ensemble Formula,
      forall n : nat,
      forall p : Formula,
      In Formula (AxiomSet ps n) p ->
      In Formula (FullAxiomSet ps) p
    .

    Lemma lemma_1_of_1_3_9 :
      forall ps : Ensemble Formula,
      forall n : nat, 
      Included Formula (Filter ps n) (TH (AxiomSet ps n)).
    Proof.
      intros ps n.
      induction n.
      - unfold Filter.
        simpl.
        intuition.
      - simpl.
        cut (
          forall l : nat,
          forall p : Formula,
          forall b : Formula,
          In Formula (FiniteMeet Formula LindenbaumBooleanAlgebra (Union Formula (Filter ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) l) b ->
          eqB (andB b p) b ->
          infers (Union Formula (AxiomSet ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) p /\ infers (Union Formula (AxiomSet ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) b
        ).
          intro.
          intros p.
          intro.
          apply InTH.
          inversion H0.
          subst.
          destruct (H n0 p b1).
          apply H1.
          apply H2.
          apply H3.
        intros l.
        induction l.
        * intros p b.
          intro.
          intro.
          simpl in *.
          destruct H0.
          inversion H.
          subst.
          inversion H2.
          assert (infers (Empty_set Formula) b).
            apply (cut_property (Empty_set Formula) trueB b).
            apply NegationI.
            apply Assumption.
            apply Union_intror.
            apply In_singleton.
            apply (extend_infers (Singleton Formula trueB) b H4).
            intros h.
            intro.
            inversion H5.
            subst.
            apply Union_intror.
            apply In_singleton.
          assert (infers (Empty_set Formula) p).
            apply (cut_property (Empty_set Formula) b p).
            apply H5.
            apply (ConjunctionE2 _ b p).
            apply (extend_infers (Singleton Formula b) (ConjunctionF b p) H1).
            intros h.
            intro.
            inversion H6.
            apply Union_intror.
            apply In_singleton.
          constructor.
          apply (extend_infers (Empty_set Formula) p H6).
          intros h.
          intro.
          inversion H7.
          apply (extend_infers (Empty_set Formula) b H5).
          intros h.
          intro.
          inversion H7.
        * intros p b.
          intro.
          intro.
          inversion H.
          subst.
          assert (
            infers (Union Formula (AxiomSet ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) b2 /\ infers (Union Formula (AxiomSet ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) b2
          ).
            apply (IHl b2 b2).
            apply H3.
            apply CBA_axm_1.
          destruct H1.
          assert (
            infers (Union Formula (AxiomSet ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) b
          ).
            inversion H2.
            subst.
            assert (In Formula (TH (AxiomSet ps n)) b1).
              apply (IHn b1 H6).
            inversion H7.
            subst.
            apply (cut_property _ (andB b1 b2) b).
            apply ConjunctionI.
            apply (extend_infers (AxiomSet ps n) b1 H8).
            intros h.
            intro.
            apply Union_introl.
            apply H9.
            apply H4.
            destruct H5.
            apply (extend_infers (Singleton Formula (andB b1 b2)) b H9).
            intros h.
            intro.
            apply Union_intror.
            apply H10.
            subst.
            assert (infers (Union Formula (AxiomSet ps n) (Construction Formula LindenbaumBooleanAlgebra (Filter ps n) n)) b1).
              apply Assumption.
              apply Union_intror.
              apply H6.
            apply (cut_property _ (andB b1 b2) b).
            apply ConjunctionI.
            apply H7.
            apply H4.
            destruct H5.
            apply (extend_infers (Singleton Formula (andB b1 b2)) b H8).
            intros h.
            intro.
            apply Union_intror.
            apply H9.
          constructor.
          destruct H0.
          assert (infers (Singleton Formula b) p).
            apply (ConjunctionE2 _ b p).
            apply H7.
          apply (cut_property _ b p).
          apply H6.
          apply (extend_infers (Singleton Formula b) p H8).
          intros h.
          intro.
          inversion H9.
          subst.
          apply Union_intror.
          apply In_singleton.
          apply H6.
    Qed.

    Lemma lemma_2_of_1_3_9 :
      forall n : nat,
      forall ps : Ensemble Formula,
      Included Formula (TH (AxiomSet ps n)) (Filter ps n).
    Proof.
      intros n.
      unfold Filter.
      induction n.
      - simpl.
        intros ps p.
        intro.
        apply H.
      - intros ps p.
        simpl.
        intro.
        inversion H.
        subst.

    Qed.

    Lemma lemma_3_of_1_3_9 :
      forall ps : Ensemble Formula,
      Included Formula (CompleteFilter ps) (TH (FullAxiomSet ps)).
    Proof.
      intros ps.
      intros p.
      intro.
      inversion H.
      subst.
      assert (In Formula (TH (AxiomSet ps n)) p).
        apply lemma_1_of_1_3_9.
        apply H0.
      inversion H1.
      subst.
      apply InTH.
      apply (extend_infers (AxiomSet ps n) p H2).
      intros h.
      intro.
      apply (InFullAxiomSet ps n h).
      apply H3.
    Qed.

    Lemma lemma_4_of_1_3_9 :
      forall ps : Ensemble Formula,
      Included Formula (TH (FullAxiomSet ps)) (CompleteFilter ps).
    Proof.
      intros ps p.
      intro.
      inversion H.
      subst.
      cut (
        forall bound : nat,
        forall hs : Ensemble Formula,
        Included Formula hs (FullAxiomSet ps) ->
        infers hs p ->
        (forall h : Formula, In Formula hs h -> exists n : nat, enumerateFormula n = h /\ n < bound) ->
        In Formula (Filter ps bound) p
      ).
    Qed.

  End Completeness.

End PropositionalLogic.

forall bs : Ensemble B,
forall n1 : nat,
forall n2 : nat,
n1 <= n2 ->
Included B (SequenceConstruction bs n1) (SequenceConstruction bs n2).

Inductive FiniteMeet : Ensemble B -> nat -> Ensemble B :=
| FiniteMeetZ :
  forall b : B,
  forall bs : Ensemble B,
  b == trueB ->
  In B (FiniteMeet bs 0) b
| FiniteMeetS :
  forall b : B,
  forall bs : Ensemble B,
  forall n : nat,
  forall b1 : B,
  forall b2 : B,
  In B bs b1 ->
  In B (FiniteMeet bs n) b2 ->
  b == andB b1 b2 ->
  In B (FiniteMeet bs (S n)) b
.
