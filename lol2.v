Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export Lia.
Require Export Ensembles.

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

End Helper.

Module PropositionalLogic.

  Import Helper.

  Section Syntax.

    Definition PropVar : Set := 
      nat
    .

    Inductive Formula : Set :=
    | AtomF : PropVar -> Formula
    | ContradictionF : Formula
    | NegationF : Formula -> Formula
    | ConjunctionF : Formula -> Formula -> Formula
    | DisjunctionF : Formula -> Formula -> Formula
    | ImplicationF : Formula -> Formula -> Formula
    | BiconditionalF : Formula -> Formula -> Formula
    .
    
    Proposition eq_Formula_dec :
      forall p1 p2 : Formula,
      {p1 = p2} + {p1 <> p2}.
    Proof.
      intros p1.
      induction p1.
      - intros p2.
        destruct p2.
        * destruct (Nat.eq_dec p p0).
          + intuition.
          + assert (AtomF p <> AtomF p0).
              intro.
              inversion H.
              intuition.
            intuition.
        * assert (AtomF p <> ContradictionF).
            intro.
            inversion H.
          intuition.
        * assert (AtomF p <> NegationF p2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF p <> ConjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF p <> DisjunctionF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF p <> ImplicationF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (AtomF p <> BiconditionalF p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        induction p2.
        * assert (ContradictionF <> AtomF p).
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
        * assert (NegationF p1 <> AtomF p).
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
        * assert (ConjunctionF p1_1 p1_2 <> AtomF p).
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
        * assert (DisjunctionF p1_1 p1_2 <> AtomF p).
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
        * assert (ImplicationF p1_1 p1_2 <> AtomF p).
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
        * assert (BiconditionalF p1_1 p1_2 <> AtomF p).
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
        * exists p.
          simpl.
          tauto.
        * assert (exists seed : nat, (0, S (S (S (S (S (S p)))))) = mapsLineToPlane seed).
          exists (sum_from_0_to (0 + S (S (S (S (S (S p)))))) + S (S (S (S (S (S p)))))).
          apply (proj2 (H (sum_from_0_to (0 + S (S (S (S (S (S p)))))) + S (S (S (S (S (S p)))))) 0 (S (S (S (S (S (S p))))))) eq_refl).
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
      match mapsLineToPlane n with
      | (x, y) => enum_formula_aux x y
      end
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

  Section Semantics.

    Definition Assignment : Set :=
      PropVar -> bool
    .

    Fixpoint satisfies (v : Assignment) (p : Formula) : bool :=
      match p with
      | AtomF i => v i
      | ContradictionF => false
      | NegationF p1 =>
        match satisfies v p1 with
        | false => true
        | true => false
        end
      | ConjunctionF p1 p2 =>
        match (satisfies v p1, satisfies v p2) with
        | (false, false) => false
        | (false, true) => false
        | (true, false) => false
        | (true, true) => true
        end
      | DisjunctionF p1 p2 =>
        match (satisfies v p1, satisfies v p2) with
        | (false, false) => false
        | (false, true) => true
        | (true, false) => true
        | (true, true) => true
        end
      | ImplicationF p1 p2 =>
        match (satisfies v p1, satisfies v p2) with
        | (false, false) => true
        | (false, true) => true
        | (true, false) => false
        | (true, true) => true
        end
      | BiconditionalF p1 p2 =>
        match (satisfies v p1, satisfies v p2) with
        | (false, false) => true
        | (false, true) => false
        | (true, false) => false
        | (true, true) => true
        end
      end
    .

    Definition FormulaSet : Type :=
      Ensemble Formula
    .

    Definition EmptyFormulaSet : FormulaSet :=
      Empty_set Formula
    .

    Definition Insert (h : Formula) (hs : FormulaSet) : FormulaSet :=
      Add Formula hs h
    . 

    Definition entails (hs : FormulaSet) (c : Formula) : Prop :=
      forall v : Assignment, (forall h : Formula, In Formula hs h -> satisfies v h = true) -> satisfies v c = true
    .

    Lemma extend_entails :
      forall hs1 : FormulaSet,
      forall c : Formula,
      entails hs1 c ->
      forall hs2 : FormulaSet,
      Included Formula hs1 hs2 ->
      entails hs2 c.
    Proof.
      intros hs1 c.
      intro.
      intros hs2.
      intro.
      intros v.
      intro.
      apply (H v).
      intros h.
      intro.
      apply (H1 h).
      apply (H0 h).
      apply H2.
    Qed.

  End Semantics.

  Section InferenceRules.

    Inductive infers : FormulaSet -> Formula -> Prop :=
    | Assumption :
      forall hs : FormulaSet,
      forall h : Formula,
      In Formula hs h ->
      infers hs h
    | ContradictionI :
      forall hs : FormulaSet,
      forall a : Formula,
      infers hs a ->
      infers hs (NegationF a) ->
      infers hs ContradictionF
    | ContradictionE :
      forall hs : FormulaSet,
      forall a : Formula,
      infers hs ContradictionF ->
      infers hs a
    | NegationI :
      forall hs : FormulaSet,
      forall a : Formula,
      infers (Insert a hs) ContradictionF ->
      infers hs (NegationF a)
    | NegationE :
      forall hs : FormulaSet,
      forall a : Formula,
      infers (Insert (NegationF a) hs) ContradictionF ->
      infers hs a
    | ConjunctionI :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs a ->
      infers hs b ->
      infers hs (ConjunctionF a b)
    | ConjunctionE1 :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs (ConjunctionF a b) ->
      infers hs a
    | ConjunctionE2 :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs (ConjunctionF a b) ->
      infers hs b
    | DisjunctionI1 :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs a ->
      infers hs (DisjunctionF a b)
    | DisjunctionI2 :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs b ->
      infers hs (DisjunctionF a b)
    | DisjunctionE :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      forall c : Formula,
      infers hs (DisjunctionF a b) ->
      infers (Insert a hs) c ->
      infers (Insert b hs) c ->
      infers hs c
    | ImplicationI :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers (Insert a hs) b ->
      infers hs (ImplicationF a b)
    | ImplicationE :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs (ImplicationF a b) ->
      infers hs a ->
      infers hs b
    | BiconditionalI :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers (Insert a hs) b ->
      infers (Insert b hs) a ->
      infers hs (BiconditionalF a b)
    | BiconditionalE1 :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs (BiconditionalF a b) ->
      infers hs a ->
      infers hs b
    | BiconditionalE2 :
      forall hs : FormulaSet,
      forall a : Formula,
      forall b : Formula,
      infers hs (BiconditionalF a b) ->
      infers hs b ->
      infers hs a
    .

    Example exclusive_middle :
      forall p : Formula,
      infers EmptyFormulaSet (DisjunctionF p (NegationF p)).
    Proof.
      intros p.
      apply (NegationE EmptyFormulaSet (DisjunctionF p (NegationF p))).
      apply (ContradictionI (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet) (DisjunctionF p (NegationF p))).
      apply (DisjunctionI2 (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet) p (NegationF p)).
      apply (NegationI (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet) p).
      apply (ContradictionI (Insert p (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet)) (DisjunctionF p (NegationF p))).
      apply (DisjunctionI1 (Insert p (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet)) p (NegationF p)).
      apply (Assumption (Insert p (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet)) p).
      unfold Insert.
      unfold Add.
      apply Union_intror.
      apply In_singleton.
      apply (Assumption (Insert p (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet)) (NegationF (DisjunctionF p (NegationF p)))).
      unfold Insert.
      unfold Add.
      apply Union_introl.
      apply Union_intror.
      apply In_singleton.
      apply (Assumption (Insert (NegationF (DisjunctionF p (NegationF p))) EmptyFormulaSet) (NegationF (DisjunctionF p (NegationF p)))).
      unfold Insert.
      unfold Add.
      apply Union_intror.
      apply In_singleton.
    Qed.

  End InferenceRules.

  Section Soundness.

    Lemma extend_infers :
      forall hs1 : FormulaSet,
      forall c : Formula,
      infers hs1 c ->
      forall hs2 : FormulaSet,
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
        apply (IHinfers (Insert a hs2)).
        apply Included_Add.
        apply H0.
      - intros hs2.
        intro.
        apply (NegationE hs2 a).
        apply (IHinfers (Insert (NegationF a) hs2)).
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
        apply (IHinfers2 (Insert a hs2)).
        apply Included_Add.
        apply H2.
        apply (IHinfers3 (Insert b hs2)).
        apply Included_Add.
        apply H2.
      - intros hs2.
        intro.
        apply (ImplicationI hs2 a b).
        apply (IHinfers (Insert a hs2)).
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
        apply (IHinfers1 (Insert a hs2)).
        apply Included_Add.
        apply H1.
        apply (IHinfers2 (Insert b hs2)).
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
      forall hs : FormulaSet,
      forall c : Formula,
      In Formula hs c ->
      entails hs c.
    Proof.
      intros hs c.
      assert (In Formula (Singleton Formula c) c).
        apply In_singleton.
      assert (entails (Singleton Formula c) c).
        intros v.
        intro.
        apply (H0 c H).
      intro.
      apply (extend_entails (Singleton Formula c) c H0 hs).
      intros x.
      intro.
      inversion H2.
      subst.
      apply H1.
    Qed.

    Lemma ContradictionI_preserves :
      forall hs : FormulaSet,
      forall a : Formula,
      entails hs a ->
      entails hs (NegationF a) ->
      entails hs ContradictionF.
    Proof.
      intros hs a.
      intro.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v a = true
      ).
        apply (H v H1).
      assert (
        satisfies v (NegationF a) = true
      ).
        apply (H0 v H1).
      inversion H3.
      rewrite H2 in H5.
      inversion H5.
    Qed.

    Lemma ContradictionE_preserves :
      forall hs : FormulaSet,
      forall a : Formula,
      entails hs ContradictionF ->
      entails hs a.
    Proof.
      intros hs a.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v ContradictionF = true
      ).
        apply (H v H0).
      inversion H1.
    Qed.

    Lemma NegationI_preserves :
      forall hs : FormulaSet,
      forall a : Formula,
      entails (Insert a hs) ContradictionF ->
      entails hs (NegationF a).
    Proof.
      intros hs a.
      intro.
      intros v.
      intro.
      assert (
        (forall h : Formula, In Formula (Insert a hs) h -> satisfies v h = true) ->
        satisfies v ContradictionF = true
      ).
        apply (H v).
      cut (
        satisfies v a = false
      ).
        intro.
        simpl.
        rewrite H2.
        intuition.
      assert (satisfies v a = true \/ satisfies v a = false).
        induction (satisfies v a).
        intuition.
        intuition.
      destruct H2.
      - elimtype False.
        cut (satisfies v ContradictionF = true).
          simpl.
          intuition.
        apply H1.
        intros premise.
        simpl.
        intro.
        destruct H3.
        * apply (H0 x H3).
        * rewrite H3 in H2.
          apply H2.
      - apply H2.
    Qed.

    Lemma NegationE_preserves :
      forall hs : FormulaSet,
      forall a : Formula,
      entails (Insert (NegationF a) hs) ContradictionF ->
      entails hs a.
    Proof.
      intros hs a.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        (forall h : Formula, In Formula (Insert (NegationF a) hs) h -> satisfies v h = true) ->
        satisfies v ContradictionF = true
      ).
        apply (H v).
      assert (
        satisfies v a = true \/ satisfies v a = false
      ).
        induction (satisfies v a).
        intuition.
        intuition.
      destruct H2.
      - apply H2.
      - elimtype False.
        cut (satisfies v ContradictionF = true).
          simpl.
          intuition.
        apply H1.
        intros premise.
        simpl.
        intro.
        destruct H3.
        * apply (H0 x H3).
        * rewrite <- H3.
          simpl.
          rewrite H2.
          intuition.
    Qed.

    Lemma ConjunctionI_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs a ->
      entails hs b ->
      entails hs (ConjunctionF a b).
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v a = true
      ).
        apply (H v H1).
      assert (
        satisfies v b = true
      ).
        apply (H0 v H1).
      simpl.
      rewrite H2.
      rewrite H3.
      intuition.
    Qed.

    Lemma ConjunctionE1_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs (ConjunctionF a b) ->
      entails hs a.
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v (ConjunctionF a b) = true
      ).
        apply (H v H0).
      assert (
        satisfies v a = true \/ satisfies v a = false
      ).
        induction (satisfies v a).
        intuition.
        intuition.
      destruct H2.
        apply H2.
        inversion H1.
        rewrite H2.
      assert (
        satisfies v b = true \/ satisfies v b = false
      ).
        induction (satisfies v b).
        intuition.
        intuition.
        destruct H3.
        rewrite H3.
        tauto.
        rewrite H3.
        tauto.
    Qed.

    Lemma ConjunctionE2_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs (ConjunctionF a b) ->
      entails hs b.
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v (ConjunctionF a b) = true
      ).
        apply (H v H0).
      assert (
        satisfies v b = true \/ satisfies v b = false
      ).
        induction (satisfies v b).
        intuition.
        intuition.
      destruct H2.
        apply H2.
        inversion H1.
        rewrite H2.
      assert (
        satisfies v a = true \/ satisfies v a = false
      ).
        induction (satisfies v a).
        intuition.
        intuition.
        destruct H3.
        rewrite H3.
        tauto.
        rewrite H3.
        tauto.
    Qed.

    Lemma DisjunctionI1_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs a ->
      entails hs (DisjunctionF a b).
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v a = true
      ).
        apply (H v H0).
      cut (satisfies v b = true \/ satisfies v b = false).
        intro.
        simpl.
        rewrite H1.
        destruct H2.
          rewrite H2.
          tauto.
          rewrite H2.
          tauto.
      induction (satisfies v b).
        tauto.
        tauto.
    Qed.

    Lemma DisjunctionI2_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs b ->
      entails hs (DisjunctionF a b).
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (
        satisfies v b = true
      ).
        apply (H v H0).
      cut (satisfies v a = true \/ satisfies v a = false).
        intro.
        simpl.
        rewrite H1.
        destruct H2.
          rewrite H2.
          tauto.
          rewrite H2.
          tauto.
      induction (satisfies v a).
        tauto.
        tauto.
    Qed.

    Lemma DisjunctionE_preserves :
      forall hs : FormulaSet,
      forall a b c : Formula,
      entails hs (DisjunctionF a b) ->
      entails (Insert a hs) c ->
      entails (Insert b hs) c ->
      entails hs c.
    Proof.
      intros hs a b c.
      unfold entails in *.
      intro.
      intro.
      intro.
      intros v.
      intro.
      assert (satisfies v a = true \/ satisfies v b = true).
        assert (satisfies v (DisjunctionF a b) = true).
          apply (H v H2).
        inversion H3.
        cut (satisfies v a = true \/ satisfies v a = false).
          intro.
          destruct H4.
            rewrite H4 in *.
            apply or_introl.
            rewrite H5.
            tauto.
            cut (satisfies v b = true \/ satisfies v b = false).
              intro.
              rewrite H4 in *.
              destruct H6.
                rewrite H6 in *.
                tauto.
                rewrite H6 in *.
                inversion H5.
            induction (satisfies v b).
              tauto.
              tauto.
        induction (satisfies v a).
          tauto.
          tauto.
      destruct H3.
      - apply (H0 v).
        intros h.
        simpl.
        intro.
        destruct H4.
        * apply (H2 x H4).
        * rewrite H4 in H3.
          apply H3.
      - apply (H1 v).
        intros h.
        simpl.
        intro.
        destruct H4.
        * apply (H2 x H4).
        * rewrite H4 in H3.
          apply H3.
    Qed.

    Lemma ImplicationI_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails (Insert a hs) b ->
      entails hs (ImplicationF a b).
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (satisfies v a = true \/ satisfies v a = false).
        induction (satisfies v a).
          tauto.
          tauto.
      assert (satisfies v b = true \/ satisfies v b = false).
        induction (satisfies v b).
          tauto.
          tauto.
      destruct H1.
      - destruct H2.
        * simpl.
          rewrite H1.
          rewrite H2.
          tauto.
        * assert (satisfies v b = true).
            apply (H v).
            intros h.
            simpl.
            intro.
            destruct H3.
              apply (H0 x H3).
              rewrite <- H3.
              apply H1.
          rewrite H3 in H2.
          inversion H2.
      - simpl.
        destruct H2.
        * rewrite H1.
          rewrite H2.
          tauto.
        * rewrite H1.
          rewrite H2.
          tauto.
    Qed.

    Lemma ImplicationE_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs (ImplicationF a b) ->
      entails hs a ->
      entails hs b.
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (satisfies v a = true).
        apply (H0 v H1).
      cut (satisfies v (ImplicationF a b) = true).
        intro.
        cut (satisfies v b = true \/ satisfies v b = false).
          intro.
          destruct H4.
            apply H4.
            cut (satisfies v (ImplicationF a b) = false).
              intro.
              rewrite H3 in H5.
              inversion H5.
            simpl.
            rewrite H2.
            rewrite H4.
            tauto.
        destruct (satisfies v b).
          tauto.
          tauto.
      apply (H v H1).
    Qed.

    Lemma BiconditionalI_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails (Insert a hs) b ->
      entails (Insert b hs) a ->
      entails hs (BiconditionalF a b).
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (satisfies v a = true \/ satisfies v a = false).
        induction (satisfies v a).
          tauto.
          tauto.
      assert (satisfies v b = true \/ satisfies v b = false).
        induction (satisfies v b).
          tauto.
          tauto.
      destruct H2.
      - destruct H3.
        * simpl.
          rewrite H2.
          rewrite H3.
          tauto.
        * assert (satisfies v b = true).
            apply (H v).
            intros h.
            simpl.
            intro.
            destruct H4.
              apply (H1 x H4).
              rewrite <- H4.
              apply H2.
          rewrite H4 in H3.
          inversion H3.
      - destruct H3.
        * assert (satisfies v a = true).
            apply (H0 v).
            intros h.
            simpl.
            intro.
            destruct H4.
              apply (H1 x H4).  
              rewrite <- H4.
              apply H3.
          rewrite H4 in H2.
          inversion H2.
        * simpl.
          rewrite H2.
          rewrite H3.
          tauto.
    Qed.

    Lemma BiconditionalE1_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs (BiconditionalF a b) ->
      entails hs a ->
      entails hs b.
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (satisfies v b = true \/ satisfies v b = false).
        induction (satisfies v b).
          tauto.
          tauto.
      destruct H2.
        apply H2.
      assert (satisfies v a = true).
        apply (H0 v H1).
      assert (satisfies v (BiconditionalF a b) = false).
        simpl.
        rewrite H2.
        rewrite H3.
        tauto.
      assert (satisfies v (BiconditionalF a b) = true).
        apply (H v H1).
      rewrite H4 in H5.
      inversion H5.
    Qed.

    Lemma BiconditionalE2_preserves :
      forall hs : FormulaSet,
      forall a b : Formula,
      entails hs (BiconditionalF a b) ->
      entails hs b ->
      entails hs a.
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros v.
      intro.
      assert (satisfies v a = true \/ satisfies v a = false).
        induction (satisfies v a).
          tauto.
          tauto.
      destruct H2.
        apply H2.
      assert (satisfies v b = true).
        apply (H0 v H1).
      assert (satisfies v (BiconditionalF a b) = false).
        simpl.
        rewrite H2.
        rewrite H3.
        tauto.
      assert (satisfies v (BiconditionalF a b) = true).
        apply (H v H1).
      rewrite H4 in H5.
      inversion H5.
    Qed.

    Theorem soundness :
      forall hs : FormulaSet,
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

    Inductive InsertWithConsistency : FormulaSet -> Formula -> FormulaSet :=
    | InsertN :
      forall hs : FormulaSet,
      forall h : Formula,
      forall p : Formula,
      In Formula hs p ->
      In Formula (InsertWithConsistency hs h) p
    | InsertT :
      forall hs : FormulaSet,
      forall h : Formula,
      infers hs h ->
      In Formula (InsertWithConsistency hs h) h
    | InsertF :
      forall hs : FormulaSet,
      forall h : Formula,
      ~ infers hs h ->
      In Formula (InsertWithConsistency hs h) (NegationF h)
    .

    Fixpoint Lindenbaum (hs : FormulaSet) (i : nat) : FormulaSet :=
      match i with
      | 0 => hs
      | S i' =>
        let hs' := Lindenbaum hs i' in
        let p' := enumerateFormula i' in
        InsertWithConsistency hs' p'
      end
    .

    Lemma Lindenbaum_property :
      forall hs : FormulaSet,
      ~ infers hs ContradictionF ->
      forall i : nat,
      Included Formula hs (Lindenbaum hs i) /\ ~ infers (Lindenbaum hs i) ContradictionF.
    Proof.
      intros hs H i.
      induction i.
      - simpl.
        constructor.
        * apply Included_refl.
        * apply H.
      - destruct IHi.
        simpl in *.
        constructor.
        * intros h.
          intro.
          apply InsertN.
          apply (H0 h H2).
        * intro.
          assert (~ infers (Lindenbaum hs i) (enumerateFormula i)).
            intro.
            assert (Included Formula (InsertWithConsistency (Lindenbaum hs i) (enumerateFormula i)) (Insert (enumerateFormula i) (Lindenbaum hs i))).
              intros h.
              intro.
              inversion H4.
              subst.
              apply Union_introl.
              tauto.
              subst.
              apply Union_intror.
              apply In_singleton.
              tauto.
            apply H1.
            apply (ContradictionI (Lindenbaum hs i) (enumerateFormula i)).
            apply H3.
            apply (NegationI (Lindenbaum hs i) (enumerateFormula i)).
            apply (extend_infers (InsertWithConsistency (Lindenbaum hs i) (enumerateFormula i)) ContradictionF H2 (Insert (enumerateFormula i) (Lindenbaum hs i)) H4).
          assert (infers (Lindenbaum hs i) (enumerateFormula i)).
            assert (Included Formula (InsertWithConsistency (Lindenbaum hs i) (enumerateFormula i)) (Insert (NegationF (enumerateFormula i)) (Lindenbaum hs i))).
              intros h.
              intro.
              inversion H4.
              subst.
              apply Union_introl.
              tauto.
              tauto.
              apply Union_intror.
              apply In_singleton.
            apply (NegationE (Lindenbaum hs i) (enumerateFormula i)).
            apply (extend_infers (InsertWithConsistency (Lindenbaum hs i) (enumerateFormula i)) ContradictionF H2 (Insert (NegationF (enumerateFormula i)) (Lindenbaum hs i)) H4).
          tauto.
    Qed.

    Inductive MaximalConsistentSet (hs : FormulaSet) : FormulaSet :=
    | UnionsLindenbaum :
      forall n : nat,
      forall h : Formula,
      In Formula (Lindenbaum hs n) h ->
      In Formula (MaximalConsistentSet hs) h
    .

    Lemma MaximalConsistentSet_property :
      forall hs : FormulaSet,
      forall h : Formula,
      ~ In Formula (MaximalConsistentSet hs) h ->
      infers (Insert h (MaximalConsistentSet hs)) ContradictionF.
    Proof.
      intros hs h H.
      destruct (Formula_is_enumerable h) as [n H0].
      assert (forall i : nat, Included Formula (Lindenbaum hs i) (MaximalConsistentSet hs)).
        intros i p.
        intro.
        apply (UnionsLindenbaum hs i p H1).
      subst.
      assert (~ infers (Lindenbaum hs n) (enumerateFormula n)).
        intro.
        assert (In Formula (Lindenbaum hs (S n)) (enumerateFormula n)).
          apply (InsertT (Lindenbaum hs n) (enumerateFormula n) H0).
        apply H.
        apply (H1 (S n) (enumerateFormula n) H2).
      assert (In Formula (Lindenbaum hs (S n)) (NegationF (enumerateFormula n))).
        apply (InsertF (Lindenbaum hs n) (enumerateFormula n) H0).
      assert (In Formula (MaximalConsistentSet hs) (NegationF (enumerateFormula n))).
        apply (H1 (S n) (NegationF (enumerateFormula n)) H2).
      assert (infers (MaximalConsistentSet hs) (NegationF (enumerateFormula n))).
        apply (Assumption (MaximalConsistentSet hs) (NegationF (enumerateFormula n)) H3).
      apply (ContradictionI (Insert (enumerateFormula n) (MaximalConsistentSet hs)) (enumerateFormula n)).
      apply (Assumption (Insert (enumerateFormula n) (MaximalConsistentSet hs)) (enumerateFormula n)).
      apply Union_intror.
      apply In_singleton.
      apply (extend_infers (MaximalConsistentSet hs) (NegationF (enumerateFormula n)) H4 (Insert (enumerateFormula n) (MaximalConsistentSet hs))).
      intros h.
      intro.
      apply Union_introl.
      apply H5.
    Qed.

  End Completeness.

End PropositionalLogic.
