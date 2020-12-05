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

  Section Semantics.

    Class CountableBooleanAlgebra (B : Type) : Type :=
      { eqB : B -> B -> Prop
      ; trueB : B
      ; falseB : B
      ; negB : B -> B
      ; andB : B -> B -> B
      ; orB : B -> B -> B
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
      ; CBA_AXM_4 :
        forall b1 : B,
        forall b1' : B,
        eqB b1 b1' ->
        eqB (negB b1) (negB b1')
      ; CBA_AXM_5 :
        forall b1 : B,
        forall b1' : B,
        forall b2 : B,
        forall b2' : B,
        eqB b1 b1' ->
        eqB b2 b2' ->
        eqB (orB b1 b2) (orB b1' b2')
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
      ; CBA_axm_2 :
        forall b1 : B,
        eqB (orB b1 b1) b1
      ; CBA_axm_3 :
        forall b1 : B,
        forall b2 : B,
        eqB (andB b1 b2) (andB b2 b1)
      ; CBA_axm_4 :
        forall b1 : B,
        forall b2 : B,
        eqB (orB b1 b2) (orB b2 b1)
      ; CBA_axm_5 :
        forall b1 : B,
        forall b2 : B,
        forall b3 : B,
        eqB (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3)
      ; CBA_axm_6 :
        forall b1 : B,
        forall b2 : B,
        forall b3 : B, eqB (orB b1 (orB b2 b3)) (orB (orB b1 b2) b3)
      ; CBA_axm_7 :
        forall b1 : B,
        forall b2 : B,
        forall b3 : B,
        eqB (andB b1 (orB b2 b3)) (orB (andB b1 b2) (andB b1 b3))
      ; CBA_axm_8 :
        forall b1 : B,
        forall b2 : B,
        forall b3 : B,
        eqB (orB b1 (andB b2 b3)) (andB (orB b1 b2) (orB b1 b3))
      ; CBA_axm_9 :
        forall b1 : B,
        eqB (andB falseB b1) falseB
      ; CBA_axm_10 :
        forall b1 : B,
        eqB (andB trueB b1) b1
      ; CBA_axm_11 :
        forall b1 : B,
        eqB (orB falseB b1) b1
      ; CBA_axm_12 :
        forall b1 : B,
        eqB (orB trueB b1) trueB
      ; CBA_axm_13 :
        forall b1 : B,
        eqB (andB b1 (negB b1)) falseB
      ; CBA_axm_14 :
        forall b1 : B,
        eqB (orB b1 (negB b1)) trueB
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
            assert (forall i : nat, forall b : B, In B (FiniteMeet (Union B (SequenceConstruction bs n)(Construction (SequenceConstruction bs n) n)) i) b ->  (FiniteMeet (Add B (SequenceConstruction bs n) (enumB n)) i) b).
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

  End Semantics.

End PropositionalLogic.
