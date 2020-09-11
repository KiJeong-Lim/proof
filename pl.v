Require Export List.
Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export Lia.

(* THANKS_TO:
  1. Taeseung Sohn: "https://github.com/paulsohn";
  2. Junyoung Clare Jang: "https://github.com/Ailrun";
*)

Module PropositionalLogic.

  Import ListNotations.

  Section Syntax.

    Inductive formula : Set :=
    | PropVar : nat -> formula
    | Contradiction : formula
    | Negation : formula -> formula
    | Conjunction : formula -> formula -> formula
    | Disjunction : formula -> formula -> formula
    | Implication : formula -> formula -> formula
    | Biconditional : formula -> formula -> formula
    .

    Proposition eq_formula_dec :
      forall p1 p2 : formula,
      {p1 = p2} + {p1 <> p2}.
    Proof.
      intros p1.
      induction p1.
      - intros p2.
        destruct p2.
        * destruct (Nat.eq_dec n n0).
          + intuition.
          + assert (PropVar n <> PropVar n0).
              intro.
              inversion H.
              intuition.
            intuition.
        * assert (PropVar n <> Contradiction).
            intro.
            inversion H.
          intuition.
        * assert (PropVar n <> Negation p2).
            intro.
            inversion H.
          intuition.
        * assert (PropVar n <> Conjunction p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (PropVar n <> Disjunction p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (PropVar n <> Implication p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (PropVar n <> Biconditional p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        induction p2.
        * assert (Contradiction <> PropVar n).
            intro.
            inversion H.
          intuition.
        * intuition.
        * assert (Contradiction <> Negation p2).
            intro.
            inversion H.
          intuition.
        * assert (Contradiction <> Conjunction p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (Contradiction <> Disjunction p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (Contradiction <> Implication p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (Contradiction <> Biconditional p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        destruct p2.
        * assert (Negation p1 <> PropVar n).
            intro.
            inversion H.
          intuition.
        * assert (Negation p1 <> Contradiction).
            intro.
            inversion H.
          intuition.
        * destruct (IHp1 p2).
            subst.
            tauto.
            assert (Negation p1 <> Negation p2).
              intro.
              inversion H.
              apply (n H1).
            intuition.
        * assert (Negation p1 <> Conjunction p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (Negation p1 <> Disjunction p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (Negation p1 <> Implication p2_1 p2_2).
            intro.
            inversion H.
          intuition.
        * assert (Negation p1 <> Biconditional p2_1 p2_2).
            intro.
            inversion H.
          intuition.
      - intros p2.
        destruct p2.
        * assert (Conjunction p1_1 p1_2 <> PropVar n).
            intro.
            inversion H.
          intuition.
        * assert (Conjunction p1_1 p1_2 <> Contradiction).
            intro.
            inversion H.
          intuition.
        * assert (Conjunction p1_1 p1_2 <> Negation p2).
            intro.
            inversion H.
          intuition.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (Conjunction p1_1 p1_2 <> Conjunction p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (Conjunction p1_1 p1_2 <> Conjunction p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (Conjunction p1_1 p1_2 <> Disjunction p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (Conjunction p1_1 p1_2 <> Implication p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (Conjunction p1_1 p1_2 <> Biconditional p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        destruct p2.
        * assert (Disjunction p1_1 p1_2 <> PropVar n).
            intro.
            inversion H.
          tauto.
        * assert (Disjunction p1_1 p1_2 <> Contradiction).
            intro.
            inversion H.
          tauto.
        * assert (Disjunction p1_1 p1_2 <> Negation p2).
            intro.
            inversion H.
          tauto.
        * assert (Disjunction p1_1 p1_2 <> Conjunction p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (Disjunction p1_1 p1_2 <> Disjunction p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (Disjunction p1_1 p1_2 <> Disjunction p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (Disjunction p1_1 p1_2 <> Implication p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (Disjunction p1_1 p1_2 <> Biconditional p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        induction p2.
        * assert (Implication p1_1 p1_2 <> PropVar n).
            intro.
            inversion H.
          tauto.
        * assert (Implication p1_1 p1_2 <> Contradiction).
            intro.
            inversion H.
          tauto.
        * assert (Implication p1_1 p1_2 <> Negation p2).
            intro.
            inversion H.
          tauto.
        * assert (Implication p1_1 p1_2 <> Conjunction p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (Implication p1_1 p1_2 <> Disjunction p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (Implication p1_1 p1_2 <> Implication p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (Implication p1_1 p1_2 <> Implication p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
        * assert (Implication p1_1 p1_2 <> Biconditional p2_1 p2_2).
            intro.
            inversion H.
          tauto.
      - intros p2.
        destruct p2.
        * assert (Biconditional p1_1 p1_2 <> PropVar n).
            intro.
            inversion H.
          tauto.
        * assert (Biconditional p1_1 p1_2 <> Contradiction).
            intro.
            inversion H.
          tauto.
        * assert (Biconditional p1_1 p1_2 <> Negation p2).
            intro.
            inversion H.
          tauto.
        * assert (Biconditional p1_1 p1_2 <> Conjunction p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (Biconditional p1_1 p1_2 <> Disjunction p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * assert (Biconditional p1_1 p1_2 <> Implication p2_1 p2_2).
            intro.
            inversion H.
          tauto.
        * destruct (IHp1_1 p2_1).
            destruct (IHp1_2 p2_2).
              subst.
              intuition.
              assert (Biconditional p1_1 p1_2 <> Biconditional p2_1 p2_2).
                intro.
                inversion H.
                tauto.
              tauto.
            assert (Biconditional p1_1 p1_2 <> Biconditional p2_1 p2_2).
              intro.
              inversion H.
              tauto.
            tauto.
    Qed.

  End Syntax.

  Section Semantics.

    Fixpoint satisfies (assignment : nat -> bool) (p : formula) : bool :=
      match p with
      | PropVar n => assignment n
      | Contradiction => false
      | Negation p1 =>
        match satisfies assignment p1 with
        | true => false
        | false => true
        end
      | Conjunction p1 p2 =>
        match satisfies assignment p1, satisfies assignment p2 with
        | true, true => true
        | true, false => false
        | false, true => false
        | false, false => false
        end
      | Disjunction p1 p2 =>
        match satisfies assignment p1, satisfies assignment p2 with
        | true, true => true
        | true, false => true
        | false, true => true
        | false, false => false
        end
      | Implication p1 p2 =>
        match satisfies assignment p1, satisfies assignment p2 with
        | true, true => true
        | true, false => false
        | false, true => true
        | false, false => true
        end
      | Biconditional p1 p2 =>
        match satisfies assignment p1, satisfies assignment p2 with
        | true, true => true
        | true, false => false
        | false, true => false
        | false, false => true
        end
      end
    .

    Definition entails (premises : list formula) (consequence : formula) : Prop :=
      forall assignment : nat -> bool,
      (forall premise : formula, In premise premises -> satisfies assignment premise = true) ->
      satisfies assignment consequence = true
    .

    Lemma premise_more_then_still_entails :
      forall hs1 : list formula,
      forall a : formula,
      entails hs1 a ->
      forall hs2 : list formula,
      (forall h : formula, In h hs1 -> In h hs2) ->
      entails hs2 a.
    Proof.
      intros hs1 a.
      intro.
      intros hs2.
      intro.
      intros assignment.
      intro.
      apply (H assignment).
      intros premise.
      intro.
      apply (H1 premise (H0 premise H2)).
    Qed.

    Theorem always_entails_premise :
      forall premises : list formula,
      forall consequence : formula,
      In consequence premises ->
      entails premises consequence.
    Proof.
      intros premises consequence.
      assert (In consequence [consequence]).
        simpl.
        intuition.
      assert (entails [consequence] consequence).
        intros assignment.
        intro.
        apply (H0 consequence H).
      intro.
      apply (premise_more_then_still_entails [consequence] consequence H0 premises).
      intro.
      simpl.
      intro.
      destruct H2.
      subst.
      apply H1.
      inversion H2.
    Qed.

  End Semantics.
  
  Section InferenceRules.

    Inductive infers : list formula -> formula -> Prop :=
    | Assumption :
      forall hypotheses : list formula,
      forall conclusion : formula,
      In conclusion hypotheses ->
      infers hypotheses conclusion
    | BottomIntro :
      forall hs : list formula,
      forall a : formula,
      infers hs a ->
      infers hs (Negation a) ->
      infers hs Contradiction
    | BottomElim :
      forall hs : list formula,
      forall a : formula,
      infers hs Contradiction ->
      infers hs a
    | NotIntro :
      forall hs : list formula,
      forall a : formula,
      infers (a :: hs) Contradiction ->
      infers hs (Negation a)
    | NotElim :
      forall hs : list formula,
      forall a : formula,
      infers (Negation a :: hs) Contradiction ->
      infers hs a
    | AndIntro :
      forall hs : list formula,
      forall a b : formula,
      infers hs a ->
      infers hs b ->
      infers hs (Conjunction a b)
    | AndElim1 :
      forall hs : list formula,
      forall a b : formula,
      infers hs (Conjunction a b) ->
      infers hs a
    | AndElim2 :
      forall hs : list formula,
      forall a b : formula,
      infers hs (Conjunction a b) ->
      infers hs b
    | OrIntro1 :
      forall hs : list formula,
      forall a b : formula,
      infers hs a ->
      infers hs (Disjunction a b)
    | OrIntro2 :
      forall hs : list formula,
      forall a b : formula,
      infers hs b ->
      infers hs (Disjunction a b)
    | OrElim :
      forall hs : list formula,
      forall a b c : formula,
      infers hs (Disjunction a b) ->
      infers (a :: hs) c ->
      infers (b :: hs) c ->
      infers hs c
    | IfthenIntro :
      forall hs : list formula,
      forall a b : formula,
      infers (a :: hs) b ->
      infers hs (Implication a b)
    | IfthenElim :
      forall hs : list formula,
      forall a b : formula,
      infers hs (Implication a b) ->
      infers hs a ->
      infers hs b
    | IffIntro :
      forall hs : list formula,
      forall a b : formula,
      infers (a :: hs) b ->
      infers (b :: hs) a ->
      infers hs (Biconditional a b)
    | IffElim1 :
      forall hs : list formula,
      forall a b : formula,
      infers hs (Biconditional a b) ->
      infers hs a ->
      infers hs b
    | IffElim2 :
      forall hs : list formula,
      forall a b : formula,
      infers hs (Biconditional a b) ->
      infers hs b ->
      infers hs a
    .

    Lemma assume_more_then_still_proves :
      forall hs1 : list formula,
      forall a : formula,
      infers hs1 a ->
      forall hs2 : list formula,
      (forall h : formula, In h hs1 -> In h hs2) ->
      infers hs2 a.
    Proof.
      intros hs1 a.
      intro.
      induction H.
      - intros hs2.
        intro.
        apply (Assumption hs2 conclusion).
        apply (H0 conclusion H).
      - intros hs2.
        intro.
        apply (BottomIntro hs2 a).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (BottomElim hs2 a).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (NotIntro hs2 a).
        apply (IHinfers (a :: hs2)).
        simpl.
        intuition.
      - intros hs2.
        intro.
        apply (NotElim hs2 a).
        apply (IHinfers (Negation a :: hs2)).
        simpl.
        intuition.
      - intros hs2.
        intro.
        apply (AndIntro hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (AndElim1 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (AndElim2 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (OrIntro1 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (OrIntro2 hs2 a b).
        apply (IHinfers hs2 H0).
      - intros hs2.
        intro.
        apply (OrElim hs2 a b c).
        apply (IHinfers1 hs2 H2).
        apply (IHinfers2 (a :: hs2)).
        simpl.
        intuition.
        apply (IHinfers3 (b :: hs2)).
        simpl.
        intuition.
      - intros hs2.
        intro.
        apply (IfthenIntro hs2 a b).
        apply (IHinfers (a :: hs2)).
        simpl.
        intuition.
      - intros hs2.
        intro.
        apply (IfthenElim hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (IffIntro hs2 a b).
        apply (IHinfers1 (a :: hs2)).
        simpl.
        intuition.
        apply (IHinfers2 (b :: hs2)).
        simpl.
        intuition.
      - intros hs2.
        intro.
        apply (IffElim1 hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
      - intros hs2.
        intro.
        apply (IffElim2 hs2 a b).
        apply (IHinfers1 hs2 H1).
        apply (IHinfers2 hs2 H1).
    Qed.

    Theorem implication_is_equal_to_assumption :
      forall hs : list formula,
      forall a b : formula,
      infers hs (Implication a b) <-> infers (a :: hs) b.
    Proof.
      assert (
        forall hs : list formula,
        forall a b : formula,
        infers hs (Implication a b) -> infers (a :: hs) b
      ).
        intros hs a b.
        intro.
        cut (infers (a :: hs) (Implication a b)).
          intro.
          apply (IfthenElim (a :: hs) a b H0).
          apply (Assumption (a :: hs) a).
          simpl.
          tauto.
          apply (assume_more_then_still_proves hs (Implication a b) H (a :: hs)).
          simpl.
          intuition.
      intros hs a b.
      constructor.
        apply (H hs a b).
        apply (IfthenIntro hs a b).
    Qed.

  End InferenceRules.

  Section Soundness.

    Proposition bottom_intro_preserves :
      forall hs : list formula,
      forall a : formula,
      entails hs a ->
      entails hs (Negation a) ->
      entails hs Contradiction.
    Proof.
      intros hs a.
      intro.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment a = true
      ).
        apply (H assignment H1).
      assert (
        satisfies assignment (Negation a) = true
      ).
        apply (H0 assignment H1).
      inversion H3.
      rewrite H2 in H5.
      inversion H5.
    Qed.

    Proposition bottom_elim_preserves :
      forall hs : list formula,
      forall a : formula,
      entails hs Contradiction ->
      entails hs a.
    Proof.
      intros hs a.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment Contradiction = true
      ).
        apply (H assignment H0).
      inversion H1.
    Qed.

    Proposition not_intro_preserves :
      forall hs : list formula,
      forall a : formula,
      entails (a :: hs) Contradiction ->
      entails hs (Negation a).
    Proof.
      intros hs a.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        (forall premise : formula, In premise (a :: hs) -> satisfies assignment premise = true) ->
        satisfies assignment Contradiction = true
      ).
        apply (H assignment).
      cut (
        satisfies assignment a = false
      ).
        intro.
        simpl.
        rewrite H2.
        intuition.
      assert (satisfies assignment a = true \/ satisfies assignment a = false).
        induction (satisfies assignment a).
        intuition.
        intuition.
      destruct H2.
      - elimtype False.
        cut (satisfies assignment Contradiction = true).
          simpl.
          intuition.
        apply H1.
        intros premise.
        simpl.
        intro.
        destruct H3.
        * rewrite H3 in H2.
          apply H2.
        * apply (H0 premise H3).
      - apply H2.
    Qed.

    Proposition not_elim_preserves :
      forall hs : list formula,
      forall a : formula,
      entails (Negation a :: hs) Contradiction ->
      entails hs a.
    Proof.
      intros hs a.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        (forall premise : formula, In premise (Negation a :: hs) -> satisfies assignment premise = true) ->
        satisfies assignment Contradiction = true
      ).
        apply (H assignment).
      assert (
        satisfies assignment a = true \/ satisfies assignment a = false
      ).
        induction (satisfies assignment a).
        intuition.
        intuition.
      destruct H2.
      - apply H2.
      - elimtype False.
        cut (satisfies assignment Contradiction = true).
          simpl.
          intuition.
        apply H1.
        intros premise.
        simpl.
        intro.
        destruct H3.
        * rewrite <- H3.
          simpl.
          rewrite H2.
          intuition.
        * apply (H0 premise H3).
    Qed.

    Proposition and_intro_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs a ->
      entails hs b ->
      entails hs (Conjunction a b).
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment a = true
      ).
        apply (H assignment H1).
      assert (
        satisfies assignment b = true
      ).
        apply (H0 assignment H1).
      simpl.
      rewrite H2.
      rewrite H3.
      intuition.
    Qed.

    Proposition and_elim1_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs (Conjunction a b) ->
      entails hs a.
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment (Conjunction a b) = true
      ).
        apply (H assignment H0).
      assert (
        satisfies assignment a = true \/ satisfies assignment a = false
      ).
        induction (satisfies assignment a).
        intuition.
        intuition.
      destruct H2.
        apply H2.
        inversion H1.
        rewrite H2.
      assert (
        satisfies assignment b = true \/ satisfies assignment b = false
      ).
        induction (satisfies assignment b).
        intuition.
        intuition.
        destruct H3.
        rewrite H3.
        tauto.
        rewrite H3.
        tauto.
    Qed.

    Proposition and_elim2_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs (Conjunction a b) ->
      entails hs b.
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment (Conjunction a b) = true
      ).
        apply (H assignment H0).
      assert (
        satisfies assignment b = true \/ satisfies assignment b = false
      ).
        induction (satisfies assignment b).
        intuition.
        intuition.
      destruct H2.
        apply H2.
        inversion H1.
        rewrite H2.
      assert (
        satisfies assignment a = true \/ satisfies assignment a = false
      ).
        induction (satisfies assignment a).
        intuition.
        intuition.
        destruct H3.
        rewrite H3.
        tauto.
        rewrite H3.
        tauto.
    Qed.

    Proposition or_intro1_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs a ->
      entails hs (Disjunction a b).
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment a = true
      ).
        apply (H assignment H0).
      cut (satisfies assignment b = true \/ satisfies assignment b = false).
        intro.
        simpl.
        rewrite H1.
        destruct H2.
          rewrite H2.
          tauto.
          rewrite H2.
          tauto.
      induction (satisfies assignment b).
        tauto.
        tauto.
    Qed.

    Proposition or_intro2_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs b ->
      entails hs (Disjunction a b).
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (
        satisfies assignment b = true
      ).
        apply (H assignment H0).
      cut (satisfies assignment a = true \/ satisfies assignment a = false).
        intro.
        simpl.
        rewrite H1.
        destruct H2.
          rewrite H2.
          tauto.
          rewrite H2.
          tauto.
      induction (satisfies assignment a).
        tauto.
        tauto.
    Qed.

    Proposition or_elim_preserves :
      forall hs : list formula,
      forall a b c : formula,
      entails hs (Disjunction a b) ->
      entails (a :: hs) c ->
      entails (b :: hs) c ->
      entails hs c.
    Proof.
      intros hs a b c.
      unfold entails in *.
      intro.
      intro.
      intro.
      intros assignment.
      intro.
      assert (satisfies assignment a = true \/ satisfies assignment b = true).
        assert (satisfies assignment (Disjunction a b) = true).
          apply (H assignment H2).
        inversion H3.
        cut (satisfies assignment a = true \/ satisfies assignment a = false).
          intro.
          destruct H4.
            rewrite H4 in *.
            apply or_introl.
            rewrite H5.
            tauto.
            cut (satisfies assignment b = true \/ satisfies assignment b = false).
              intro.
              rewrite H4 in *.
              destruct H6.
                rewrite H6 in *.
                tauto.
                rewrite H6 in *.
                inversion H5.
            induction (satisfies assignment b).
              tauto.
              tauto.
        induction (satisfies assignment a).
          tauto.
          tauto.
      destruct H3.
      - apply (H0 assignment).
        intros premise.
        simpl.
        intro.
        destruct H4.
        * rewrite H4 in H3.
          apply H3.
        * apply (H2 premise H4).
      - apply (H1 assignment).
        intros premise.
        simpl.
        intro.
        destruct H4.
        * rewrite H4 in H3.
          apply H3.
        * apply (H2 premise H4).
    Qed.

    Proposition ifthen_intro_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails (a :: hs) b ->
      entails hs (Implication a b).
    Proof.
      intros hs a b.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (satisfies assignment a = true \/ satisfies assignment a = false).
        induction (satisfies assignment a).
          tauto.
          tauto.
      assert (satisfies assignment b = true \/ satisfies assignment b = false).
        induction (satisfies assignment b).
          tauto.
          tauto.
      destruct H1.
      - destruct H2.
        * simpl.
          rewrite H1.
          rewrite H2.
          tauto.
        * assert (satisfies assignment b = true).
            apply (H assignment).
            intros premise.
            simpl.
            intro.
            destruct H3.
              rewrite <- H3.
              apply H1.
              apply (H0 premise H3).
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

    Proposition ifthen_elim_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs (Implication a b) ->
      entails hs a ->
      entails hs b.
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (satisfies assignment a = true).
        apply (H0 assignment H1).
      cut (satisfies assignment (Implication a b) = true).
        intro.
        cut (satisfies assignment b = true \/ satisfies assignment b = false).
          intro.
          destruct H4.
            apply H4.
            cut (satisfies assignment (Implication a b) = false).
              intro.
              rewrite H3 in H5.
              inversion H5.
            simpl.
            rewrite H2.
            rewrite H4.
            tauto.
        destruct (satisfies assignment b).
          tauto.
          tauto.
      apply (H assignment H1).
    Qed.

    Proposition iff_intro_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails (a :: hs) b ->
      entails (b :: hs) a ->
      entails hs (Biconditional a b).
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (satisfies assignment a = true \/ satisfies assignment a = false).
        induction (satisfies assignment a).
          tauto.
          tauto.
      assert (satisfies assignment b = true \/ satisfies assignment b = false).
        induction (satisfies assignment b).
          tauto.
          tauto.
      destruct H2.
      - destruct H3.
        * simpl.
          rewrite H2.
          rewrite H3.
          tauto.
        * assert (satisfies assignment b = true).
            apply (H assignment).
            intros premise.
            simpl.
            intro.
            destruct H4.
              rewrite <- H4.
              apply H2.
              apply (H1 premise H4).
          rewrite H4 in H3.
          inversion H3.
      - destruct H3.
        * assert (satisfies assignment a = true).
            apply (H0 assignment).
            intros premise.
            simpl.
            intro.
            destruct H4.
              rewrite <- H4.
              apply H3.
              apply (H1 premise H4).
          rewrite H4 in H2.
          inversion H2.
        * simpl.
          rewrite H2.
          rewrite H3.
          tauto.
    Qed.

    Proposition iff_elim1_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs (Biconditional a b) ->
      entails hs a ->
      entails hs b.
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (satisfies assignment b = true \/ satisfies assignment b = false).
        induction (satisfies assignment b).
          tauto.
          tauto.
      destruct H2.
        apply H2.
      assert (satisfies assignment a = true).
        apply (H0 assignment H1).
      assert (satisfies assignment (Biconditional a b) = false).
        simpl.
        rewrite H2.
        rewrite H3.
        tauto.
      assert (satisfies assignment (Biconditional a b) = true).
        apply (H assignment H1).
      rewrite H4 in H5.
      inversion H5.
    Qed.

    Proposition iff_elim2_preserves :
      forall hs : list formula,
      forall a b : formula,
      entails hs (Biconditional a b) ->
      entails hs b ->
      entails hs a.
    Proof.
      intros hs a b.
      intro.
      intro.
      unfold entails in *.
      intros assignment.
      intro.
      assert (satisfies assignment a = true \/ satisfies assignment a = false).
        induction (satisfies assignment a).
          tauto.
          tauto.
      destruct H2.
        apply H2.
      assert (satisfies assignment b = true).
        apply (H0 assignment H1).
      assert (satisfies assignment (Biconditional a b) = false).
        simpl.
        rewrite H2.
        rewrite H3.
        tauto.
      assert (satisfies assignment (Biconditional a b) = true).
        apply (H assignment H1).
      rewrite H4 in H5.
      inversion H5.
    Qed.

    Theorem weak_soundness :
      forall hypotheses : list formula,
      forall conclusion : formula,
      infers hypotheses conclusion ->
      entails hypotheses conclusion.
    Proof.
      intros hs c.
      intro.
      induction H.
      - apply (always_entails_premise hypotheses conclusion H).
      - apply (bottom_intro_preserves hs a IHinfers1 IHinfers2).
      - apply (bottom_elim_preserves hs a IHinfers).
      - apply (not_intro_preserves hs a IHinfers).
      - apply (not_elim_preserves hs a IHinfers).
      - apply (and_intro_preserves hs a b IHinfers1 IHinfers2).
      - apply (and_elim1_preserves hs a b IHinfers).
      - apply (and_elim2_preserves hs a b IHinfers).
      - apply (or_intro1_preserves hs a b IHinfers).
      - apply (or_intro2_preserves hs a b IHinfers).
      - apply (or_elim_preserves hs a b c IHinfers1 IHinfers2 IHinfers3).
      - apply (ifthen_intro_preserves hs a b IHinfers).
      - apply (ifthen_elim_preserves hs a b IHinfers1 IHinfers2).
      - apply (iff_intro_preserves hs a b IHinfers1 IHinfers2).
      - apply (iff_elim1_preserves hs a b IHinfers1 IHinfers2).
      - apply (iff_elim2_preserves hs a b IHinfers1 IHinfers2).
    Qed.

  End Soundness.

  Section Completeness.

    Inductive is_literal : formula -> Prop :=
    | literalPosVar :
      forall n : nat,
      is_literal (PropVar n)
    | literalNegVar :
      forall n : nat,
      is_literal (Negation (PropVar n))
    .

    Inductive occurs : nat -> formula -> Prop :=
    | occursPropVar :
      forall n : nat,
      occurs n (PropVar n)
    | occursNegation :
      forall n : nat,
      forall p1 : formula,
      occurs n p1 ->
      occurs n (Negation p1)
    | occursConjunction :
      forall n : nat,
      forall p1 p2 : formula,
      occurs n p1 \/ occurs n p2 ->
      occurs n (Conjunction p1 p2)
    | occursDisjunction :
      forall n : nat,
      forall p1 p2 : formula,
      occurs n p1 \/ occurs n p2 ->
      occurs n (Disjunction p1 p2)
    | occursImplication :
      forall n : nat,
      forall p1 p2 : formula,
      occurs n p1 \/ occurs n p2 ->
      occurs n (Implication p1 p2)
    | occursBiconditional :
      forall n : nat,
      forall p1 p2 : formula,
      occurs n p1 \/ occurs n p2 ->
      occurs n (Biconditional p1 p2)
    .

    Definition makeLine (assignment : nat -> bool) : list nat -> list formula :=
      List.map
        ( fun n : nat =>
            if assignment n
            then PropVar n
            else Negation (PropVar n)
        )
    .

    Lemma line_is_list_of_literals :
      forall ns : list nat,
      forall assignment : nat -> bool,
      let hs := makeLine assignment ns in
      forall h : formula,
      In h hs -> is_literal h.
    Proof.
      intros ns.
      induction ns as [| n ns].
      - intros assignment.
        simpl.
        intuition.
      - intros assignment.
        simpl.
        destruct (assignment n).
        * intros h.
          simpl.
          intro.
          destruct H.
          subst.
          apply literalPosVar.
          apply (IHns assignment h H).
        * intros h.
          simpl.
          intro.
          destruct H.
          subst.
          apply literalNegVar.
          apply (IHns assignment h H).
    Qed.

    Lemma prove_line :
      forall c : formula,
      exists ns : list nat,
      (forall n : nat, In n ns <-> occurs n c) /\
      forall assignment : nat -> bool,
      let hs := makeLine assignment ns in
      if satisfies assignment c
      then infers hs c
      else infers hs (Negation c).
    Proof.
      intros c.
      induction c.
      - exists [n].
        constructor.
        * intros n0.
          simpl.
          constructor.
          + intro.
            destruct H.
              subst.
              apply (occursPropVar n0).
              inversion H.
          + intro.
            inversion H.
            tauto.
        * intros assignment.
          assert (assignment n = true \/ assignment n = false).
            destruct (assignment n).
              intuition.
              intuition.
          destruct H.
          + simpl in *.
            rewrite H in *.
            apply (Assumption [PropVar n] (PropVar n)).
            intuition.
          + simpl in *.
            rewrite H in *.
            apply (Assumption [Negation (PropVar n)] (Negation (PropVar n))).
            intuition.
      - exists [].
        constructor.
        * intros n.
          simpl.
          constructor.
          intro.
          destruct H.
          intro.
          inversion H.
        * intros assignment.
          simpl in *.
          apply (NotIntro [] Contradiction).
          apply (Assumption [Contradiction] Contradiction).
          intuition.
      - destruct IHc as [ns H].
        destruct H.
        exists ns.
        constructor.
        * intros n.
          constructor.
          + intro.
            apply (occursNegation n c).
            apply (proj1 (H n) H1).
          + intro.
            inversion H1.
            subst.
            apply (proj2 (H n) H4).
        * intros assignment.
          intros hs.
          assert (satisfies assignment c = true \/ satisfies assignment c = false).
            destruct (satisfies assignment c).
              tauto.
              tauto.
          destruct H1.
          + simpl.
            assert (if satisfies assignment c then infers hs c else infers hs (Negation c)).
              apply (H0 assignment).
            rewrite H1 in *.
            apply (NotIntro hs (Negation c)).
            assert (infers (Negation c :: hs) c).
              apply (assume_more_then_still_proves hs c H2 (Negation c :: hs)).
              intuition.
            assert (infers (Negation c :: hs) (Negation c)).
              apply (Assumption (Negation c :: hs) (Negation c)).
              intuition.
            apply (BottomIntro (Negation c :: hs) c H3 H4).
          + simpl.
            assert (if satisfies assignment c then infers hs c else infers hs (Negation c)).
              apply (H0 assignment).
            rewrite H1 in *.
            apply H2.
      - destruct IHc1 as [ns1].
        destruct IHc2 as [ns2].
        exists (ns1 ++ ns2).
        destruct H.
        destruct H0.
        constructor.
        * intros n.
          constructor.
          + intro.
            apply (occursConjunction n c1).
            destruct (List.in_app_or ns1 ns2 n H3).
            apply (or_introl (proj1 (H n) H4)).
            apply (or_intror (proj1 (H0 n) H4)).
          + intro.
            inversion H3.
            subst.
            apply (List.in_or_app ns1 ns2 n).
            destruct H6.
            apply (or_introl (proj2 (H n) H4)).
            apply (or_intror (proj2 (H0 n) H4)).
        * intros assignment.
          intros hs.
          assert (satisfies assignment c1 = true \/ satisfies assignment c1 = false).
            destruct (satisfies assignment c1).
              tauto.
              tauto.
          assert (satisfies assignment c2 = true \/ satisfies assignment c2 = false).
            destruct (satisfies assignment c2).
              tauto.
              tauto.
          assert (hs = makeLine assignment ns1 ++ makeLine assignment ns2).
            unfold hs.
            apply (map_app).
          assert (
            if satisfies assignment c1
            then infers (makeLine assignment ns1) c1
            else infers (makeLine assignment ns1) (Negation c1)
          ).
            apply (H1 assignment).
          assert (
            if satisfies assignment c2
            then infers (makeLine assignment ns2) c2
            else infers (makeLine assignment ns2) (Negation c2)
          ).
            apply (H2 assignment).
          destruct H3.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c1).
                apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c2).
                apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              apply AndIntro.
              tauto.
              tauto.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c1).
                apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              assert (infers (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Negation c2)).
                apply (assume_more_then_still_proves (makeLine assignment ns2) (Negation c2) H7 (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_cons.
                apply in_or_app.
                intuition.
              apply NotIntro.
              apply (BottomIntro (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply (AndElim2 ((Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2)) c1 c2).
              apply (Assumption (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Conjunction c1 c2)).
              intuition.
              intuition.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              assert (infers (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Negation c1)).
                apply (assume_more_then_still_proves (makeLine assignment ns1) (Negation c1) H6 (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_cons.
                apply in_or_app.
                intuition.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c2).
                apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              apply NotIntro.
              apply (BottomIntro (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply (AndElim1 ((Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2)) c1 c2).
              apply (Assumption (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Conjunction c1 c2)).
              intuition.
              intuition.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply NotIntro.
              apply (BottomIntro (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply (AndElim1 (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1 c2).
              apply (Assumption (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Conjunction c1 c2)).
              intuition.
              assert (infers (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Negation c1)).
                apply (assume_more_then_still_proves (makeLine assignment ns1) (Negation c1) H6 (Conjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_cons.
                apply in_or_app.
                intuition.
              apply H8.
      - destruct IHc1 as [ns1].
        destruct IHc2 as [ns2].
        exists (ns1 ++ ns2).
        destruct H.
        destruct H0.
        constructor.
        * intros n.
          constructor.
          + intro.
            apply (occursDisjunction n c1).
            destruct (List.in_app_or ns1 ns2 n H3).
            apply (or_introl (proj1 (H n) H4)).
            apply (or_intror (proj1 (H0 n) H4)).
          + intro.
            inversion H3.
            subst.
            apply (List.in_or_app ns1 ns2 n).
            destruct H6.
            apply (or_introl (proj2 (H n) H4)).
            apply (or_intror (proj2 (H0 n) H4)).
        * intros assignment.
          intros hs.
          assert (satisfies assignment c1 = true \/ satisfies assignment c1 = false).
            destruct (satisfies assignment c1).
              tauto.
              tauto.
          assert (satisfies assignment c2 = true \/ satisfies assignment c2 = false).
            destruct (satisfies assignment c2).
              tauto.
              tauto.
          assert (hs = makeLine assignment ns1 ++ makeLine assignment ns2).
            unfold hs.
            apply (map_app).
          assert (
            if satisfies assignment c1
            then infers (makeLine assignment ns1) c1
            else infers (makeLine assignment ns1) (Negation c1)
          ).
            apply (H1 assignment).
          assert (
            if satisfies assignment c2
            then infers (makeLine assignment ns2) c2
            else infers (makeLine assignment ns2) (Negation c2)
          ).
            apply (H2 assignment).
          destruct H3.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c1).
                apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              apply OrIntro1.
              apply H8.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c1).
                apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              apply OrIntro1.
              apply H8.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              assert (infers (makeLine assignment ns1 ++ makeLine assignment ns2) c2).
                apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7 (makeLine assignment ns1 ++ makeLine assignment ns2)).
                intros h.
                intro.
                apply in_or_app.
                intuition.
              apply OrIntro2.
              apply H8.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply NotIntro.
              apply (OrElim (Disjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1 c2 Contradiction).
              apply (Assumption (Disjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Disjunction c1 c2)).
              intuition.
              apply (BottomIntro (c1 :: Disjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply (Assumption (c1 :: Disjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) (Negation c1) H6).
              intros h.
              intro.
              apply List.in_cons.
              apply List.in_cons.
              apply in_or_app.
              intuition.
              apply (BottomIntro (c2 :: Disjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply (Assumption (c2 :: Disjunction c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns2) (Negation c2) H7).
              intros h.
              intro.
              apply List.in_cons.
              apply List.in_cons.
              apply in_or_app.
              intuition.
      - destruct IHc1 as [ns1].
        destruct IHc2 as [ns2].
        exists (ns1 ++ ns2).
        destruct H.
        destruct H0.
        constructor.
        * intros n.
          constructor.
          + intro.
            apply (occursImplication n c1).
            destruct (List.in_app_or ns1 ns2 n H3).
            apply (or_introl (proj1 (H n) H4)).
            apply (or_intror (proj1 (H0 n) H4)).
          + intro.
            inversion H3.
            subst.
            apply (List.in_or_app ns1 ns2 n).
            destruct H6.
            apply (or_introl (proj2 (H n) H4)).
            apply (or_intror (proj2 (H0 n) H4)).
        * intros assignment.
          intros hs.
          assert (satisfies assignment c1 = true \/ satisfies assignment c1 = false).
            destruct (satisfies assignment c1).
              tauto.
              tauto.
          assert (satisfies assignment c2 = true \/ satisfies assignment c2 = false).
            destruct (satisfies assignment c2).
              tauto.
              tauto.
          assert (hs = makeLine assignment ns1 ++ makeLine assignment ns2).
            unfold hs.
            apply (map_app).
          assert (
            if satisfies assignment c1
            then infers (makeLine assignment ns1) c1
            else infers (makeLine assignment ns1) (Negation c1)
          ).
            apply (H1 assignment).
          assert (
            if satisfies assignment c2
            then infers (makeLine assignment ns2) c2
            else infers (makeLine assignment ns2) (Negation c2)
          ).
            apply (H2 assignment).
          destruct H3.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply (IfthenIntro).
              apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply (NotIntro).
              apply (BottomIntro (Implication c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply (IfthenElim (Implication c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1 c2).
              apply (Assumption (Implication c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) (Implication c1 c2)).
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns2) (Negation c2) H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply (IfthenIntro).
              apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply (IfthenIntro).
              apply (BottomElim (c1 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply (BottomIntro (c1 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply (Assumption (c1 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) (Negation c1) H6).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
      - destruct IHc1 as [ns1].
        destruct IHc2 as [ns2].
        exists (ns1 ++ ns2).
        destruct H.
        destruct H0.
        constructor.
        * intros n.
          constructor.
          + intro.
            apply (occursBiconditional n c1).
            destruct (List.in_app_or ns1 ns2 n H3).
            apply (or_introl (proj1 (H n) H4)).
            apply (or_intror (proj1 (H0 n) H4)).
          + intro.
            inversion H3.
            subst.
            apply (List.in_or_app ns1 ns2 n).
            destruct H6.
            apply (or_introl (proj2 (H n) H4)).
            apply (or_intror (proj2 (H0 n) H4)).
        * intros assignment.
          intros hs.
          assert (satisfies assignment c1 = true \/ satisfies assignment c1 = false).
            destruct (satisfies assignment c1).
              tauto.
              tauto.
          assert (satisfies assignment c2 = true \/ satisfies assignment c2 = false).
            destruct (satisfies assignment c2).
              tauto.
              tauto.
          assert (hs = makeLine assignment ns1 ++ makeLine assignment ns2).
            unfold hs.
            apply (map_app).
          assert (
            if satisfies assignment c1
            then infers (makeLine assignment ns1) c1
            else infers (makeLine assignment ns1) (Negation c1)
          ).
            apply (H1 assignment).
          assert (
            if satisfies assignment c2
            then infers (makeLine assignment ns2) c2
            else infers (makeLine assignment ns2) (Negation c2)
          ).
            apply (H2 assignment).
          destruct H3.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply IffIntro.
              apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply NotIntro.
              apply (BottomIntro (Biconditional c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply (IffElim1 (Biconditional c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1 c2).
              apply Assumption.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) c1 H6).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns2) (Negation c2) H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
          + destruct H4.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply NotIntro.
              apply (BottomIntro (Biconditional c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply (IffElim2 (Biconditional c1 c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1 c2).
              apply Assumption.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns2) c2 H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) (Negation c1) H6).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              simpl in *.
              rewrite H3 in *.
              rewrite H4 in *.
              rewrite H5 in *.
              apply IffIntro.
              apply (BottomElim (c1 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply (BottomIntro (c1 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply Assumption.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns1) (Negation c1) H6).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
              apply (BottomElim (c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c1).
              apply (BottomIntro (c2 :: makeLine assignment ns1 ++ makeLine assignment ns2) c2).
              apply Assumption.
              intuition.
              apply (assume_more_then_still_proves (makeLine assignment ns2) (Negation c2) H7).
              intros h.
              intro.
              apply in_cons.
              apply in_or_app.
              intuition.
    Qed.

    Proposition proof_of_ex_middle :
      forall p : formula,
      infers [] (Disjunction p (Negation p)).
    Proof.
      intros c.
      apply (NotElim [] (Disjunction c (Negation c))).
      apply (BottomIntro [Negation (Disjunction c (Negation c))] (Disjunction c (Negation c))).
      apply (OrIntro2 [Negation (Disjunction c (Negation c))] c (Negation c)).
      apply (NotIntro [Negation (Disjunction c (Negation c))] c).
      apply (BottomIntro [c; Negation (Disjunction c (Negation c))] (Disjunction c (Negation c))).
      apply (OrIntro1 [c; Negation (Disjunction c (Negation c))] c ((Negation c))).
      apply (Assumption [c; Negation (Disjunction c (Negation c))] c).
      intuition.
      apply (Assumption [c; Negation (Disjunction c (Negation c))] (Negation (Disjunction c (Negation c)))).
      intuition.
      apply (Assumption [Negation (Disjunction c (Negation c))] (Negation (Disjunction c (Negation c)))).
      intuition.
    Qed.

    Lemma merge_line :
      forall ns : list nat,
      forall c : formula,
      (forall n : nat, In n ns -> occurs n c) ->
      (forall assignment : nat -> bool, infers (makeLine assignment ns) c) ->
      infers [] c.
    Proof.
      assert (
        forall f1 f2 : nat -> formula,
        forall xs : list nat,
        (forall x : nat, In x xs -> f1 x = f2 x) ->
        map f1 xs = map f2 xs
      ).
        intros f1 f2.
        intros xs.
        induction xs as [| x xs].
          intuition.
          intuition.
          simpl.
          assert (f1 x = f2 x).
            apply (H x).
            intuition.
          assert (map f1 xs = map f2 xs).
            apply IHxs.
            intros x0.
            intro.
            apply (H x0).
            intuition.
          rewrite H0.
          rewrite H1.
          tauto. 
      intros ns.
      induction ns as [| n ns].
      - intros c.
        simpl.
        intro.
        intro.
        apply H1.
        intros n.
        apply false.
      - intros c.
        intro.
        intro.
        destruct (List.in_dec Nat.eq_dec n ns).
        * apply IHns.
          intros n0.
          assert (In n0 (n :: ns) -> occurs n0 c).
            apply (H0 n0).
          simpl.
          destruct (Nat.eq_dec n0 n).
          subst.
          intuition.
          intro.
          subst.
          simpl In in H1. 
          intuition.
          intuition.
          apply (assume_more_then_still_proves (makeLine assignment (n :: ns)) c).
          apply (H1 assignment).
          intros h.
          simpl.
          intro.
          destruct H2.
          unfold makeLine.
          subst.
          apply (
            in_map
              ( fun n0 : nat =>
                if assignment n0
                then PropVar n0
                else Negation (PropVar n0)
              )
              ns
              n
              i
          ).
          apply H2.
        * apply IHns.
          intros n1.
          intro.
          assert (n <> n1).
            intro.
            subst.
            apply (n0 H2).
          intuition.
          intro.
          assert (assignment n = true \/ assignment n = false).
            destruct (assignment n).
              tauto.
              tauto.
          destruct H2.
          + assert (
              let assignment1 :=
                fun n1 : nat =>
                  if Nat.eq_dec n1 n
                  then false
                  else assignment n1
              in
              infers (Negation (PropVar n) :: makeLine assignment1 ns) c
            ).
              intro.
              assert (infers (makeLine assignment1 (n :: ns)) c).
                apply (H1 assignment1).
              unfold makeLine in *.
              unfold assignment1 in *.
              simpl in H3.
              destruct (Nat.eq_dec n n).
              apply H3.
              tauto.
            assert (
              let assignment1 :=
                fun n1 : nat =>
                  if Nat.eq_dec n1 n
                  then false
                  else assignment n1
              in
              makeLine assignment1 ns = makeLine assignment ns
            ).
              apply H.
              intros x.
              intro.
              destruct (Nat.eq_dec x n).
              subst.
              tauto.
              tauto.
            assert (infers (makeLine assignment (n :: ns)) c).
              apply (H1 assignment).
            simpl in H5.
            rewrite H2 in H5.
            assert (infers (Negation (PropVar n) :: makeLine assignment ns) c).
              rewrite <- H4.
              apply H3.
            assert (infers (makeLine assignment ns) (Disjunction (PropVar n) (Negation (PropVar n)))).
              apply (assume_more_then_still_proves [] (Disjunction (PropVar n) (Negation (PropVar n)))).
              apply (proof_of_ex_middle (PropVar n)).
              intros h.
              simpl.
              intuition.
            apply (OrElim (makeLine assignment ns) (PropVar n) (Negation (PropVar n)) c H7 H5 H6).
          + assert (
              let assignment1 :=
                fun n1 : nat =>
                  if Nat.eq_dec n1 n
                  then true
                  else assignment n1
              in
              infers (PropVar n :: makeLine assignment1 ns) c
            ).
              intro.
              assert (infers (makeLine assignment1 (n :: ns)) c).
                apply (H1 assignment1).
              unfold makeLine in *.
              unfold assignment1 in *.
              simpl in H3.
              destruct (Nat.eq_dec n n).
              apply H3.
              tauto.
            assert (
              let assignment1 :=
                fun n1 : nat =>
                  if Nat.eq_dec n1 n
                  then true
                  else assignment n1
              in
              makeLine assignment1 ns = makeLine assignment ns
            ).
              apply H.
              intros x.
              intro.
              destruct (Nat.eq_dec x n).
              subst.
              tauto.
              tauto.
            assert (infers (makeLine assignment (n :: ns)) c).
              apply (H1 assignment).
            simpl in H5.
            rewrite H2 in H5.
            assert (infers (PropVar n :: makeLine assignment ns) c).
              rewrite <- H4.
              apply H3.
            assert (infers (makeLine assignment ns) (Disjunction (PropVar n) (Negation (PropVar n)))).
              apply (assume_more_then_still_proves [] (Disjunction (PropVar n) (Negation (PropVar n)))).
              apply (proof_of_ex_middle (PropVar n)).
              intros h.
              simpl.
              intuition.
            apply (OrElim (makeLine assignment ns) (PropVar n) (Negation (PropVar n)) c H7 H6 H5).
    Qed.

    Theorem tautology_is_theorem :
      forall c : formula,
      entails [] c ->
      infers [] c.
    Proof.
      intros c.
      unfold entails.
      simpl.
      intro.
      assert (
        exists ns : list nat,
        (forall n : nat, In n ns -> occurs n c) /\
        forall assignment : nat -> bool,
        let hs := makeLine assignment ns in
        if satisfies assignment c
        then infers hs c
        else infers hs (Negation c)
      ).
        destruct (prove_line c) as [ns].
        exists ns.
        intuition.
        apply (proj1 (H1 n) H0).
      destruct H0 as [ns H0].
      destruct H0.
      apply (merge_line ns c).
      apply H0.
      intros assignment.
      cut (satisfies assignment c = true).
        assert (
          let hs := makeLine assignment ns in
          if satisfies assignment c
          then infers hs c
          else infers hs (Negation c)
        ).
          apply (H1 assignment).
        intro.
        rewrite H3 in *.
        apply H2.
      apply (H assignment).
      tauto.
    Qed.

    Fixpoint charge_implication (hs : list formula) (c : formula) : formula :=
      match hs with
      | [] => c
      | h :: hs' => charge_implication hs' (Implication h c)
      end
    .

    Lemma charging_implication_preserves_entailment :
      forall hs : list formula,
      forall c : formula,
      entails hs c <-> entails [] (charge_implication hs c).
    Proof.
      intros hs.
      induction hs as [| h hs].
      - simpl.
        tauto.
      - simpl.
        intros c.
        assert (entails hs (Implication h c) <-> entails [] (charge_implication hs (Implication h c))).
          apply (IHhs (Implication h c)).
        cut (entails hs (Implication h c) <-> entails (h :: hs) c).
          intuition.
        constructor.
        * intro.
          apply (ifthen_elim_preserves (h :: hs) h c).
          apply (premise_more_then_still_entails hs (Implication h c) H0).
          intuition.
          apply (always_entails_premise (h :: hs) h).
          intuition.
        * apply (ifthen_intro_preserves hs h c).
    Qed.

    Lemma charging_implication_preserves_proof :
      forall hs : list formula,
      forall c : formula,
      infers hs c <-> infers [] (charge_implication hs c).
    Proof.
      intros hs.
      induction hs as [| h hs].
      - simpl.
        intuition.
      - intros c.
        simpl.
        assert (infers hs (Implication h c) <-> infers [] (charge_implication hs (Implication h c))).
          apply (IHhs (Implication h c)).
        cut (infers hs (Implication h c) <-> infers (h :: hs) c).
          intuition.
        constructor.
        * intro.
          apply (IfthenElim (h :: hs) h c).
          apply (assume_more_then_still_proves hs (Implication h c) H0).
          intuition.
          apply (Assumption (h :: hs) h).
          intuition.
        * apply (IfthenIntro).
    Qed.

    Theorem weak_completeness :
      forall premises : list formula,
      forall consequence : formula,
      entails premises consequence ->
      infers premises consequence.
    Proof.
      intros hs c.
      intro.
      apply (proj2 (charging_implication_preserves_proof hs c)).
      apply (tautology_is_theorem (charge_implication hs c)).
      apply (proj1 (charging_implication_preserves_entailment hs c) H).
    Qed.

  End Completeness.

End PropositionalLogic.
