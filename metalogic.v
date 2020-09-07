Require Export List.
Require Export Bool.
Require Export PeanoNat.

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

    Proposition or_intros2_preserves :
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

(* Theorem soundness_of_propositional_logic :
      forall hypotheses : list formula,
      forall conclusion : formula,
      infers hypotheses conclusion ->
      entails hypotheses conclusion.
    Proof.
    Qed.
*)

  End Soundness.

  Section Completeness.

(*  Theorem completeness_of_propositional_logic :
      forall consequence : formula,
      forall premises : list formula,
      entails premises consequence ->
      infers premises consequence.
    Proof.
    Qed.
*)

  End Completeness.

End PropositionalLogic.
