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
