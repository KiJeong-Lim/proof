Require Export List.
Require Export Bool.

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

    Fixpoint satisfy (assignment : nat -> bool) (p : formula) : bool :=
      match p with
      | PropVar n => assignment n
      | Contradiction => false
      | Negation p1 =>
        match satisfy assignment p1 with
        | true => false
        | false => true
        end
      | Conjunction p1 p2 =>
        match satisfy assignment p1, satisfy assignment p2 with
        | true, true => true
        | true, false => false
        | false, true => false
        | false, false => false
        end
      | Disjunction p1 p2 =>
        match satisfy assignment p1, satisfy assignment p2 with
        | true, true => true
        | true, false => true
        | false, true => true
        | false, false => false
        end
      | Implication p1 p2 =>
        match satisfy assignment p1, satisfy assignment p2 with
        | true, true => true
        | true, false => false
        | false, true => true
        | false, false => true
        end
      | Biconditional p1 p2 =>
        match satisfy assignment p1, satisfy assignment p2 with
        | true, true => true
        | true, false => false
        | false, true => false
        | false, false => true
        end
      end
    .

    Fixpoint is_model (assignment : nat -> bool) (premises : list formula) : bool :=
      match premises with
      | [] => true
      | premise :: premises' => andb (satisfy assignment premise) (is_model assignment premises')
      end
    .

    Definition entails (premises : list formula) (consequence : formula) : Prop := forall assignment : nat -> bool, is_model assignment premises = true -> satisfy assignment consequence = true.

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

  End InferenceRules.
  
  Section Soundness.

    Theorem soundness_of_propositional_logic :
      forall conclusion : formula,
      forall hypotheses : list formula,
      infers hypotheses conclusion ->
      entails hypotheses conclusion.
    Proof.
    Qed.

  End Soundness.

  Section Completeness.

    Theorem completeness_of_propositional_logic :
      forall consequence : formula,
      forall premises : list formula,
      entails premises consequence ->
      infers premises consequence.
    Proof.
    Qed.

  End Completeness.

End PropositionalLogic.
