(* Goedel's Incompleteness Theorems - Ranymond M. Smullyan *)

Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export List.
Require Export Lia.

Module Helper.

  Import ListNotations.

  Section NaturalNumber.

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

    Theorem SecondPrincipleOfFiniteInduction :
      forall phi : nat -> Prop,
      let phi' : nat -> Prop := fun k : nat => (forall i : nat, i < k -> phi i) in
      (forall k : nat, phi' k -> phi k) ->
      (forall n : nat, phi n).
    Proof.
      intros phi.
      intros phi'.
      intro.
      cut (
        (forall n : nat, phi n /\ phi' n)
      ).
        intro.
        intros n.
        destruct (H0 n).
        apply H1.
      intros n.
      induction n.
      - assert (phi' 0).
          intros i.
          lia.
        constructor.
        apply H.
        apply H0.
        apply H0.
      - assert (phi' (S n)).
          intros i.
          intro.
          inversion H0.
          destruct IHn.
          apply H1.
          subst.
          destruct IHn.
          apply (H3 i).
          lia.
        constructor.
        apply H.
        apply H0.
        apply H0.
    Qed.

    Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => if p (first_nat p n') then first_nat p n' else n
      end
    .

    Lemma well_ordering_principle : 
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

    Theorem WellOrderingPrinciple :
      forall Phi : nat -> Prop,
      (forall i : nat, {Phi i} + {~ Phi i}) ->
      {n : nat | Phi n} ->
      {m : nat | Phi m /\ (forall i : nat, Phi i -> i >= m)}.
    Proof.
      intros Phi H_Phi_dec H_n_exists.
      destruct H_n_exists as [n].
      destruct (well_ordering_principle (fun i : nat => if H_Phi_dec i then true else false) n).
      destruct (H_Phi_dec n).
      tauto.
      tauto.
      apply (exist (fun m : nat => Phi m /\ (forall i : nat, Phi i -> i >= m)) (first_nat (fun i : nat => if H_Phi_dec i then true else false) n)).
      constructor.
      destruct (H_Phi_dec (first_nat (fun i : nat => if H_Phi_dec i then true else false) n)).
      apply p0.
      contradiction n0.
      inversion H.
      intros i.
      intro.
      apply H0.
      destruct (H_Phi_dec i).
      tauto.
      tauto.
    Qed.

  End NaturalNumber.

  Section CantorPairing.

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

  End CantorPairing.

  Section Ensembles.

    Definition Ensemble (A : Type) : Type :=
      A -> Prop
    .

    Definition member {A : Type} (x : A) (xs : Ensemble A) : Prop :=
      xs x
    .

    Definition isSubsetOf {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Prop :=
      forall x : A, member x xs1 -> member x xs2
    .

    Inductive empty {A : Type} : Ensemble A :=
    .

    Inductive singleton {A : Type} : A -> Ensemble A :=
    | InSingleton :
      forall x : A,
      member x (singleton x)
    .

    Inductive union {A : Type} : Ensemble A -> Ensemble A -> Ensemble A :=
    | InUnionL :
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      forall x : A,
      member x xs1 ->
      member x (union xs1 xs2)
    | InUnionR :
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      forall x : A,
      member x xs2 ->
      member x (union xs1 xs2)
    .

    Definition insert {A : Type} (x1 : A) (xs2 : Ensemble A) : Ensemble A :=
      union (singleton x1) xs2
    .

    Definition intersection {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs1 /\ member x xs2
    .

    Definition complement {A : Type} (xs1 : Ensemble A) : Ensemble A :=
      fun x : A => ~ member x xs1
    .

    Definition difference {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs1 /\ member x (complement xs2)
    .

    Definition delete {A : Type} (x1 : A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs2 /\ x <> x1
    .

  End Ensembles.

  Section Classic.

    Axiom ExclusiveMiddle : forall P : Prop, P \/ ~ P.

  End Classic.

End Helper.

Module The_General_Idea_Behind_Goedel's_Proof.

  Import ListNotations.

  Import Helper.
  
  Section Abstract_Forms_Of_Goedel's_and_Tarski's_Theorems.

    Class GoedelianLanguage (E : Type) : Type :=
      { enumE : nat -> E
      ; eq_E_dec : forall e1 : E, forall e2 : E, {e1 = e2} + {e1 <> e2}
      ; E_is_denumerable : forall e : E, {n : nat | enumE n = e}
      ; isSentence : Ensemble E
      ; isProvable : Ensemble E
      ; isRefutable : Ensemble E
      ; isPredicate : Ensemble E
      ; nat_application : E -> nat -> E
      ; isTrue : Ensemble E
      ; provable_sentence : isSubsetOf isProvable isSentence 
      ; refutable_sentence : isSubsetOf isRefutable isSentence
      ; atomic_sentence : forall h : E, isPredicate h -> forall n : nat, isSentence (nat_application h n)
      ; true_sentence : isSubsetOf isTrue isSentence
      }
    .

    Variable E : Type.

    Variable L : GoedelianLanguage E.

    Definition diagonalize (n : nat) : nat :=
      proj1_sig (E_is_denumerable (nat_application (enumE n) n))
    .

    Lemma property_of_diagonalization :
      forall n : nat,
      forall e : E,
      enumE n = e ->
      enumE (diagonalize n) = nat_application e n.
    Proof.
      intros n e equality.
      unfold diagonalize.
      subst.
      destruct (E_is_denumerable (nat_application (enumE n) n)) as [n'].
      simpl.
      apply e.
    Qed.

    Definition express (h : E) (ns : Ensemble nat) : Prop :=
      forall n : nat, isTrue (nat_application h n) <-> member n ns
    .

    Inductive star : Ensemble nat -> Ensemble nat :=
    | InStar :
      forall n : nat,
      forall ns : Ensemble nat,
      member (diagonalize n) ns ->
      member n (star ns)
    .

    Definition isCorrect : Prop :=
      isSubsetOf isProvable isTrue /\ isSubsetOf (intersection isRefutable isTrue) empty
    .

    Inductive provables : Ensemble nat :=
    | InProvables :
      forall n : nat,
      isProvable (enumE n) ->
      member n provables
    .

    Theorem After_Goedel_with_shades_of_Tarski :
      forall L_is_correct : isCorrect,
      forall star_of_completement_of_provables_is_expressible : exists h : E, express h (star (complement provables)),
      exists e : E, isTrue e /\ ~ isProvable e.
    Proof.
      intros L_is_correct star_of_completement_of_provables_is_expressible.
      destruct star_of_completement_of_provables_is_expressible as [h].
      destruct (E_is_denumerable h) as [n].
      assert (isTrue (enumE (diagonalize n)) <-> member n (star (complement provables))).
        assert (isTrue (nat_application h n) <-> member n (star (complement provables))).
          apply H.
        assert (enumE (diagonalize n) = nat_application h n).
          apply property_of_diagonalization.
          apply e.
        rewrite H1.
        apply H0.
      assert (isTrue (enumE (diagonalize n)) <-> ~ isProvable (enumE (diagonalize n))).
        assert (member n (star (complement provables)) <-> ~ isProvable (enumE (diagonalize n))).
          constructor.
          intro.
          intro.
          inversion H1.
          subst.
          contradiction H3.
          apply InProvables.
          apply H2.
          intro.
          apply InStar.
          intro.
          contradiction H1.
          inversion H2.
          subst.
          apply H3.
        intuition.
      exists (enumE (diagonalize n)).
      destruct (ExclusiveMiddle (isProvable (enumE (diagonalize n)))).
      assert (~ isTrue (enumE (diagonalize n))).
        intuition.
      contradiction H3.
      destruct L_is_correct.
      apply H4.
      apply H2.
      intuition.
    Qed.

    Definition GOAL1 : Prop :=
      forall ns : Ensemble nat, (exists h : E, express h ns) -> (exists h : E, express h (star ns))
    .

    Definition GOAL2 : Prop :=
      forall ns : Ensemble nat, (exists h : E, express h ns) -> (exists h : E, express h (complement ns))
    .

    Definition GOAL3 : Prop :=
      (exists h : E, express h provables)
    .

  End Abstract_Forms_Of_Goedel's_and_Tarski's_Theorems.

End The_General_Idea_Behind_Goedel's_Proof.
