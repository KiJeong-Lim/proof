(* Goedel's Incompleteness Theorems - Ranymond M. Smullyan *)

Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export List.
Require Export Lia.

Module Preliminaries.

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

  Section Lists.
    
    Fixpoint lookup {A : Type} {B : Type} (eq_A_dec : forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2}) (x : A) (ps : list (A * B)) : option B :=
      match ps with
      | [] => None
      | (x1, y1) :: ps2 => if eq_A_dec x x1 then Some y1 else lookup eq_A_dec x ps2
      end
    .

  End Lists.

End Preliminaries.

Module The_General_Idea_Behind_Goedel's_Proof.

  Import ListNotations.

  Import Preliminaries.
  
  Section Abstract_Forms_Of_Goedel's_and_Tarski's_Theorems.

    Class GoedelianLanguage (E : Type) : Type :=
      { enumE : nat -> E
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

    Definition isExpressible (ns : Ensemble nat) : Prop :=
      exists h : E, express h ns
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
      isCorrect ->
      isExpressible (star (complement provables)) ->
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
      assert (~ isProvable (enumE (diagonalize n))).
        intro.
        destruct L_is_correct.
        assert (isTrue (enumE (diagonalize n))).
          apply H3.
          apply H2.
        apply (proj1 H1).
        apply H5.
        apply H2.
      tauto.
    Qed.

    Definition GOAL1 : Prop :=
      forall ns : Ensemble nat, isExpressible ns -> isExpressible (star ns)
    .

    Definition GOAL2 : Prop :=
      forall ns : Ensemble nat, isExpressible ns -> isExpressible (complement ns)
    .

    Definition GOAL3 : Prop :=
      isExpressible provables
    .

    Definition isGoedelSentence (e : E) (ns : Ensemble nat) : Prop :=
      exists n : nat, (enumE n = e) /\ (isTrue e <-> member n ns)
    .

    Lemma A_Diagonal_Lemma_a :
      forall ns : Ensemble nat,
      isExpressible (star ns) ->
      exists e : E, isGoedelSentence e ns.
    Proof.
      intros ns.
      intro.
      destruct H as [h].
      destruct (E_is_denumerable h) as [n].
      exists (nat_application h n).
      assert (isTrue (nat_application h n) <-> member (diagonalize n) ns).
        assert (member (diagonalize n) ns <-> member n (star ns)).
          constructor.
          intro.
          apply InStar.
          apply H0.
          intro.
          inversion H0.
          apply H1.
        assert (isTrue (nat_application h n) <-> member n (star ns)).
          apply H.
        intuition.
      exists (diagonalize n).
      constructor.
      apply property_of_diagonalization.
      apply e.
      apply H0.
    Qed.

    Lemma A_Diagonal_Lemma_b :
      GOAL1 ->
      forall ns : Ensemble nat,
      isExpressible ns ->
      exists e : E, isGoedelSentence e ns.
    Proof.
      intros goal_1 ns ns_is_expressible.
      apply A_Diagonal_Lemma_a.
      apply goal_1.
      apply ns_is_expressible.
    Qed.

    Inductive trues : Ensemble nat :=
    | InTrues :
      forall n : nat,
      isTrue (enumE n) ->
      member n trues
    .

    Lemma there_is_no_goedel_sentence_of_complement_of_trues :
      ~ (exists e : E, isGoedelSentence e (complement trues)).
    Proof.
      intro.
      destruct H as [h].
      destruct H as [n].
      destruct H.
      assert (isTrue h <-> ~ member n trues).
        assert (member n (complement trues) <-> ~ member n trues).
          unfold complement.
          unfold member.
          tauto.
        intuition.
      assert (isTrue h <-> member n trues).
        constructor.
        intro.
        apply InTrues.
        rewrite H.
        apply H2.
        intro.
        inversion H2.
        subst.
        apply H3.
      intuition.
    Qed.

    Theorem After_Tarski_1 :
      ~ isExpressible (star (complement trues)).
    Proof.
      intro.
      destruct (A_Diagonal_Lemma_a (complement trues) H) as [h].
      apply there_is_no_goedel_sentence_of_complement_of_trues.
      exists h.
      apply H0.
    Qed.

    Theorem After_Tarski_2 :
      GOAL1 ->
      ~ isExpressible (complement trues).
    Proof.
      intro.
      intro.
      apply After_Tarski_1.
      apply H.
      apply H0.
    Qed.

    Theorem After_Tarski_3 :
      GOAL1 ->
      GOAL2 ->
      ~ isExpressible trues.
    Proof.
      intro.
      intro.
      intro.
      apply After_Tarski_1.
      apply H.
      apply H0.
      apply H1.
    Qed.

  End Abstract_Forms_Of_Goedel's_and_Tarski's_Theorems.

  Section Undecidable_Sentences_of_L.

    Variable E : Type.

    Variable L : GoedelianLanguage E. 

    Definition isDecidable (e : E) : Prop :=
      isProvable e \/ isRefutable e
    .

    Definition isIncomplete : Prop :=
      exists e : E, ~ isDecidable e
    .

    Theorem theorem_of_1_2_1 :
      isCorrect E L ->
      isExpressible E L (star E L (complement (provables E L))) ->
      isIncomplete.
    Proof.
      intro.
      intro.
      destruct (After_Goedel_with_shades_of_Tarski E L H H0) as [e].
      exists e.
      intro.
      destruct H2.
      tauto.
      destruct H.
      assert (member e empty).
        apply H3.
        constructor.
        tauto.
        tauto.
      inversion H4.
    Qed.

    Inductive refutables : Ensemble nat :=
    | InRefutables :
      forall n : nat,
      isRefutable (enumE n) ->
      member n refutables
    .

    Theorem theorem_of_1_2_2 :
      isCorrect E L ->
      forall k : E,
      express E L k (star E L refutables) ->
      forall n : nat,
      enumE n = k ->
      ~ isDecidable (nat_application k n).
    Proof.
      intro.
      intros k.
      intro.
      intros n.
      intro.
      intro.
      assert (isTrue (nat_application k n) <-> member (diagonalize E L n) refutables).
        assert (member (diagonalize E L n) refutables <-> member n (star E L refutables)).
          constructor.
          intro.
          apply InStar.
          apply H3.
          intro.
          inversion H3.
          apply H4.
        assert (isTrue (nat_application k n) <-> member n (star E L refutables)).
          apply H0.
        intuition.
      assert (enumE (diagonalize E L n) = nat_application (enumE n) n).
        apply property_of_diagonalization.
        tauto.
      destruct H.
      destruct H2.
      assert (isTrue (nat_application k n)).
        apply (H (nat_application k n) H2).
      assert (member (nat_application k n) (intersection isRefutable isTrue)).
        constructor.
        assert (member (diagonalize E L n) refutables).
          apply (proj1 H3 H6).
        inversion H7.
        subst.
        rewrite <- H4.
        apply H8.
        tauto.
      assert (member (nat_application k n) empty).
        apply (H5 (nat_application k n) H7).
      inversion H8.
      assert (isTrue (nat_application k n)).
        apply H3.
        apply InRefutables.
        rewrite H4.
        rewrite H1.
        apply H2.
      assert (member (nat_application k n) empty).
        apply H5.
        constructor.
        apply H2.
        apply H6.
      inversion H7.
    Qed.

  End Undecidable_Sentences_of_L.

  Section Exercise.

    Variable E : Type.

    Variable L : GoedelianLanguage E.

    Example exercise_1_1 :
      isCorrect E L ->
      isExpressible E L (star E L (provables E L)) ->
      (forall h : E, exists h' : E, forall n : nat, isProvable (nat_application h' n) <-> isRefutable (nat_application h n)) ->
      isIncomplete E L.
    Proof.
      intros.
      destruct H0 as [k].
      destruct (H1 k) as [k'].
      destruct (E_is_denumerable k) as [n].
      destruct (E_is_denumerable k') as [n'].
      assert (enumE (diagonalize E L n) = nat_application k n).
        apply property_of_diagonalization.
        apply e.
      assert (enumE (diagonalize E L n') = nat_application k' n').
        apply property_of_diagonalization.
        apply e0.
      unfold express in H0.
      exists (nat_application k n').
      destruct H.
      intro.
      assert (isTrue (nat_application k n') <-> member n' (star E L (provables E L))).
        apply H0.
      destruct H6.
      assert (member n' (star E L (provables E L))).
        apply H7.
        apply H.
        apply H6.
      assert (isProvable (nat_application k' n')).
        rewrite <- H4.
        inversion H8.
        subst.
        inversion H9.
        subst.
        apply H10.
      assert (isRefutable (nat_application k n')).
        apply H2.
        apply H9.
      assert (member (nat_application k n') empty).
        apply H5.
        constructor.
        apply H10.
        apply H.
        apply H6.
      inversion H11.
      assert (isTrue (nat_application k n')).
        apply H7.
        apply InStar.
        apply InProvables.
        rewrite H4.
        apply H2.
        apply H6.
      assert (member (nat_application k n') empty).
        apply H5.
        constructor.
        apply H6.
        apply H8.
      inversion H9.
    Qed.

    Definition represent (h : E) (ns : Ensemble nat) : Prop :=
      forall n : nat, isProvable (nat_application h n) <-> member n ns
    .

    Definition isRepresentable (ns : Ensemble nat) : Prop :=
      exists h : E, represent h ns
    .

    Definition isConsistent : Prop :=
      isSubsetOf (intersection isProvable isRefutable) empty
    .

    Example exercise_1_2 :
      isConsistent ->
      isRepresentable (star E L (refutables E L)) ->
      isIncomplete E L.
    Proof.
      intro.
      intro.
      destruct H0 as [k].
      destruct (E_is_denumerable k) as [n].
      assert (enumE (diagonalize E L n) = nat_application k n).
        apply property_of_diagonalization.
        apply e.
      exists (nat_application k n).
      intro.
      destruct H2.
      assert (isRefutable (nat_application k n)).
        assert (member n (star E L (refutables E L))).
          apply H0.
          apply H2.
        inversion H3.
        subst.
        inversion H4.
        subst.
        rewrite <- H1.
        apply H5.
      assert (member (nat_application k n) empty).
        apply H.
        constructor.
        apply H2.
        apply H3.
      inversion H4.
      assert (isProvable (nat_application k n)).
        apply H0.
        apply InStar.
        apply InRefutables.
        rewrite H1.
        apply H2.
      assert (member (nat_application k n) empty).
        apply H.
        constructor.
        apply H3.
        apply H2.
      inversion H4.
    Qed.

    Example exercise_1_3 :
      forall ns : Ensemble nat,
      isSubsetOf (star E L (refutables E L)) ns ->
      isSubsetOf (intersection ns (star E L (provables E L))) empty ->
      isRepresentable ns ->
      isIncomplete E L.
    Proof.
      intros.
      destruct H1 as [k].
      destruct (E_is_denumerable k) as [n].
      assert (enumE (diagonalize E L n) = nat_application k n).
        apply property_of_diagonalization.
        apply e.
      exists (nat_application k n).
      intro.
      destruct H3.
      assert (member n ns).
        apply H1.
        apply H3.
      assert (member n empty).
        apply H0.
        constructor.
        apply H4.
        apply InStar.
        apply InProvables.
        rewrite H2.
        apply H3.
      inversion H5.
      assert (member n ns).
        apply H.
        apply InStar.
        apply InRefutables.
        rewrite H2.
        apply H3.
      assert (member n empty).
        apply H0.
        constructor.
        apply H4.
        apply InStar.
        apply InProvables.
        rewrite H2.
        apply H1.
        apply H4.
      inversion H5.
    Qed.

    Definition contrarepresent (h : E) (ns : Ensemble nat) : Prop :=
      forall n : nat, isRefutable (nat_application h n) <-> member n ns
    .

    Definition isContraprepresentable (ns : Ensemble nat) : Prop :=
      exists h : E, contrarepresent h ns
    .

    Example exercise_1_4 :
      isConsistent ->
      isContraprepresentable (star E L (provables E L)) ->
      isIncomplete E L.
    Proof.
      intro.
      intro.
      destruct H0 as [k].
      destruct (E_is_denumerable k) as [n].
      assert (enumE (diagonalize E L n) = nat_application k n).
        apply property_of_diagonalization.
        apply e.
      exists (nat_application k n).
      intro.
      destruct H2.
      assert (member n (star E L (provables E L))).
        apply InStar.
        apply InProvables.
        rewrite H1.
        apply H2.
      assert (isRefutable (nat_application k n)).
        apply H0.
        apply H3.
      assert (member (nat_application k n) empty).
        apply H.
        constructor.
        apply H2.
        apply H4.
      inversion H5.
      assert (member n (star E L (provables E L))).
        apply H0.
        apply H2.
      inversion H3.
      subst.
      inversion H4.
      subst.
      assert (member (enumE (diagonalize E L n)) empty).
        apply H.
        constructor.
        apply H5.
        rewrite H1.
        apply H2.
      inversion H6.
    Qed.

  End Exercise.

End The_General_Idea_Behind_Goedel's_Proof.

Module Tarski's_Theorem_for_Arithmetic.

  Import ListNotations.

  Import Preliminaries.

  Import The_General_Idea_Behind_Goedel's_Proof.

  Section The_Language_L_E.

    Definition Var : Set :=
      nat
    .

    Inductive Alphabet : Set :=
    | A_Ze : Alphabet
    | A_Sc : Alphabet
    | A_LP : Alphabet
    | A_RP : Alphabet
    | A_Fun : Alphabet
    | A_Dot : Alphabet
    | A_Var : Alphabet
    | A_Neg : Alphabet
    | A_Imp : Alphabet
    | A_All : Alphabet
    | A_Eqn : Alphabet
    | A_Leq : Alphabet
    | A_Sharp : Alphabet
    .

    Lemma eq_Alphabet_dec :
      forall a1 : Alphabet,
      forall a2 : Alphabet,
      {a1 = a2} + {a1 <> a2}.
    Proof.
      intros a1; induction a1.
      - intros a2; destruct a2. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto. right; intro; inversion H.
      - intros a2; destruct a2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. left; tauto.
    Qed.

    Definition E : Type :=
      list Alphabet
    .

    Definition eq_E_dec : forall e1 : E, forall e2 : E, {e1 = e2} + {e1 <> e2} :=
      list_eq_dec eq_Alphabet_dec
    .

    Fixpoint mkNumRep (n : nat) : E :=
      match n with
      | 0 => [A_Ze]
      | S n' => mkNumRep n' ++ [A_Sc]
      end
    .

    Fixpoint mkIVarRep (n : nat) : E :=
      match n with
      | 0 => [A_Var]
      | S n' => mkIVarRep n' ++ [A_Dot]
      end
    .

    Lemma mkIVarRep_injective :
      forall n1 : nat,
      forall n2 : nat,
      mkIVarRep n1 = mkIVarRep n2 ->
      n1 = n2.
    Proof.
      intros n1.
      induction n1.
      - intros n2.
        destruct n2.
        tauto.
        simpl.
        intro.
        assert (In A_Dot [A_Var]).
          rewrite H.
          apply in_or_app.
          apply or_intror.
          intuition.
        inversion H0.
        inversion H1.
        inversion H1.
      - intros n2.
        destruct n2.
        simpl.
        intro.
        assert (In A_Dot [A_Var]).
          rewrite <- H.
          apply in_or_app.
          apply or_intror.
          intuition.
        inversion H0.
        inversion H1.
        inversion H1.
        simpl.
        intro.
        cut (n1 = n2).
          intuition.
        apply IHn1.
        assert (removelast (mkIVarRep n1 ++ [A_Dot]) = removelast (mkIVarRep n2 ++ [A_Dot])).
          rewrite H.
          reflexivity.
        assert (removelast (mkIVarRep n1 ++ [A_Dot]) = mkIVarRep n1).
          apply removelast_last.
        assert (removelast (mkIVarRep n2 ++ [A_Dot]) = mkIVarRep n2).
          apply removelast_last.
        rewrite <- H1.
        rewrite <- H2.
        apply H0.
    Qed.

    Inductive Term : Set :=
    | IVar : forall i1 : Var, Term
    | Zero : Term
    | Succ : forall t1 : Term, Term
    | Plus : forall t1 : Term, forall t2 : Term, Term
    | Mult : forall t1 : Term, forall t2 : Term, Term
    | Expo : forall t1 : Term, forall t2 : Term, Term
    .

    Fixpoint showTerm (t : Term) : E :=
      match t with
      | IVar i1 => mkIVarRep i1
      | Zero => [A_Ze]
      | Succ t1 => showTerm t1 ++ [A_Sc]
      | Plus t1 t2 => [A_Fun; A_Dot; A_LP] ++ showTerm t1 ++ [A_RP; A_LP] ++ showTerm t2 ++ [A_RP]
      | Mult t1 t2 => [A_Fun; A_Dot; A_Dot; A_LP] ++ showTerm t1 ++ [A_RP; A_LP] ++ showTerm t2 ++ [A_RP]
      | Expo t1 t2 => [A_Fun; A_Dot; A_Dot; A_Dot; A_LP] ++ showTerm t1 ++ [A_RP; A_LP] ++ showTerm t2 ++ [A_RP]
      end
    .

    Lemma eq_Term_dec :
      forall t1 : Term,
      forall t2 : Term,
      {t1 = t2} + {t1 <> t2}.
    Proof.
      intros t1; induction t1.
      - intros t2; destruct t2. destruct (Nat.eq_dec i1 i0). left; rewrite e; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros t2; destruct t2. right; intro; inversion H. left; tauto. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros t2; destruct t2. right; intro; inversion H. right; intro; inversion H. destruct (IHt1 t2). left; rewrite e; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros t2; destruct t2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. destruct (IHt1_1 t2_1). rewrite e. destruct (IHt1_2 t2_2). rewrite e0. left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n. right; intro; inversion H. right; intro; inversion H.
      - intros t2; destruct t2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. destruct (IHt1_1 t2_1). rewrite e. destruct (IHt1_2 t2_2). rewrite e0. left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n. right; intro; inversion H.
      - intros t2; destruct t2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. destruct (IHt1_1 t2_1). rewrite e. destruct (IHt1_2 t2_2). rewrite e0. left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n.
    Qed.

    Inductive isTerm : E -> Prop :=
    | isIVar :
      forall i1 : nat,
      isTerm (mkIVarRep i1)
    | isZero :
      isTerm [A_Ze]
    | isSucc :
      forall e1 : E,
      isTerm e1 ->
      isTerm (e1 ++ [A_Sc])
    | isPlus :
      forall e1 : E,
      forall e2 : E,
      isTerm e1 ->
      isTerm e2 ->
      isTerm ([A_Fun; A_Dot; A_LP] ++ e1 ++ [A_RP; A_LP] ++ e2 ++ [A_RP])
    | isMult :
      forall e1 : E,
      forall e2 : E,
      isTerm e1 ->
      isTerm e2 ->
      isTerm ([A_Fun; A_Dot; A_Dot; A_LP] ++ e1 ++ [A_RP; A_LP] ++ e2 ++ [A_RP])
    | isExpo :
      forall e1 : E,
      forall e2 : E,
      isTerm e1 ->
      isTerm e2 ->
      isTerm ([A_Fun; A_Dot; A_Dot; A_Dot; A_LP] ++ e1 ++ [A_RP; A_LP] ++ e2 ++ [A_RP])
    .

    Lemma readTerm :
      forall e : E,
      isTerm e ->
      exists t : Term, showTerm t = e.
    Proof.
      intros e H.
      induction H.
      - exists (IVar i1).
        reflexivity.
      - exists Zero.
        reflexivity.
      - destruct IHisTerm as [t1].
        exists (Succ t1).
        rewrite <- H0.
        reflexivity.
      - destruct IHisTerm1 as [t1].
        destruct IHisTerm2 as [t2].
        exists (Plus t1 t2).
        rewrite <- H1.
        rewrite <- H2.
        reflexivity.
      - destruct IHisTerm1 as [t1].
        destruct IHisTerm2 as [t2].
        exists (Mult t1 t2).
        rewrite <- H1.
        rewrite <- H2.
        reflexivity.
      - destruct IHisTerm1 as [t1].
        destruct IHisTerm2 as [t2].
        exists (Expo t1 t2).
        rewrite <- H1.
        rewrite <- H2.
        reflexivity.
    Qed.

    Inductive Formula : Set :=
    | Eqn : forall t1 : Term, forall t2 : Term, Formula
    | Leq : forall t1 : Term, forall t2 : Term, Formula
    | Neg : forall f1 : Formula, Formula
    | Imp : forall f1 : Formula, forall f2 : Formula, Formula
    | All : forall i1 : Var, forall f2 : Formula, Formula
    .

    Fixpoint showFormula (f : Formula) : E :=
      match f with
      | Eqn t1 t2 => showTerm t1 ++ [A_Eqn] ++ showTerm t2
      | Leq t1 t2 => showTerm t1 ++ [A_Leq] ++ showTerm t2
      | Neg f1 => [A_Neg] ++ showFormula f1
      | Imp f1 f2 => [A_LP] ++ showFormula f1 ++ [A_Imp] ++ showFormula f2 ++ [A_RP]
      | All i1 f2 => [A_All] ++ mkIVarRep i1 ++ showFormula f2
      end
    .

    Lemma eq_Formula_dec :
      forall f1 : Formula,
      forall f2 : Formula,
      {f1 = f2} + {f1 <> f2}.
    Proof.
      intros f1; induction f1.
      - intros f2; destruct f2. destruct (eq_Term_dec t1 t0). rewrite e. destruct (eq_Term_dec t2 t3). rewrite e0; left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros f2; destruct f2. right; intro; inversion H. destruct (eq_Term_dec t1 t0). rewrite e. destruct (eq_Term_dec t2 t3). rewrite e0; left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H.
      - intros f2; destruct f2. right; intro; inversion H. right; intro; inversion H. destruct (IHf1 f2). rewrite e; left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H. right; intro; inversion H.
      - intros f2; destruct f2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. destruct (IHf1_1 f2_1). rewrite e. destruct (IHf1_2 f2_2). rewrite e0. left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n. right; intro; inversion H.
      - intros f2; destruct f2. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. right; intro; inversion H. destruct (Nat.eq_dec i1 i0). rewrite e. destruct (IHf1 f2). rewrite e0; left; tauto. right; intro; inversion H; contradiction n. right; intro; inversion H; contradiction n.
    Qed.

    Inductive isFormula : E -> Prop :=
    | isEqn :
      forall e1 : E,
      forall e2 : E,
      isTerm e1 ->
      isTerm e2 ->
      isFormula (e1 ++ [A_Eqn] ++ e2)
    | isLeq :
      forall e1 : E,
      forall e2 : E,
      isTerm e1 ->
      isTerm e2 ->
      isFormula (e1 ++ [A_Leq] ++ e2)
    | isNeg :
      forall e1 : E,
      isFormula e1 ->
      isFormula ([A_Neg] ++ e1)
    | isImp :
      forall e1 : E,
      forall e2 : E,
      isFormula e1 ->
      isFormula e2 ->
      isFormula ([A_LP] ++ e1 ++ [A_Imp] ++ e2 ++ [A_RP])
    | isAll :
      forall i1 : Var,
      forall e2 : E,
      isFormula e2 ->
      isFormula ([A_All] ++ mkIVarRep i1 ++ e2)
    .

    Lemma readFormula :
      forall e : E,
      isFormula e ->
      exists f : Formula, showFormula f = e.
    Proof.
      intros e H.
      induction H.
      - destruct (readTerm e1 H) as [t1].
        destruct (readTerm e2 H0) as [t2].
        exists (Eqn t1 t2).
        rewrite <- H1.
        rewrite <- H2.
        reflexivity.
      - destruct (readTerm e1 H) as [t1].
        destruct (readTerm e2 H0) as [t2].
        exists (Leq t1 t2).
        rewrite <- H1.
        rewrite <- H2.
        reflexivity.
      - destruct IHisFormula as [f1].
        exists (Neg f1).
        rewrite <- H0.
        reflexivity.
      - destruct IHisFormula1 as [f1].
        destruct IHisFormula2 as [f2].
        exists (Imp f1 f2).
        rewrite <- H1.
        rewrite <- H2.
        reflexivity.
      - destruct IHisFormula as [f2].
        exists (All i1 f2).
        rewrite <- H0.
        reflexivity.
    Qed.

  End The_Language_L_E.

  Section The_Notion_of_Truth_in_L_E.

    Definition Value : Type :=
      nat
    .

    Definition Assignment : Type :=
      Var -> Value
    .

    Fixpoint getFVs_Term (t : Term) : Ensemble Var :=
      match t with
      | IVar i1 => singleton i1
      | Zero => empty
      | Succ t1 => getFVs_Term t1
      | Plus t1 t2 => union (getFVs_Term t1) (getFVs_Term t2)
      | Mult t1 t2 => union (getFVs_Term t1) (getFVs_Term t2)
      | Expo t1 t2 => union (getFVs_Term t1) (getFVs_Term t2)
      end
    .

    Fixpoint getFVs_Formula (f : Formula) : Ensemble Var :=
      match f with
      | Eqn t1 t2 => union (getFVs_Term t1) (getFVs_Term t2)
      | Leq t1 t2 => union (getFVs_Term t1) (getFVs_Term t2)
      | Neg f1 => getFVs_Formula f1
      | Imp f1 f2 => union (getFVs_Formula f1) (getFVs_Formula f2)
      | All i1 f2 => delete i1 (getFVs_Formula f2)
      end
    .

    Fixpoint evalTerm (v : Assignment) (t : Term) : Value :=
      match t with
      | IVar i1 => v i1
      | Zero => 0
      | Succ t1 => S (evalTerm v t1)
      | Plus t1 t2 => (evalTerm v t1) + (evalTerm v t2)
      | Mult t1 t2 => (evalTerm v t1) * (evalTerm v t2)
      | Expo t1 t2 => (evalTerm v t1)^(evalTerm v t2)
      end
    .

    Fixpoint evalFormula (v : Assignment) (f : Formula) : Prop :=
      match f with
      | Eqn t1 t2 => evalTerm v t1 = evalTerm v t2
      | Leq t1 t2 => evalTerm v t1 <= evalTerm v t2
      | Neg f1 => ~ evalFormula v f1
      | Imp f1 f2 => evalFormula v f1 -> evalFormula v f2
      | All i1 f2 => forall n : Value, evalFormula (fun i : Var => if Nat.eq_dec i i1 then n else v i) f2
      end
    .
    
    Class HasMeaning (Expr : Set) : Type :=
      { getFVs : Expr -> Ensemble Var
      ; EvalResult : Type
      ; runEval : Assignment -> Expr -> EvalResult
      }
    .

    Definition isClosed {Expr : Set} {ExprHasMeaning : HasMeaning Expr} (e : Expr) : Prop :=
      isSubsetOf (getFVs e) empty
    .

    Instance term_has_meaning : HasMeaning Term :=
      { getFVs := getFVs_Term
      ; applySubst := applySubst_Term
      ; EvalResult := Value
      ; runEval := evalTerm
      }
    .

    Instance formula_has_meaning : HasMeaning Formula :=
      { getFVs := getFVs_Formula
      ; applySubst := applySubst_Formula
      ; EvalResult := Prop
      ; runEval := evalFormula
      }
    .

  End The_Notion_of_Truth_in_L_E.

  Section Arithmetic_and_arithmetic_Sets_and_Realations.

    Inductive relation_of_arity : nat -> Type :=
    | RelationZ : Prop -> relation_of_arity 0
    | RelationS : forall ar : nat, (nat -> relation_of_arity ar) -> relation_of_arity (S ar)
    .

    Fixpoint interprete_relation_of_arity (ar : nat) (rel : relation_of_arity ar) (f : Formula) (v : Assignment) : Prop :=
      match rel with
      | RelationZ prop => evalFormula v f <-> prop
      | RelationS ar' rel' => forall n : Value, interprete_relation_of_arity ar' (rel' n) f (fun i : Var => if Nat.eq_dec i ar' then n else v i)
      end
    .

    Definition express_relation_of_arity (f : Formula) (ar : nat) (rel : relation_of_arity ar) : Prop :=
      (forall i : Var, i < ar -> member i (getFVs_Formula f)) /\ (forall v : Assignment, interprete_relation_of_arity ar rel f v)
    .

    Inductive function_of_arity : nat -> Type :=
    | FunctionZ : nat -> function_of_arity 0
    | FunctionS : forall ar : nat, (nat -> function_of_arity ar) -> function_of_arity (S ar)
    .

    Fixpoint interprete_function_of_arity (ar : nat) (fcn : function_of_arity ar) (f : Formula) (v : Assignment) : Prop :=
      match fcn with
      | FunctionZ fcn' => forall n : Value, evalFormula (fun i : Var => if Nat.eq_dec i ar then n else v i) f <-> n = fcn'
      | FunctionS ar' fcn' => forall n : Value, interprete_function_of_arity ar' (fcn' n) f (fun i : Var => if Nat.eq_dec i ar then n else v i)
      end
    .

    Definition express_function_of_arity (f : Formula) (ar : nat) (fcn : function_of_arity ar) : Prop :=
      (forall i : Var, i <= ar -> member i (getFVs_Formula f)) /\ (forall v : Assignment, interprete_function_of_arity ar fcn f v)
    .

  End Arithmetic_and_arithmetic_Sets_and_Realations.

End Tarski's_Theorem_for_Arithmetic.
