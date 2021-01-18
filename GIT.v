(* Goedel's Incompleteness Theorems - Ranymond M. Smullyan *)

From Coq Require Export Bool.
From Coq Require Export PeanoNat.
From Coq Require Export Peano_dec.
From Coq Require Export List.
From Coq Require Export Lia.
From Coq Require Export Compare_dec.

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

    Definition IVarNum : Set :=
      nat
    .

    Definition Arity : Set :=
      nat
    .

    Fixpoint funOfArity (k : Arity) : Type :=
      match k with
      | 0 => nat
      | S k' => nat -> funOfArity k'
      end
    .

    Fixpoint relOfArity (k : Arity) : Type :=
      match k with
      | 0 => Prop
      | S k' => nat -> relOfArity k'
      end
    .

    Lemma it_is_false_that_n_lt_0 (A : Type) :
      forall n : nat,
      n < 0 -> A.
    Proof.
      intros.
      lia.
    Qed.

    Lemma S_i_lt_S_k_implies_i_lt_k :
      forall i : nat,
      forall k : nat,
      S i < S k ->
      i < k.
    Proof.
      intros i k H.
      lia.
    Qed.

    Fixpoint projectionZ (k : nat) : funOfArity (S k) :=
      match k with
      | 0 => fun x : nat => x
      | S k' => fun x : nat => fun y : nat => projectionZ k' x
      end
    .

    Example projectionZ_ex1 :
      forall x0 : nat,
      forall x1 : nat,
      forall x2 : nat,
      projectionZ 2 x0 x1 x2 = x0.
    Proof.
      intros x0 x1 x2.
      reflexivity.
    Qed.

    Fixpoint projection (k : nat) : forall i : nat, i < k -> funOfArity k :=
      fun i : nat =>
      match i as x return x < k -> funOfArity k with
      | 0 =>
        match k as y return 0 < y -> funOfArity y with
        | 0 => fun i_le_k : 0 < 0 => it_is_false_that_n_lt_0 (funOfArity 0) 0 i_le_k
        | S k' => fun i_le_k : 0 < S k' => projectionZ k'
        end
      | S i' =>
        match k as y return S i' < y -> funOfArity y with
        | 0 => fun i_le_k : S i' < 0 => it_is_false_that_n_lt_0 (funOfArity 0) (S i') i_le_k
        | S k' => fun i_le_k : S i' < S k' => fun z : nat => projection k' i' (S_i_lt_S_k_implies_i_lt_k i' k' i_le_k)
        end
      end
    .

    Example it_is_true_that_1_lt_4 :
      1 < 4.
    Proof.
      lia.
    Qed.

    Example projection_ex1 :
      forall x0 : nat,
      forall x1 : nat,
      forall x2 : nat,
      forall x3 : nat,
      projection 4 1 it_is_true_that_1_lt_4 x0 x1 x2 x3 = x1.
    Proof.
      intros x1 x2.
      reflexivity.
    Qed.

    Inductive Term (k : IVarNum) : Set :=
    | IVarT :
      forall i : IVarNum,
      i < k ->
      Term k
    | ZeroT :
      Term k
    | SuccT :
      Term k ->
      Term k
    | PlusT :
      Term k ->
      Term k ->
      Term k
    | MultT :
      Term k ->
      Term k ->
      Term k
    | ExpoT :
      Term k ->
      Term k ->
      Term k
    .

    Fixpoint liftZero (k : Arity) : funOfArity k :=
      match k as x return funOfArity x with
      | 0 => 0
      | S k' => fun x : nat => liftZero k'
      end
    .

    Fixpoint liftSucc (k : Arity) : funOfArity k -> funOfArity k :=
      match k as x return funOfArity x -> funOfArity x with
      | 0 =>
        fun v1 : funOfArity 0 =>
        S (v1)
      | S k' =>
        fun v1 : nat -> funOfArity k' =>
        fun x : nat =>
        liftSucc k' (v1 x)
      end
    .

    Fixpoint liftPlus (k : Arity) : funOfArity k -> funOfArity k -> funOfArity k :=
      match k as x return funOfArity x -> funOfArity x -> funOfArity x with
      | 0 =>
        fun v1 : funOfArity 0 =>
        fun v2 : funOfArity 0 =>
        v1 + v2
      | S k' =>
        fun v1 : nat -> funOfArity k' =>
        fun v2 : nat -> funOfArity k' =>
        fun x : nat =>
        liftPlus k' (v1 x) (v2 x)
      end
    .

    Fixpoint liftMult (k : Arity) : funOfArity k -> funOfArity k -> funOfArity k :=
      match k as x return funOfArity x -> funOfArity x -> funOfArity x with
      | 0 =>
        fun v1 : funOfArity 0 =>
        fun v2 : funOfArity 0 =>
        v1 * v2
      | S k' =>
        fun v1 : nat -> funOfArity k' =>
        fun v2 : nat -> funOfArity k' =>
        fun x : nat =>
        liftMult k' (v1 x) (v2 x)
      end
    .

    Fixpoint liftExpo (k : Arity) : funOfArity k -> funOfArity k -> funOfArity k :=
      match k as x return funOfArity x -> funOfArity x -> funOfArity x with
      | 0 =>
        fun v1 : funOfArity 0 =>
        fun v2 : funOfArity 0 =>
        v1^v2
      | S k' =>
        fun v1 : nat -> funOfArity k' =>
        fun v2 : nat -> funOfArity k' =>
        fun x : nat =>
        liftExpo k' (v1 x) (v2 x)
      end
    .

    Fixpoint evalTerm (k : Arity) (t : Term k) : funOfArity k :=
      match t with
      | IVarT _ i ilek => projection k i ilek
      | ZeroT _ => liftZero k
      | SuccT _ t1 => liftSucc k (evalTerm k t1)
      | PlusT _ t1 t2 => liftPlus k (evalTerm k t1) (evalTerm k t2)
      | MultT _ t1 t2 => liftMult k (evalTerm k t1) (evalTerm k t2)
      | ExpoT _ t1 t2 => liftExpo k (evalTerm k t1) (evalTerm k t2)
      end
    .

    Inductive Formula (k : IVarNum) : Set :=
    | EqnF :
      Term k ->
      Term k ->
      Formula k
    | LeqF :
      Term k ->
      Term k ->
      Formula k
    | NegF :
      Formula k ->
      Formula k
    | ImpF :
      Formula k ->
      Formula k ->
      Formula k
    | AllF :
      Formula (S k) ->
      Formula k
    .

    Fixpoint liftEqn (k : Arity) : funOfArity k -> funOfArity k -> relOfArity k :=
      match k as x return funOfArity x -> funOfArity x -> relOfArity x with
      | 0 =>
        fun v1 : funOfArity 0 =>
        fun v2 : funOfArity 0 =>
        v1 = v2
      | S k' =>
        fun v1 : nat -> funOfArity k' =>
        fun v2 : nat -> funOfArity k' =>
        fun x : nat =>
        liftEqn k' (v1 x) (v2 x)
      end
    .

    Fixpoint liftLeq (k : Arity) : funOfArity k -> funOfArity k -> relOfArity k :=
      match k as x return funOfArity x -> funOfArity x -> relOfArity x with
      | 0 =>
        fun v1 : funOfArity 0 =>
        fun v2 : funOfArity 0 =>
        v1 <= v2
      | S k' =>
        fun v1 : nat -> funOfArity k' =>
        fun v2 : nat -> funOfArity k' =>
        fun x : nat =>
        liftLeq k' (v1 x) (v2 x)
      end
    .

    Fixpoint liftNeg (k : Arity) : relOfArity k -> relOfArity k :=
      match k as x return relOfArity x -> relOfArity x with
      | 0 =>
        fun v1 : relOfArity 0 =>
        ~ v1
      | S k' =>
        fun v1 : nat -> relOfArity k' =>
        fun x : nat =>
        liftNeg k' (v1 x)
      end
    .

    Fixpoint liftImp (k : Arity) : relOfArity k -> relOfArity k -> relOfArity k :=
      match k as x return relOfArity x -> relOfArity x -> relOfArity x with
      | 0 =>
        fun v1 : relOfArity 0 =>
        fun v2 : relOfArity 0 =>
        v1 -> v2
      | S k' =>
        fun v1 : nat -> relOfArity k' =>
        fun v2 : nat -> relOfArity k' =>
        fun x : nat =>
        liftImp k' (v1 x) (v2 x)
      end
    .

    Fixpoint liftAll (k : Arity) : relOfArity (S k) -> relOfArity k :=
      match k as x return relOfArity (S x) -> relOfArity x with
      | 0 =>
        fun v1 : relOfArity 1 =>
        forall n : nat, v1 n
      | S k' =>
        fun v1 : nat -> relOfArity (S k') =>
        fun x : nat =>
        liftAll k' (v1 x)
      end
    .

    Fixpoint evalFormula (k : Arity) (f : Formula k) : relOfArity k :=
      match f with
      | EqnF _ t1 t2 => liftEqn k (evalTerm k t1) (evalTerm k t2)
      | LeqF _ t1 t2 => liftLeq k (evalTerm k t1) (evalTerm k t2)
      | NegF _ f1 => liftNeg k (evalFormula k f1)
      | ImpF _ f1 f2 => liftImp k (evalFormula k f1) (evalFormula k f2)
      | AllF _ f1' => liftAll k (evalFormula (S k) f1')
      end
    . 

  End The_Notion_of_Truth_in_L_E.

End Tarski's_Theorem_for_Arithmetic.
