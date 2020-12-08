Require Export Bool.
Require Export PeanoNat.
Require Export Peano_dec.
Require Export List.
Require Export Lia.

Module Helper.

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
    
    Lemma second_principle_of_finite_induction :
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
    | Singleton :
      forall x : A,
      member x (singleton x)
    .

    Inductive union {A : Type} : Ensemble A -> Ensemble A -> Ensemble A :=
    | UnionL :
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      forall x : A,
      member x xs1 ->
      member x (union xs1 xs2)
    | UnionR :
      forall xs1 : Ensemble A,
      forall xs2 : Ensemble A,
      forall x : A,
      member x xs2 ->
      member x (union xs1 xs2)
    .

    Definition insert {A : Type} (x1 : A) (xs2 : Ensemble A) : Ensemble A :=
      union xs2 (singleton x1)
    .

    Definition intersection {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs1 /\ member x xs2
    .

    Definition difference {A : Type} (xs1 : Ensemble A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x xs1 /\ ~ member x xs2
    .

    Definition delete {A : Type} (x1 : A) (xs2 : Ensemble A) : Ensemble A :=
      fun x : A => member x (difference xs2 (singleton x1))
    .

  End Ensembles.

End Helper.

Module CountableBooleanAlgebra.

  Import ListNotations.

  Import Helper.

  Section DefinitionOfCBA.

    Class CBA (B : Type) : Type :=
      { eqB : B -> B -> Prop
      ; trueB : B
      ; falseB : B
      ; negB : B -> B
      ; andB : B -> B -> B
      ; orB : B -> B -> B
      ; enumB : nat -> B
      ; eqB_refl : forall b1 : B, eqB b1 b1
      ; eqB_symm : forall b1 : B, forall b2 : B, eqB b1 b2 -> eqB b2 b1
      ; eqB_trans : forall b1 : B, forall b2 : B, forall b3 : B, eqB b1 b2 -> eqB b2 b3 -> eqB b1 b3
      ; trueB_preserves_eqB : eqB trueB trueB
      ; falseB_preserves_eqB : eqB falseB falseB
      ; negB_preserves_eqB : forall b1 : B, forall b1' : B, eqB b1 b1' -> eqB (negB b1) (negB b1')
      ; andB_preserves_eqB : forall b1 : B, forall b1' : B, forall b2 : B, forall b2' : B, eqB b1 b1' -> eqB b2 b2' -> eqB (andB b1 b2) (andB b1' b2')
      ; or_preserves_eqB : forall b1 : B, forall b1' : B, forall b2 : B, forall b2' : B, eqB b1 b1' -> eqB b2 b2' -> eqB (orB b1 b2) (orB b1' b2')
      ; andB_associative : forall b1 : B, forall b2 : B, forall b3 : B, eqB (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3)
      ; orB_associative : forall b1 : B, forall b2 : B, forall b3 : B, eqB (orB b1 (orB b2 b3)) (orB (orB b1 b2) b3)
      ; andB_idempotent : forall b1 : B, eqB (andB b1 b1) b1
      ; orB_idempotent : forall b1 : B, eqB (orB b1 b1) b1
      ; andB_commutative : forall b1 : B, forall b2 : B, eqB (andB b1 b2) (andB b2 b1)
      ; orB_commutative : forall b1 : B, forall b2 : B, eqB (orB b1 b2) (orB b2 b1)
      ; andB_distribute_orB : forall b1 : B, forall b2 : B, forall b3 : B, eqB (andB b1 (orB b2 b3)) (orB (andB b1 b2) (andB b1 b3))
      ; orB_distribute_andB : forall b1 : B, forall b2 : B, forall b3 : B, eqB (orB b1 (andB b2 b3)) (andB (orB b1 b2) (orB b1 b3))
      ; absorption_andB_orB : forall b1 : B, forall b2 : B, eqB (andB b1 (orB b1 b2)) b1
      ; absorption_orB_andB : forall b1 : B, forall b2 : B, eqB (orB b1 (andB b1 b2)) b1
      ; falseB_zero_andB : forall b1 : B, eqB (andB b1 falseB) falseB
      ; trueB_zero_orB : forall b1 : B, eqB (orB b1 trueB) trueB
      ; falseB_unit_orB : forall b1 : B, eqB (andB b1 falseB) b1
      ; trueB_unit_andB : forall b1 : B, eqB (andB b1 trueB) b1
      ; andB_negB : forall b1 : B, eqB (andB b1 (negB b1)) falseB
      ; orB_negB : forall b1 : B, eqB (orB b1 (negB b1)) trueB 
      ; enumB_surjective : forall b : B, exists n : nat, enumB n = b
      }
    .

  End DefinitionOfCBA.

  Section TheoryOfCBA.

    Variable B : Type.

    Variable cba : CBA B.

    Notation "b1 == b2" := (eqB b1 b2) (at level 80).

    Notation "b1 =< b2" := (eqB (andB b1 b2) b1) (at level 80).

    Lemma leq_CBA_refl :
      forall b1 : B,
      b1 =< b1.
    Proof.
      intros b1.
      apply andB_idempotent.
    Qed.

    Lemma leq_CBA_refl' :
      forall b1 : B,
      forall b2 : B,
      b1 == b2 ->
      b1 =< b2.
    Proof.
      intros b1 b2 H.
      apply eqB_symm.
      apply (eqB_trans b1 (andB b1 b1) (andB b1 b2)).
      apply eqB_symm.
      apply andB_idempotent.
      apply andB_preserves_eqB.
      apply eqB_refl.
      apply H.
    Qed.

    Lemma leq_CBA_asym :
      forall b1 : B,
      forall b2 : B,
      b1 =< b2 ->
      b2 =< b1 ->
      b1 == b2.
    Proof.
      intros b1 b2 H1 H2.
      apply (eqB_trans b1 (andB b1 b2) b2).
      apply eqB_symm.
      apply H1.
      apply (eqB_trans (andB b1 b2) (andB b2 b1) b2).
      apply andB_commutative.
      apply H2.
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
      apply (eqB_trans (andB b1 b3) (andB (andB b1 b2) b3) b1).
      apply andB_preserves_eqB.
      apply eqB_symm.
      apply H1.
      apply eqB_refl.
      apply eqB_symm.
      apply (eqB_trans b1 (andB b1 (andB b2 b3)) (andB (andB b1 b2) b3)).
      apply (eqB_trans b1 (andB b1 b2) (andB b1 (andB b2 b3))).
      apply eqB_symm.
      apply H1.
      apply andB_preserves_eqB.
      apply eqB_refl.
      apply eqB_symm.
      apply H2.
      apply andB_associative.
    Qed.

    Lemma leq_CBA_andB :
      forall b1 : B,
      forall b1' : B,
      forall b2 : B,
      forall b2' : B,
      b1 =< b2 ->
      b1' =< b2' ->
      andB b1 b1' =< andB b2 b2'.
    Proof.
      intros b1 b1' b2 b2' H1 H2.
      assert (andB b1 b1' =< andB b2 b1').
        apply eqB_symm.
        apply (eqB_trans (andB b1 b1') (andB (andB b1 b2) b1') (andB (andB b1 b1') (andB b2 b1'))).
        apply andB_preserves_eqB.
        apply eqB_symm.
        apply H1.
        apply eqB_refl.
        apply (eqB_trans (andB (andB b1 b2) b1') (andB b1 (andB b2 b1')) (andB (andB b1 b1') (andB b2 b1'))).
        apply eqB_symm.
        apply andB_associative.
        apply (eqB_trans (andB b1 (andB b2 b1')) (andB b1 (andB b1' (andB b2 b1'))) (andB (andB b1 b1') (andB b2 b1'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply (eqB_trans (andB b2 b1') (andB b2 (andB b1' b1')) (andB b1' (andB b2 b1'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply eqB_symm.
        apply leq_CBA_refl.
        apply eqB_symm.
        apply (eqB_trans (andB b1' (andB b2 b1')) (andB (andB b2 b1') b1') (andB b2 (andB b1' b1'))).
        apply (eqB_trans (andB b1' (andB b2 b1')) (andB (andB b1' b2) b1') (andB (andB b2 b1') b1')).
        apply andB_associative.
        apply andB_preserves_eqB.
        apply andB_commutative.
        apply eqB_refl.
        apply eqB_symm.
        apply andB_associative.
        apply andB_associative.
      assert (andB b2 b1' =< andB b2 b2').
        apply eqB_symm.
        apply (eqB_trans (andB b2 b1') (andB b2 (andB b1' b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply eqB_symm.
        apply H2.
        apply (eqB_trans (andB b2 (andB b1' b2')) (andB (andB b2 b2) (andB b1' b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_symm.
        apply leq_CBA_refl.
        apply eqB_refl.
        apply (eqB_trans (andB (andB b2 b2) (andB b1' b2')) (andB b2 (andB b2 (andB b1' b2'))) (andB (andB b2 b1') (andB b2 b2'))).
        apply eqB_symm.
        apply andB_associative.
        apply (eqB_trans (andB b2 (andB b2 (andB b1' b2'))) (andB b2 (andB (andB b2 b1') b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply andB_associative.
        apply (eqB_trans (andB b2 (andB (andB b2 b1') b2')) (andB b2 (andB (andB b1' b2) b2')) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply andB_preserves_eqB.
        apply andB_commutative.
        apply eqB_refl.
        apply (eqB_trans (andB b2 (andB (andB b1' b2) b2')) (andB b2 (andB b1' (andB b2 b2'))) (andB (andB b2 b1') (andB b2 b2'))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply eqB_symm.
        apply andB_associative.
        apply andB_associative.
        apply (leq_CBA_trans (andB b1 b1') (andB b2 b1') (andB b2 b2') H H0).
    Qed.

    Lemma andBs_CBA :
      forall ps1 : list B,
      forall ps2 : list B,
      fold_right andB trueB (ps1 ++ ps2) == andB (fold_right andB trueB ps1) (fold_right andB trueB ps2).
    Proof.
      intros ps1.
      induction ps1.
      - intros ps.
        simpl.
        apply eqB_symm.
        apply (eqB_trans (andB trueB (fold_right andB trueB ps)) (andB (fold_right andB trueB ps) trueB) (fold_right andB trueB ps)).
        apply andB_commutative.
        apply trueB_unit_andB.
      - intros ps2.
        simpl.
        apply (eqB_trans (andB a (fold_right andB trueB (ps1 ++ ps2))) (andB a (andB (fold_right andB trueB ps1) (fold_right andB trueB ps2))) (andB (andB a (fold_right andB trueB ps1)) (fold_right andB trueB ps2))).
        apply andB_preserves_eqB.
        apply eqB_refl.
        apply IHps1.
        apply andB_associative.
    Qed.

    Definition isFilter (filter : Ensemble B) : Prop :=
      (exists b0 : B, member b0 filter) /\ (forall b1 : B, forall b2 : B, member b1 filter -> b1 =< b2 -> member b2 filter) /\ (forall b1 : B, forall b2 : B, forall b : B, member b1 filter -> member b2 filter -> b == andB b1 b2 -> member b filter)
    .

    Lemma isFilter_refl' :
      forall bs1 : Ensemble B,
      isFilter bs1 ->
      forall bs2 : Ensemble B,
      isSubsetOf bs1 bs2 ->
      isSubsetOf bs2 bs1 ->
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

    Inductive Cl : Ensemble B -> Ensemble B :=
    | Closure :
      forall ps : list B,
      forall b : B,
      forall bs : Ensemble B,
      (forall p : B, In p ps -> member p bs) ->
      fold_right andB trueB ps =< b ->
      member b (Cl bs)
    .

    Definition inconsistent (bs1 : Ensemble B) : Prop :=
      exists b : B, member b bs1 /\ b == falseB
    .

    Definition equiconsistent (bs1 : Ensemble B) (bs2 : Ensemble B) : Prop :=
      inconsistent bs1 <-> inconsistent bs2
    .
    
    Definition isElementComplete (bs1 : Ensemble B) (b2 : B) : Prop :=
      equiconsistent bs1 (Cl (insert b2 bs1)) -> member b2 bs1
    .

    Definition isComplete (bs1 : Ensemble B) : Prop :=
      forall b2 : B, isElementComplete bs1 b2
    .

    Lemma fact_1_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter (Cl bs).
    Proof.
      intros bs.
      constructor.
      exists trueB.
      apply (Closure []).
      intros p.
      intro.
      inversion H.
      simpl.
      apply leq_CBA_refl.
      constructor.
      intros b1 b H1 H2.
      inversion H1.
      subst.
      apply (Closure ps).
      apply H.
      apply (leq_CBA_trans (fold_right andB trueB ps) b1 b H0 H2).
      intros b1 b2 b H1 H2 H3.
      destruct H1.
      destruct H2.
      apply (Closure (ps ++ ps0)).
      intros p.
      intro.
      destruct (in_app_or ps ps0 p H4).
      apply (H p H5).
      apply (H1 p H5).
      assert (fold_right andB trueB (ps ++ ps0) == andB (fold_right andB trueB ps) (fold_right andB trueB ps0)).
        apply andBs_CBA.
      apply (leq_CBA_trans (fold_right andB trueB (ps ++ ps0)) (andB b0 b1) b).
      apply (leq_CBA_trans (fold_right andB trueB (ps ++ ps0)) (andB (fold_right andB trueB ps) (fold_right andB trueB ps0)) (andB b0 b1)).
      apply (leq_CBA_refl' (fold_right andB trueB (ps ++ ps0)) (andB (fold_right andB trueB ps) (fold_right andB trueB ps0)) H4).
      apply (leq_CBA_andB (fold_right andB trueB ps) (fold_right andB trueB ps0) b0 b1).
      apply H0.
      apply H2.
      apply (leq_CBA_refl' (andB b0 b1) b).
      apply eqB_symm.
      apply H3.
    Qed.

    Lemma fact_2_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter bs ->
      member trueB bs.
    Proof.
      intros bs.
      intro.
      destruct H.
      destruct H0.
      destruct H as [b].
      apply (H0 b trueB).
      apply H.
      apply trueB_unit_andB.
    Qed.

    Lemma fact_3_of_1_2_8 :
      forall bs : Ensemble B,
      isSubsetOf bs (Cl bs).
    Proof.
      intros bs.
      intros b.
      intro.
      apply (Closure [b]).
      intros p.
      intro.
      inversion H0.
      subst.
      apply H.
      inversion H1.
      simpl.
      apply leq_CBA_refl'.
      apply trueB_unit_andB.
    Qed.

    Lemma fact_4_of_1_2_8 :
      forall bs1 : Ensemble B,
      forall bs2 : Ensemble B,
      isSubsetOf bs1 bs2 ->
      isSubsetOf (Cl bs1) (Cl bs2).
    Proof.
      intros bs1 bs2.
      intro.
      intros b.
      intro.
      destruct H0.
      apply (Closure ps).
      intros p.
      intro.
      apply (H p).
      apply (H0 p H2).
      apply H1.
    Qed.

    Lemma fact_5_of_1_2_8 :
      forall bs : Ensemble B,
      isFilter bs ->
      isSubsetOf (Cl bs) bs.
    Proof.
      intros bs.
      intro.
      destruct H.
      destruct H0.
      cut (
        forall ps : list B,
        (forall b : B, In b ps -> member b bs) ->
        member (fold_right andB trueB ps) bs
      ).
        intro.
        intros p.
        intro.
        destruct H3.
        apply (H0 (fold_right andB trueB ps) b).
        apply H2.
        apply H3.
        apply H4.
      intros ps.
      induction ps.
      - intro.
        simpl in *.
        destruct H as [b'].
        apply (H0 b' trueB).
        apply H.
        apply trueB_unit_andB.
      - intro.
        simpl in *.
        apply (H1 a (fold_right andB trueB ps) (andB a (fold_right andB trueB ps))).
        apply (H2 a).
        tauto.
        apply IHps.
        intros b.
        intro.
        apply H2.
        tauto.
        apply eqB_refl.
    Qed.

    Lemma proposition_1_of_1_2_9 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall b1 : B,
      member b1 bs ->
      forall b2 : B,
      b1 == b2 ->
      member b2 bs.
    Proof.
      intros bs.
      intro.
      destruct H.
      destruct H0.
      intros b1.
      intro.
      intros b2.
      intro.
      apply (H0 b1 b2).
      apply H2.
      apply leq_CBA_refl'.
      apply H3.
    Qed.

    Inductive Insert : Ensemble B -> nat -> Ensemble B :=
    | Insertion :
      forall bs : Ensemble B,
      forall n : nat,
      equiconsistent bs (Cl (insert (enumB n) bs)) ->
      member (enumB n) (Insert bs n)
    .

    Fixpoint improveFilter (bs : Ensemble B) (n : nat) : Ensemble B :=
      match n with
      | 0 => bs
      | S n' =>
        let bs' : Ensemble B := improveFilter bs n' in
        Cl (union bs' (Insert bs' n'))
      end
    .

    Lemma lemma_1_of_1_2_11 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n : nat,
      isFilter (improveFilter bs n).
    Proof.
      intros bs.
      intro.
      intros n.
      induction n.
      - simpl.
        apply H.
      - simpl.
        apply fact_1_of_1_2_8.
    Qed.

    Lemma lemma_1_of_1_2_12 :
      forall bs : Ensemble B,
      forall n1 : nat,
      forall n2 : nat,
      n1 <= n2 ->
      isSubsetOf (improveFilter bs n1) (improveFilter bs n2).
    Proof.
      intros bs n1 n2.
      intro.
      induction H.
      - unfold isSubsetOf.
        intuition.
      - assert (isSubsetOf (improveFilter bs m) (improveFilter bs (S m))).
          assert (isSubsetOf (union (improveFilter bs m) (Insert (improveFilter bs m) m)) (Cl (union (improveFilter bs m) (Insert (improveFilter bs m) m)))).
            apply fact_3_of_1_2_8.
          intros p.
          intro.
          apply H0.
          apply UnionL.
          apply H1.
        intros p.
        intro.
        apply H0.
        apply IHle.
        apply H1.
    Qed.

    Lemma lemma_1_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n : nat,
      equiconsistent bs (improveFilter bs n).
    Proof.
      intros bs.
      intro HHH.
      intros n.
      induction n.
      - simpl.
        unfold equiconsistent.
        intuition.
      - constructor.
        unfold inconsistent.
        intro.
        destruct H as [b'].
        destruct H.
        exists b'.
        constructor.
        apply (lemma_1_of_1_2_12 bs 0 (S n)).
        lia.
        simpl.
        apply H.
        apply H0.
        intro.
        cut (
          forall ps : list B,
          (forall p : B, In p ps -> member p (union (improveFilter bs n) (Insert (improveFilter bs n) n))) ->
          member (fold_right andB trueB ps) (improveFilter bs n) \/ (exists p' : B, In p' ps /\ member p' (Insert (improveFilter bs n) n))
        ).
          intro.
          destruct H as [b'].
          destruct H.
          inversion H.
          subst.
          destruct (H0 ps H2).
          apply (proj2 IHn).
          exists (fold_right andB trueB ps).
          constructor.
          apply H4.
          apply leq_CBA_asym.
          apply (leq_CBA_trans (fold_right andB trueB ps) b' falseB).
          apply H3.
          apply leq_CBA_refl'.
          apply H1.
          apply (eqB_trans (andB falseB (fold_right andB trueB ps)) (andB (fold_right andB trueB ps) falseB) falseB).
          apply andB_commutative.
          apply falseB_zero_andB.
          destruct H4 as [p'].
          destruct H4.
          assert (member p' (union (improveFilter bs n) (Insert (improveFilter bs n) n))).
            apply (H2 p' H4).
          assert (member falseB (Cl (union (improveFilter bs n) (Insert (improveFilter bs n) n)))).
            apply (Closure ps).
            apply H2.
            apply (leq_CBA_trans (fold_right andB trueB ps) b' falseB).
            apply H3.
            apply leq_CBA_refl'.
            apply H1.
          inversion H5.
          subst.
          apply (proj2 IHn).
          apply (proj2 H8).
          exists falseB.
          constructor.
          assert (isSubsetOf (union (improveFilter bs n) (Insert (improveFilter bs n) n)) (insert (enumB n) (improveFilter bs n))).
            intros p.
            intro.
            inversion H9.
            subst.
            apply UnionL.
            apply H10.
            subst.
            inversion H10.
            subst.
            apply UnionR.
            apply Singleton.
          assert (isSubsetOf (Cl (union (improveFilter bs n) (Insert (improveFilter bs n) n))) (Cl (insert (enumB n) (improveFilter bs n)))).
            apply fact_4_of_1_2_8.
            apply H9.
          apply H10.
          apply H7.
          apply eqB_refl.
        intros ps.
        induction ps.
        * simpl in *.
          intro.
          apply or_introl.
          apply fact_2_of_1_2_8.
          apply lemma_1_of_1_2_11.
          apply HHH.
        * simpl in *.
          intro.
          assert (
            forall p : B,
            In p ps ->
            member p (union (improveFilter bs n) (Insert (improveFilter bs n) n))
          ).
            intros p.
            intro.
            apply (H0 p).
            tauto.
          assert (member a (union (improveFilter bs n) (Insert (improveFilter bs n) n))).
            apply H0.
            tauto.
          assert (isFilter (improveFilter bs n)).
            apply lemma_1_of_1_2_11.
            apply HHH.
          destruct (IHps H1).
          inversion H2.
          subst.
          destruct H3.
          destruct H6.
          apply or_introl.
          apply (H7 a (fold_right andB trueB ps)).
          apply H5.
          apply H4.
          apply eqB_refl.
          subst.
          apply or_intror.
          exists a.
          tauto.
          apply or_intror.
          destruct H4 as [p'].
          exists p'.
          destruct H4.
          constructor.
          tauto.
          apply H5.
    Qed.

    Lemma lemma_2_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      forall n1 : nat,
      forall n2 : nat,
      equiconsistent (improveFilter bs n1) (improveFilter bs n2).
    Proof.
      intros bs HHH n1 n2.
      assert (equiconsistent bs (improveFilter bs n1)).
        apply lemma_1_of_1_2_13.
        apply HHH.
      assert (equiconsistent bs (improveFilter bs n2)).
        apply lemma_1_of_1_2_13.
        apply HHH.
      unfold equiconsistent in *.
      intuition.
    Qed.

    Inductive CompleteFilter : Ensemble B -> Ensemble B :=
    | InCompleteFilter :
      forall n : nat,
      forall bs : Ensemble B,
      forall b : B,
      member b (improveFilter bs n) ->
      member b (CompleteFilter bs)
    .

    Lemma lemma_3_of_1_2_13 :
      forall bs : Ensemble B,
      isFilter bs ->
      equiconsistent bs (CompleteFilter bs).
    Proof.
      intros bs HHH.
      constructor.
      intro.
      destruct H as [p'].
      destruct H.
      exists p'.
      constructor.
      apply (InCompleteFilter 0).
      simpl.
      apply H.
      apply H0.
      intro.
      destruct H as [p'].
      destruct H.
      inversion H.
      subst.
      assert (equiconsistent bs (improveFilter bs n)).
        apply lemma_1_of_1_2_13.
        apply HHH.
      apply (proj2 H2).
      exists p'.
      tauto.
    Qed.

    Theorem theorem_1_2_14 :
      forall bs : Ensemble B,
      isFilter bs ->
      isSubsetOf bs (CompleteFilter bs) /\ isFilter (CompleteFilter bs) /\ isComplete (CompleteFilter bs) /\ equiconsistent bs (CompleteFilter bs).
    Proof.
      intros bs HHH.
      assert (isSubsetOf bs (CompleteFilter bs)).
        intros p.
        intro.
        apply (InCompleteFilter 0).
        simpl.
        apply H.
      constructor.
      apply H.
      constructor.
      inversion HHH.
      destruct H0 as [b0].
      constructor.
      exists b0.
      apply H.
      apply H0.
      constructor.
      intros b1 b2.
      intro.
      intro.
      inversion H2.
      subst.
      assert (isFilter (improveFilter bs n)).
        apply lemma_1_of_1_2_11.
        apply HHH.
      destruct H5.
      destruct H6.
      apply (InCompleteFilter n).
      apply (H6 b1 b2 H4 H3).
      intros b1 b2 b.
      intro.
      intro.
      intro.
      inversion H2.
      subst.
      inversion H3.
      subst.
      assert (n >= n0 \/ n0 >= n).
        lia.
      destruct H7.
      assert (isFilter (improveFilter bs n)).
        apply lemma_1_of_1_2_11.
        apply HHH.
      destruct H8.
      destruct H9.
      apply (InCompleteFilter n).
      apply (H10 b1 b2 b).
      apply H5.
      assert (isSubsetOf (improveFilter bs n0) (improveFilter bs n)).
        apply lemma_1_of_1_2_12.
        lia.
      apply H11.
      apply H6.
      apply H4.
      assert (isFilter (improveFilter bs n0)).
        apply lemma_1_of_1_2_11.
        apply HHH.
      destruct H8.
      destruct H9.
      apply (InCompleteFilter n0).
      apply (H10 b1 b2 b).
      assert (isSubsetOf (improveFilter bs n) (improveFilter bs n0)).
        apply lemma_1_of_1_2_12.
        lia.
      apply H11.
      apply H5.
      apply H6.
      apply H4.
      constructor.
      intros b.
      intro.
      destruct (enumB_surjective b) as [n].
      cut (equiconsistent (improveFilter bs n) (Cl (union (improveFilter bs n) (singleton b)))).
        intro.
        apply (InCompleteFilter (S n)).
        simpl.
        apply (Closure [b]).
        intros p.
        intro.
        inversion H3.
        subst.
        apply UnionR.
        apply Insertion.
        apply H2.
        inversion H4.
        simpl.
        apply leq_CBA_refl'.
        apply trueB_unit_andB.
      constructor.
      intro.
      destruct H2 as [b'].
      destruct H2.
      exists b'.
      constructor.
      apply (Closure [b']).
      intros p.
      intro.
      inversion H4.
      subst.
      apply UnionL.
      apply H2.
      inversion H5.
      simpl.
      apply leq_CBA_refl'.
      apply trueB_unit_andB.
      apply H3.
      intro.
      cut (inconsistent (Cl (insert b (CompleteFilter bs)))).
        assert (equiconsistent bs (improveFilter bs n)).
          apply lemma_1_of_1_2_13.
          apply HHH.
        assert (equiconsistent bs (CompleteFilter bs)).
          apply lemma_3_of_1_2_13.
          apply HHH.
        unfold equiconsistent in *.
        tauto.
      destruct H2 as [b'].
      destruct H2.
      exists b'.
      constructor.
      assert (isSubsetOf (Cl (union (improveFilter bs n) (singleton b))) (Cl (insert b (CompleteFilter bs)))).
        apply fact_4_of_1_2_8.
        intros p.
        intro.
        inversion H4.
        subst.
        apply UnionL.
        apply (InCompleteFilter n).
        apply H5.
        subst.
        apply UnionR.
        apply H5.
      apply H4.
      apply H2.
      apply H3.
      apply lemma_3_of_1_2_13.
      apply HHH.
    Qed.

  Section TheoryOfCBA.

End CountableBooleanAlgebra.

Module PropositionalLogic.

  Import ListNotations.

  Import Helper.

  Import CountableBooleanAlgebra.

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

End PropositionalLogic.
