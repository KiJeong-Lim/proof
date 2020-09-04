Require Export List.
Require Export Bool.
Require Export Lia.

Module Preliminary.

  Import ListNotations.

  Axiom ex_middle : forall P : Prop, P \/ ~P.

  Section Ordering.

    Fixpoint predecessor (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n'
      end
    .

    Inductive Ordering : Set :=
    | LT : Ordering
    | EQ : Ordering
    | GT : Ordering
    .

    Fixpoint compare (lhs : nat) (rhs : nat) : Ordering :=
      match lhs, rhs with
      | 0, 0 => EQ
      | 0, S rhs' => LT
      | S lhs', 0 => GT
      | S lhs', S rhs' => compare lhs' rhs'
      end
    .

    Lemma compare_property :
      forall n : nat,
      forall lhs rhs : nat,
      (lhs <= n \/ rhs <= n) ->
      ((compare lhs rhs = LT /\ lhs < rhs) \/ (compare lhs rhs = EQ /\ lhs = rhs) \/ (compare lhs rhs = GT /\ lhs > rhs)).
    Proof.
      intros n.
      induction n.
      - intros lhs rhs.
        intro.
        destruct H.
        * assert (lhs = 0).
            lia.
          assert (rhs = 0 \/ rhs > 0).
            lia.
          destruct H1.
          + subst.
            simpl.
            tauto.
          + inversion H1.
              subst.
              simpl.
              tauto.
              subst.
              simpl.
              tauto.
        * assert (rhs = 0).
            lia.
          assert (lhs = 0 \/ lhs > 0).
            lia.
          destruct H1.
          + subst.
            simpl.
            tauto.
          + inversion H1.
              subst.
              simpl.
              tauto.
              subst.
              simpl.
              tauto.
      - intros lhs rhs.
        intro.
        destruct H.
        * assert (lhs <= n \/ lhs = S n).
            lia.
          destruct H0.
          + apply (IHn lhs rhs (or_introl H0)).
          + assert (rhs <= n \/ rhs > n).
              lia.
            destruct H1.
              apply (IHn lhs rhs (or_intror H1)).
              inversion H1.
                subst.
                simpl.
                assert (compare n n = EQ).
                  assert (compare n n = LT /\ n < n \/ compare n n = EQ /\ n = n \/ compare n n = GT /\ n > n).
                    apply (IHn n n).
                      lia.
                  assert (~ n < n).
                    lia.
                  assert (~ n > n).
                    lia.
                  tauto.
                tauto.
                subst.
                simpl.
                assert (S n < S m).
                  lia.
                assert (compare n m = LT).
                  assert (compare n m = LT /\ n < m \/ compare n m = EQ /\ n = m \/ compare n m = GT /\ n > m).
                    apply (IHn n m).
                      lia.
                  assert (~ n = m).
                    lia.
                  assert (~ n > m).
                    lia.
                  tauto.
                tauto.
        * assert (rhs <= n \/ rhs = S n).
            lia.
          destruct H0.
          + apply (IHn lhs rhs (or_intror H0)).
          + assert (lhs <= n \/ lhs > n).
              lia.
            destruct H1.
              apply (IHn lhs rhs (or_introl H1)).
              inversion H1.
                subst.
                simpl.
                assert (compare n n = EQ).
                  assert (compare n n = LT /\ n < n \/ compare n n = EQ /\ n = n \/ compare n n = GT /\ n > n).
                    apply (IHn n n).
                      lia.
                  assert (~ n < n).
                    lia.
                  assert (~ n > n).
                    lia.
                  tauto.
                tauto.
                subst.
                simpl.
                assert (S n < S m).
                  lia.
                assert (compare m n = GT).
                  assert (compare m n = LT /\ m < n \/ compare m n = EQ /\ m = n \/ compare m n = GT /\ m > n).
                    apply (IHn m n).
                      lia.
                  assert (~ m = n).
                    lia.
                  assert (~ m < n).
                    lia.
                  tauto.
                tauto.
    Qed.

    Theorem ordering_property :
      forall lhs rhs : nat,
      (LT = compare lhs rhs <-> lhs < rhs) /\
      (EQ = compare lhs rhs <-> lhs = rhs) /\
      (GT = compare lhs rhs <-> lhs > rhs).
    Proof.
      intros lhs rhs.
      assert ((compare lhs rhs = LT /\ lhs < rhs) \/ (compare lhs rhs = EQ /\ lhs = rhs) \/ (compare lhs rhs = GT /\ lhs > rhs)).
        apply (compare_property lhs lhs rhs).
          lia.
      constructor.
        constructor.
          intro.
          destruct H.
            tauto.
          destruct H.
          destruct H.
          elimtype False.
            assert (LT = EQ).
              rewrite H in H0.
              apply H0.
            discriminate H2.
          destruct H.
          elimtype False.
            assert (LT = GT).
              rewrite H in H0.
              apply H0.
            discriminate H2.
        intro.
        assert (~ lhs = rhs).
          lia.
        assert (~ lhs > rhs).
          lia.
        assert (lhs < rhs).
          lia.
        intuition.
      constructor.
        constructor.
            intro.
            destruct H.
            destruct H.
            elimtype False.
              assert (EQ = LT).
                rewrite H in H0.
                apply H0.
              discriminate H2.
            destruct H.
            destruct H.
            tauto.
            destruct H.
            elimtype False.
              assert (EQ = GT).
                rewrite H in H0.
                apply H0.
              discriminate H2.
          intro.
          assert (~ lhs < rhs).
            lia.
          assert (~ lhs > rhs).
            lia.
          assert (lhs = rhs).
            lia.
          intuition.
        constructor.
            intro.
            destruct H.
            destruct H.
            elimtype False.
              assert (GT = LT).
                rewrite H in H0.
                apply H0.
              discriminate H2.
            destruct H.
            elimtype False.
              destruct H.
              assert (GT = EQ).
                rewrite H in H0.
                apply H0.
              discriminate H2.
              tauto.
          intro.
          assert (~ lhs < rhs).
            lia.
          assert (~ lhs = rhs).
            lia.
          intuition.  
    Qed.

  End Ordering.

End Preliminary.