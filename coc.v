Require Export List.
Require Export Bool.
Require Export Lia.

Module Preliminary.

  Import ListNotations.

  Section Classic.

    Axiom ex_middle : forall P : Prop, P \/ ~P.
  
  End Classic.

  Section Ordering.

    Definition predecessor (n : nat) : nat :=
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

    Theorem LT_property :
      forall lhs rhs : nat,
      LT = compare lhs rhs <-> lhs < rhs.
    Proof.
      intros lhs rhs.
      assert ((compare lhs rhs = LT /\ lhs < rhs) \/ (compare lhs rhs = EQ /\ lhs = rhs) \/ (compare lhs rhs = GT /\ lhs > rhs)).
        apply (compare_property lhs lhs rhs).
          lia.
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
    Qed.

    Theorem EQ_property :
      forall lhs rhs : nat,
      EQ = compare lhs rhs <-> lhs = rhs.
    Proof.
      intros lhs rhs.
      assert ((compare lhs rhs = LT /\ lhs < rhs) \/ (compare lhs rhs = EQ /\ lhs = rhs) \/ (compare lhs rhs = GT /\ lhs > rhs)).
        apply (compare_property lhs lhs rhs).
          lia.
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
    Qed.

    Theorem GT_property :
      forall lhs rhs : nat,
      GT = compare lhs rhs <-> lhs > rhs.
    Proof.
      intros lhs rhs.
      assert ((compare lhs rhs = LT /\ lhs < rhs) \/ (compare lhs rhs = EQ /\ lhs = rhs) \/ (compare lhs rhs = GT /\ lhs > rhs)).
        apply (compare_property lhs lhs rhs).
          lia.
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

Module Coc.

  Import ListNotations.

  Import Preliminary.

  Section Syntax.

    Inductive OSort : Set :=
    | OSKind : OSort
    | OSProp : OSort
    .
    
    Inductive OTerm : Set :=
    | OTSort : OSort -> OTerm
    | OTIdx : nat -> OTerm
    | OTAbs : OTerm -> OTerm -> OTerm
    | OTApp : OTerm -> OTerm -> OTerm
    | OTProd : OTerm -> OTerm -> OTerm
    .
    
    Fixpoint lift (n : nat) (k : nat) (t : OTerm) : OTerm :=
      match t with
      | OTSort s => OTSort s
      | OTIdx i =>
        match compare i k with
        | EQ | GT => OTIdx (i + n)
        | LT => OTIdx i
        end
      | OTAbs t1 t2 => OTAbs (lift n k t1) (lift n (S k) t2)
      | OTApp t1 t2 => OTApp (lift n k t1) (lift n k t2)
      | OTProd t1 t2 => OTProd (lift n k t1) (lift n (S k) t2)
      end
    .

    Fixpoint substitute (t : OTerm) (k : nat) (t' : OTerm) : OTerm :=
      match t with
      | OTSort s => OTSort s
      | OTIdx i =>
        match compare i k with
        | GT => OTIdx (predecessor i)
        | EQ => lift k 0 t'
        | LT => OTIdx i
        end
      | OTAbs t1 t2 => OTAbs (substitute t1 k t') (substitute t2 (S k) t')
      | OTApp t1 t2 => OTApp (substitute t1 k t') (substitute t2 k t')
      | OTProd t1 t2 => OTProd (substitute t1 k t') (substitute t2 (S k) t')
      end
    .
    
    Lemma lift_0 :
      forall t : OTerm,
      forall k : nat,
      lift 0 k t = t.
    Proof.
      intros t.
      induction t.
      - intros k.
        simpl.
        tauto.
      - intros k.
        assert (n > k \/ n = k \/ n < k).
          lia.
        destruct H.
          assert (GT = compare n k).
            apply (proj2 (GT_property n k) H).
          simpl.
          rewrite <- H0.
          assert (n + 0 = n).
            lia.
          rewrite H1.
          tauto.
          destruct H.
            assert (EQ = compare n k).
              apply (proj2 (EQ_property n k) H).
            simpl.
            rewrite <- H0.
            assert (n + 0 = n).
              lia.
            rewrite H1.
            tauto.
            assert (LT = compare n k).
              apply (proj2 (LT_property n k) H).
            simpl.
            rewrite <- H0.
            tauto.
      - intros k.
        simpl.
        assert (lift 0 k t1 = t1).
          apply (IHt1 k).
        assert (lift 0 (S k) t2 = t2).
          apply (IHt2 (S k)).
        rewrite H.
        rewrite H0.
        tauto.
      - intros k.
        simpl.
        assert (lift 0 k t1 = t1).
          apply (IHt1 k).
        assert (lift 0 k t2 = t2).
          apply (IHt2 k).
        rewrite H.
        rewrite H0.
        tauto.
      - intros k.
        simpl.
        assert (lift 0 k t1 = t1).
          apply (IHt1 k).
        assert (lift 0 (S k) t2 = t2).
          apply (IHt2 (S k)).
        rewrite H.
        rewrite H0.
        tauto.
    Qed.

    Lemma simpl_lift :
      forall p i n k : nat,
      forall t : OTerm,
      k <= i <= k + n ->
      lift p i (lift n k t) = lift (p + n) k t.
    Proof.
    Qed.

    Lemma permute_lift :
      forall p i n k : nat,
      forall t : OTerm,
      i <= k ->
      lift p i (lift n k t) = lift n (p + k) (lift p i t).
    Proof.
    Qed.

    Lemma simpl_substitute :
      forall n k p : nat,
      forall t t' : OTerm,
      k <= p <= n + k ->
      substitute (lift (S n) k t) p t' = lift n k t.
    Proof.
    Qed.
    
    Lemma commute_lift_substitute :
      forall n k p : nat,
      forall t t' : OTerm,
      k <= p ->
      lift n k (substitute t p t') = substitute (lift n k t) (n + p) t'.
    Proof.
    Qed.

    Lemma distr_lift_substitute :
      forall n k p : nat,
      forall t t' : OTerm,
      lift n (p + k) (substitute t p t') = substitute (lift n (S (p + l)) t) p (lift n k t').
    Proof.
    Qed.

    Lemma distr_subst :
      forall p n : nat,
      forall t t' t'' : OTerm,
      substitute (substitute t p t') (p + n) t'' = substitute (substitute t (S (p + n)) t'') p (substitute t' n t'').
    Proof.
    Qed.

  End Syntax.
  
  Section BetaReduction.

    Inductive BetaReducesTo : OTerm -> OTerm -> Prop :=
    | BRT_BETA :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo (OTApp (OTAbs t1 t2) t3) (substitute t2 0 t3)
    | BRT_ABS_L :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo t1 t2 ->
      BetaReducesTo (OTAbs t1 t3) (OTAbs t2 t3)
    | BRT_ABS_R :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo t2 t3 ->
      BetaReducesTo (OTAbs t1 t2) (OTAbs t1 t3)
    | BRT_APP_L :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo t1 t2 ->
      BetaReducesTo (OTApp t1 t3) (OTApp t2 t3)
    | BRT_APP_R :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo t2 t3 ->
      BetaReducesTo (OTApp t1 t2) (OTApp t1 t3)
    | BRT_PROD_L :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo t1 t2 ->
      BetaReducesTo (OTProd t1 t3) (OTProd t2 t3)
    | BRT_PROD_R :
      forall t1 t2 t3 : OTerm,
      BetaReducesTo t2 t3 ->
      BetaReducesTo (OTProd t1 t2) (OTProd t1 t3)
    .

  End BetaReduction.

End Coc.

