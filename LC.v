From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.

Module Helper.

  Definition N : Set :=
    nat
  .

  Definition Bool : Set :=
    bool
  .

  Theorem SecondPrincipleOfFiniteInduction :
    forall phi : N -> Prop,
    let phi' : N -> Prop := fun k : N => (forall i : N, i < k -> phi i) in
    (forall k : N, phi' k -> phi k) ->
    (forall n : N, phi n).
  Proof.
    intros phi.
    intros phi'.
    intro.
    cut (
      (forall n : N, phi n /\ phi' n)
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

  Fixpoint first_nat (p : N -> bool) (n : N) : N :=
    match n with
    | 0 => 0
    | S n' =>
      if p (first_nat p n')
      then first_nat p n'
      else n
    end
  .

  Lemma well_ordering_principle : 
    forall p : N -> bool,
    forall n : N,
    p n = true ->
    let m : N := first_nat p n in
    p m = true /\ (forall i : nat, p i = true -> i >= m).
  Proof.
    intros p.
    assert (forall x : nat, p x = true -> p (first_nat p x) = true).
      intros x.
      induction x.
      tauto.
      simpl.
      cut (let b : Bool := p (first_nat p x) in p (S x) = true -> p (if b then first_nat p x else S x) = true).
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
    assert (forall x : N, first_nat p x <= x).
      intros x.
      induction x.
        simpl.
        lia.
        simpl.
        cut (let b : Bool := p (first_nat p x) in (if b then first_nat p x else S x) <= S x).
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
    assert (forall x : N, p (first_nat p x) = true -> (forall y : N, x < y -> first_nat p x = first_nat p y)).
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
    assert (forall x : N, forall y : N, p y = true -> first_nat p x <= y).
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
    unfold m.
    apply H5.
  Qed.

  Theorem WellOrderingPrinciple :
    forall Phi : N -> Prop,
    (forall i : N, {Phi i} + {~ Phi i}) ->
    {n : N | Phi n} ->
    {m : N | Phi m /\ (forall i : N, Phi i -> i >= m)}.
  Proof.
    intros Phi H_Phi_dec H_n_exists.
    destruct H_n_exists as [n].
    destruct (well_ordering_principle (fun i : N => if H_Phi_dec i then true else false) n).
    destruct (H_Phi_dec n).
    tauto.
    tauto.
    apply (exist (fun m : N => Phi m /\ (forall i : N, Phi i -> i >= m)) (first_nat (fun i : N => if H_Phi_dec i then true else false) n)).
    constructor.
    destruct (H_Phi_dec (first_nat (fun i : N => if H_Phi_dec i then true else false) n)).
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

  Lemma fold_right_max_0_property1 :
    forall Phi : N -> Prop,
    (forall i : N, {Phi i} + {~ Phi i}) ->
    forall ns : list N,
    (forall i : N, Phi i -> In i ns) ->
    forall n : N,
    Phi n ->
    fold_right max 0 ns >= n.
  Proof.
    intros Phi Phi_dec ns.
    induction ns.
    - simpl.
      intros.
      contradiction (H n).
    - simpl.
      intros.
      assert (a >= n \/ a < n).
        lia.
      destruct H1.
      * lia.
      * cut (fold_right max 0 ns >= n).
          lia.
        destruct (Phi_dec n).
        + destruct (H n p).
          { lia.
          }
          { cut (
              forall ks : list N,
              forall k : N,
              In k ks ->
              fold_right max 0 ks >= k
            ).
              intros.
              apply H3.
              apply H2.
            intros ks.
            induction ks.
            { simpl.
              intros.
              tauto.
            }
            { simpl.
              intros.
              destruct H3.
              { subst.
                lia.
              }
              { cut (fold_right Init.Nat.max 0 ks >= k).
                  lia.
                apply IHks.
                apply H3.
              }
            }
          }
        + apply IHns.
          { intros.
            destruct (H i H2).
            { subst.
              contradiction n0.
            }
            apply H3.
          }
          contradiction n0.
  Qed.

  Lemma fold_right_max_0_property2 :
    forall ns : list N,
    forall n : N,
    fold_right max 0 ns > n <-> (exists i : N, In i ns /\ i > n).
  Proof.
    intros ns.
    induction ns.
    - simpl.
      intros.
      constructor.
      * lia.
      * intro.
        destruct H.
        destruct H.
        contradiction H.
    - simpl.
      intros.
      assert (a > (fold_right Init.Nat.max 0 ns) \/ a <= (fold_right Init.Nat.max 0 ns)).
        lia.
      destruct H.
      * constructor.
        + intros.
          exists a.
          constructor.
          left.
          reflexivity.
          lia.
        + intros.
          destruct H0 as [i].
          destruct H0.
          destruct H0.
          subst.
          lia.
          assert (fold_right Init.Nat.max 0 ns > n).
            apply IHns.
            exists i.
            constructor.
            apply H0.
            apply H1.
          lia.
      * constructor.
        + intros.
          assert (fold_right Init.Nat.max 0 ns > n).
            lia.
          destruct (proj1 (IHns n) H1) as [i].
          destruct H2.
          exists i.
          constructor.
          right.
          apply H2.
          apply H3.
        + intros.
          destruct H0 as [i].
          destruct H0.
          destruct H0.
          subst.
          lia.
          assert (fold_right max 0 ns > n).
            apply IHns.
            exists i.
            constructor.
            apply H0.
            apply H1.
          lia.
  Qed.

  Lemma fold_right_max_0_property3 :
    forall ns1 : list N,
    forall ns2 : list N,
    fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
  Proof.
    intros ns1.
    induction ns1.
    - intros ns2.
      simpl.
      reflexivity.
    - intros ns2.
      simpl.
      assert (H := IHns1 ns2).
      rewrite H.
      lia.
  Qed.

  Lemma fold_right_max_0_property4 :
    forall ns : list N,
    forall n : N,
    In n ns ->
    fold_right max 0 ns >= n.
  Proof.
    intros ns.
    induction ns.
    - simpl.
      tauto.
    - simpl.
      intros.
      destruct H.
      * subst.
        lia.
      * assert (fold_right max 0 ns >= n).
          apply IHns.
        apply H.
        lia.
  Qed.

  Lemma fold_right_max_0_property5 :
    forall ns1 : list N,
    forall ns2 : list N,
    (forall n : N, In n ns1 -> In n ns2) ->
    fold_right max 0 ns1 <= fold_right max 0 ns2.
  Proof.
    intros ns1.
    induction ns1.
    - simpl.
      intros.
      lia.
    - simpl.
      intros.
      assert (a <= fold_right max 0 ns1 \/ a > fold_right max 0 ns1).
        lia.
      destruct H0.
      * cut (fold_right max 0 ns1 <= fold_right max 0 ns2).
          lia.
        apply IHns1.
        intros.
        apply H.
        right.
        apply H1.
      * cut (a <= fold_right max 0 ns2).
          lia.
        apply fold_right_max_0_property4.
        apply H.
        tauto.
  Qed.

  Lemma forallb_true_iff {A : Type} {Phi : A -> Bool} :
    forall xs : list A,
    forallb Phi xs = true <-> (forall x : A, In x xs -> Phi x = true).
  Proof.
    intros xs.
    induction xs.
    - simpl.
      tauto.
    - simpl.
      constructor.
      * intros.
        assert (Phi a = true /\ forallb Phi xs = true).
          apply andb_true_iff.
          apply H.
        destruct H1.
        destruct H0.
        + subst.
          apply H1.
        + apply IHxs.
          apply H2.
          apply H0.
      * intros.
        cut (Phi a = true /\ forallb Phi xs = true).
          apply andb_true_iff.
        constructor.
        + apply H.
          left.
          reflexivity.
        + apply IHxs.
          intros.
          apply H.
          right.
          apply H0.
  Qed.

End Helper.

Module STLC.

  Import ListNotations.

  Import Helper.

  Definition IVar : Set :=
    N
  .

  Inductive Tm : Set :=
  | Var : forall iv : IVar, Tm
  | App : forall tm1 : Tm, forall tm2 : Tm, Tm
  | Abs : forall iv : IVar, forall tm1 : Tm, Tm
  .

  Lemma Tm_eq_dec :
    forall tm1 : Tm,
    forall tm2 : Tm,
    {tm1 = tm2} + {tm1 <> tm2}.
  Proof.
    intros tm1.
    induction tm1.
    - intros tm2.
      destruct tm2.
      * destruct (Nat.eq_dec iv iv0).
        + left.
          subst.
          reflexivity.
        + right.
          intro.
          inversion H.
          contradiction n.
      * right.
        intro.
        inversion H.
      * right.
        intro.
        inversion H.
    - intros tm2.
      destruct tm2.
      * right.
        intro.
        inversion H.
      * destruct (IHtm1_1 tm2_1).
        + subst.
          destruct (IHtm1_2 tm2_2).
          { subst.
            left.
            reflexivity.
          }
          { right.
            intro.
            inversion H.
            contradiction n.
          }
        + right.
          intro.
          inversion H.
          contradiction n.
      * right.
        intro.
        inversion H.
    - intros tm2.
      destruct tm2.
      * right.
        intro.
        inversion H.
      * right.
        intro.
        inversion H.
      * destruct (Nat.eq_dec iv iv0).
        + subst.
          destruct (IHtm1 tm2).
          { subst.
            left.
            reflexivity.
          }
          { right.
            intro.
            inversion H.
            contradiction n.
          }
        + right.
          intro.
          inversion H.
          contradiction n.
  Qed.

  Fixpoint isFreeIn (iv0 : IVar) (tm : Tm) : Bool :=
    match tm with
    | Var iv => if Nat.eq_dec iv0 iv then true else false
    | App tm1 tm2 => orb (isFreeIn iv0 tm1) (isFreeIn iv0 tm2)
    | Abs iv tm1 => andb (isFreeIn iv0 tm1) (if Nat.eq_dec iv0 iv then false else true)
    end
  .

  Definition FreeIn (iv0 : IVar) (tm : Tm) : Prop :=
    isFreeIn iv0 tm = true
  .

  Lemma FreeIn_dec :
    forall iv0 : IVar,
    forall tm : Tm,
    {FreeIn iv0 tm} + {~ FreeIn iv0 tm}.
  Proof.
    cut (
      forall tm : Tm,
      forall iv0 : IVar,
      {FreeIn iv0 tm} + {~ FreeIn iv0 tm}
    ).
      intros.
      destruct (H tm iv0).
      tauto.
      tauto.
    intros.
    unfold FreeIn.
    destruct (isFreeIn iv0 tm).
    left.
    reflexivity.
    right.
    intro.
    inversion H.
  Qed.

  Lemma FreeIn_Var :
    forall iv0 : IVar,
    forall iv : IVar,
    FreeIn iv0 (Var iv) <-> iv0 = iv.
  Proof.
    intros.
    constructor.
    - intros.
      inversion H.
      destruct (Nat.eq_dec iv0 iv).
      * apply e.
      * inversion H1.
    - intros.
      subst.
      unfold FreeIn.
      simpl.
      destruct (Nat.eq_dec iv iv).
      * reflexivity.
      * contradiction n.
        reflexivity.
  Qed.

  Definition FreshIn (iv0 : IVar) (tm : Tm) : Prop :=
    isFreeIn iv0 tm = false
  .

  Lemma FreshIn_iff :
    forall iv0 : IVar,
    forall tm : Tm,
    FreshIn iv0 tm <-> ~ FreeIn iv0 tm.
  Proof.
    intros.
    unfold FreeIn.
    unfold FreshIn.
    destruct (isFreeIn iv0 tm).
    - intuition.
    - intuition.
  Qed.

  Lemma FreshIn_dec :
    forall iv0 : IVar,
    forall tm : Tm,
    {FreshIn iv0 tm} + {~ FreshIn iv0 tm}.
  Proof.
    intros.
    assert (FreshIn iv0 tm <-> ~ FreeIn iv0 tm).
      apply FreshIn_iff.
    destruct (FreeIn_dec iv0 tm).
    - right.
      tauto.
    - left.
      tauto.
  Qed.

  Lemma FreshIn_Var :
    forall iv0 : IVar,
    forall iv : IVar,
    FreshIn iv0 (Var iv) <-> iv0 <> iv.
  Proof.
    intros.
    assert (FreshIn iv0 (Var iv) <-> ~ FreeIn iv0 (Var iv)).
      apply FreshIn_iff.
    assert (FreeIn iv0 (Var iv) <-> iv0 = iv).
      apply FreeIn_Var.
    tauto.
  Qed.

  Fixpoint getFVs (tm : Tm) : list IVar :=
    match tm with
    | Var iv => [iv]
    | App tm1 tm2 => getFVs tm1 ++ getFVs tm2
    | Abs iv tm1 => remove Nat.eq_dec iv (getFVs tm1)
    end
  .

  Lemma getFVs_returns_free_vars :
    forall iv : IVar,
    forall tm : Tm,
    In iv (getFVs tm) <-> FreeIn iv tm.
  Proof.
    cut (
      forall tm : Tm,
      forall iv0 : IVar,
      In iv0 (getFVs tm) <-> FreeIn iv0 tm
    ).
      intros.
      apply (H tm iv).
    intros tm.
    induction tm.
    - intros.
      constructor.
      * intros.
        inversion H.
        + subst.
          apply FreeIn_Var.
          reflexivity.
        + inversion H0.
      * intros.
        simpl.
        left.
        cut (iv0 = iv).
          intuition.
        apply FreeIn_Var.
        apply H.
    - intros.
      unfold FreeIn.
      simpl.
      constructor.
      * intros.
        destruct (in_app_or _ _ _ H).
        + apply orb_true_iff.
          left.
          apply IHtm1.
          apply H0.
        + apply orb_true_iff.
          right.
          apply IHtm2.
          apply H0.
      * intros.
        assert (isFreeIn iv0 tm1 = true \/ isFreeIn iv0 tm2 = true).
          apply orb_true_iff.
          apply H.
        destruct H0.
        + apply in_or_app.
          left.
          apply IHtm1.
          apply H0.
        + apply in_or_app.
          right.
          apply IHtm2.
          apply H0.
    - intros.
      unfold FreeIn.
      simpl.
      constructor.
      * intro.
        apply andb_true_iff.
        constructor.
        + apply IHtm.
          apply (in_remove Nat.eq_dec _ iv0 iv).
          apply H.
        + destruct (Nat.eq_dec iv0 iv).
          { subst.
            contradiction (remove_In _ (getFVs tm) iv H).
          }
          { reflexivity.
          }
      * intro.
        assert (isFreeIn iv0 tm = true /\ (if Nat.eq_dec iv0 iv then false else true) = true).
          apply andb_true_iff.
          apply H.
        destruct H0.
        apply in_in_remove.
        + destruct (Nat.eq_dec iv0 iv).
          { inversion H1.
          }
          { apply n.
          }
        + apply IHtm.
          apply H0.
  Qed.

  Definition Subst : Type :=
    list (IVar * Tm)
  .

  Fixpoint runSubst_Var (sub : Subst) (iv0 : IVar) : Tm :=
    match sub with
    | [] => Var iv0
    | (iv, tm) :: sub' =>
      if Nat.eq_dec iv iv0
      then tm
      else runSubst_Var sub' iv0
    end
  .

  Inductive IsProperSubst : Subst -> Prop :=
  | NilSubst :
    IsProperSubst []
  | ConsSubst :
    forall iv : IVar,
    forall tm : Tm,
    forall sub : Subst,
    Var iv <> tm ->
    ~ In iv (map fst sub) ->
    IsProperSubst sub ->
    IsProperSubst ((iv, tm) :: sub)
  .

  Lemma IsProperSubst_property1 :
    forall sub : Subst,
    IsProperSubst sub ->
    forall iv : IVar,
    runSubst_Var sub iv = Var iv <-> ~ In iv (map fst sub).
  Proof.
    intros sub H.
    induction H.
    - intros.
      unfold runSubst_Var.
      simpl.
      tauto.
    - intros.
      unfold runSubst_Var.
      destruct (Nat.eq_dec iv iv0).
      * subst.
        constructor.
        + intro.
          contradiction H.
          intuition.
        + simpl.
          intro.
          contradiction H2.
          left.
          reflexivity.
      * simpl.
        constructor.
        + intros.
          intro.
          destruct H3.
          contradiction n.
          apply (proj1 (IHIsProperSubst iv0) H2).
          apply H3.
        + intro.
          assert (~ In iv0 (map fst sub)).
            intro.
            apply H2.
            right.
            apply H3.
          assert (runSubst_Var sub iv0 = Var iv0).
            apply IHIsProperSubst.
            apply H3.
          apply H4.
  Qed.

  Definition FreshInSubst (iv0 : IVar) (sub : Subst) (tm : Tm) : Prop :=
    forallb (fun iv : IVar => if FreshIn_dec iv0 (runSubst_Var sub iv) then true else false) (getFVs tm) = true
  .

  Definition getFreeVarBound (tm : Tm) : N :=
    fold_right max 0 (getFVs tm)
  .

  Lemma getFreeVarBound_property1 :
    forall tm : Tm,
    forall iv : IVar,
    iv > getFreeVarBound tm ->
    FreshIn iv tm.
  Proof.
    intros tm iv.
    assert (FreeIn iv tm -> getFreeVarBound tm >= iv).
      intros.
      apply (fold_right_max_0_property1 (fun iv0 : IVar => FreeIn iv0 tm)).
      { intros.
        apply FreeIn_dec.
      }
      { intros.
        apply getFVs_returns_free_vars.
        apply H0.
      }
      { apply H.
      }
      { intro.
        assert (~ FreeIn iv tm).
          intro.
          assert (getFreeVarBound tm >= iv).
            apply H.
            apply H1.
          lia.
        apply FreshIn_iff.
        apply H1.
      }
  Qed.

  Definition chi (sub : Subst) (tm : Tm) : IVar :=
    S (fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub iv0)) (getFVs tm)))
  .

  Lemma chi_property1 :
    forall sub : Subst,
    forall tm : Tm,
    forall iv : IVar,
    FreeIn iv tm ->
    FreshIn (chi sub tm) (runSubst_Var sub iv).
  Proof.
    intros sub tm.
    assert (
      forall iv : IVar,
      FreeIn iv tm ->
      getFreeVarBound (runSubst_Var sub iv) < chi sub tm 
    ).
    { intros.
      unfold chi.
      cut (
        fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub iv0)) (getFVs tm)) >= getFreeVarBound (runSubst_Var sub iv)
      ).
        lia.
      apply (fold_right_max_0_property1 (fun iv' : IVar => In iv' (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub iv0)) (getFVs tm)))).
      { intros.
        apply In_dec.
        apply Nat.eq_dec.
      }
      { tauto.
      }
      { apply in_map_iff.
        exists iv.
        constructor.
        reflexivity.
        apply getFVs_returns_free_vars.
        apply H.
      }
    }
    intros.
    apply getFreeVarBound_property1.
    apply H.
    apply H0.
  Qed.

  Lemma chi_gives_FreshInSubst :
    forall sub : Subst,
    forall tm : Tm,
    FreshInSubst (chi sub tm) sub tm.
  Proof.
    intros sub tm.
    unfold FreshInSubst.
    cut (
      forall iv : IVar,
      In iv (getFVs tm) ->
      FreshIn (chi sub tm) (runSubst_Var sub iv)
    ).
      intros.
      apply forallb_true_iff.
      intros iv H0.
      assert (In iv (getFVs tm) -> FreshIn (chi sub tm) (runSubst_Var sub iv)).
        apply H.
      destruct (FreshIn_dec (chi sub tm) (runSubst_Var sub iv)).
      { reflexivity.
      }
      { contradiction n.
        apply H1.
        apply H0.
      }
    intros.
    apply chi_property1.
    apply getFVs_returns_free_vars.
    apply H.
  Qed.

  Lemma chi_bounds_FreshInSubst :
    forall sub : Subst,
    forall tm : Tm,
    forall iv : IVar,
    iv >= chi sub tm ->
    FreshInSubst iv sub tm.
  Proof.
    assert (
      forall sub : Subst,
      forall tm : Tm,
      forall iv : IVar,
      (exists iv0 : IVar, FreeIn iv0 tm /\ FreeIn iv (runSubst_Var sub iv0)) ->
      fold_right max 0 (map (fun iv0 : IVar => S (getFreeVarBound (runSubst_Var sub iv0))) (getFVs tm)) > iv
    ).
      intros.
      apply fold_right_max_0_property2.
      destruct H as [iv0].
      destruct H.
      exists (S (getFreeVarBound (runSubst_Var sub iv0))).
      constructor.
      apply in_map_iff.
      exists iv0.
      constructor.
      reflexivity.
      apply getFVs_returns_free_vars.
      apply H.
      cut (~ getFreeVarBound (runSubst_Var sub iv0) < iv).
        lia.
      intro.
      contradiction (proj1 (FreshIn_iff iv (runSubst_Var sub iv0))).
      apply getFreeVarBound_property1.
      apply H1.
    intros.
    assert (~ (exists iv0 : IVar, FreeIn iv0 tm /\ FreeIn iv (runSubst_Var sub iv0))).
      intro.
      assert (fold_right max 0 (map (fun iv0 : IVar => S (getFreeVarBound (runSubst_Var sub iv0))) (getFVs tm)) > iv).
        apply H.
        apply H1.
      assert (
        chi sub tm >= fold_right max 0 (map (fun iv0 : IVar => S (getFreeVarBound (runSubst_Var sub iv0))) (getFVs tm))
      ).
      { unfold chi.
        induction (getFVs tm).
        - simpl.
          lia.
        - simpl in *.
          destruct (fold_right max 0 (map (fun iv0 : IVar => S (getFreeVarBound (runSubst_Var sub iv0))) l)).
          lia.
          lia.
      }
      lia.
    unfold FreshInSubst.
    apply forallb_true_iff.
    intros iv0 H2.
    assert (~ (if FreshIn_dec iv (runSubst_Var sub iv0) then true else false) = false).
    { intro.
      apply H1.
      exists iv0.
      constructor.
      apply getFVs_returns_free_vars.
      apply H2.
      destruct (FreshIn_dec iv (runSubst_Var sub iv0)).
      inversion H3.
      unfold FreeIn.
      unfold FreshIn in n.
      destruct (isFreeIn iv (runSubst_Var sub iv0)).
      reflexivity.
      contradiction n.
    }
    destruct (FreshIn_dec iv (runSubst_Var sub iv0)).
    reflexivity.
    contradiction H3.
    reflexivity.
  Qed.

  Lemma chi_property2 :
    forall sub : Subst,
    forall tm : Tm,
    forall iv0 : IVar,
    iv0 >= chi sub tm ->
    forall iv : IVar,
    FreeIn iv tm ->
    FreshIn iv0 (runSubst_Var sub iv).
  Proof.
    intros sub tm iv0 H.
    assert (XXX := chi_bounds_FreshInSubst sub tm iv0 H).
    unfold FreshInSubst in XXX.
    assert (forall iv : IVar, In iv (getFVs tm) -> (if FreshIn_dec iv0 (runSubst_Var sub iv) then true else false) = true).
      apply forallb_true_iff.
      apply XXX.
    intros.
    assert ((if FreshIn_dec iv0 (runSubst_Var sub iv) then true else false) = true).
      apply H0.
      apply getFVs_returns_free_vars.
      apply H1.
    destruct (FreshIn_dec iv0 (runSubst_Var sub iv)).
    apply f.
    inversion H2.
  Qed.

  Lemma chi_empty_fresh :
    forall tm : Tm,
    FreshIn (chi [] tm) tm.
  Proof.
    cut (
      forall tm0 : Tm,
      forall iv0 : IVar,
      FreeIn iv0 tm0 ->
      chi [] tm0 > iv0
    ).
      intros.
      unfold FreshIn.
      assert (FreeIn (chi [] tm) tm -> chi [] tm > chi [] tm).
        apply H.
      unfold FreeIn in H0.
      destruct (isFreeIn (chi [] tm) tm).
      assert (chi [] tm > chi [] tm).
        apply H0.
        tauto.
        lia.
      reflexivity.
    intros tm.
    assert (
      forall iv0 : IVar,
      iv0 >= chi [] tm ->
      forall iv : IVar,
      FreeIn iv tm ->
      FreshIn iv0 (runSubst_Var [] iv)
    ).
      intros.
      apply (chi_property2 [] tm).
      apply H.
      apply H0.
    intros.
    cut (~ iv0 >= chi [] tm).
      lia.
    intro.
    assert (FreshIn iv0 (runSubst_Var [] iv0)).
    simpl.
    apply H.
    apply H1.
    apply H0.
    simpl in H2.
    unfold FreshIn in H2.
    simpl in H2.
    destruct (Nat.eq_dec iv0 iv0).
    inversion H2.
    contradiction n.
    reflexivity.
  Qed.

  Fixpoint runSubst_Term (sub : Subst) (tm : Tm) : Tm :=
    match tm with
    | Var iv => runSubst_Var sub iv
    | App tm1 tm2 => App (runSubst_Term sub tm1) (runSubst_Term sub tm2)
    | Abs iv tm1 =>
      let iv' : IVar := chi sub tm in
      Abs iv' (runSubst_Term ((iv', Var iv) :: sub) tm1)
    end
  .

  Lemma identity_subst :
    forall tm : Tm,
    runSubst_Term [] tm = tm.

  Lemma simultaneous_subst :
    forall sub : Subst,
    forall tm1 : Tm,
    forall tm2 : Tm,
    forall iv3 : IVar,
    runSubst_Term ((iv3, runSubst_Term sub tm2) :: sub) tm1 = runSubst_Term sub (runSubst_Term [(iv3, tm2)] tm1).

End STLC.
