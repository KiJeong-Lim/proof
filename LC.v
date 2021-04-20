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

  Lemma first_nat_ext :
    forall p1 : N -> bool,
    forall p2 : N -> bool,
    (forall n : N, p1 n = p2 n) ->
    forall n : N,
    first_nat p1 n = first_nat p2 n.
  Proof.
    intros.
    induction n.
    - simpl.
      reflexivity.
    - simpl.
      rewrite H.
      rewrite IHn.
      reflexivity.
  Qed.

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

  Definition equivSubst (sub1 : Subst) (sub2 : Subst) : Prop :=
    forall iv : IVar, runSubst_Var sub1 iv = runSubst_Var sub2 iv
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

  Lemma FreshInSubst_dec :
    forall iv0 : IVar,
    forall sub : Subst,
    forall tm : Tm,
    {FreshInSubst iv0 sub tm} + {~ FreshInSubst iv0 sub tm}.
  Proof.
    intros.
    unfold FreshInSubst.
    destruct (forallb (fun iv : IVar => if FreshIn_dec iv0 (runSubst_Var sub iv) then true else false) (getFVs tm)).
    - left.
      reflexivity.
    - right.
      intro.
      inversion H.
  Qed.

  Lemma equivSubst_property1 :
    forall tm : Tm,
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubst sub1 sub2 ->
    forall iv : IVar,
    FreshInSubst iv sub1 tm <-> FreshInSubst iv sub2 tm.
  Proof.
    intros tm.
    induction tm.
    - intros.
      unfold FreshInSubst.
      constructor.
      * intro.
        apply forallb_true_iff.
        intros iv' H1.
        assert (runSubst_Var sub1 iv' = runSubst_Var sub2 iv').
          apply H.
        rewrite <- H2.
        assert (
          forall iv' : IVar,
          In iv' (getFVs (Var iv)) ->
          (if FreshIn_dec iv0 (runSubst_Var sub1 iv') then true else false) = true
        ).
          apply forallb_true_iff.
          apply H0.
        apply H3.
        apply H1.
      * intro.
        apply forallb_true_iff.
        intros iv' H1.
        assert (runSubst_Var sub1 iv' = runSubst_Var sub2 iv').
          apply H.
        rewrite H2.
        assert (
          forall iv' : IVar,
          In iv' (getFVs (Var iv)) ->
          (if FreshIn_dec iv0 (runSubst_Var sub2 iv') then true else false) = true
        ).
          apply forallb_true_iff.
          apply H0.
        apply H3.
        apply H1.
    - intros.
      unfold FreshInSubst.
      constructor.
      * intro.
        apply forallb_true_iff.
        intros iv' H1.
        rewrite <- H.
        assert (
          forall iv' : IVar,
          In iv' (getFVs (App tm1 tm2)) ->
          (if FreshIn_dec iv (runSubst_Var sub1 iv') then true else false) = true
        ).
          apply forallb_true_iff.
          apply H0.
        apply H2.
        apply H1.
      * intro.
        apply forallb_true_iff.
        intros iv' H1.
        rewrite H.
        assert (
          forall iv' : IVar,
          In iv' (getFVs (App tm1 tm2)) ->
          (if FreshIn_dec iv (runSubst_Var sub2 iv') then true else false) = true
        ).
          apply forallb_true_iff.
          apply H0.
        apply H2.
        apply H1.
    - intros.
      unfold FreshInSubst.
      constructor.
      * intro.
        apply forallb_true_iff.
        intros iv' H1.
        rewrite <- H.
        assert (
          forall iv' : IVar,
          In iv' (getFVs (Abs iv tm)) ->
          (if FreshIn_dec iv0 (runSubst_Var sub1 iv') then true else false) = true
        ).
          apply forallb_true_iff.
          apply H0.
        apply H2.
        apply H1.
      * intro.
        apply forallb_true_iff.
        intros iv' H1.
        rewrite H.
        assert (
          forall iv' : IVar,
          In iv' (getFVs (Abs iv tm)) ->
          (if FreshIn_dec iv0 (runSubst_Var sub2 iv') then true else false) = true
        ).
          apply forallb_true_iff.
          apply H0.
        apply H2.
        apply H1.
  Qed.

  Lemma FreshInSubst_nil :
    forall tm : Tm,
    forall iv : IVar,
    FreshIn iv tm <-> FreshInSubst iv [] tm.
  Proof.
    intros tm.
    induction tm.
    - intros.
      constructor.
      * intro.
        inversion H.
        unfold FreshInSubst.
        apply forallb_true_iff.
        intros iv' H0.
        simpl.
        destruct (FreshIn_dec iv0 (Var iv')).
        + reflexivity.
        + destruct (Nat.eq_dec iv0 iv).
          { inversion H1.
          }
          { inversion H0.
            - subst.
              contradiction n.
            - inversion H2.
          }
      * intro.
        inversion H.
        destruct (FreshIn_dec iv0 (Var iv)).
        + apply f.
        + inversion H1.
    - intros.
      constructor.
      * intro.
        inversion H.
        assert (isFreeIn iv tm1 = false /\ isFreeIn iv tm2 = false).
          apply orb_false_iff.
          apply H1.
        destruct H0.
        unfold FreshInSubst.
        apply forallb_true_iff.
        intros iv' H3.
        simpl.
        destruct (FreshIn_dec iv (Var iv')).
        + reflexivity.
        + contradiction n.
          apply FreshIn_Var.
          intro.
          subst.
          contradiction (proj1 (FreshIn_iff iv' (App tm1 tm2))).
          apply getFVs_returns_free_vars.
          apply H3.
      * intro.
        unfold FreshIn.
        simpl.
        apply orb_false_iff.
        constructor.
        + apply IHtm1.
          apply forallb_true_iff.
          intros iv' H0.
          simpl.
          destruct (FreshIn_dec iv (Var iv')).
          { reflexivity.
          }
          { contradiction n.
            apply FreshIn_Var.
            intro.
            subst.
            inversion H.
            assert (
              forall iv : IVar,
              In iv (getFVs tm1 ++ getFVs tm2) ->
              (if FreshIn_dec iv' (Var iv) then true else false) = true
            ).
              apply forallb_true_iff.
              apply H2.
            assert (
              (if FreshIn_dec iv' (Var iv') then true else false) = true
            ).
              apply H1.
              apply in_or_app.
              tauto.
            destruct (FreshIn_dec iv' (Var iv')).
            - contradiction n.
            - inversion H3.
          }
        + apply IHtm2.
          apply forallb_true_iff.
          intros iv' H0.
          simpl.
          destruct (FreshIn_dec iv (Var iv')).
          { reflexivity.
          }
          { contradiction n.
            apply FreshIn_Var.
            intro.
            subst.
            inversion H.
            assert (
              forall iv : IVar,
              In iv (getFVs tm1 ++ getFVs tm2) ->
              (if FreshIn_dec iv' (Var iv) then true else false) = true
            ).
              apply forallb_true_iff.
              apply H2.
            assert (
              (if FreshIn_dec iv' (Var iv') then true else false) = true
            ).
              apply H1.
              apply in_or_app.
              tauto.
            destruct (FreshIn_dec iv' (Var iv')).
            - contradiction n.
            - inversion H3.
          }
    - intros.
      constructor.
      * intro.
        inversion H.
        assert (isFreeIn iv0 tm = false \/ iv0 = iv).
        { assert (isFreeIn iv0 tm = false \/ (if Nat.eq_dec iv0 iv then false else true) = false).
            apply andb_false_iff.
            apply H1.
          destruct H0.
          - tauto.
          - destruct (Nat.eq_dec iv0 iv).
            * tauto.
            * inversion H0.
        }
        destruct H0.
        + apply forallb_true_iff.
          intros iv' H2.
          simpl.
          destruct (FreshIn_dec iv0 (Var iv')).
          { reflexivity.
          }
          { contradiction n.
            apply FreshIn_Var.
            intro.
            subst.
            contradiction (proj1 (FreshIn_iff iv' (Abs iv tm))).
            apply getFVs_returns_free_vars.
            apply H2.
          }
        + subst.
          unfold FreshInSubst.
          apply forallb_true_iff.
          intros iv' H0.
          simpl.
          destruct (FreshIn_dec iv (Var iv')).
          { reflexivity.
          }
          { contradiction n.
            apply FreshIn_Var.
            intro.
            subst.
            contradiction (proj1 (FreshIn_iff iv' (Abs iv' tm))).
            apply getFVs_returns_free_vars.
            apply H0.
          }
      * intros.
        unfold FreshIn.
        simpl.
        apply andb_false_iff.
        destruct (Nat.eq_dec iv0 iv).
        { subst.
          tauto.
        }
        { left.
          apply IHtm.
          apply forallb_true_iff.
          intros iv' H0.
          simpl.
          destruct (FreshIn_dec iv0 (Var iv')).
          { reflexivity.
          }
          { contradiction n0.
            apply FreshIn_Var.
            intro.
            subst.
            unfold FreshInSubst in H.
            assert (
              forall iv0 : IVar,
              In iv0 (getFVs (Abs iv tm)) ->
              (if FreshIn_dec iv' (runSubst_Var [] iv0) then true else false) = true
            ).
              apply forallb_true_iff.
              apply H.
            assert ((if FreshIn_dec iv' (runSubst_Var [] iv') then true else false) = true).
            { apply H1.
              apply getFVs_returns_free_vars.
              unfold FreeIn.
              simpl.
              apply andb_true_iff.
              constructor.
              - apply getFVs_returns_free_vars.
                apply H0.
              - destruct (Nat.eq_dec iv' iv).
                * contradiction n.
                * reflexivity.
            }
            simpl in H2.
            destruct (FreshIn_dec iv' (Var iv')).
            - contradiction n0.
            - inversion H2.
          }
        }
  Qed.

  Lemma FreshInSubst_cons :
    forall sub : Subst,
    forall iv : IVar,
    forall tm : Tm,
    FreshInSubst iv sub tm ->
    forall iv0 : IVar,
    forall tm0 : Tm,
    FreshIn iv tm0 ->
    FreshInSubst iv ((iv0, tm0) :: sub) tm.
  Proof.
    intros.
    unfold FreshInSubst.
    simpl.
    apply forallb_true_iff.
    intros.
    destruct (Nat.eq_dec iv0 x).
    * subst.
      destruct (FreshIn_dec iv tm0).
      + reflexivity.
      + contradiction n.
    * unfold FreshInSubst in H.
      assert (
        forall iv' : IVar,
        In iv' (getFVs tm) ->
        (if FreshIn_dec iv (runSubst_Var sub iv') then true else false) = true
      ).
        apply forallb_true_iff.
        apply H.
      apply H2.
      apply H1.
  Qed.

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
    intro.
    assert (~ FreeIn iv tm).
      intro.
      assert (getFreeVarBound tm >= iv).
        apply H.
        apply H1.
      lia.
    apply FreshIn_iff.
    apply H1.
  Qed.

  Definition chi' (sub : Subst) (tm : Tm) : IVar :=
    S (fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub iv0)) (getFVs tm)))
  .

  Lemma equivSubst_property2 :
    forall tm : Tm,
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubst sub1 sub2 ->
    chi' sub1 tm = chi' sub2 tm.
  Proof.
    intros.
    unfold chi'.
    cut (
      forall ns : list N,
      fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub1 iv0)) ns) = fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub2 iv0)) ns)
    ).
      intro.
      rewrite H0.
      reflexivity.
    intros ns.
    induction ns.
    - simpl.
      reflexivity.
    - simpl.
      rewrite H.
      rewrite IHns.
      reflexivity.
  Qed.

  Lemma chi'_property1 :
    forall sub : Subst,
    forall tm : Tm,
    forall iv : IVar,
    FreeIn iv tm ->
    FreshIn (chi' sub tm) (runSubst_Var sub iv).
  Proof.
    intros sub tm.
    assert (
      forall iv : IVar,
      FreeIn iv tm ->
      getFreeVarBound (runSubst_Var sub iv) < chi' sub tm 
    ).
    { intros.
      unfold chi'.
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

  Lemma chi'_gives_FreshInSubst :
    forall sub : Subst,
    forall tm : Tm,
    FreshInSubst (chi' sub tm) sub tm.
  Proof.
    intros sub tm.
    unfold FreshInSubst.
    cut (
      forall iv : IVar,
      In iv (getFVs tm) ->
      FreshIn (chi' sub tm) (runSubst_Var sub iv)
    ).
      intros.
      apply forallb_true_iff.
      intros iv H0.
      assert (In iv (getFVs tm) -> FreshIn (chi' sub tm) (runSubst_Var sub iv)).
        apply H.
      destruct (FreshIn_dec (chi' sub tm) (runSubst_Var sub iv)).
      { reflexivity.
      }
      { contradiction n.
        apply H1.
        apply H0.
      }
    intros.
    apply chi'_property1.
    apply getFVs_returns_free_vars.
    apply H.
  Qed.

  Lemma chi'_bounds_FreshInSubst :
    forall sub : Subst,
    forall tm : Tm,
    forall iv : IVar,
    iv >= chi' sub tm ->
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
        chi' sub tm >= fold_right max 0 (map (fun iv0 : IVar => S (getFreeVarBound (runSubst_Var sub iv0))) (getFVs tm))
      ).
      { unfold chi'.
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

  Lemma chi'_property2 :
    forall sub : Subst,
    forall tm : Tm,
    forall iv0 : IVar,
    iv0 >= chi' sub tm ->
    forall iv : IVar,
    FreeIn iv tm ->
    FreshIn iv0 (runSubst_Var sub iv).
  Proof.
    intros sub tm iv0 H.
    assert (XXX := chi'_bounds_FreshInSubst sub tm iv0 H).
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

  Lemma chi'_empty_fresh :
    forall tm : Tm,
    FreshIn (chi' [] tm) tm.
  Proof.
    cut (
      forall tm0 : Tm,
      forall iv0 : IVar,
      FreeIn iv0 tm0 ->
      chi' [] tm0 > iv0
    ).
      intros.
      unfold FreshIn.
      assert (FreeIn (chi' [] tm) tm -> chi' [] tm > chi' [] tm).
        apply H.
      unfold FreeIn in H0.
      destruct (isFreeIn (chi' [] tm) tm).
      assert (chi' [] tm > chi' [] tm).
        apply H0.
        tauto.
        lia.
      reflexivity.
    intros tm.
    assert (
      forall iv0 : IVar,
      iv0 >= chi' [] tm ->
      forall iv : IVar,
      FreeIn iv tm ->
      FreshIn iv0 (runSubst_Var [] iv)
    ).
      intros.
      apply (chi'_property2 [] tm).
      apply H.
      apply H0.
    intros.
    cut (~ iv0 >= chi' [] tm).
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

  Definition chi (iv : IVar) (sub : Subst) (tm : Tm) : IVar :=
    if FreshInSubst_dec iv sub tm then iv else first_nat (fun iv0 : IVar => forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub iv') then true else false) (getFVs tm)) (chi' sub tm)
  .

  Lemma equivSubst_property3 :
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubst sub1 sub2 ->
    forall tm : Tm,
    forall iv : IVar,
    chi iv sub1 tm = chi iv sub2 tm.
  Proof.
    intros.
    unfold chi.
    assert (FreshInSubst iv sub1 tm <-> FreshInSubst iv sub2 tm).
      apply equivSubst_property1.
      apply H.
    destruct (FreshInSubst_dec iv sub1 tm).
    - destruct (FreshInSubst_dec iv sub2 tm).
      * reflexivity.
      * tauto.
    - destruct (FreshInSubst_dec iv sub2 tm).
      * tauto.
      * rewrite (equivSubst_property2 tm sub1 sub2 H).
        assert (
          forall iv0 : IVar,
          forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub1 iv') then true else false) (getFVs tm) = forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub2 iv') then true else false) (getFVs tm)
        ).
        { cut (
            forall xs : list N,
            forall iv0 : IVar,
            forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub1 iv') then true else false) xs = forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub2 iv') then true else false) xs
          ).
            intros.
            rewrite (H1 (getFVs tm)).
            reflexivity.
          intros xs.
          induction xs.
          - simpl.
            tauto.
          - simpl.
            intros.
            rewrite H.
            rewrite IHxs.
            reflexivity.
        }
        rewrite (first_nat_ext _ _ H1).
        reflexivity.
  Qed.

  Lemma chi_property1 :
    forall tm : Tm,
    forall iv : IVar,
    FreshIn iv tm ->
    chi iv [] tm = iv.
  Proof.
    intros tm.
    induction tm.
    - intros.
      unfold chi.
      destruct (FreshInSubst_dec iv0 [] (Var iv)).
      * reflexivity.
      * contradiction n.
        unfold FreshInSubst.
        apply forallb_true_iff.
        intros iv' H0.
        simpl.
        destruct (FreshIn_dec iv0 (Var iv')).
        + reflexivity.
        + assert (iv' = iv).
            apply FreeIn_Var.
            apply getFVs_returns_free_vars.
            apply H0.
          subst.
          contradiction n0.
    - intros.
      unfold chi.
      destruct (FreshInSubst_dec iv [] (App tm1 tm2)).
      * reflexivity.
      * contradiction n.
        unfold FreshInSubst.
        apply forallb_true_iff.
        intros iv' H0.
        simpl.
        assert (iv <> iv').
          intro.
          subst.
          contradiction (proj1 (FreshIn_iff iv' (App tm1 tm2))).
          apply getFVs_returns_free_vars.
          apply H0.
        destruct (FreshIn_dec iv (Var iv')).
        + reflexivity.
        + contradiction n0.
          apply FreshIn_Var.
          apply H1.
    - intros.
      unfold chi.
      destruct (FreshInSubst_dec iv0 [] (Abs iv tm)).
      * reflexivity.
      * contradiction n.
        unfold FreshInSubst.
        apply forallb_true_iff.
        intros iv' H0.
        simpl.
        destruct (FreshIn_dec iv0 (Var iv')).
        + reflexivity.
        + contradiction n0.
          apply FreshIn_Var.
          intro.
          subst.
          contradiction (proj1 (FreshIn_iff iv' ((Abs iv tm)))).
          apply getFVs_returns_free_vars.
          apply H0.
  Qed.

  Lemma chi_property2 :
    forall tm : Tm,
    forall sub : Subst,
    forall iv : IVar,
    FreshInSubst iv sub tm <-> chi iv sub tm = iv.
  Proof.
    intros.
    unfold chi.
    constructor.
    - intro.
      destruct (FreshInSubst_dec iv sub tm).
      * reflexivity.
      * contradiction n.
    - intro.
      assert (
        let p : N -> Bool := fun iv0 : IVar => forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub iv') then true else false) (getFVs tm) in
        p (first_nat p (chi' sub tm)) = true /\ (forall i : nat, p i = true -> i >= first_nat p (chi' sub tm))
      ).
      { apply well_ordering_principle.
        apply chi'_gives_FreshInSubst.
      }
      destruct H0.
      destruct (FreshInSubst_dec iv sub tm).
      * apply f.
      * rewrite H in H0.
        apply H0.
  Qed.

(*Fixpoint runSubst_Term (sub : Subst) (tm : Tm) : Tm :=
    match tm with
    | Var iv => runSubst_Var sub iv
    | App tm1 tm2 => App (runSubst_Term sub tm1) (runSubst_Term sub tm2)
    | Abs iv tm1 =>
      let iv' : IVar := chi iv sub tm in
      if Nat.eq_dec iv' iv
      then Abs iv' (runSubst_Term sub tm1)
      else Abs iv' (runSubst_Term ((iv', Var iv) :: sub) tm1)
    end
  .

  Lemma equivSubst_property4 :
    forall tm : Tm,
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubst sub1 sub2 ->
    runSubst_Term sub1 tm = runSubst_Term sub2 tm.
  Proof.
    intros tm.
    induction tm.
    - intros.
      simpl.
      rewrite H.
      reflexivity.
    - intros.
      simpl.
      rewrite (IHtm1 sub1 sub2 H).
      rewrite (IHtm2 sub1 sub2 H).
      reflexivity.
    - intros.
      assert (chi iv sub1 (Abs iv tm) = chi iv sub2 (Abs iv tm)).
        apply equivSubst_property3.
        apply H.
      simpl.
      rewrite H0.
      assert (equivSubst ((chi iv sub2 (Abs iv tm), Var iv) :: sub1) ((chi iv sub2 (Abs iv tm), Var iv) :: sub2)).
      { unfold equivSubst.
        intros iv0.
        simpl.
        destruct (Nat.eq_dec (chi iv sub2 (Abs iv tm))).
        - reflexivity.
        - apply H.
      }
      rewrite (IHtm _ _ H1).
      rewrite (IHtm _ _ H).
      reflexivity.
  Qed.

  Lemma runSubst_Term_property1 :
    forall tm : Tm,
    runSubst_Term [] tm = tm.
  Proof.
    intros tm.
    induction tm.
    - unfold runSubst_Term.
      reflexivity.
    - simpl.
      rewrite IHtm1.
      rewrite IHtm2.
      reflexivity.
    - simpl.
      assert (chi iv [] (Abs iv tm) = iv).
        apply chi_property1.
        apply FreshIn_iff.
        unfold FreeIn.
        simpl.
        destruct (Nat.eq_dec iv iv).
        assert (isFreeIn iv tm && false = false).
          apply andb_false_iff.
          tauto.
        rewrite H.
        intro.
        inversion H0.
        contradiction n.
        reflexivity.
      rewrite H.
      destruct (Nat.eq_dec iv iv).
      rewrite IHtm.
      reflexivity.
      contradiction n.
      reflexivity.
  Qed.

  Lemma IsProperSubst_property2 :
    forall tm : Tm,
    forall sub : Subst,
    IsProperSubst sub ->
    (forall iv : IVar, FreeIn iv tm -> ~ In iv (map fst sub)) <-> runSubst_Term sub tm = tm.
  Proof.
    intros tm.
    induction tm.
    - intros.
      simpl.
      constructor.
      * intros.
        apply IsProperSubst_property1.
        apply H.
        apply H0.
        apply FreeIn_Var.
        reflexivity.
      * intros.
        apply IsProperSubst_property1.
        apply H.
        assert (iv0 = iv).
          apply FreeIn_Var.
          apply H1.
        subst.
        apply H0.
    - intros.
      simpl.
      constructor.
      * intros.
        assert (
          runSubst_Term sub tm1 = tm1
        ).
          apply IHtm1.
          apply H.
          { intros.
            apply H0.
            unfold FreeIn in *.
            simpl.
            apply orb_true_iff.
            tauto.
          }
        assert (
          runSubst_Term sub tm2 = tm2
        ).
          apply IHtm2.
          apply H.
          { intros.
            apply H0.
            unfold FreeIn in *.
            simpl.
            apply orb_true_iff.
            tauto.
          }
        rewrite H1.
        rewrite H2.
        reflexivity.
      * intros.
        inversion H0.
        assert (
          (forall iv : IVar, FreeIn iv tm1 -> ~ In iv (map fst sub))
        ).
          apply (proj2 (IHtm1 sub H) H3).
        assert (
          (forall iv : IVar, FreeIn iv tm2 -> ~ In iv (map fst sub))
        ).
          apply (proj2 (IHtm2 sub H) H4).
        inversion H1.
        assert (
          isFreeIn iv tm1 = true \/ isFreeIn iv tm2 = true
        ).
          apply orb_true_iff.
          apply H7.
        destruct H6.
        apply H2.
        apply H6.
        apply H5.
        apply H6.
    - intros sub.
      induction sub.
      * intros.
        constructor.
        + intros.
          apply runSubst_Term_property1.
        + intros.
          tauto.
      * destruct a as [iv0 tm0].
        intros.
        inversion H.
        subst.
        constructor.
        + intros.
          assert (chi iv ((iv0, tm0) :: sub) (Abs iv tm) = iv).
          { apply chi_property2.
            apply forallb_true_iff.
            intros iv1 H6.
            simpl.
            assert (
              FreeIn iv1 (Abs iv tm) -> ~ In iv1 (map fst ((iv0, tm0) :: sub))
            ).
              apply H0.
            simpl in H1.
            destruct (Nat.eq_dec iv0 iv1).
            - subst.
              destruct (FreshIn_dec iv tm0).
              * reflexivity.
              * assert (~ (iv1 = iv1 \/ In iv1 (map fst sub))).
                { apply H1.
                  apply getFVs_returns_free_vars.
                  apply H6.
                }
                contradiction H2.
                tauto.
            - destruct (FreshIn_dec iv (runSubst_Var sub iv1)).
              * reflexivity.
              * assert (iv1 <> iv).
                { assert (FreeIn iv1 (Abs iv tm)).
                    apply getFVs_returns_free_vars.
                    apply H6.
                  inversion H2.
                  assert (isFreeIn iv1 tm = true /\ (if Nat.eq_dec iv1 iv then false else true) = true).
                    apply andb_true_iff.
                    apply H8.
                  destruct H7.
                  destruct (Nat.eq_dec iv1 iv).
                  inversion H9.
                  apply n1.
                }
                assert (runSubst_Var sub iv0 = Var iv0).
                { assert (runSubst_Var sub iv0 = Var iv0 <-> ~ In iv0 (map fst sub)).
                    apply IsProperSubst_property1.
                    apply H5.
                  tauto.
                }
                assert (runSubst_Var sub iv1 = Var iv1 <-> ~ In iv1 (map fst sub)).
                { apply IsProperSubst_property1.
                  apply H5.
                }
                destruct (Tm_eq_dec (runSubst_Var sub iv1) (Var iv1)).
                + rewrite e in n0.
                  assert (iv = iv1).
                  { apply FreeIn_Var.
                    assert (FreshIn iv (Var iv1) <-> ~ FreeIn iv (Var iv1)).
                      apply FreshIn_iff.
                    destruct (FreeIn_dec iv (Var iv1)).
                    - apply f.
                    - tauto.
                  }
                  subst.
                  contradiction H2.
                  reflexivity.
                + assert (In iv1 (map fst sub)).
                  { destruct (In_dec Nat.eq_dec iv1 (map fst sub)).
                    - tauto.
                    - tauto.
                  }
                  contradiction H1.
                  apply getFVs_returns_free_vars.
                  apply H6.
                  tauto.
          }
          simpl.
          destruct (Nat.eq_dec (chi iv ((iv0, tm0) :: sub) (Abs iv tm)) iv).
          { 
            assert (runSubst_Term sub tm = tm).
            { apply IHtm.
              apply H5.
              intros.
              assert (
                FreeIn iv1 (Abs iv tm) ->
                ~ In iv1 (map fst ((iv0, tm0) :: sub))
              ).
                apply H0.
              simpl in H6.
              destruct (Nat.eq_dec iv0 iv1).
              - subst.
                intro.
                contradiction H6.
                * contradiction H4.
                * tauto.
              - assert (FreshInSubst iv ((iv0, tm0) :: sub) (Abs iv tm)).
                { apply chi_property2.
                  apply e.
                }
                unfold FreshInSubst in H7.
                assert (
                  forall iv' : IVar,
                  In iv' (getFVs (Abs iv tm)) ->
                  FreshIn iv (runSubst_Var ((iv0, tm0) :: sub) iv')
                ).
                { assert (
                    forall iv' : IVar,
                    In iv' (getFVs (Abs iv tm)) ->
                    (if FreshIn_dec iv (runSubst_Var ((iv0, tm0) :: sub) iv') then true else false) = true
                  ).
                    apply forallb_true_iff.
                    apply H7.
                  intros.
                  assert ((if FreshIn_dec iv (runSubst_Var ((iv0, tm0) :: sub) iv') then true else false) = true).
                    apply H8.
                    apply H9.
                  destruct (FreshIn_dec iv (runSubst_Var ((iv0, tm0) :: sub) iv')).
                  apply f.
                  inversion H10.
                }
                intro.
                assert (~ FreeIn iv1 (Abs iv tm)).
                { intro.
                  assert (In iv1 (map fst ((iv0, tm0) :: sub))).
                  { destruct (In_dec Nat.eq_dec iv1 (map fst ((iv0, tm0) :: sub))).
                    - tauto.
                    - simpl in n0.
                      contradiction n0.
                      tauto.
                  }
                  contradiction (H0 iv1). 
                }
                assert (iv1 = iv).
                { assert (FreshIn iv1 (Abs iv tm)).
                    apply FreshIn_iff.
                    apply H10.
                  inversion H11.
                  assert (isFreeIn iv1 tm = false \/ (if Nat.eq_dec iv1 iv then false else true) = false).
                    apply andb_false_iff.
                    apply H13.
                  destruct H12.
                  - contradiction (proj1 (FreshIn_iff iv1 tm)).
                  - destruct (Nat.eq_dec iv1 iv).
                    * apply e0.
                    * inversion H12.
                }
                subst.
              assert (runSubst_Term sub (Abs iv tm) = Abs iv tm).
              { apply IHsub.
                apply H5.
                intros.
                inversion H11.
                assert (isFreeIn iv1 tm = true /\ (if Nat.eq_dec iv1 iv then false else true) = true).
                  apply andb_true_iff.
                  apply H13.
                destruct H12.
                destruct (Nat.eq_dec iv1 iv).
                - inversion H14.
                - assert (~ In iv1 (map fst ((iv0, tm0) :: sub))).
                    apply H0.
                  apply H11.
                  simpl in H15.
                  intro.
                  contradiction H15.
                  tauto. 
              }
              simpl in H11.
              destruct (Nat.eq_dec (chi iv sub (Abs iv tm)) iv).
              * rewrite e0 in H11.
                inversion H11.
                assert (
                  forall iv' : IVar,
                  FreeIn iv' tm ->
                  ~ In iv' (map fst sub)
                ).
                { apply IHtm.
                  apply H5.
                  apply H13. 
                }
                contradiction (H12 iv).
              * inversion H11.
                contradiction n0.
            }
            assert (forall iv' : IVar, FreeIn iv' tm -> ~ In iv' (map fst sub)).
              apply (IHtm sub).
              apply H5.
              apply H2.
            assert (FreshIn iv0 (Abs iv tm)).
              apply FreshIn_iff.
              intro.
              contradiction (H0 iv0).
              simpl.
              tauto.
            assert (isFreeIn iv0 tm = false \/ iv0 = iv).
            { assert (isFreeIn iv0 tm = false \/ (if Nat.eq_dec iv0 iv then false else true) = false).
                apply andb_false_iff.
                apply H7.
              destruct H8.
              - tauto.
              - destruct (Nat.eq_dec iv0 iv).
                * tauto.
                * inversion H8.
            }
            destruct H8.
            - rewrite e.
              assert (runSubst_Term ((iv0, tm0) :: sub) tm = tm).
              { apply IHtm.
                apply H.
                intros.
                simpl.
                intro.
                destruct H10.
                - subst.
                  contradiction (proj1 (FreshIn_iff iv1 tm)).
                - contradiction (H6 iv1).
              }
              rewrite H9.
              reflexivity.
            - subst.
              assert (runSubst_Term sub (Abs iv tm) = Abs iv tm).
              { apply IHsub.
                apply H5.
                intros.
                apply H6.
                unfold FreeIn in H8.
                simpl in H8.
                assert (isFreeIn iv0 tm = true /\ (if Nat.eq_dec iv0 iv then false else true) = true).
                  apply andb_true_iff.
                  apply H8.
                destruct H9.
                apply H9.
              }
              simpl in H8.
              destruct (Nat.eq_dec (chi iv sub (Abs iv tm)) iv).
              * rewrite e.
                assert (runSubst_Term ((iv, tm0) :: sub) tm = tm).
                { apply IHtm.
                  apply H.
                  cut (
                    forall iv0 : IVar,
                    In iv0 (map fst ((iv, tm0) :: sub)) ->
                    ~ FreeIn iv0 tm
                  ).
                  { intros.
                    intro.
                    contradiction (H9 iv0).
                  }
                  intros.
                  inversion H9.
                  simpl in H10.
                  subst.
                }
          }
  Qed.

  Lemma runSubst_Term_property3 :
    forall tm : Tm,
    forall iv1 : IVar,
    forall tm1 : Tm,
    forall iv2 : IVar,
    forall tm2 : Tm,
    let sub1 : Subst := [(iv1, tm1)] in
    IsProperSubst sub1 ->
    let sub2 : Subst := [(iv2, tm2)] in
    IsProperSubst sub2 ->
    let sub3 : Subst := if Nat.eq_dec iv1 iv2 then [(iv1, runSubst_Term sub2 tm1)] else [(iv1, runSubst_Term sub2 tm1); (iv2, tm2)] in
    IsProperSubst sub3 ->
    runSubst_Term sub3 tm = runSubst_Term sub2 (runSubst_Term sub1 tm).
  Proof.
    intros tm.
    induction tm.
    - simpl.
      intros.
      destruct (Nat.eq_dec iv1 iv2).
      * subst.
        destruct (Nat.eq_dec iv2 iv).
        + subst.
          simpl.
          destruct (Nat.eq_dec iv iv).
          { reflexivity.
          }
          { contradiction n.
            reflexivity.
          }
        + simpl.
          destruct (Nat.eq_dec iv2 iv).
          { contradiction n.
          }
          { reflexivity.
          }
      * destruct (Nat.eq_dec iv1 iv).
        + subst.
          simpl.
          destruct (Nat.eq_dec iv iv).
          { reflexivity.
          }
          { destruct (Nat.eq_dec iv2 iv).
            - contradiction n.
              rewrite e.
              reflexivity.
            - contradiction n0.
              reflexivity.
          }
        + simpl.
          destruct (Nat.eq_dec iv1 iv).
          { subst.
            contradiction n0.
            reflexivity.
          }
          { reflexivity.
          }
    - intros.
      simpl.
      assert (
        runSubst_Term sub3 tm1 = runSubst_Term sub2 (runSubst_Term sub1 tm1)
      ).
        apply IHtm1.
        apply H.
        apply H0.
        apply H1.
      assert (
        runSubst_Term sub3 tm2 = runSubst_Term sub2 (runSubst_Term sub1 tm2)
      ).
        apply IHtm2.
        apply H.
        apply H0.
        apply H1.
      rewrite H2.
      rewrite H3.
      reflexivity.
    - cut (
        forall tm1 : Tm,
        forall iv1 : IVar,
        forall tm2 : Tm,
        forall iv2 : IVar,
        let sub1 : Subst := [(iv1, tm1)] in
        IsProperSubst sub1 ->
        let sub2 : Subst := [(iv2, tm2)] in
        IsProperSubst sub2 ->
        let sub3 : Subst :=
          if Nat.eq_dec iv1 iv2
          then [(iv1, runSubst_Term sub2 tm1)]
          else [(iv1, runSubst_Term sub2 tm1); (iv2, tm2)]
        in
        IsProperSubst sub3 ->
        runSubst_Term sub3 (Abs iv tm) = runSubst_Term sub2 (runSubst_Term sub1 (Abs iv tm))
      ).
        intuition.
      intros tm1.
      induction tm1.
      * simpl.
        intros.
        destruct (Nat.eq_dec iv1 iv2).
        { subst.
          destruct (Nat.eq_dec iv2 iv0).
          { subst.
            inversion H.
            subst.
            contradiction H5.
            reflexivity.
          }
          { destruct (Nat.eq_dec (chi iv [(iv2, Var iv0)] (Abs iv tm)) iv).
            - rewrite e.
              assert (FreshInSubst iv [(iv2, Var iv0)] (Abs iv tm)).
                apply chi_property2.
                apply e.
              
          }
        }
  Qed.
*)
End STLC.
