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

  Lemma fold_right_max_0_ext :
    forall ns1 : list N,
    forall ns2 : list N,
    (forall n : N, In n ns1 <-> In n ns2) ->
    fold_right max 0 ns1 = fold_right max 0 ns2.
  Proof.
    intros.
    assert (fold_right max 0 ns1 <= fold_right max 0 ns2).
      apply fold_right_max_0_property5.
      apply H.
    assert (fold_right max 0 ns2 <= fold_right max 0 ns1).
      apply fold_right_max_0_property5.
      apply H.
    lia.
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

  Lemma forallb_isn't_true_iff {A : Type} {Phi : A -> Bool} :
    forall xs : list A,
    forallb Phi xs <> true <-> (exists x : A, In x xs /\ Phi x = false).
  Proof.
    intros xs.
    induction xs.
    - simpl.
      constructor.
      * intros.
        contradiction H.
        reflexivity.
      * intros.
        destruct H as [x].
        destruct H.
        contradiction H.
    - simpl.
      assert (Phi a = true \/ Phi a = false).
      { destruct (Phi a).
        - tauto.
        - tauto.
      }
      destruct H.
      * rewrite H.
        simpl.
        constructor.
        + intros.
          destruct (proj1 IHxs H0) as [x].
          exists x.
          tauto.
        + intros.
          apply (proj2 IHxs).
          destruct H0 as [x].
          exists x.
          destruct H0.
          destruct H0.
          { subst.
            rewrite H in H1.
            inversion H1.
          }
          { tauto.
          }
      * rewrite H.
        simpl.
        constructor.
        + intros.
          exists a.
          tauto.
        + intros.
          intro.
          inversion H1.
  Qed.

  Lemma forallb_ext {A : Type} :
    forall fun1 : A -> bool,
    forall fun2 : A -> bool,
    forall xs : list A,
    (forall x : A, In x xs -> fun1 x = fun2 x) ->
    forallb fun1 xs = forallb fun2 xs.
  Proof.
    intros fun1 fun2 xs.
    induction xs.
    - simpl.
      intros.
      reflexivity.
    - simpl.
      intros.
      assert (fun1 a = fun2 a).
        apply H.
        tauto.
      assert (forallb fun1 xs = forallb fun2 xs).
        apply IHxs.
        intros.
        apply H.
        tauto.
      rewrite H0.
      rewrite H1.
      reflexivity.
  Qed.

End Helper.

Module UntypedLC.

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

  Definition equivSubstOn (tm : Tm) (sub1 : Subst) (sub2 : Subst) : Prop :=
    forall iv : IVar, FreeIn iv tm -> runSubst_Var sub1 iv = runSubst_Var sub2 iv
  .

  Lemma equivSubstOn_property1 :
    forall tm : Tm,
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubstOn tm sub1 sub2 ->
    forall iv : IVar,
    FreshInSubst iv sub1 tm <-> FreshInSubst iv sub2 tm.
  Proof.
    unfold equivSubstOn.
    intros tm.
    induction tm.
    - unfold FreshInSubst in *.
      intros.
      simpl.
      assert (runSubst_Var sub1 iv = runSubst_Var sub2 iv).
      { apply H.
        apply FreeIn_Var.
        reflexivity.
      }
      rewrite H0.
      reflexivity.
    - unfold FreshInSubst in *.
      intros.
      simpl.
      assert (
        forall iv0 : IVar,
        In iv0 (getFVs tm1 ++ getFVs tm2) ->
        (if FreshIn_dec iv (runSubst_Var sub1 iv0) then true else false) = (if FreshIn_dec iv (runSubst_Var sub2 iv0) then true else false)
      ).
      { intros.
        cut ((runSubst_Var sub1 iv0) = (runSubst_Var sub2 iv0)).
          intros.
          rewrite H1.
          reflexivity.
        apply H.
        apply  getFVs_returns_free_vars.
        simpl.
        apply H0.
      }
      assert (
        forallb (fun iv0 : IVar => if FreshIn_dec iv (runSubst_Var sub1 iv0) then true else false) (getFVs tm1 ++ getFVs tm2) = forallb (fun iv0 : IVar => if FreshIn_dec iv (runSubst_Var sub2 iv0) then true else false) (getFVs tm1 ++ getFVs tm2)
      ).
      { apply forallb_ext.
        apply H0.
      }
      rewrite H1.
      reflexivity.
    - unfold FreshInSubst in *.
      simpl.
      intros.
      assert (
        forallb (fun iv1 : IVar => if FreshIn_dec iv0 (runSubst_Var sub1 iv1) then true else false) (remove Nat.eq_dec iv (getFVs tm)) = forallb (fun iv1 : IVar => if FreshIn_dec iv0 (runSubst_Var sub2 iv1) then true else false) (remove Nat.eq_dec iv (getFVs tm))
      ).
      { apply forallb_ext.
        intros.
        cut (runSubst_Var sub1 x = runSubst_Var sub2 x).
          intros.
          rewrite H1.
          reflexivity.
        apply H.
        apply getFVs_returns_free_vars.
        apply H0.
      }
      rewrite H0.
      reflexivity.
  Qed.

  Fixpoint weakenSubst (tm : Tm) (sub : Subst) : Subst :=
    match sub with
    | [] => []
    | (iv1, tm1) :: sub' =>
      if FreeIn_dec iv1 tm
      then (iv1, tm1) :: weakenSubst tm sub'
      else weakenSubst tm sub'
    end
  .

  Lemma weakenSubst_property1 :
    forall sub : Subst,
    forall tm : Tm,
    equivSubstOn tm (weakenSubst tm sub) sub.
  Proof.
    unfold equivSubstOn.
    intros sub.
    induction sub.
    - simpl.
      intros.
      reflexivity.
    - destruct a as [iv1 tm1].
      simpl.
      intros.
      destruct (FreeIn_dec iv1 tm).
      * simpl.
        destruct (Nat.eq_dec iv1 iv).
        + reflexivity.
        + apply IHsub.
          apply H.
      * destruct (Nat.eq_dec iv1 iv).
        + subst.
          contradiction n.
        + apply IHsub.
          apply H.
  Qed.

  Lemma FreshInSubst_nil :
    forall iv : IVar,
    forall tm : Tm,
    FreshInSubst iv [] tm <-> FreshIn iv tm.
  Proof.
    cut (
      forall tm : Tm,
      forall iv : IVar,
      FreshIn iv tm <-> FreshInSubst iv [] tm
    ).
    { intros.
      rewrite H.
      reflexivity.
    }
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

  Lemma FreshInSubst_con :
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

  Lemma equivSubstOn_property2 :
    forall tm : Tm,
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubstOn tm sub1 sub2 ->
    chi' sub1 tm = chi' sub2 tm.
  Proof.
    intros.
    unfold chi'.
    cut (
      forall ivs : list IVar,
      (forall iv : IVar, In iv ivs -> FreeIn iv tm) ->
      fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub1 iv0)) ivs) = fold_right max 0 (map (fun iv0 : IVar => getFreeVarBound (runSubst_Var sub2 iv0)) ivs)
    ).
      intro.
      rewrite H0.
      reflexivity.
      intros.
      apply getFVs_returns_free_vars.
      apply H1.
    intros ns.
    induction ns.
    - simpl.
      intros.
      reflexivity.
    - simpl.
      intros.
      rewrite H.
      rewrite IHns.
      reflexivity.
      intros.
      apply H0.
      tauto.
      apply H0.
      tauto.
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

  Lemma equivSubstOn_property3 :
    forall sub1 : Subst,
    forall sub2 : Subst,
    forall tm : Tm,
    equivSubstOn tm sub1 sub2 ->
    forall iv : IVar,
    chi iv sub1 tm = chi iv sub2 tm.
  Proof.
    intros.
    unfold chi.
    assert (FreshInSubst iv sub1 tm <-> FreshInSubst iv sub2 tm).
      apply equivSubstOn_property1.
      apply H.
    destruct (FreshInSubst_dec iv sub1 tm).
    - destruct (FreshInSubst_dec iv sub2 tm).
      * reflexivity.
      * tauto.
    - destruct (FreshInSubst_dec iv sub2 tm).
      * tauto.
      * rewrite (equivSubstOn_property2 tm sub1 sub2 H).
        assert (
          forall iv0 : IVar,
          forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub1 iv') then true else false) (getFVs tm) = forallb (fun iv' : IVar => if FreshIn_dec iv0 (runSubst_Var sub2 iv') then true else false) (getFVs tm)
        ).
        { intros.
          apply forallb_ext.
          intros.
          assert (runSubst_Var sub1 x = runSubst_Var sub2 x).
            apply H.
            apply getFVs_returns_free_vars.
            apply H1.
          rewrite H2.
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

  Fixpoint runSubst_Term (sub : Subst) (tm : Tm) : Tm :=
    match tm with
    | Var iv => runSubst_Var sub iv
    | App tm1 tm2 => App (runSubst_Term sub tm1) (runSubst_Term sub tm2)
    | Abs iv tm1 =>
      let iv' : IVar := chi iv sub tm in
      Abs iv' (runSubst_Term ((iv, Var iv') :: sub) tm1)
    end
  .

  Lemma equivSubstOn_property4 :
    forall tm : Tm,
    forall sub1 : Subst,
    forall sub2 : Subst,
    equivSubstOn tm sub1 sub2 ->
    runSubst_Term sub1 tm = runSubst_Term sub2 tm.
  Proof.
    intros tm.
    induction tm.
    - intros.
      simpl.
      rewrite H.
      reflexivity.
      apply FreeIn_Var.
      reflexivity.
    - intros.
      simpl.
      assert (runSubst_Term sub1 tm1 = runSubst_Term sub2 tm1).
        apply IHtm1.
        unfold equivSubstOn.
        intros.
        apply H.
        unfold FreeIn.
        simpl.
        apply orb_true_iff.
        left.
        apply H0.
      assert (runSubst_Term sub1 tm2 = runSubst_Term sub2 tm2).
        apply IHtm2.
        unfold equivSubstOn.
        intros.
        apply H.
        unfold FreeIn.
        simpl.
        apply orb_true_iff.
        right.
        apply H1.
      rewrite H0.
      rewrite H1.
      reflexivity.
    - intros.
      assert (chi iv sub1 (Abs iv tm) = chi iv sub2 (Abs iv tm)).
        apply equivSubstOn_property3.
        apply H.
      simpl.
      rewrite H0.
      assert (equivSubstOn tm ((iv, Var (chi iv sub2 (Abs iv tm))) :: sub1) ((iv, Var (chi iv sub2 (Abs iv tm))) :: sub2)).
      { unfold equivSubstOn.
        intros.
        simpl.
        destruct (Nat.eq_dec iv iv0).
        - reflexivity.
        - apply H.
          unfold FreeIn.
          simpl.
          apply andb_true_iff.
          constructor.
          apply H1.
          destruct (Nat.eq_dec iv0 iv).
          contradiction n.
          rewrite e.
          reflexivity.
          reflexivity.
      }
      assert ((runSubst_Term ((iv, Var (chi iv sub2 (Abs iv tm))) :: sub1) tm) = (runSubst_Term ((iv, Var (chi iv sub2 (Abs iv tm))) :: sub2) tm)).
      { apply IHtm.
        apply H1.
      }
      rewrite H2.
      reflexivity.
  Qed.

  Lemma runSubst_Term_property1 :
    forall tm : Tm,
    forall sub : Subst,
    (forall iv0 : IVar, forall tm0 : Tm, In (iv0, tm0) sub -> tm0 = Var iv0) ->
    runSubst_Term sub tm = tm.
  Proof.
    intros tm.
    induction tm.
    - intros sub.
      induction sub.
      * simpl.
        intros.
        reflexivity.
      * destruct a as [iv0 tm0].
        simpl.
        intros.
        destruct (Nat.eq_dec iv0 iv).
        { subst.
          apply H.
          tauto.
        }
        { apply IHsub.
          intros.
          apply H.
          tauto.
        }
    - simpl.
      intros.
      assert (runSubst_Term sub tm1 = tm1).
      { apply IHtm1.
        apply H.
      }
      assert (runSubst_Term sub tm2 = tm2).
      { apply IHtm2.
        apply H.
      }
      rewrite H0.
      rewrite H1.
      reflexivity.
    - simpl.
      intros H.
      cut (
        forall sub : Subst,
        (forall (iv0 : IVar) (tm0 : Tm), In (iv0, tm0) sub -> tm0 = Var iv0) ->
        Abs (chi iv sub (Abs iv tm)) (runSubst_Term ((iv, Var (chi iv sub (Abs iv tm))) :: sub) tm) = Abs iv tm /\ iv = chi iv sub (Abs iv tm)
      ).
        intros.
        apply H0.
        apply H1.
      induction sub.
      * simpl.
        intros.
        assert (chi iv [] (Abs iv tm) = iv).
        { apply chi_property1.
          unfold FreshIn.
          simpl.
          apply andb_false_iff.
          right.
          destruct (Nat.eq_dec iv iv).
          reflexivity.
          contradiction n.
          reflexivity.
        }
        rewrite H1.
        assert (runSubst_Term [(iv, Var iv)] tm = tm).
        { apply IHtm.
          intros.
          inversion H2.
          inversion H3.
          reflexivity.
          inversion H3.
        }
        constructor.
        rewrite H2.
        reflexivity.
        reflexivity.
      * destruct a as [iv1 tm1].
        simpl.
        intros.
        assert (tm1 = Var iv1).
          apply H0.
          tauto.
        subst.
        assert (chi iv ((iv1, Var iv1) :: sub) (Abs iv tm) = iv).
        { apply chi_property2.
          assert (iv = chi iv sub (Abs iv tm)).
            apply IHsub.
            intros.
            apply H0.
            tauto.
          assert (FreshInSubst iv sub (Abs iv tm)).
            apply chi_property2.
            rewrite <- H1.
            reflexivity.
          apply forallb_true_iff.
          intros.
          simpl.
          destruct (Nat.eq_dec iv1 x).
          - destruct (FreshIn_dec iv (Var iv1)).
            * reflexivity.
            * subst.
              assert (iv = x).
                apply FreeIn_Var.
                unfold FreeIn.
                unfold FreshIn in n.
                destruct (isFreeIn iv (Var x)).
                reflexivity.
                contradiction n.
                reflexivity.
              subst.
              assert (FreeIn x (Abs x tm)).
                apply getFVs_returns_free_vars.
                apply H3.
              unfold FreeIn in H4.
              simpl in H4.
              assert (isFreeIn x tm = true /\ (if Nat.eq_dec x x then false else true) = true).
                apply andb_true_iff.
                apply H4.
              destruct H5.
              destruct (Nat.eq_dec x x).
              apply H6.
              contradiction n0.
              reflexivity.
          - assert (forall x : IVar, In x (getFVs (Abs iv tm)) -> (if FreshIn_dec iv (runSubst_Var sub x) then true else false) = true).
              apply forallb_true_iff.
              apply H2.
            apply H4.
            apply H3.
        }
        rewrite H1.
        assert (runSubst_Term ((iv, Var iv) :: (iv1, Var iv1) :: sub) tm = tm).
        { apply IHtm.
          simpl.
          intros.
          destruct H2.
          inversion H2.
          subst.
          tauto.
          apply H0.
          apply H2.
        }
        rewrite H2.
        tauto.
  Qed.

  Lemma weakenSubst_property2 :
    forall tm : Tm,
    forall sub : Subst,
    runSubst_Term (weakenSubst tm sub) tm = runSubst_Term sub tm.
  Proof.
    intros.
    apply equivSubstOn_property4.
    apply weakenSubst_property1.
  Qed.

  Lemma equivSubstOn_property5 :
    forall sub : Subst,
    forall M : Tm,
    forall x : IVar,
    forall N : Tm,
    (forall iv : IVar, In iv (map fst sub) -> iv = x) ->
    equivSubstOn M ((x, N) :: sub) [(x, N)].
  Proof.
    unfold equivSubstOn.
    intros sub.
    induction sub.
    - intros.
      reflexivity.
    - intros.
      destruct a as [iv1 tm1].
      assert (iv1 = x).
        apply H.
        simpl.
        tauto.
      subst.
      simpl.
      destruct (Nat.eq_dec x iv).
      { reflexivity.
      }
      { assert (runSubst_Var ((x, N0) :: sub) iv = runSubst_Var [(x, N0)] iv).
          apply (IHsub M).
          intros.
          apply H.
          simpl.
          tauto.
        simpl in H0.
        destruct (Nat.eq_dec x iv).
        contradiction n.
        apply H0.
        simpl in H1.
        destruct (Nat.eq_dec x iv).
        contradiction n.
        apply H1.
      }
  Qed.

  Inductive AlphaSubst : Subst -> Tm -> Tm -> Prop :=
  | AlphaSubstVar :
    forall sub : Subst,
    forall iv : IVar,
    forall tm : Tm,
    runSubst_Var sub iv = tm ->
    AlphaSubst sub (Var iv) tm
  | AlphaSubstApp :
    forall sub : Subst,
    forall tm1_1 : Tm,
    forall tm1_2 : Tm,
    forall tm2_1 : Tm,
    forall tm2_2 : Tm,
    AlphaSubst sub tm1_1 tm2_1 ->
    AlphaSubst sub tm1_2 tm2_2 ->
    AlphaSubst sub (App tm1_1 tm1_2) (App tm2_1 tm2_2)
  | AlphaSubstAbs :
    forall sub : Subst,
    forall iv1 : IVar,
    forall iv2 : IVar,
    forall tm1 : Tm,
    forall tm2 : Tm,
    AlphaSubst ((iv1, Var iv2) :: sub) tm1 tm2 ->
    AlphaSubst sub (Abs iv1 tm1) (Abs iv2 tm2)
  .

  Lemma AlphaSubst_property1 :
    forall sub : Subst,
    forall tm1 : Tm,
    forall tm2 : Tm,
    runSubst_Term sub tm1 = tm2 -> AlphaSubst sub tm1 tm2.
  Proof.
    cut (
      forall tm1 : Tm,
      forall sub : Subst,
      forall tm2 : Tm,
      runSubst_Term sub tm1 = tm2 -> AlphaSubst sub tm1 tm2
    ).
      intros.
      apply H.
      apply H0.
    intros tm1.
    induction tm1.
    - intros.
      simpl.
      intros.
      rewrite <- H.
      constructor.
      reflexivity.
    - intros.
      simpl.
      intros.
      rewrite <- H.
      constructor.
      apply IHtm1_1.
      reflexivity.
      apply IHtm1_2.
      reflexivity.
    - intros.
      simpl.
      intros.
      rewrite <- H.
      constructor.
      apply IHtm1.
      reflexivity.
  Qed.

  Definition AlphaEquiv (tm1 : Tm) (tm2 : Tm) : Prop :=
    AlphaSubst [] tm1 tm2
  .

  Lemma AlphaEquiv_refl :
    forall tm1 : Tm,
    AlphaEquiv tm1 tm1.
  Proof.
    unfold AlphaEquiv.
    intros.
    assert (
      runSubst_Term [] tm1 = tm1
    ).
      apply runSubst_Term_property1.
      intros.
      inversion H.
    apply AlphaSubst_property1.
    apply H.
  Qed.

End UntypedLC.
