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

  Fixpoint isFreeIn (iv0 : IVar) (tm : Tm) : Bool :=
    match tm with
    | Var iv => if Nat.eq_dec iv0 iv then true else false
    | App tm1 tm2 => orb (isFreeIn iv0 tm1) (isFreeIn iv0 tm2)
    | Abs iv tm1 => andb (isFreeIn iv0 tm1) (negb (Nat.eqb iv0 iv))
    end
  .

  Definition FreeIn (iv0 : IVar) (tm : Tm) : Prop :=
    isFreeIn iv0 tm = true
  .

  Definition FreshIn (iv0 : IVar) (tm : Tm) : Prop :=
    isFreeIn iv0 tm = false
  .

  Definition Subst : Type :=
    list (IVar * Tm)
  .

  Fixpoint substVar (sigma : Subst) (iv0 : IVar) : Tm :=
    match sigma with
    | [] => Var iv0
    | (iv, tm) :: sigma' =>
      if Nat.eq_dec iv0 iv
      then tm
      else substVar sigma' iv0
    end
  .

  Lemma getFreshVariableBound :
    forall sigma : Subst,
    forall tm : Tm,
    { bound : N
    | forall iv0 : IVar,
      iv0 > bound ->
      forall iv : IVar,
      FreeIn iv tm ->
      FreshIn iv0 (substVar sigma iv)
    }.
  Proof.
    assert ( claim1 :
      forall tm : Tm,
      { iv0 : IVar
      | forall iv : IVar,
        isFreeIn iv tm = true ->
        iv0 >= iv
      }
    ).
      intros tm; induction tm.
      (* 1st *)
        exists iv.
        simpl.
        intros.
        destruct (Nat.eq_dec iv0 iv).
        (* e : iv0 = iv *)
        lia.
        (* n : iv0 <> iv *)
        inversion H.
      (* 2nd *)
        destruct IHtm1 as [iv1 H1].
        destruct IHtm2 as [iv2 H2].
        exists (max iv1 iv2).
        simpl.
        intros.
        assert (isFreeIn iv tm1 = true \/ isFreeIn iv tm2 = true).
          apply orb_true_iff.
          apply H.
        destruct H0.
        (* isFreeIn iv tm1 = true *)
        assert (iv1 >= iv).
          apply H1.
          apply H0.
        lia.
        (* isFreeIn iv tm2 = true *)
        assert (iv2 >= iv).
          apply H2.
          apply H0.
        lia.
      (* 3rd *)
      destruct IHtm as [iv1 H1].
      exists iv1.
      intros.
      inversion H.
      assert (isFreeIn iv0 tm = true).
        apply (andb_true_iff _ (negb (iv0 =? iv))).
        apply H2.
      apply H1.
      apply H0.
    assert ( claim2 :
      forall tm : Tm,
      forall iv : IVar,
      (forall iv0 : IVar, isFreeIn iv0 tm = true -> iv0 < iv) ->
      FreshIn iv tm
    ).
      intros.
      unfold FreshIn.
      assert (isFreeIn iv tm = true -> iv < iv).
        apply H.
      destruct (isFreeIn iv tm).
      assert (iv < iv).
        apply H0.
        reflexivity.
      lia.
      reflexivity.
    intros sigma; induction sigma.
    - intros tm.
      destruct (claim1 tm) as [iv0].
      exists iv0.
      intros.
      apply claim2.
      simpl.
      intros.
      destruct (Nat.eq_dec iv2 iv).
      subst.
      assert (iv0 >= iv).
        apply g.
        apply H0.
      lia.
      inversion H1.
    - destruct a as [iv1 tm1].
      destruct (claim1 tm1) as [iv0].
      intros.
      destruct (IHsigma tm) as [iv].
      exists (max iv iv0).
      simpl.
      intros.
      destruct (Nat.eq_dec iv3 iv1).
      subst.
      apply claim2.
      intros.
      assert (iv0 >= iv3).
        apply g.
        apply H1.
      lia.
      apply f.
      lia.
      apply H0.
  Qed.

  Definition funcCHI (sigma : Subst) (tm : Tm) : IVar :=
    S (proj1_sig (getFreshVariableBound sigma tm))
  .

  Lemma funcCHI_gives_fresh_var :
    forall sigma : Subst,
    forall tm : Tm,
    forall iv : IVar,
    FreeIn iv tm ->
    FreshIn (funcCHI sigma tm) (substVar sigma iv).
  Proof.
    intros.
    unfold funcCHI.
    destruct (getFreshVariableBound sigma tm) as [bound H0].
    apply H0.
    simpl.
    lia.
    apply H.
  Qed.

  Fixpoint substTerm (sigma : Subst) (tm : Tm) : Tm :=
    match tm with
    | Var iv => substVar sigma iv
    | App tm1 tm2 => App (substTerm sigma tm1) (substTerm sigma tm2)
    | Abs iv tm1 =>
      let iv' : IVar := funcCHI sigma tm in
      Abs iv' (substTerm ((iv, Var iv') :: sigma) tm1)
    end
  .

  Lemma lemma_1_of_2_6 :
    forall tm : Tm,
    forall sigma : Subst,
    forall iv0 : IVar,
    FreeIn iv0 tm ->
    FreshIn (funcCHI sigma tm) (substVar sigma iv0).
  Proof.
    cut (
      forall tm : Tm,
      forall sigma : Subst,
      forall iv0 : IVar,
      FreeIn iv0 tm ->
      FreshIn (S (proj1_sig (getFreshVariableBound sigma tm))) (substVar sigma iv0)
    ).
      intros.
      apply H.
      apply H0.
    intros.
    inversion H.
    assert (
      forall iv0 : IVar,
      iv0 > proj1_sig (getFreshVariableBound sigma tm) ->
      forall iv1 : IVar,
      FreeIn iv1 tm ->
      FreshIn iv0 (substVar sigma iv1)
    ).
      apply (proj2_sig (getFreshVariableBound sigma tm)).
    apply H0.
    lia.
    apply H1.
  Qed.

  Lemma lemma_2_of_2_6 :
    forall tm : Tm,
    FreshIn (funcCHI [] tm) tm.
  Proof.
    cut (
      forall tm0 : Tm,
      forall iv0 : IVar,
      FreeIn iv0 tm0 ->
      iv0 < funcCHI [] tm0
    ).
      intros.
      unfold FreshIn.
      assert (FreeIn (funcCHI [] tm) tm -> funcCHI [] tm < funcCHI [] tm).
        apply H.
      unfold FreeIn in H0.
      destruct (isFreeIn (funcCHI [] tm) tm).
      assert (funcCHI [] tm < funcCHI [] tm). 
        tauto.
      lia.
      reflexivity.
    intros tm.
    unfold funcCHI.
    assert (
      forall iv0 : IVar,
      iv0 > proj1_sig (getFreshVariableBound [] tm) ->
      forall iv : IVar,
      FreeIn iv tm ->
      FreshIn iv0 (substVar [] iv)
    ).
      apply (proj2_sig (getFreshVariableBound [] tm)).
    intros.
    cut (~ iv0 >= S (proj1_sig (getFreshVariableBound [] tm))).
      lia.
    intro.
    assert (FreshIn iv0 (substVar [] iv0)).
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

End STLC.
