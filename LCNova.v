From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.

Module AuxiliaPalatina.  

  Import ListNotations.

  Section forNat.

  Theorem SecondPrincipleOfFiniteInduction (phi : nat -> Prop) :
    let phi' : nat -> Prop := fun k : nat => (forall i : nat, i < k -> phi i) in
    (forall k : nat, phi' k -> phi k) ->
    (forall n : nat, phi n).
  Proof.
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
    | S n' =>
      if p (first_nat p n')
      then first_nat p n'
      else n
    end
  .

  Lemma well_ordering_principle : 
    forall p : nat -> bool,
    forall n : nat,
    p n = true ->
    let m : nat := first_nat p n in
    p m = true /\ (forall i : nat, p i = true -> i >= m).
  Proof.
    intros p.
    assert (forall x : nat, p x = true -> p (first_nat p x) = true).
      intros x.
      induction x.
      tauto.
      simpl.
      cut (let b : bool := p (first_nat p x) in p (S x) = true -> p (if b then first_nat p x else S x) = true).
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
        cut (let b : bool := p (first_nat p x) in (if b then first_nat p x else S x) <= S x).
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
    unfold m.
    apply H5.
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
    exists (first_nat (fun i : nat => if H_Phi_dec i then true else false) n).
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

  End forNat.

End AuxiliaPalatina.

Module UntypedLambdaCalculus.

  Import ListNotations.

  Import AuxiliaPalatina.

  Section Syntax.

  Definition IVar : Set :=
    nat
  .

  Lemma IVar_eq_dec :
    forall x : IVar,
    forall y : IVar,
    {x = y} + {x <> y}.
  Proof.
    apply Nat.eq_dec.
  Qed.

  Inductive Term : Set :=
  | Var :
    forall x : IVar,
    Term
  | App :
    forall P1 : Term,
    forall P2 : Term,
    Term
  | Lam :
    forall y : IVar,
    forall Q : Term,
    Term
  .

  Lemma Term_eq_dec :
    forall M : Term,
    forall N : Term,
    {M = N} + {M <> N}.
  Proof.
    intros M.
    induction M.
    - intros N.
      destruct N.
      * destruct (IVar_eq_dec x x0).
        { left.
          subst.
          reflexivity.
        }
        { right.
          intro.
          inversion H.
          contradiction n.
        }
      * right.
        intro.
        inversion H.
      * right.
        intro.
        inversion H.
    - intros N.
      destruct N.
      * right.
        intro.
        inversion H.
      * destruct (IHM1 N1).
        { destruct (IHM2 N2).
          { left.
            subst.
            reflexivity.
          }
          { right.
            intro.
            inversion H.
            contradiction n.
          }
        }
        { right.
          intro.
          inversion H.
          contradiction n.
        }
      * right.
        intro.
        inversion H.
    - intros N.
      destruct N.
      * right.
        intro.
        inversion H.
      * right.
        intro.
        inversion H.
      * destruct (IHM N).
        { destruct (IVar_eq_dec y y0).
          { left.
            subst.
            reflexivity.
          }
          { right.
            intro.
            inversion H.
            contradiction n.
          }
        }
        { right.
          intro.
          inversion H.
          contradiction n.
        }
  Qed.

  Inductive IsSubtermOf : Term -> Term -> Set :=
  | IsSubtermOfRefl :
    forall M : Term,
    IsSubtermOf M M
  | IsSubtermOfApp1 :
    forall M : Term,
    forall P1 : Term,
    forall P2 : Term,
    IsSubtermOf M P1 ->
    IsSubtermOf M (App P1 P2)
  | IsSubtermOfApp2 :
    forall M : Term,
    forall P1 : Term,
    forall P2 : Term,
    IsSubtermOf M P2 ->
    IsSubtermOf M (App P1 P2)
  | IsSubtermOfLam0 :
    forall M : Term,
    forall y : IVar,
    forall Q : Term,
    IsSubtermOf M Q ->
    IsSubtermOf M (Lam y Q)
  .

  Fixpoint getRankOfTerm (M : Term) : nat :=
    match M with
    | Var x => 0
    | App P1 P2 => S (max (getRankOfTerm P1) (getRankOfTerm P2))
    | Lam y Q => S (getRankOfTerm Q)
    end
  .

  Lemma getRankOfTerm_property1 :
    forall M : Term,
    forall N : Term,
    IsSubtermOf M N ->
    getRankOfTerm M <= getRankOfTerm N.
  Proof.
    intros.
    induction H.
    - lia.
    - simpl.
      lia.
    - simpl.
      lia.
    - simpl.
      lia.
  Qed.

  Lemma getRankOfTerm_property2 :
    forall M : Term,
    forall N : Term,
    IsSubtermOf M N ->
    getRankOfTerm M = getRankOfTerm N ->
    M = N.
  Proof.
    intros M N X.
    destruct X.
    - tauto.
    - assert (getRankOfTerm M <= getRankOfTerm P1).
        apply getRankOfTerm_property1.
        apply X.
      simpl.
      lia.
    - assert (getRankOfTerm M <= getRankOfTerm P2).
        apply getRankOfTerm_property1.
        apply X.
      simpl.
      lia.
    - assert (getRankOfTerm M <= getRankOfTerm Q).
        apply getRankOfTerm_property1.
        apply X.
      simpl.
      lia.
  Qed.

  Lemma IsSubtermOf_refl :
    forall M : Term,
    IsSubtermOf M M.
  Proof.
    apply IsSubtermOfRefl.
  Qed.

  Lemma IsSubtermOf_asym :
    forall M : Term,
    forall N : Term,
    IsSubtermOf M N ->
    IsSubtermOf N M ->
    M = N.
  Proof.
    intros.
    apply getRankOfTerm_property2.
    apply H.
    assert (getRankOfTerm M <= getRankOfTerm N).
      apply getRankOfTerm_property1.
      tauto.
    assert (getRankOfTerm N <= getRankOfTerm M).
      apply getRankOfTerm_property1.
      tauto.
    lia.
  Qed.

  Lemma IsSubtermOf_trans :
    forall M : Term,
    forall N : Term,
    forall L : Term,
    IsSubtermOf M N ->
    IsSubtermOf N L ->
    IsSubtermOf M L.
  Proof.
    cut (
      forall L : Term,
      forall N : Term,
      forall M : Term,
      IsSubtermOf M N ->
      IsSubtermOf N L ->
      IsSubtermOf M L
    ).
      intros.
      apply (H L N M).
      apply H0.
      apply H1.
    intros L.
    induction L.
    - intros N.
      induction N.
      * intros.
        inversion H0.
        { subst.
          apply H.
        }
      * intros.
        inversion H0.
      * intros.
        inversion H0.
    - intros N.
      induction N.
      * intros.
        inversion H0.
        { subst.
          apply IsSubtermOfApp1.
          apply (IHL1 (Var x)).
          apply H.
          apply H3.
        }
        { subst.
          apply IsSubtermOfApp2.
          apply (IHL2 (Var x)).
          apply H.
          apply H3.
        }
      * intros.
        inversion H.
        { subst.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            apply H.
          }
          { subst.
            apply IsSubtermOfApp1.
            apply (IHL1 (App N1 N2)).
            apply H.
            apply H4.
          }
          { subst.
            apply IsSubtermOfApp2.
            apply (IHL2 (App N1 N2)).
            apply H.
            apply H4.
          }
        }
        { subst.
          inversion H0.
          { subst.
            apply H.
          }
          { subst.
            apply IsSubtermOfApp1.
            apply (IHL1 (App N1 N2)).
            apply H.
            apply H4.
          }
          { subst.
            apply IsSubtermOfApp2.
            apply (IHL2 (App N1 N2)).
            apply H.
            apply H4.
          }
        }
      * intros.
        inversion H.
        { subst.
          inversion H0.
          { subst.
            apply H0.
          }
          { subst.
            apply H0.
          }
        }
        { subst.
          inversion H0.
          { subst.
            apply IsSubtermOfApp1.
            apply (IHL1 (Lam y N)).
            apply H.
            apply H4.
          }
          { subst.
            apply IsSubtermOfApp2.
            apply (IHL2 (Lam y N)).
            apply H.
            apply H4.
          }
        }
    - intros N.
      induction N.
      * intros.
        inversion H.
        { subst.
          apply H0.
        }
      * intros.
        inversion H.
        { subst.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            apply IsSubtermOfLam0.
            apply (IHL (App N1 N2)).
            apply H.
            apply H4.
          } 
        }
        { subst.
          inversion H0.
          { subst.
            apply IsSubtermOfLam0.
            apply (IHL (App N1 N2)).
            apply H.
            apply H4.
          }
        }
      * intros.
        inversion H.
        { subst.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            apply H.
          }
          { subst.
            apply IsSubtermOfLam0.
            apply (IHL (Lam y0 N)).
            apply H.
            apply H4.
          }
        }
  Qed.

  Theorem StrongInductionOnTm (Phi : Term -> Prop) :
    (forall M : Term, (forall N : Term, IsSubtermOf N M -> N <> M -> Phi N) -> Phi M) ->
    forall M : Term,
    Phi M.
  Proof.
    cut (
      (forall M : Term, (forall N : Term, IsSubtermOf N M -> N <> M -> Phi N) -> Phi M) ->
      forall M : Term,
      forall N : Term,
      IsSubtermOf N M ->
      Phi N
    ).
    { intros.
      apply (H H0 M M).
      apply IsSubtermOf_refl.
    }
    intros XXX.
    intros M.
    induction M.
    - intros.
      apply XXX.
      intros.
      inversion H0.
      * subst.
        contradiction H1.
        reflexivity.
      * subst.
        inversion H.
      * subst.
        inversion H.
      * subst.
        inversion H.
    - intros.
      apply XXX.
      intros.
      inversion H0.
      * subst.
        inversion H.
        + subst.
          contradiction H1.
          reflexivity.
        + subst.
          apply IHM1.
          apply H4.
        + subst.
          apply IHM2.
          apply H4.
      * subst.
        inversion H.
        + subst.
          apply IHM1.
          apply H2.
        + subst.
          apply IHM1.
          apply (IsSubtermOf_trans N0 (App P1 P2)).
          apply IsSubtermOfApp1.
          apply H2.
          apply H5.
        + subst.
          apply IHM2.
          apply (IsSubtermOf_trans N0 (App P1 P2)).
          apply IsSubtermOfApp1.
          apply H2.
          apply H5.
      * subst.
        inversion H.
        + subst.
          apply IHM2.
          apply H2.
        + subst.
          apply IHM1.
          apply (IsSubtermOf_trans N0 (App P1 P2)).
          apply IsSubtermOfApp2.
          apply H2.
          apply H5.
        + subst.
          apply IHM2.
          apply (IsSubtermOf_trans N0 (App P1 P2)).
          apply IsSubtermOfApp2.
          apply H2.
          apply H5.
      * subst.
        inversion H.
        + subst.
          apply IHM1.
          apply (IsSubtermOf_trans N0 (Lam y Q)).
          apply H0.
          apply H5.
        + subst.
          apply IHM2.
          apply (IsSubtermOf_trans N0 (Lam y Q)).
          apply H0.
          apply H5.
    - intros.
      apply XXX.
      intros.
      inversion H0.
      * subst.
        contradiction H1.
        reflexivity.
      * subst.
        inversion H.
        + subst.
          apply IHM.
          apply (IsSubtermOf_trans N0 (App P1 P2)).
          apply H0.
          apply H5.
      * subst.
        inversion H.
        + subst.
          apply IHM.
          apply (IsSubtermOf_trans N0 (App P1 P2)).
          apply H0.
          apply H5.
      * subst.
        inversion H.
        + subst.
          apply IHM.
          apply H2.
        + subst.
          apply IHM.
          apply (IsSubtermOf_trans N0 (Lam y0 Q)).
          apply H0.
          apply H5.
  Qed.

  Fixpoint isFreeIn (z : IVar) (M : Term) : bool :=
    match M with
    | Var x => if IVar_eq_dec x z then true else false
    | App P1 P2 => isFreeIn z P1 || isFreeIn z P2
    | Lam y Q => (if IVar_eq_dec y z then false else true) && isFreeIn z Q
    end
  .

  Lemma isFreeIn_Var :
    forall z : IVar,
    forall x : IVar,
    isFreeIn z (Var x) = true <-> x = z.
  Proof.
    intros.
    simpl.
    destruct (IVar_eq_dec x z).
    - tauto.
    - constructor.
      * intros.
        inversion H.
      * intros.
        contradiction n.
  Qed.

  Lemma isFreeIn_App :
    forall z : IVar,
    forall P1 : Term,
    forall P2 : Term,
    isFreeIn z (App P1 P2) = true <-> isFreeIn z P1 = true \/ isFreeIn z P2 = true.
  Proof.
    intros.
    simpl.
    rewrite orb_true_iff.
    reflexivity.
  Qed.

  Lemma isFreeIn_Lam :
    forall z : IVar,
    forall y : IVar,
    forall Q : Term,
    isFreeIn z (Lam y Q) = true <-> y <> z /\ isFreeIn z Q = true.
  Proof.
    intros.
    simpl.
    rewrite andb_true_iff.
    destruct (IVar_eq_dec y z).
    - constructor.
      * intros.
        destruct H.
        inversion H.
      * intros.
        destruct H.
        contradiction H.
    - tauto.
  Qed.

  Lemma isFreeIn_property1 :
    forall M : Term,
    forall z : IVar,
    isFreeIn z M = true ->
    IsSubtermOf (Var z) M.
  Proof.
    intros M.
    induction M.
    - simpl.
      intros.
      destruct (IVar_eq_dec x z).
      * subst.
        apply IsSubtermOfRefl.
      * inversion H.
    - simpl.
      intros.
      assert (isFreeIn z M1 = true -> IsSubtermOf (Var z) M1).
        apply IHM1.
      assert (isFreeIn z M2 = true -> IsSubtermOf (Var z) M2).
        apply IHM2.
      destruct (isFreeIn z M1).
      * apply IsSubtermOfApp1.
        apply H0.
        reflexivity.
      * destruct (isFreeIn z M2).
        + apply IsSubtermOfApp2.
          apply H1.
          reflexivity.
        + simpl in H.
          inversion H.
    - simpl.
      intros.
      assert (isFreeIn z M = true -> IsSubtermOf (Var z) M).
        apply IHM.
      destruct (isFreeIn z M).
      * apply IsSubtermOfLam0.
        apply H0.
        reflexivity.
      * destruct (IVar_eq_dec y z).
        + simpl in H.
          inversion H.
        + simpl in H.
          inversion H.
  Qed.

  Fixpoint legio (Phi : IVar -> list IVar -> Prop) (Gamma : list IVar) (N : Term) : Prop :=
    match N with
    | Var x => Phi x Gamma
    | App P1 P2 => legio Phi Gamma P1 /\ legio Phi Gamma P2
    | Lam y Q => legio Phi (y :: Gamma) Q
    end
  .

  Lemma isFreeIn_property2 :
    let Phi : IVar -> list IVar -> Prop := fun x : IVar => fun Gamma : list IVar => In x Gamma in
    forall M : Term,
    forall Gamma : list IVar,
    legio Phi Gamma M <-> (forall x : IVar, isFreeIn x M = true -> Phi x Gamma).
  Proof.
    intros Phi M.
    induction M.
    - simpl.
      intros.
      unfold Phi.
      constructor.
      * intros.
        destruct (IVar_eq_dec x x0).
        + subst.
          tauto.
        + intros.
          inversion H0.
      * intros.
        apply H.
        destruct (IVar_eq_dec x x).
        + reflexivity.
        + contradiction n.
          reflexivity.
    - simpl.
      intros.
      unfold Phi.
      constructor.
      * intros.
        rewrite orb_true_iff in H0.
        destruct H0.
        + apply IHM1. 
          apply H.
          apply H0.
        + apply IHM2.
          apply H.
          apply H0.
      * intros. 
        constructor.
        + apply IHM1.
          intros.
          apply H.
          apply orb_true_iff.
          tauto.
        + apply IHM2.
          intros.
          apply H.
          apply orb_true_iff.
          tauto.
    - simpl.
      intros.
      unfold Phi.
      constructor.
      * intros.
        rewrite andb_true_iff in H0.
        destruct H0.
        destruct (IVar_eq_dec y x).
        + inversion H0.
        + cut (In x (y :: Gamma)).
            simpl.
            tauto.
          apply IHM.
          apply H.
          apply H1.
      * intros.
        apply IHM.
        intros.
        simpl.
        assert ((if IVar_eq_dec y x then false else true) && isFreeIn x M = true -> In x Gamma).
          apply H.
        destruct (IVar_eq_dec y x).
        + tauto.
        + assert (In x Gamma).
            simpl in H1.
            apply H1.
            apply H0.
          tauto.
  Qed.

  Lemma isFreeIn_property3 :
    let Phi : IVar -> list IVar -> Prop := fun x : IVar => fun Gamma : list IVar => In x Gamma in
    forall M : Term,
    legio Phi [] M <-> (forall x : IVar, isFreeIn x M = false).
  Proof.
    intros.
    assert (legio Phi [] M <-> (forall x : IVar, isFreeIn x M = true -> Phi x [])).
      apply isFreeIn_property2.
    cut ((forall x : IVar, isFreeIn x M = true -> Phi x []) <-> (forall x : IVar, isFreeIn x M = false)).
      tauto.
    constructor.
    - intros.
      assert (isFreeIn x M = true -> Phi x []).
        apply H0.
      destruct (isFreeIn x M).
      * contradiction H1.
        reflexivity.
      * reflexivity.
    - intros.
      assert (isFreeIn x M = false).
        apply H0.
      rewrite H1 in H2.
      inversion H2.
  Qed.

  Inductive WellFormedCtx : list IVar -> Term -> Term -> Prop :=
  | WellFormedCtxRefl :
    forall M : Term,
    WellFormedCtx [] M M
  | WellFormedCtxApp1 :
    forall M : Term,
    forall P1 : Term,
    forall P2 : Term,
    forall Gamma : list IVar,
    WellFormedCtx Gamma M P1 ->
    WellFormedCtx Gamma M (App P1 P2)
  | WellFormedCtxApp2 :
    forall M : Term,
    forall P1 : Term,
    forall P2 : Term,
    forall Gamma : list IVar,
    WellFormedCtx Gamma M P2 ->
    WellFormedCtx Gamma M (App P1 P2)
  | WellFormedCtxLam0 :
    forall M : Term,
    forall y : IVar,
    forall Q : Term,
    forall Gamma : list IVar,
    WellFormedCtx (y :: Gamma) M Q ->
    WellFormedCtx Gamma M (Lam y Q)
  .

  Lemma WellFormedCtx_refl :
    forall M : Term,
    WellFormedCtx [] M M.
  Proof.
    apply WellFormedCtxRefl.
  Qed.

  Lemma WellFormedCtx_trans :
    forall M : Term,
    forall N : Term,
    forall L : Term,
    forall Gamma1 : list IVar,
    forall Gamma2 : list IVar,
    WellFormedCtx Gamma1 M N ->
    WellFormedCtx Gamma2 N L ->
    WellFormedCtx (Gamma2 ++ Gamma1) M L.
  Proof.
    cut (
      forall L : Term,
      forall N : Term,
      forall M : Term,
      forall Gamma1 : list IVar,
      forall Gamma2 : list IVar,
      WellFormedCtx Gamma2 M N ->
      WellFormedCtx Gamma1 N L ->
      WellFormedCtx (Gamma1 ++ Gamma2) M L
    ).
      intros.
      apply (H L N M Gamma2 Gamma1).
      apply H0.
      apply H1.
    intros L.
    induction L.
    - intros N.
      induction N.
      * intros.
        inversion H.
        { subst.
          simpl.
          rewrite app_nil_r.
          apply H0.
        }
      * intros.
        inversion H.
        { subst.
          simpl.
          rewrite app_nil_r.
          apply H0.
        }
        { subst.
          inversion H0.
        }
        { subst.
          inversion H0.
        }
      * intros.
        inversion H.
        { subst.
          simpl.
          rewrite app_nil_r.
          apply H0.
        }
        { subst.
          inversion H0.
        }
    - intros N.
      induction N.
      * intros.
        inversion H.
        { subst.
          simpl.
          rewrite app_nil_r.
          apply H0.
        }
      * intros.
        inversion H.
        { subst.
          rewrite app_nil_r.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            apply H.
          }
          { subst.
            apply WellFormedCtxApp1.
            apply (IHL1 (App N1 N2)).
            apply H.
            apply H5.
          }
          { subst.
            apply WellFormedCtxApp2.
            apply (IHL2 (App N1 N2)).
            apply H.
            apply H5.
          }
        }
        { subst.
          inversion H0.
          { subst.
            apply H.
          }
          { subst.
            apply WellFormedCtxApp1.
            apply (IHL1 (App N1 N2)).
            apply H.
            apply H5.
          }
          { subst.
            apply WellFormedCtxApp2.
            apply (IHL2 (App N1 N2)).
            apply H.
            apply H5.
          }
        }
      * intros.
        inversion H.
        { subst.
          rewrite app_nil_r.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            apply WellFormedCtxApp1.
            apply (IHL1 (Lam y N)).
            apply H.
            apply H5.
          }
          { subst.
            apply WellFormedCtxApp2.
            apply (IHL2 (Lam y N)).
            apply H.
            apply H5.
          }
        }
    - intros N.
      induction N.
      * intros.
        inversion H.
        { subst.
          simpl.
          rewrite app_nil_r.
          apply H0.
        }
      * intros.
        inversion H.
        { subst.
          simpl.
          rewrite app_nil_r.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            apply WellFormedCtxLam0.
            apply (IHL (App N1 N2) M (y :: Gamma1) Gamma2).
            apply H.
            apply H5.
          }
        }
        { subst.
          inversion H0.
          { subst.
            apply WellFormedCtxLam0.
            apply (IHL (App N1 N2) M (y :: Gamma1) Gamma2).
            apply H.
            apply H5.
          }
        }
      * intros.
        inversion H.
        { subst.
          rewrite app_nil_r.
          apply H0.
        }
        { subst.
          inversion H0.
          { subst.
            simpl.
            apply H.
          }
          { subst.
            apply WellFormedCtxLam0.
            apply (IHL (Lam y0 N) M (y :: Gamma1) Gamma2).
            apply H.
            apply H5.
          }
        }
  Qed.

  End Syntax.

End UntypedLambdaCalculus.
