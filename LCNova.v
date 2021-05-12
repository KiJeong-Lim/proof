From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.
From Coq.Program Require Export Equality.

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

  Section forFinSet.

  Inductive FinSet : nat -> Set :=
  | FinSetZ :
    forall n : nat,
    FinSet (S n)
  | FinSetS :
    forall n : nat,
    FinSet n ->
    FinSet (S n)
  .

  Lemma makeFinSet :
    forall n : nat,
    forall i : nat,
    i < n ->
    FinSet n.
  Proof.
    intros n.
    induction n.
    - intros.
      lia.
    - intros.
      destruct (Nat.eq_dec i n).
      * apply FinSetZ.
      * apply FinSetS.
        apply (IHn i).
        lia.
  Qed.

  Lemma runFinSet :
    forall n : nat,
    FinSet n ->
    {i : nat | i < n}.
  Proof.
    intros.
    induction H.
    * exists n.
      lia.
    * destruct IHFinSet as [i].
      exists i.
      lia.
  Qed.

  Fixpoint FinSet_eqb {n1 : nat} {n2 : nat} (fs1 : FinSet n1) (fs2 : FinSet n2) : bool :=
    match fs1 with
    | FinSetZ _ =>
      match fs2 with
      | FinSetZ _ => true
      | FinSetS _ fs2' => false 
      end
    | FinSetS _ fs1' =>
      match fs2 with
      | FinSetZ _ => false
      | FinSetS _ fs2' => FinSet_eqb fs1' fs2'
      end
    end
  .

  End forFinSet.

  Section forZip.

  Fixpoint zip {A : Type} {B : Type} (xs : list A) (ys : list B) : list (A * B) :=
    match xs, ys with
    | x :: xs', y :: ys' => (x, y) :: zip xs' ys'
    | _, _ => []
    end
  .

  Lemma zip_main_property {A : Type} {B : Type} :
    forall xs : list A,
    forall ys : list B,
    length xs = length ys ->
    let zs : list (A * B) := zip xs ys in
    map fst zs = xs /\ map snd zs = ys.
  Proof.
    intros xs.
    induction xs.
    - intros ys.
      destruct ys.
      * intros.
        simpl.
        tauto.
      * intros.
        inversion H.
    - intros ys.
      destruct ys.
      * intros.
        inversion H.
      * intros.
        inversion H.
        assert (map fst (zip xs ys) = xs /\ map snd (zip xs ys) = ys).
          apply IHxs.
          tauto.
        destruct H0.
        unfold zs.
        simpl.
        rewrite H0.
        rewrite H2.
        tauto.
  Qed.

  Lemma zip_property1 {A : Type} {B : Type} :
    forall zs : list (A * B),
    zip (map fst zs) (map snd zs) = zs.
  Proof.
    intros zs.
    induction zs.
    - reflexivity.
    - destruct a as [x y].
      simpl.
      rewrite IHzs.
      reflexivity.
  Qed.

  End forZip.

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

  Theorem StrongInductionOnTerm (Phi : Term -> Prop) :
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

  Definition Subst : Set :=
    list (IVar * Term)
  .

  Fixpoint runSubst_Var (sigma : Subst) (x : IVar) : Term :=
    match sigma with
    | [] => Var x
    | (z, N) :: sigma' =>
      if IVar_eq_dec x z
      then N
      else runSubst_Var sigma' x
    end
  .
  End Syntax.

  Lemma runSubst_Var_main_property :
    forall sigma : Subst,
    forall x : IVar,
    forall M : Term,
    runSubst_Var sigma x = M <-> (if In_dec IVar_eq_dec x (map fst sigma) then (exists sigma1 : Subst, exists sigma2 : Subst, sigma = sigma1 ++ [(x, M)] ++ sigma2 /\ ~ In x (map fst sigma1)) else Var x = M).
  Proof.
    intros sigma.
    induction sigma.
    - simpl.
      intros.
      tauto.
    - destruct a as [x1 M1].
      simpl.
      intros.
      destruct (IVar_eq_dec x x1).
      * subst.
        destruct (IVar_eq_dec x1 x1).
        + constructor.
          { intros.
            exists [].
            exists sigma.
            simpl.
            subst.
            tauto.
          }
          { intros.
            destruct H as [sigma1].
            destruct H as [sigma2].
            destruct H.
            destruct sigma1.
            - simpl in H.
              inversion H.
              subst.
              reflexivity.
            - simpl in H.
              destruct p as [x2 M2].
              inversion H.
              subst.
              contradiction H0.
              simpl.
              tauto.
          }
        + contradiction n.
          reflexivity.
      * destruct (IVar_eq_dec x1 x).
        + contradiction n.
          rewrite e.
          reflexivity.
        + rewrite IHsigma.
          destruct (in_dec IVar_eq_dec x (map fst sigma)).
          { simpl.
            constructor.
            - intros.
              destruct H as [sigma1].
              destruct H as [sigma2].
              exists ((x1, M1) :: sigma1).
              exists sigma2.
              simpl.
              destruct H.
              constructor.
              rewrite H.
              reflexivity.
              tauto.
            - intros.
              destruct H as [sigma1].
              destruct H as [sigma2].
              destruct H.
              destruct sigma1.
              * simpl in H.
                inversion H.
                subst.
                contradiction n.
                reflexivity.
              * exists sigma1.
                exists sigma2.
                simpl in H.
                inversion H.
                subst.
                constructor.
                reflexivity.
                simpl in H0.
                tauto.
          }
          { reflexivity.
          }
  Qed.

  Lemma runSubst_Var_property1 :
    forall sigma : Subst,
    forall x : IVar,
    forall M : Term,
    runSubst_Var sigma x = M ->
    (exists sigma1 : Subst, exists sigma2 : Subst, sigma = sigma1 ++ [(x, M)] ++ sigma2) \/ Var x = M.
  Proof.
    intros sigma.
    induction sigma.
    - simpl.
      intros.
      right.
      apply H.
    - destruct a as [x1 M1].
      simpl.
      intros.
      destruct (IVar_eq_dec x x1).
      * left.
        exists [].
        exists sigma.
        simpl.
        subst.
        reflexivity.
      * assert ((exists sigma1 sigma2 : Subst, sigma = sigma1 ++ [(x, M)] ++ sigma2) \/ Var x = M).
          apply IHsigma.
          apply H.
        destruct H0.
        + destruct H0 as [sigma1].
          destruct H0 as [sigma2].
          left.
          exists ((x1, M1) :: sigma1).
          exists sigma2.
          simpl.
          rewrite H0.
          reflexivity.
        + right.
          apply H0.
  Qed.

  Section Scoping.

  Fixpoint legio (Phi : IVar -> list IVar -> Prop) (M : Term) (Gamma : list IVar) : Prop :=
    match M with
    | Var x => Phi x Gamma
    | App P1 P2 => legio Phi P1 Gamma /\ legio Phi P2 Gamma
    | Lam y Q => legio Phi Q (y :: Gamma)
    end
  . 

  Inductive OccursIn : IVar -> Term -> Set :=
  | OccursInRefl :
    forall x : IVar,
    OccursIn x (Var x)
  | OccursInApp1 :
    forall x : IVar,
    forall P1 : Term,
    forall P2 : Term,
    OccursIn x P1 ->
    OccursIn x (App P1 P2)
  | OccursInApp2 :
    forall x : IVar,
    forall P1 : Term,
    forall P2 : Term,
    OccursIn x P2 ->
    OccursIn x (App P1 P2)
  | OccursInLam0 :
    forall x : IVar,
    forall y : IVar,
    forall Q : Term,
    OccursIn x Q ->
    OccursIn x (Lam y Q)
  .

  Fixpoint makeScope_aux (Gamma : list IVar) (x : IVar) (M : Term) (H : OccursIn x M) : list IVar :=
    match H with
    | OccursInRefl x => Gamma
    | OccursInApp1 x P1 P2 H1 => makeScope_aux Gamma x P1 H1
    | OccursInApp2 x P1 P2 H2 => makeScope_aux Gamma x P2 H2
    | OccursInLam0 x y Q H0 => makeScope_aux (y :: Gamma) x Q H0
    end
  .

  Lemma legio_main_property (Phi : IVar -> list IVar -> Prop) :
    forall M : Term,
    forall Gamma : list IVar,
    legio Phi M Gamma <-> (forall z : IVar, forall H : OccursIn z M, Phi z (makeScope_aux Gamma z M H)).
  Proof.
    assert ( claim1 :
      forall M : Term,
      forall z : IVar,
      forall H : OccursIn z M,
      forall Gamma : list IVar,
      legio Phi M Gamma ->
      Phi z (makeScope_aux Gamma z M H)
    ).
    { intros M z H.
      induction H.
      - simpl.
        tauto.
      - simpl.
        intros.
        apply IHOccursIn.
        apply H0.
      - simpl.
        intros.
        apply IHOccursIn.
        apply H0.
      - simpl.
        intros.
        apply IHOccursIn.
        apply H0.
    }
    assert ( claim2 :
      forall M : Term,
      forall Gamma : list IVar,
      (forall (z : IVar) (H : OccursIn z M), Phi z (makeScope_aux Gamma z M H)) ->
      legio Phi M Gamma
    ).
    { intros M.
      induction M.
      - simpl.
        intros.
        apply (H x (OccursInRefl x)).
      - simpl.
        intros.
        constructor.
        { apply IHM1.
          intros.
          apply (H z (OccursInApp1 z M1 M2 H0)).
        }
        { apply IHM2.
          intros.
          apply (H z (OccursInApp2 z M1 M2 H0)).
        }
      - simpl.
        intros.
        apply IHM.
        intros.
        apply (H z (OccursInLam0 z y M H0)).
    }
    intros.
    constructor.
    - intros.
      apply claim1.
      apply H.
    - intros.
      apply claim2.
      apply H.
  Qed.

  End Scoping.

  Section DeBruijn.

  Fixpoint getDeBruijnIndex (Gamma : list IVar) (z : IVar) : option nat :=
    match Gamma with
    | [] => None
    | x :: Gamma' => 
      if IVar_eq_dec x z
      then Some 0
      else
      match getDeBruijnIndex Gamma' z with
      | None => None
      | Some n => Some (S n)
      end
    end
  .

  Lemma getDeBruijnIndex_property1 :
    forall Gamma : list IVar,
    forall z : IVar,
    getDeBruijnIndex Gamma z = None <-> ~ In z Gamma.
  Proof.
    intros Gamma.
    induction Gamma.
    - intros.
      simpl.
      tauto.
    - intros.
      simpl.
      destruct (IVar_eq_dec a z).
      * constructor.
        + intros.
          inversion H.
        + intros.
          contradiction H.
          tauto.
      * assert (getDeBruijnIndex Gamma z = None <-> ~ In z Gamma).
          apply IHGamma.
        constructor.
        + intros.
          destruct (getDeBruijnIndex Gamma z).
          { inversion H0.
          }
          { tauto.
          }
        + intros.
          destruct (getDeBruijnIndex Gamma z).
          { contradiction H0.
            right.
            assert (~ Some n0 = None).
              intro.
              inversion H1.
            tauto.
          }
          { reflexivity.
          }
  Qed.

  Lemma getDeBruijnIndex_property2 :
    forall Gamma : list IVar,
    forall z : IVar,
    In z Gamma ->
    exists idx : nat, getDeBruijnIndex Gamma z = Some idx.
  Proof.
    intros Gamma.
    induction Gamma.
    - intros.
      inversion H.
    - intros.
      simpl in H.
      destruct (IVar_eq_dec a z).
      * exists 0.
        simpl.
        destruct (IVar_eq_dec a z).
        + reflexivity.
        + contradiction n.
      * assert (In z Gamma).
          tauto.
        destruct (IHGamma z H0) as [idx].
        exists (S idx).
        simpl.
        rewrite H1.
        destruct (IVar_eq_dec a z).
        + contradiction n.
        + reflexivity.
  Qed.

  Lemma getDeBruijnIndex_property3 :
    forall Gamma : list IVar,
    forall z : IVar,
    forall idx : nat,
    getDeBruijnIndex Gamma z = Some idx -> 
    exists Gamma1 : list IVar,
    exists Gamma2 : list IVar,
    ((Gamma = Gamma1 ++ [z] ++ Gamma2 /\ length Gamma1 = idx) /\ (forall x : IVar, In x Gamma1 -> x <> z)).
  Proof.
    intros Gamma.
    induction Gamma.
    - simpl.
      intros.
      inversion H.
    - simpl.
      intros.
      destruct (IVar_eq_dec a z).
      * inversion H.
        subst.
        exists [].
        exists Gamma.
        constructor.
        + tauto.
        + intros.
          inversion H0.
      * assert (
          forall idx : IVar,
          getDeBruijnIndex Gamma z = Some idx ->
          exists Gamma1 : list IVar,
          exists Gamma2 : list IVar,
          (Gamma = Gamma1 ++ [z] ++ Gamma2 /\ length Gamma1 = idx) /\ (forall x : IVar, In x Gamma1 -> x <> z)
        ).
          apply IHGamma.
        destruct (getDeBruijnIndex Gamma z).
        + inversion H.
          subst.
          assert (
            exists Gamma1 : list IVar,
            exists Gamma2 : list IVar,
            (Gamma = Gamma1 ++ [z] ++ Gamma2 /\ length Gamma1 = n0) /\ (forall x : IVar, In x Gamma1 -> x <> z)
          ).
            apply H0.
            reflexivity.
          destruct H1 as [Gamma1].
          destruct H1 as [Gamma2].
          destruct H1.
          destruct H1.
          exists (a :: Gamma1).
          exists Gamma2.
          constructor.
          constructor.
          rewrite H1.
          simpl.
          reflexivity.
          simpl.
          rewrite H3.
          reflexivity.
          intros.
          simpl in H4.
          destruct H4.
          subst.
          apply n.
          apply H2.
          apply H4.
        + inversion H.
  Qed.

  Inductive DeBruijnTerm : Set :=
  | BVar : nat -> DeBruijnTerm
  | FVar : IVar -> DeBruijnTerm
  | IApp : DeBruijnTerm -> DeBruijnTerm -> DeBruijnTerm
  | IAbs : DeBruijnTerm -> DeBruijnTerm
  .

  Fixpoint makeDeBruijnTerm_aux (Gamma : list IVar) (M : Term) : DeBruijnTerm :=
    match M with
    | Var x =>
      match getDeBruijnIndex Gamma x with
      | None => FVar x
      | Some idx => BVar idx
      end
    | App P1 P2 => IApp (makeDeBruijnTerm_aux Gamma P1) (makeDeBruijnTerm_aux Gamma P2)
    | Lam y Q => IAbs (makeDeBruijnTerm_aux (y :: Gamma) Q)
    end
  .

  Inductive mapsToDeBruijn : list IVar -> Term -> DeBruijnTerm -> Prop :=
  | mapsToDeBruijnBVar :
    forall Gamma : list IVar,
    forall x : IVar,
    forall idx : nat,
    getDeBruijnIndex Gamma x = Some idx ->
    mapsToDeBruijn Gamma (Var x) (BVar idx)
  | mapsToDeBruijnFVar :
    forall Gamma : list IVar,
    forall x : IVar,
    getDeBruijnIndex Gamma x = None ->
    mapsToDeBruijn Gamma (Var x) (FVar x)
  | mapsToDeBruijnIApp :
    forall Gamma : list IVar,
    forall P1 : Term,
    forall P2 : Term,
    forall P1' : DeBruijnTerm,
    forall P2' : DeBruijnTerm,
    mapsToDeBruijn Gamma P1 P1' ->
    mapsToDeBruijn Gamma P2 P2' ->
    mapsToDeBruijn Gamma (App P1 P2) (IApp P1' P2')
  | mapsToDeBruijnIAbs :
    forall Gamma : list IVar,
    forall y : IVar,
    forall Q : Term,
    forall Q' : DeBruijnTerm,
    mapsToDeBruijn (y :: Gamma) Q Q' ->
    mapsToDeBruijn Gamma (Lam y Q) (IAbs Q')
  .

  Lemma makeDeBruijnTerm_aux_main_property :
    forall M : Term,
    forall M' : DeBruijnTerm,
    forall Gamma : list IVar,
    M' = makeDeBruijnTerm_aux Gamma M <-> mapsToDeBruijn Gamma M M'.
  Proof.
    intros M.
    induction M.
    - intros.
      simpl.
      cut (
        let idx' : option nat := getDeBruijnIndex Gamma x in
        idx' = getDeBruijnIndex Gamma x ->
        M' = (match idx' with | Some idx => BVar idx | None => FVar x end) <-> mapsToDeBruijn Gamma (Var x) M'
      ).
        intros.
        apply H.
        reflexivity.
      intros.
      destruct idx'.
      * constructor.
        + intros.
          subst.
          apply (mapsToDeBruijnBVar Gamma x n).
          rewrite H.
          reflexivity.
        + intros.
          inversion H0.
          { subst.
            rewrite H3 in H.
            inversion H.
            subst.
            reflexivity.
          }
          { subst.
            rewrite H3 in H.
            inversion H.
          }
      * constructor.
        + intros.
          subst.
          apply (mapsToDeBruijnFVar Gamma x).
          rewrite H.
          reflexivity.
        + intros.
          inversion H0.
          { subst.
            rewrite H3 in H.
            inversion H.
          }
          { subst.
            rewrite H3 in H.
            inversion H.
            subst.
            reflexivity.
          }
    - intros.
      constructor.
      * intros.
        subst.
        simpl.
        apply mapsToDeBruijnIApp.
        apply IHM1.
        reflexivity.
        apply IHM2.
        reflexivity.
      * intros.
        inversion H.
        subst.
        simpl.
        assert (P1' = makeDeBruijnTerm_aux Gamma M1).
          apply IHM1.
          apply H3.
        assert (P2' = makeDeBruijnTerm_aux Gamma M2).
          apply IHM2.
          apply H5.
        rewrite H0.
        rewrite H1.
        reflexivity.
    - intros.
      constructor.
      * intros.
        subst.
        simpl.
        apply mapsToDeBruijnIAbs.
        apply IHM.
        reflexivity.
      * intros.
        inversion H.
        subst.
        simpl.
        assert (Q' = makeDeBruijnTerm_aux (y :: Gamma) M).
          apply IHM.
          apply H4.
        rewrite H0.
        reflexivity.
  Qed.

  Definition makeDeBruijnTerm : Term -> DeBruijnTerm :=
    makeDeBruijnTerm_aux []
  .

  End DeBruijn.

  Section AlphaEquiv.

  End AlphaEquiv.

End UntypedLambdaCalculus.
