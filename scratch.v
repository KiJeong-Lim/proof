Require Export List.
Require Export Bool.
Require Export Lia.
Require Export Peano_dec.

Module Classic.

  Lemma axiom_of_choice (A : Set) (B : Set) :
    forall phi : A -> B -> Prop,
    (forall x : A, { y : B | phi x y }) ->
    { f : A -> B | forall x : A, phi x (f x) }.
  Proof.
    intros phi.
    intro H.
    apply (exist (fun f : A -> B => forall x : A, phi x (f x)) (fun x : A => proj1_sig (H x))).
    intros x.
    unfold proj1_sig.
    destruct (H x).
    apply p.
  Qed.

  Axiom ex_middle : forall P : Prop, P \/ ~P.

End Classic.

Module Ordering.

  Inductive ordering : Set :=
  | LT : ordering
  | EQ : ordering
  | GT : ordering
  .

  Fixpoint compareNats (lhs : nat) (rhs : nat) : ordering :=
    match lhs, rhs with
    | 0, 0 => EQ
    | 0, S rhs' => LT
    | S lhs', 0 => GT
    | S lhs', S rhs' => compareNats lhs' rhs'
    end
  .

  Lemma property_compareNats :
    forall lhs rhs : nat,
    (lhs < rhs /\ compareNats lhs rhs = LT) \/
    (lhs = rhs /\ compareNats lhs rhs = EQ) \/
    (lhs > rhs /\ compareNats lhs rhs = GT).
  Proof.
    intros lhs.
    induction lhs.
    - destruct rhs.
      * simpl.
        tauto.
      * simpl.
        assert (0 < S rhs).
          lia.
        tauto.
    - destruct rhs.
      * simpl.
        assert (S lhs > 0).
          lia.
        tauto.
      * simpl.
        assert
          ( lhs < rhs /\ compareNats lhs rhs = LT \/
            lhs = rhs /\ compareNats lhs rhs = EQ \/
            lhs > rhs /\ compareNats lhs rhs = GT
          ).
        apply (IHlhs rhs).
        intuition.
  Qed.

  Theorem property_LT :
    forall lhs rhs : nat,
    LT = compareNats lhs rhs <-> lhs < rhs.
  Proof.
    intros lhs rhs.
    assert
      ( lhs < rhs /\ compareNats lhs rhs = LT \/
        lhs = rhs /\ compareNats lhs rhs = EQ \/
        lhs > rhs /\ compareNats lhs rhs = GT
      ).
      apply (property_compareNats lhs rhs).
    constructor.
      intro.
      intuition.
      assert (LT = EQ).
        rewrite <- H0 in H2.
        apply H2.
      discriminate H.
      assert (LT = GT).
        rewrite <- H0 in H2.
        apply H2.
      discriminate H.
      intro.
      assert (~lhs = rhs).
        lia.
      assert (~lhs > rhs).
        lia.
      intuition.
  Qed.

  Theorem property_EQ :
    forall lhs rhs : nat,
    EQ = compareNats lhs rhs <-> lhs = rhs.
  Proof.
    intros lhs rhs.
    assert
      ( lhs < rhs /\ compareNats lhs rhs = LT \/
        lhs = rhs /\ compareNats lhs rhs = EQ \/
        lhs > rhs /\ compareNats lhs rhs = GT
      ).
      apply (property_compareNats lhs rhs).
    constructor.
      intro.
      intuition.
      assert (EQ = LT).
        rewrite <- H0 in H2.
        apply H2.
      discriminate H1.
      assert (EQ = GT).
        rewrite <- H0 in H2.
        apply H2.
      discriminate H.
      intro.
      assert (~lhs < rhs).
        lia.
      assert (~lhs > rhs).
        lia.
      intuition.
  Qed.

  Theorem property_GT :
    forall lhs rhs : nat,
    GT = compareNats lhs rhs <-> lhs > rhs.
  Proof.
    intros lhs rhs.
    assert
      ( lhs < rhs /\ compareNats lhs rhs = LT \/
        lhs = rhs /\ compareNats lhs rhs = EQ \/
        lhs > rhs /\ compareNats lhs rhs = GT
      ).
      apply (property_compareNats lhs rhs).
    constructor.
      intro.
      intuition.
      assert (GT = LT).
        rewrite <- H0 in H2.
        apply H2.
      discriminate H1.
      assert (GT = EQ).
        rewrite <- H0 in H2.
        apply H2.
      discriminate H.
      intro.
      assert (~lhs < rhs).
        lia.
      assert (~lhs = rhs).
        lia.
      intuition.
  Qed.

End Ordering.

Module ListTheory.

  Section General.

    Import ListNotations.

    Variable A : Type.

    Variable eq_A_dec : forall x y : A, {x = y} + {x <> y}.

    Variable B : Type.

    Fixpoint areAllDistinct (xs : list A) : Prop :=
      match xs with
      | [] => True
      | x :: xs' => not (In x xs') /\ areAllDistinct xs'
      end
    .

    Lemma len_append :
      forall (xs ys : list A),
      length (xs ++ ys) = length xs + length ys.
    Proof.
      intros xs ys.
      induction xs.
      - simpl.
        reflexivity.
      - simpl.
        lia.
    Qed.

    Lemma len_map :
      forall f : A -> B,
      forall xs : list A,
      length xs = length (map f xs).
    Proof.
      intros f xs.
      induction xs.
      - simpl.
        tauto.
      - simpl.
        lia.
    Qed.

    Lemma in_or_not_in :
      forall xs : list A,
      forall x : A,
      In x xs \/ ~ In x xs.
    Proof.
      intros xs.
      induction xs.
      simpl.
      tauto.
      simpl.
      intro x.
      destruct (eq_A_dec a x).
      tauto.
      destruct (IHxs x).
      tauto.
      tauto.
    Qed.

    Lemma in_append :
      forall x : A,
      forall (xs ys : list A),
      In x (xs ++ ys) <-> (In x xs \/ In x ys).
    Proof.
      intros x xs ys.
      constructor.
      - induction xs.
        * simpl.
          tauto.
        * simpl.
          tauto.
      - intro.
        induction xs.
        * simpl.
          destruct H.
          + elimtype False.
            apply H.
          + apply H.
        * simpl.
          destruct H.
          + destruct H.
            apply (or_introl H).
            apply or_intror.
            tauto.
          + tauto.
    Qed.

    Lemma in_map :
      forall f : A -> B,
      forall xs : list A,
      forall x : A,
      In x xs -> In (f x) (map f xs).
    Proof.
      intros f xs.
      induction xs.
      - simpl.
        tauto.
      - intros x.
        simpl.
        intro.
        destruct H.
        * subst.
          tauto.
        * apply (or_intror (IHxs x H)).
    Qed.

    Lemma in_middle :
      forall (x y : A),
      forall (xs ys : list A),
      In x (xs ++ y :: ys) <-> (x = y \/ In x (xs ++ ys)).
    Proof.
      intros x y xs ys.
      induction xs.
      - constructor.
        * simpl.
          intro.
          destruct H.
          apply or_introl.
          auto.
          tauto.
        * simpl.
          intro.
          destruct H.
          auto.
          auto.
      - constructor.
        * simpl.
          tauto.
        * simpl.
          tauto.
    Qed.

    Lemma in_map_in :
      forall f : A -> B,
      forall xs : list A,
      forall y : B,
      In y (map f xs) ->
      exists x : A, y = f x /\ In x xs.
    Proof.
      intros f xs.
      induction xs.
      - intros y.
        simpl.
        tauto.
      - intros y.
        simpl.
        intro.
        destruct H.
        * exists a.
          subst.
          tauto.
        * destruct (IHxs y H).
          exists x.
          tauto.
    Qed.

    Lemma in_map_inj :
      forall f : A -> B,
      (forall x1 x2 : A, f x1 = f x2 -> x1 = x2) ->
      forall xs : list A,
      forall x : A,
      In (f x) (map f xs) -> In x xs.
    Proof.
      intros f.
      intro.
      intros xs.
      induction xs.
      - intros x.
        simpl.
        tauto.
      - intros x.
        simpl.
        intro.
        destruct H0.
        * apply (or_introl (H a x H0)).
        * apply (or_intror (IHxs x H0)).
    Qed.

    Lemma split_middle :
      forall x : A,
      forall xs : list A,
      In x xs ->
      exists ls : list A,
      exists rs : list A,
      xs = ls ++ x :: rs.
    Proof.
      intros x xs.
      induction xs.
      - simpl.
        intro.
        elimtype False.
        apply H.
      - intro.
        destruct H.
        * exists [].
          exists xs.
          subst.
          simpl.
          reflexivity.
        * destruct (IHxs H) as [ls H0].
          destruct (H0) as [rs].
          exists (a :: ls).
          exists rs.
          subst.
          simpl.
          reflexivity.
    Qed.

    Theorem pigeon_hole :
      forall (xs xs' : list A),
      (forall x : A, In x xs -> In x xs') ->
      length xs' < length xs ->
      not (areAllDistinct xs).
    Proof.
      intros xs.
      induction xs.
      - intros xs'.
        simpl.
        intro.
        lia.
      - intros xs'.
        simpl.
        intro.
        assert (H0 : exists ls : list A, exists rs : list A, xs' = ls ++ a :: rs).
        apply (fun H0 : In a xs' => split_middle a xs' H0).
        apply (H a).
        simpl.
        tauto.
        destruct H0 as [ls H0].
        destruct H0 as [rs H0].
        subst.
        assert (H0 : length (ls ++ a :: rs) = length ls + length (a :: rs)).
        apply (len_append ls (a :: rs)).
        subst.
        rewrite H0.
        simpl.
        intro.
        intro.
        destruct H2.
        apply (IHxs (ls ++ rs)).
        * intros x.
          intro.
          apply (proj2 (in_append x ls rs)).
          destruct (eq_A_dec a x).
          + subst.
            elimtype False.
            apply (H2 H4).
          + apply (proj1 (in_append x ls rs)).
            assert (H6 : In x (ls ++ a :: rs)).
            apply (H x (or_intror H4)).
            assert (H7 : a = x \/ In x (ls ++ rs)).
            destruct (proj1 (in_middle x a ls rs)).
            apply H6.
            apply or_introl.
            subst.
            reflexivity.
            apply or_intror.
            apply H5.
            destruct H7.
            elimtype False.
            apply (n H5).
            apply H5.
        * assert (H4 : length (ls ++ rs) = length ls + length rs).
          apply (len_append ls rs).
          lia.
        * apply H3.
    Qed.

  End General.

  Section Nat.

    Import ListNotations.

    Lemma enum_exists :
      forall from : nat,
      forall to : nat,
      forall f_le_t : from <= to,
      exists enum : list nat,
      (from + length enum = to) /\
      (areAllDistinct nat enum) /\
      forall n : nat,
      In n enum <->
      (from <= n /\ n < to)
      .
    Proof.
      intros from to f_le_t.
      induction f_le_t as [| to].
      - exists [].
        constructor.
        simpl.
        lia.
        simpl.
        constructor.
        trivial.
        intros n.
        lia.
      - destruct IHf_le_t as [enum H].
        destruct H.
        exists (to :: enum).
        constructor.
        simpl.
        lia.
        simpl.
        destruct H0.
        constructor.
        constructor.
        intro.
        assert (from <= to < to).
        apply (proj1 (H1 to) H2).
        lia.
        apply H0.
        intros n.
        constructor.
        intro.
        destruct H2.
        subst.
        lia.
        assert (from <= n /\ n < to).
        apply (proj1 (H1 n) H2).
        lia.
        intro.
        destruct (eq_nat_dec to n).
        simpl.
        tauto.
        assert (from <= n /\ n < to).
        lia.
        simpl.
        apply or_intror.
        apply (proj2 (H1 n) H3).
    Qed.

    Theorem pigeon_hole_nat :
      forall size : nat,
      forall ns : list nat,
      (forall n : nat, In n ns <-> n < size) ->
      areAllDistinct nat ns ->
      length ns = size.
    Proof.
      intros size ns.
      destruct (enum_exists 0 size) as [enum H].
      lia.
      intro.
      intro.
      assert (not (length ns > size)).
      intro.
      apply (pigeon_hole nat eq_nat_dec ns enum).
      destruct H.
      destruct H3.
      intros n.
      assert (n < size <-> 0 <= n < size).
      lia.
      intro.
      apply (proj2 (H4 n)).
      apply (proj1 H5).
      apply (proj1 (H0 n) H6).
      destruct H.
      lia.
      apply H1.
      destruct H.
      destruct H3.
      assert (not (length ns < size)).
      intro.
      apply (pigeon_hole nat eq_nat_dec enum ns).
      intros n.
      assert (n < size <-> 0 <= n < size).
      lia.
      intro.
      apply (proj2 (H0 n)).
      apply (proj2 H6).
      apply (proj1 (H4 n) H7).
      lia.
      apply H3.
      lia.
    Qed.

  End Nat.

End ListTheory.

Module GraphTheory.

  Record Graph : Type :=
    { Vertex : Set
    ; Edge : Vertex -> Vertex -> Prop
    }
  .

  Section General.

    Import ListNotations.

    Import ListTheory.
    
    Variable g : Graph.
  
    Variable eq_gVertex_dec : forall v1 v2 : g.(Vertex), {v1 = v2} + {v1 <> v2}.

    Inductive Path : list g.(Vertex) -> g.(Vertex) -> g.(Vertex) -> Prop :=
    | PZ :
      forall beg : g.(Vertex),
      Path [beg] beg beg
    | PS :
      forall beg cur next : g.(Vertex),
      forall visiteds : list g.(Vertex),
      g.(Edge) cur next ->
      not (In next visiteds) ->
      Path visiteds beg cur ->
      Path (next :: visiteds) beg next
    .

    Inductive Walk : list g.(Vertex) -> g.(Vertex) -> g.(Vertex) -> Prop :=
    | WZ :
      forall beg : g.(Vertex),
      Walk [] beg beg
    | WS :
      forall trace : list g.(Vertex),
      forall beg cur next : g.(Vertex),
      g.(Edge) cur next ->
      Walk trace beg cur ->
      Walk (cur :: trace) beg next
    .

    Lemma subpath_exist :
      forall visiteds : list g.(Vertex),
      forall beg cur : g.(Vertex),
      Path visiteds beg cur ->
      forall prev : g.(Vertex),
      In prev visiteds ->
      exists visiteds' : list g.(Vertex),
      Path visiteds' beg prev.
    Proof.
      intros visiteds beg cur.
      intro.
      induction H.
      intros prev.
      intro.
      inversion H.
      exists [beg].
      subst.
      apply PZ.
      inversion H0.
      intros prev.
      intro.
      inversion H2.
      subst.
      exists (prev :: visiteds).
      apply (PS beg cur prev visiteds H H0 H1).
      apply (IHPath prev H3).
    Qed.

    Theorem walk_implies_path :
      forall trace : list g.(Vertex),
      forall beg cur : g.(Vertex),
      Walk trace beg cur ->
      exists visiteds,
      Path visiteds beg cur.
    Proof.
      intros trace beg cur.
      intro.
      induction H.
      exists [beg].
      apply (PZ beg).
      destruct IHWalk as [visiteds].
      destruct (in_or_not_in g.(Vertex) eq_gVertex_dec visiteds next).
      apply (subpath_exist visiteds beg cur H1 next H2).
      exists (next :: visiteds).
      apply (PS beg cur next visiteds H H2 H1).
    Qed.

    Proposition visiteds_are_all_distinct :
      forall visiteds : list g.(Vertex),
      forall beg cur : g.(Vertex),
      Path visiteds beg cur ->
      areAllDistinct g.(Vertex) visiteds.
    Proof.
      intros visiteds beg cur.
      intro.
      induction H.
      - subst.
        simpl.
        tauto.
      - subst.
        simpl.
        tauto.
    Qed.

  End General.

  Section Finite.

    Import ListNotations.

    Import ListTheory.

    Variable g : Graph.
  
    Variable eq_gVertex_dec : forall v1 v2 : g.(Vertex), {v1 = v2} + {v1 <> v2}.

    Variable size : nat.

    Variable can_enum_vertices : (exists vertices : list g.(Vertex), areAllDistinct g.(Vertex) vertices /\ length vertices = size /\ (forall v : g.(Vertex), In v vertices)).

    Proposition len_path_leq_size : 
      forall visiteds : list g.(Vertex),
      forall beg cur : g.(Vertex),
      Path g visiteds beg cur ->
      length visiteds <= size.
    Proof.
      intros visiteds beg cur.
      intro.
      destruct can_enum_vertices as [vertices].
      assert (not (length visiteds > size)).
        intro.
        destruct H0.
        destruct H2.
        apply (pigeon_hole g.(Vertex) eq_gVertex_dec visiteds vertices).
          intros v.
          intro.
          apply (H3 v).
          lia.
          apply (visiteds_are_all_distinct g visiteds beg cur H).
        lia.
    Qed.

  End Finite.

End GraphTheory.

Module ETC.

  Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' => if p (first_nat p n') then first_nat p n' else n
    end
  .

  Theorem well_ordering_principle : 
    forall p : nat -> bool,
    (exists n : nat, p n = true) ->
    (exists m : nat, p m = true /\ (forall i : nat, p i = true -> i >= m)).
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
    intro.
    destruct H3.
    exists (first_nat p x).
    constructor.
    apply (H x H3).
    intros i.
    intro.
    assert (first_nat p x <= i).
      apply (H2 x i H4).
    lia.
  Qed.

End ETC.
