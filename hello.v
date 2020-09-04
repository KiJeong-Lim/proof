Require Export Omega.
Require Export List.

Axiom classic : forall P : Prop, P \/ not P.

Module ListTheory.

  Section General.

    Import ListNotations.

    Fixpoint AreAllDistinct {A : Type} (xs : list A) : Prop :=
      match xs with
      | [] => True
      | x :: xs' => not (In x xs') /\ AreAllDistinct xs'
      end
    .

    Lemma len_append {A : Type} :
      forall (xs ys : list A),
      length (xs ++ ys) = length xs + length ys.
    Proof.
      intros xs ys.
      induction xs.
      - simpl.
        reflexivity.
      - simpl.
        omega.
    Qed.

    Lemma len_map {A : Type} {B : Type} :
      forall f : A -> B,
      forall xs : list A,
      length xs = length (map f xs).
    Proof.
      intros f xs.
      induction xs.
      - simpl.
        tauto.
      - simpl.
        omega.
    Qed.

    Lemma in_append {A : Type} :
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

    Lemma in_map {A : Type} {B : Type} :
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

    Lemma in_middle {A : Type} :
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

    Lemma in_map_in {A : Type} {B : Type} :
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

    Lemma in_map_inj {A : Type} {B : Type} :
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

    Lemma split_middle {A : Type} :
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

    Theorem pigeon_hole {A : Type} :
      forall (xs xs' : list A),
      (forall x : A, In x xs -> In x xs') ->
      length xs' < length xs ->
      not (AreAllDistinct xs).
    Proof.
      intros xs.
      induction xs.
      - intros xs'.
        simpl.
        intro.
        omega.
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
          destruct (classic (a = x)).
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
            apply H7.
            destruct H7.
            elimtype False.
            apply (H5 H7).
            apply H7.
        * assert (H4 : length (ls ++ rs) = length ls + length rs).
          apply (len_append ls rs).
          omega.
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
      (AreAllDistinct enum) /\
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
        omega.
        simpl.
        constructor.
        trivial.
        intros n.
        omega.
      - destruct IHf_le_t as [enum H].
        destruct H.
        exists (to :: enum).
        constructor.
        simpl.
        omega.
        simpl.
        destruct H0.
        constructor.
        constructor.
        intro.
        assert (from <= to < to).
        apply (proj1 (H1 to) H2).
        omega.
        apply H0.
        intros n.
        constructor.
        intro.
        destruct H2.
        subst.
        omega.
        assert (from <= n /\ n < to).
        apply (proj1 (H1 n) H2).
        omega.
        intro.
        destruct (classic (to = n)).
        simpl.
        tauto.
        assert (from <= n /\ n < to).
        omega.
        simpl.
        apply or_intror.
        apply (proj2 (H1 n) H4).
    Qed.

    Theorem pigeon_hole_nat :
      forall size : nat,
      forall ns : list nat,
      (forall n : nat, In n ns <-> n < size) ->
      AreAllDistinct ns ->
      length ns = size.
    Proof.
      intros size ns.
      destruct (enum_exists 0 size) as [enum H].
      omega.
      intro.
      intro.
      assert (not (length ns > size)).
      intro.
      apply (pigeon_hole ns enum).
      destruct H.
      destruct H3.
      intros n.
      assert (n < size <-> 0 <= n < size).
      omega.
      intro.
      apply (proj2 (H4 n)).
      apply (proj1 H5).
      apply (proj1 (H0 n) H6).
      destruct H.
      omega.
      apply H1.
      destruct H.
      destruct H3.
      assert (not (length ns < size)).
      intro.
      apply (pigeon_hole enum ns).
      intros n.
      assert (n < size <-> 0 <= n < size).
      omega.
      intro.
      apply (proj2 (H0 n)).
      apply (proj2 H6).
      apply (proj1 (H4 n) H7).
      omega.
      apply H3.
      omega.
    Qed.
  End Nat.
End ListTheory.

Module GraphTheory.

  Record Graph : Type :=
    { Vertex : Set
    ; Edge : Vertex -> Vertex -> Prop
    }
  .

  Variable g : Graph.

  Section General.

    Import ListNotations.

    Import ListTheory.

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
      destruct (classic (In next visiteds)).
      apply (subpath_exist visiteds beg cur H1 next H2).
      exists (next :: visiteds).
      apply (PS beg cur next visiteds H H2 H1).
    Qed.

    Proposition visiteds_are_all_distinct :
      forall visiteds : list g.(Vertex),
      forall beg cur : g.(Vertex),
      Path visiteds beg cur ->
      AreAllDistinct visiteds.
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

    Variable size : nat.

    Variable can_enum_vertices : (exists vertices : list g.(Vertex), AreAllDistinct vertices /\ length vertices = size /\ (forall v : g.(Vertex), In v vertices)).

    Proposition len_path_leq_size : 
      forall visiteds : list g.(Vertex),
      forall beg cur : g.(Vertex),
      Path visiteds beg cur ->
      length visiteds <= size.
    Proof.
      intros visiteds beg cur.
      intro.
      destruct can_enum_vertices as [vertices].
      assert (not (length visiteds > size)).
        intro.
        destruct H0.
        destruct H2.
        apply (pigeon_hole visiteds vertices).
          intros v.
          intro.
          apply (H3 v).
          omega.
          apply (visiteds_are_all_distinct visiteds beg cur H).
      omega.
    Qed.
  End Finite.
End GraphTheory.