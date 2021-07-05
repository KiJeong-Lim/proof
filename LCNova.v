Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.

Global Create HintDb my_hints.

Module MyStructures.

  Import ListNotations.

  Definition ensemble : Type -> Type :=
    fun A : Type =>
    arrow A Prop
  .

  Definition member {A : Type} : A -> ensemble A -> Prop :=
    fun x : A =>
    fun xs : ensemble A =>
    xs x
  .

  Global Hint Unfold member : my_hints.

  Global Notation "x '\in' xs" := (member x xs) (at level 70, no associativity) : type_scope.

  Definition isSubsetOf {A : Type} : ensemble A -> ensemble A -> Prop :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    forall x : A,
    member x xs1 ->
    member x xs2
  .

  Global Hint Unfold isSubsetOf : my_hints.

  Global Notation "xs1 '\subseteq' xs2" := (isSubsetOf xs1 xs2) (at level 70, no associativity) : type_scope.

  Inductive finite {A : Type} : list A -> ensemble A :=
  | in_finite {x : A} :
    forall xs : list A,
    In x xs ->
    member x (finite xs)
  .

  Global Hint Constructors finite : my_hints.

  Definition empty {A : Type} : ensemble A :=
    finite []
  .

  Lemma in_empty_iff {A : Type} :
    forall x : A,
    member x empty <-> False.
  Proof with eauto with *.
    intros x.
    split...
    intros H.
    inversion H; subst...
  Qed.

  Global Hint Resolve in_empty_iff : my_hints.

  Definition singleton {A : Type} : A -> ensemble A :=
    fun x : A => finite [x]
  .

  Lemma in_singleton_iff {A : Type} :
    forall x : A,
    forall x1 : A,
    member x (singleton x1) <-> x1 = x.
  Proof with eauto with *.
    intros x x1.
    split.
    - intros H.
      inversion H; subst.
      destruct H0 as [H0 | []]...
    - intros H.
      subst...
  Qed.

  Global Hint Resolve in_singleton_iff : my_hints.

  Inductive unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
  | in_unions {x : A} :
    forall xs : ensemble A,
    forall xss : ensemble (ensemble A),
    member x xs ->
    member xs xss ->
    member x (unions xss)
  .

  Global Hint Constructors unions : my_hints.

  Definition union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    unions (finite [xs1; xs2])
  .

  Lemma in_union_iff {A : Type} :
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    forall x : A,
    member x (union xs1 xs2) <-> (member x xs1 \/ member x xs2).
  Proof with eauto with *.
    intros xs1 xs2 x.
    split.
    - intros H.
      inversion H; subst.
      inversion H1; subst.
      destruct H2 as [H2 | [H2 | []]]; subst...
    - intros [H | H]; [apply (in_unions xs1) | apply (in_unions xs2)]...
  Qed.

  Global Hint Resolve in_union_iff : my_hints.

  Inductive intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
  | in_intersection {x : A} :
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    member x xs1 ->
    member x xs2 ->
    member x (intersection xs1 xs2)
  .

  Global Hint Constructors intersection : my_hints.

  Inductive full {A : Type} : ensemble A :=
  | in_full {x : A} :
    member x full
  .

  Global Hint Constructors full : my_hints.

  Inductive image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
  | in_image {x : A} :
    forall f : A -> B,
    forall xs : ensemble A,
    member x xs ->
    member (f x) (image f xs)
  .

  Global Hint Constructors image : my_hints.

  Inductive preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
  | in_preimage {x : A} :
    forall f : A -> B,
    forall ys : ensemble B,
    member (f x) ys ->
    member x (preimage f ys)
  .

  Global Hint Constructors preimage : my_hints.

  Definition nonempty {A : Type} : ensemble A -> Prop :=
    fun xs : ensemble A =>
    exists x : A, member x xs
  .

  Global Hint Unfold nonempty : my_hints.

  Class isSetoid (A : Type) : Type :=
    { eqProp : A -> A -> Prop
    ; Setoid_requiresEquivalence :> Equivalence eqProp
    }
  .

  Global Notation "x == y" := (eqProp x y) (at level 70, no associativity) : type_scope.

  Lemma Setoid_refl {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    x1 == x1.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_refl : my_hints.

  Lemma Setoid_sym {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x2 == x1.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_sym : my_hints.

  Lemma Setoid_trans {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 == x2 ->
    x2 == x3 ->
    x1 == x3.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_trans : my_hints.

  Definition preservesSetoid {A : Type} {B : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    f x1 == f x2
  .

  Global Hint Unfold preservesSetoid : my_hints.

  Global Program Instance arrow_isSetoid {A : Type} {B : Type} (B_requiresSetoid : isSetoid B) : isSetoid (A -> B) :=
    { eqProp :=
      fun f1 : A -> B =>
      fun f2 : A -> B =>
      forall x : A,
      f1 x == f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Global Program Instance ensemble_isSetoid {A : Type} : isSetoid (ensemble A) :=
    { eqProp :=
      fun X1 : ensemble A =>
      fun X2 : ensemble A =>
      forall x : A,
      member x X1 <-> member x X2
    }
  .

  Next Obligation with firstorder with my_hints.
    split...
  Qed.

  Class isPoset (A : Type) : Type :=
    { leProp : A -> A -> Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; Poset_requiresPreOrder :> PreOrder leProp
    ; Poset_requiresPartialOrder :> PartialOrder eqProp leProp
    }
  .

  Global Notation "x =< y" := (leProp x y) (at level 70, no associativity) : type_scope.

  Lemma Poset_refl {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    x1 =< x1.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_refl : my_hints.

  Lemma Poset_refl1 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x1 =< x2.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl1 : my_hints.

  Lemma Poset_refl2 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x2 =< x1.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl2 : my_hints.

  Lemma Poset_asym {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 =< x2 ->
    x2 =< x1 ->
    x1 == x2.
  Proof.
    intros x1 x2 H H0.
    apply Poset_requiresPartialOrder.
    split.
    - apply H.
    - apply H0.
  Qed.

  Global Hint Resolve Poset_asym : my_hints.

  Lemma Poset_trans {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 =< x2 ->
    x2 =< x3 ->
    x1 =< x3.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_trans : my_hints.

  Definition isMonotonicMap {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall x1 : A,
    forall x2 : A,
    x1 =< x2 ->
    f x1 =< f x2
  .

  Global Hint Unfold isMonotonicMap : my_hints.

  Lemma MonotonicMap_preservesSetoid {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} :
    forall f : A -> B,
    isMonotonicMap f ->
    preservesSetoid f.
  Proof with eauto with *.
    unfold isMonotonicMap, preservesSetoid.
    intros f H x1 x2 H0.
    apply Poset_asym...
  Qed.

  Global Hint Unfold MonotonicMap_preservesSetoid : my_hints.

  Definition isSupremum {A : Type} `{A_isPoset : isPoset A} : A -> ensemble A -> Prop :=
    fun sup_X : A =>
    fun X : ensemble A =>
    forall a : A,
    sup_X =< a <-> (forall x : A, member x X -> x =< a)
  .

  Global Hint Unfold isSupremum : my_hints.

  Definition isInfimum {A : Type} `{A_isPoset : isPoset A} : A -> ensemble A -> Prop :=
    fun inf_X : A =>
    fun X : ensemble A =>
    forall a : A,
    a =< inf_X <-> (forall x : A, member x X -> a =< x)
  .

  Global Hint Unfold isInfimum : my_hints.

  Global Program Instance ensemble_isPoset {A : Type} : isPoset (ensemble A) :=
    { leProp := isSubsetOf
    ; Poset_requiresSetoid := ensemble_isSetoid
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder.
    split...
  Qed.

  Class isTopologicalSpace (A : Type) : Type :=
    { isOpen : ensemble A -> Prop
    ; open_for_full :
      isOpen full
    ; open_for_unions :
      forall xss : ensemble (ensemble A),
      (forall xs : ensemble A, member xs xss -> isOpen xs) ->
      isOpen (unions xss)
    ; open_for_intersection :
      forall xs1 : ensemble A,
      forall xs2 : ensemble A,
      isOpen xs1 ->
      isOpen xs2 ->
      isOpen (intersection xs1 xs2)
    }
  .

  Global Hint Resolve open_for_full : my_hints.

  Global Hint Resolve open_for_unions : my_hints.

  Global Hint Resolve open_for_intersection : my_hints.

  Definition isClosed {A : Type} `{A_isTopologicalSpace : isTopologicalSpace A} : ensemble A -> Prop :=
    fun X : ensemble A =>
    isOpen (fun x : A => ~ member x X)
  .

  Global Hint Unfold isClosed : my_hints.

  Definition isContinuousMap {A : Type} {B : Type} `{A_isTopologicalSpace : isTopologicalSpace A} `{B_isTopologicalSpace : isTopologicalSpace B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall ys : ensemble B,
    isOpen ys ->
    isOpen (preimage f ys)
  .

  Global Hint Unfold isContinuousMap : my_hints.

End MyStructures.

Module DomainTheory.

  Import ListNotations.

  Import MyStructures.

  Lemma isSupremum_upperbound {D : Type} `{D_isPoset : isPoset D} :
    forall sup_X : D,
    forall X : ensemble D,
    isSupremum sup_X X ->
    forall x : D,
    member x X ->
    x =< sup_X.
  Proof with eauto with *.
    intros sup_X X H x H0.
    apply H...
  Qed.

  Global Hint Resolve isSupremum_upperbound : my_hints.

  Lemma isSupremum_isSubsetOf {D : Type} `{D_isPoset : isPoset D} :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    isSubsetOf X1 X2 ->
    forall sup_X1 : D,
    isSupremum sup_X1 X1 ->
    forall sup_X2 : D,
    isSupremum sup_X2 X2 ->
    sup_X1 =< sup_X2.
  Proof with eauto with *.
    intros X1 X2 H sup_X1 H0 sup_X2 H1.
    apply H0...
  Qed.

  Global Hint Resolve isSupremum_isSubsetOf : my_hints.

  Lemma isSupremum_ext {D : Type} `{D_isPoset : isPoset D} :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    (forall x : D, member x X1 <-> member x X2) ->
    forall sup_X1 : D,
    isSupremum sup_X1 X1 ->
    forall sup_X2 : D,
    isSupremum sup_X2 X2 <-> sup_X1 == sup_X2.
  Proof with eauto with *.
    intros X1 X2 H sup_X1 H0 sup_X2.
    assert (claim1 := fun x : D => fun H1 : member x X1 => proj1 (H x) H1).
    assert (claim2 := fun x : D => fun H1 : member x X2 => proj2 (H x) H1).
    split...
    intros H1.
    intros x.
    split.
    - intros H2 x' H3.
      apply H0...
    - intros H2.
      enough (H3 : sup_X1 =< x) by apply (Poset_trans sup_X2 sup_X1 x (Poset_refl2 sup_X1 sup_X2 H1) H3).
      apply H0...
  Qed.

  Global Hint Resolve isSupremum_ext : my_hints.

  Lemma isSupremum_unique {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup1 : D,
    isSupremum sup1 X ->
    forall sup2 : D,
    isSupremum sup2 X <-> sup1 == sup2.
  Proof with eauto with *.
    intros X sup1 H sup2...
  Qed.

  Global Hint Resolve isSupremum_unique : my_hints.

    Definition image_sup {D : Type} `{D_isPoset : isPoset D} : ensemble (ensemble D) -> ensemble D :=
      fun Xs : ensemble (ensemble D) =>
      fun sup_X : D =>
      exists X : ensemble D, member X Xs /\ isSupremum sup_X X
    .

  Global Hint Unfold image_sup : my_hints.

  Lemma sup_image_sup_isGreaterThan {D : Type} `{D_isPoset : isPoset D} :
    forall Xs : ensemble (ensemble D),
    forall sup : D,
    isSupremum sup (image_sup Xs) ->
    forall X : ensemble D,
    member X Xs ->
    forall sup_X : D,
    isSupremum sup_X X ->
    sup_X =< sup.
  Proof with eauto with *.
    intros Xs sup H X H0 sup_X H1.
    apply H...
  Qed.

  Global Hint Resolve sup_image_sup_isGreaterThan : my_hints.

  Lemma isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs {D : Type} `{D_isPoset : isPoset D} :
    forall Xs : ensemble (ensemble D),
    (forall X : ensemble D, member X Xs -> exists sup_X : D, isSupremum sup_X X) ->
    forall sup : D,
    isSupremum sup (unions Xs) <-> isSupremum sup (image_sup Xs).
  Proof with eauto with *.
    intros Xs H sup.
    split.
    - intros H0 x.
      split.
      + intros H1 x' [X [H2 H3]].
        apply H3...
      + intros H1.
        apply H0.
        intros x' H2.
        inversion H2; subst.
        destruct (H xs H4) as [sup_xs H5].
        apply H5...
        apply H1...
    - intros H0 x.
      split.
      + intros H1 x' H2.
        inversion H2; subst.
        destruct (H xs H4) as [sup_xs H5].
        apply H5...
      + intros H1.
        apply H0.
        intros x' [X [H2 H3]].
        apply H3...
  Qed.

  Global Hint Resolve isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs : my_hints.

  Class isCompleteLattice (D : Type) : Type :=
    { CompleteLattice_requiresPoset :> isPoset D
    ; supremum_always_exists_in_CompleteLattice :
      forall X : ensemble D,
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Global Hint Resolve CompleteLattice_requiresPoset : my_hints.

  Lemma compute_Infimum_in_CompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall X : ensemble D,
    forall inf_X : D,
    isSupremum inf_X (fun d : D => forall x : D, member x X -> d =< x) ->
    isInfimum inf_X X.
  Proof with eauto with *.
    intros X inf_X H d.
    split.
    - intros H0 x H1.
      transitivity inf_X...
      apply H...
    - intros H0.
      apply H...
  Qed.

  Global Hint Resolve compute_Infimum_in_CompleteLattice : my_hints.

  Definition infimum_always_exists_in_CompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall X : ensemble D,
    {inf_X : D | isInfimum inf_X X}.
  Proof.
    intros X.
    destruct (supremum_always_exists_in_CompleteLattice (fun d : D => forall x : D, member x X -> d =< x)) as [inf_X H].
    exists inf_X.
    apply compute_Infimum_in_CompleteLattice, H.
  Defined.

  Lemma unions_isSupremum {A : Type} :
    forall Xs : ensemble (ensemble A),
    isSupremum (unions Xs) Xs.
  Proof with eauto with *.
    intros Xs X.
    split.
    - intros H xs H0.
      transitivity (unions Xs)...
      intros x H1.
      apply (in_unions xs)...
    - intros H x H0.
      inversion H0; subst.
      apply (H xs)...
  Qed.

  Global Instance ensemble_isCompleteLattice {A : Type} : isCompleteLattice (ensemble A) :=
    { CompleteLattice_requiresPoset := ensemble_isPoset
    ; supremum_always_exists_in_CompleteLattice :=
      fun Xs : ensemble (ensemble A) =>
      exist (fun unions_Xs : ensemble A => isSupremum unions_Xs Xs) (unions Xs) (unions_isSupremum Xs)
    }
  .

  Definition monotonic_map {D : Type} {D' : Type} : isPoset D -> isPoset D' -> Type :=
    fun D_requiresPoset : isPoset D =>
    fun D'_requiresPoset : isPoset D' =>
    {f : D -> D' | isMonotonicMap f}
  .

  Global Program Instance MonotonicMap_isSetoid {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isSetoid (monotonic_map D_requiresPoset D'_requiresPoset) :=
    { eqProp :=
      fun f1 : monotonic_map D_requiresPoset D'_requiresPoset =>
      fun f2 : monotonic_map D_requiresPoset D'_requiresPoset =>
      forall x : D,
      proj1_sig f1 x == proj1_sig f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Global Program Instance MonotonicMap_can_be_pointwise_partially_ordered {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isPoset (monotonic_map D_requiresPoset D'_requiresPoset) :=
    { leProp :=
      fun f1 : monotonic_map D_requiresPoset D'_requiresPoset =>
      fun f2 : monotonic_map D_requiresPoset D'_requiresPoset =>
      forall x : D,
      proj1_sig f1 x =< proj1_sig f2 x
    ; Poset_requiresSetoid := MonotonicMap_isSetoid D_requiresPoset D'_requiresPoset
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder with my_hints.
    split...
  Qed.

  Definition supOfMonotonicMaps {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} : ensemble (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice)) -> D -> D' :=
    fun fs : ensemble (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice)) =>
    fun x : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice) => proj1_sig f_i x) fs))
  .

  Lemma supOfMonotonicMaps_isMonotonic {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} :
    forall fs : ensemble (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice)),
    isMonotonicMap (supOfMonotonicMaps fs).
  Proof with eauto with *.
    intros fs x1 x2 H.
    unfold supOfMonotonicMaps.
    destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice)) => proj1_sig f_i x1) fs)) as [sup1 H0].
    destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice)) => proj1_sig f_i x2) fs)) as [sup2 H1].
    simpl.
    apply H0.
    intros x H2.
    inversion H2; subst.
    rename x0 into f_i.
    transitivity (proj1_sig f_i x2).
    - apply (proj2_sig f_i)...
    - apply H1...
      apply (in_image (fun f_i' : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice) => proj1_sig f_i' x2))...
  Qed.

  Lemma supOfMonotonicMaps_isSupremum {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} :
    forall fs : ensemble (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice)),
    isSupremum (exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs)) fs.
  Proof with eauto with *.
    intros fs f.
    split.
    - intros H0 f' H1.
      transitivity (exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs))...
      intros x.
      simpl.
      apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice) => proj1_sig f_i x) fs)))...
      apply (in_image (fun f_i' : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice) => proj1_sig f_i' x))...
    - intros H x.
      simpl.
      apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D' D'_isCompleteLattice) => proj1_sig f_i x) fs)))...
      intros f' H0.
      inversion H0; subst.
      rename x0 into f'.
      apply (H f' H1 x).
  Qed.

  Global Instance MonotonicMaps_on_CompleteLattice_constitute_CompleteLattice {D : Type} {D' : Type} (D_requiresCompleteLattice : isCompleteLattice D) (D'_requiresCompleteLattice : isCompleteLattice D') : isCompleteLattice (monotonic_map (@CompleteLattice_requiresPoset D D_requiresCompleteLattice) (@CompleteLattice_requiresPoset D' D'_requiresCompleteLattice)) :=
    { CompleteLattice_requiresPoset := MonotonicMap_can_be_pointwise_partially_ordered (@CompleteLattice_requiresPoset D D_requiresCompleteLattice) (@CompleteLattice_requiresPoset D' D'_requiresCompleteLattice)
    ; supremum_always_exists_in_CompleteLattice :=
      fun fs : ensemble (monotonic_map (@CompleteLattice_requiresPoset D D_requiresCompleteLattice) (@CompleteLattice_requiresPoset D' D'_requiresCompleteLattice)) =>
      exist _ (exist _ (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs)) (supOfMonotonicMaps_isSupremum fs)
    }
  .

  Definition fixed_points {D : Type} `{D_isPoset : isPoset D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun fix_f : D =>
    fix_f == f fix_f
  .

  Global Hint Unfold fixed_points : my_hints.

  Definition isLeastFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun lfp : D =>
    fun f : D -> D =>
    member lfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> lfp =< fix_f)
  .

  Global Hint Unfold isLeastFixedPoint : my_hints.

  Lemma LeastFixedPointOfPoset {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonicMap f ->
    forall lfp : D,
    isInfimum lfp (fun x : D => f x =< x) ->
    isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H lfp H0.
    split.
    - assert (H1 : f lfp =< lfp).
      { apply H0.
        intros x H1.
        transitivity (f x)...
        apply H...
        transitivity (f x)...
        apply H0...
      }
      apply Poset_asym.
      + apply H0...
      + apply H1.
    - intros fix_f H1.
      apply H0...
  Qed.

  Lemma LeastFixedPointOfCompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D -> D,
    isMonotonicMap f ->
    exists lfp : D, isInfimum lfp (fun x : D => f x =< x) /\ isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H.
    destruct (infimum_always_exists_in_CompleteLattice (fun x : D => f x =< x)) as [lfp H0].
    exists lfp.
    split...
    apply LeastFixedPointOfPoset...
  Qed.

  Definition isGreatestFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun gfp : D =>
    fun f : D -> D =>
    member gfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> fix_f =< gfp)
  .

  Global Hint Unfold isGreatestFixedPoint : my_hints.

  Lemma GreatestFixedPointOfPoset {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonicMap f ->
    forall gfp : D,
    isSupremum gfp (fun x : D => x =< f x) ->
    isGreatestFixedPoint gfp f.
  Proof with eauto with *.
    intros f H gfp H0.
    split.
    - assert (H1 : gfp =< f gfp).
      { apply H0.
        intros x H1.
        transitivity (f x)...
      }
      apply Poset_asym.
      + apply H1.
      + apply H0...
    - intros fix_f H1.
      apply H0...
  Qed.

  Lemma GreatestFixedPointOfCompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D -> D,
    isMonotonicMap f ->
    exists gfp : D, isSupremum gfp (fun x : D => x =< f x) /\ isGreatestFixedPoint gfp f.
  Proof with eauto with *.
    intros f H.
    destruct (supremum_always_exists_in_CompleteLattice (fun x : D => x =< f x)) as [gfp H0].
    exists gfp.
    split...
    apply GreatestFixedPointOfPoset...
  Qed.

  Definition nu {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice), {gfp : D | isGreatestFixedPoint gfp (proj1_sig f)} :=
    fun f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice) =>
    match supremum_always_exists_in_CompleteLattice (fun x : D => x =< proj1_sig f x) with
    | exist _ gfp H => exist _ gfp (GreatestFixedPointOfPoset (proj1_sig f) (proj2_sig f) gfp H)
    end
  .

  Definition or_plus {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : D -> D -> D :=
    fun x1 : D =>
    fun x2 : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))
  .

  Lemma le_or_plus {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2 /\ x2 =< or_plus x1 x2.
  Proof with eauto with *.
    intros x1 x2.
    assert (H : isSupremum (or_plus x1 x2) (finite [x1; x2])) by apply (proj2_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))).
    split...
  Qed.

  Lemma le_or_plus1 {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Defined.

  Global Hint Resolve le_or_plus1 : my_hints.

  Lemma le_or_plus2 {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x2 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Defined.

  Global Hint Resolve le_or_plus2 : my_hints.

  Lemma or_plus_le_iff {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    forall d : D,
    or_plus x1 x2 =< d <-> (x1 =< d /\ x2 =< d).
  Proof with eauto with *.
    intros x1 x2 d.
    assert (H : isSupremum (or_plus x1 x2) (finite [x1; x2])) by apply (proj2_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))).
    split.
    - intros H0.
      split...
    - intros [H0 H1].
      apply H.
      intros x H2.
      inversion H2; subst.
      destruct H3 as [H3 | [H3 | []]]; subst...
  Qed.

  Lemma PrincipleOfTarski {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    forall x : D,
    x =< proj1_sig f x -> x =< proj1_sig (nu f).
  Proof with eauto with *.
    intros f x H.
    unfold nu.
    destruct (supremum_always_exists_in_CompleteLattice (fun x0 : D => x0 =< proj1_sig f x0)) as [gfp H0].
    simpl.
    apply H0...
  Qed.

  Lemma StrongCoinduction {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    forall x : D,
    x =< proj1_sig (nu f) <-> x =< proj1_sig f (or_plus x (proj1_sig (nu f))).
  Proof with eauto with *.
    intros f.
    destruct (proj2_sig (nu f)) as [H H0].
    assert (claim1 : forall x : D, proj1_sig f (proj1_sig (nu f)) =< proj1_sig f (or_plus x (proj1_sig (nu f)))).
    { intros x.
      apply (proj2_sig f).
      apply le_or_plus.
    }
    intros x.
    split.
    - intros H1.
      transitivity (proj1_sig (nu f))...
    - intros H1.
      enough (claim2 : or_plus x (proj1_sig (nu f)) =< proj1_sig f (or_plus x (proj1_sig (nu f)))).
      { transitivity (proj1_sig f (or_plus x (proj1_sig (nu f))))...
        apply PrincipleOfTarski.
        apply (proj2_sig f)... 
      }
      apply or_plus_le_iff...
  Qed.

  Example G_f_aux_isMonotonic {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    forall x : D,
    isMonotonicMap (fun y : D => proj1_sig f (or_plus x y)).
  Proof with eauto with *.
    intros f d x1 x2 H.
    apply (proj2_sig f).
    apply or_plus_le_iff.
    split.
    - apply le_or_plus.
    - transitivity x2...
  Qed.

  Definition G_f {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice) -> (D -> D) :=
    fun f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice) =>
    let G_f_aux : D -> D -> D := fun x : D => fun y : D => proj1_sig f (or_plus x y) in
    fun x : D =>
    proj1_sig (nu (exist _ (G_f_aux x) (G_f_aux_isMonotonic f x)))
  .

  Lemma G_f_isMonotoinc {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    isMonotonicMap (G_f f).
  Proof with eauto with *.
    intros f.
    set (G_f_aux := fun x : D => fun y : D => proj1_sig f (or_plus x y)).
    intros x1 x2 H.
    apply StrongCoinduction.
    unfold nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus x2 y))) as [gfp2 H0].
    simpl in *.
    assert (claim1 : G_f f x1 == proj1_sig f (or_plus x1 (G_f f x1))) by apply (proj2_sig (nu (exist _ (G_f_aux x1) (G_f_aux_isMonotonic f x1)))).
    transitivity (proj1_sig f (or_plus x1 (G_f f x1)))...
    apply (proj2_sig f).
    transitivity (or_plus x2 (G_f f x1)).
    - apply or_plus_le_iff...
    - apply or_plus_le_iff...
  Qed.

  Definition ParameterizedGreatestFixedpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice) -> monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice) :=
    fun f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice) =>
    exist _ (G_f f) (G_f_isMonotoinc f)
  .

  Lemma ParameterizedGreatestFixedpoint_isMonotonic {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    @isMonotonicMap (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice)) (monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice)) (MonotonicMap_can_be_pointwise_partially_ordered (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice)) (MonotonicMap_can_be_pointwise_partially_ordered (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice)) ParameterizedGreatestFixedpoint.
  Proof with eauto with *.
    intros f1 f2 H x.
    simpl.
    unfold G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f1 (or_plus x y))) as [gfp1 H0].
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f2 (or_plus x y))) as [gfp2 H1].
    simpl.
    apply H0.
    unfold member.
    intros y H2.
    apply H1...
  Qed.

  Definition bot {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : D :=
    proj1_sig (supremum_always_exists_in_CompleteLattice empty)
  .

  Lemma bot_isBottom {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x : D,
    bot =< x.
  Proof.
    intros x.
    apply (proj2_sig (supremum_always_exists_in_CompleteLattice empty)).
    intros x' H.
    inversion H; subst.
    contradiction H0.
  Qed.

  Global Hint Resolve bot_isBottom : my_hints.

  Lemma initialize_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    proj1_sig (nu f) == proj1_sig (ParameterizedGreatestFixedpoint f) bot.
  Proof with eauto with *.
    intros f.
    symmetry.
    unfold ParameterizedGreatestFixedpoint, G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus bot y))) as [gfp1 H].
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f y)) as [gfp2 H0].
    simpl.
    apply Poset_asym.
    - apply H.
      intros x H1.
      apply H0...
      unfold member in *.
      transitivity (proj1_sig f (or_plus bot x)).
      + apply H1.
      + apply (proj2_sig f).
        apply or_plus_le_iff...
    - apply H0.
      intros x H1.
      apply H...
      unfold member in *.
      transitivity (proj1_sig f x).
      + apply H1.
      + apply (proj2_sig f)...
  Qed.

  Lemma unfold_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    forall x : D,
    proj1_sig (ParameterizedGreatestFixedpoint f) x == proj1_sig f (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x)).
  Proof with eauto with *.
    intros f x.
    unfold ParameterizedGreatestFixedpoint.
    simpl.
    unfold G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus x y))) as [gfp1 H].
    simpl.
    assert (claim1 := GreatestFixedPointOfPoset (fun y : D => proj1_sig f (or_plus x y)) (G_f_aux_isMonotonic f x) gfp1 H).
    apply claim1.
  Qed.

  Lemma accumulate_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : monotonic_map (@CompleteLattice_requiresPoset D D_isCompleteLattice) (@CompleteLattice_requiresPoset D D_isCompleteLattice),
    forall x : D,
    forall y : D,
    y =< proj1_sig (ParameterizedGreatestFixedpoint f) x <-> y =< proj1_sig (ParameterizedGreatestFixedpoint f) (or_plus x y).
  Proof with eauto with *.
    unfold ParameterizedGreatestFixedpoint.
    simpl.
    intros f.
    split.
    - intros H.
      transitivity (G_f f x).
      + apply H.
      + apply G_f_isMonotoinc...
    - intros H.
      assert (claim1 : proj1_sig (ParameterizedGreatestFixedpoint f) (or_plus x y) == proj1_sig f (or_plus (or_plus x y) (G_f f (or_plus x y)))) by now apply unfold_cofixpoint.
      assert (claim2 : proj1_sig f (or_plus (or_plus x y) (G_f f (or_plus x y))) =< proj1_sig f (or_plus x (G_f f (or_plus x y)))).
      { apply (proj2_sig f).
        apply or_plus_le_iff.
        split.
        - apply or_plus_le_iff...
        - apply le_or_plus.
      }
      assert (claim3 : G_f f (or_plus x y) =< G_f f x).
      { apply PrincipleOfTarski.
        simpl.
        transitivity (proj1_sig f (or_plus (or_plus x y) (G_f f (or_plus x y))))...
      }
      transitivity (G_f f (or_plus x y))...
  Qed.

(* [PROVE ME] 2021-07-05
\begin{lstlisting}
  Theorem KnasterTarski {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonic f ->
    forall fps : ensemble D,
    isSubsetOf fps (fixed_points f) ->
    {sup_fps : D | isSupremum sup_fps fps}.
\end{lstlisting}
*)

  Definition isDirected {D : Type} `{D_isPoset : isPoset D} : ensemble D -> Prop :=
    fun X : ensemble D =>
    nonempty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ x1 =< x3 /\ x2 =< x3)
  .

  Global Hint Unfold isDirected : my_hints.

  Class isCompletePartialOrder (D : Type) : Type :=
    { CompletePartialOrder_requiresPoset :> isPoset D
    ; bottom_exists : {min_D : D | forall x : D, min_D =< x}
    ; square_up_exists :
      forall X : ensemble D,
      isDirected X ->
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Global Program Instance CompleteLattice_isCompletePartialOrder {D : Type} (D_requiresCompleteLattice : isCompleteLattice D) : isCompletePartialOrder D :=
    { CompletePartialOrder_requiresPoset := CompleteLattice_requiresPoset
    }
  .

  Next Obligation.
    destruct (supremum_always_exists_in_CompleteLattice empty) as [min_D H].
    exists min_D.
    intros x.
    apply H.
    intros x' H0.
    inversion H0; subst.
    inversion H1.
  Defined.

  Next Obligation.
    apply supremum_always_exists_in_CompleteLattice.
  Defined.

  Global Program Instance ScottTopology_isTopologicalSpace {D : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) : isTopologicalSpace D :=
    { isOpen :=
      fun O : ensemble D =>
      (forall x : D, forall y : D, member x O -> x =< y -> member y O) /\ (forall X : ensemble D, isDirected X -> forall sup_X : D, isSupremum sup_X X -> member sup_X O -> nonempty (intersection X O))
    }
  .

  Next Obligation with eauto with *.
    split...
    intros.
    destruct H as [[x H] H2]...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros.
      destruct H0.
      apply (in_unions xs)...
      apply (proj1 (H xs H2) x y)...
    - intros.
      inversion H0; subst.
      inversion H2; subst.
      destruct (proj2 (H xs H6) X H0 sup_X H1 H5) as [x H7].
      inversion H7; subst...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros.
      destruct H3...
    - intros.
      inversion H5; subst.
      destruct (H2 X H3 sup_X H4 H6) as [x1 H8].
      destruct (H1 X H3 sup_X H4 H7) as [x2 H9].
      inversion H3; subst.
      inversion H8; inversion H9; subst.
      destruct (H11 x1 H12 x2 H17) as [x [H14 [H15 H16]]].
      exists x...
  Qed.

End DomainTheory.
