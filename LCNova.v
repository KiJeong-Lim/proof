Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.

Global Create HintDb my_hints.

Module MyStructures.

Class isPoset (A : Type) : Type :=
  { leProp : A -> A -> Prop
  ; Poset_requiresPreOrder :> PreOrder leProp
  ; Poset_requiresPartialOrder :> PartialOrder (@eq A) leProp
  }
.

Global Hint Resolve Poset_requiresPreOrder : my_hints.

Global Hint Resolve Poset_requiresPartialOrder : my_hints.

Global Notation "x =< y" := (leProp x y) (at level 70, no associativity) : type_scope.

Lemma Poset_refl {A : Type} `{A_isPoset : isPoset A} :
  forall x : A,
  x =< x.
Proof.
  apply Poset_requiresPreOrder.
Qed.

Global Hint Resolve Poset_refl : my_hints.

Lemma Poset_refl1 {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  forall x2 : A,
  x1 = x2 ->
  x1 =< x2.
Proof.
  apply Poset_requiresPartialOrder.
Qed.

Global Hint Resolve Poset_refl1 : my_hints.

Lemma Poset_refl2 {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  forall x2 : A,
  x1 = x2 ->
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
  x1 = x2.
Proof.
  intros x1 x2 H H0.
  apply Poset_requiresPartialOrder.
  split; [apply H | apply H0].
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

End MyStructures.

Module MyEnsemble.

Import ListNotations.

Import MyStructures.

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

Global Program Instance ensemble_isPoset {A : Type} : isPoset (ensemble A) :=
  { leProp := isSubsetOf
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Next Obligation with eauto with *.
  intros xs1 xs2.
  split.
  - repeat red.
    split.
    + subst...
    + red.
      subst...
  - intros [H H0].
    apply functional_extensionality.
    intros x.
    apply propositional_extensionality.
    split.
    + apply (H x).
    + apply (H0 x).
Qed.

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

End MyEnsemble.

Module GeneralTopology.

Import ListNotations.

Import MyStructures.

Import MyEnsemble.

Class isTopologicalSpace (X : Type) : Type :=
  { isOpen : ensemble X -> Prop
  ; open_for_full :
    isOpen full
  ; open_for_unions :
    forall xss : ensemble (ensemble X),
    (forall xs : ensemble X, member xs xss -> isOpen xs) ->
    isOpen (unions xss)
  ; open_for_intersection :
    forall xs1 : ensemble X,
    forall xs2 : ensemble X,
    isOpen xs1 ->
    isOpen xs2 ->
    isOpen (intersection xs1 xs2)
  }
.

Global Hint Resolve open_for_full : my_hints.

Global Hint Resolve open_for_unions : my_hints.

Global Hint Resolve open_for_intersection : my_hints.

Definition isContinuousMap {X : Type} {Y : Type} `{X_isTopologicalSpace : isTopologicalSpace X} `{Y_isTopologicalSpace : isTopologicalSpace Y} : (X -> Y) -> Prop :=
  fun f : X -> Y =>
  forall ys : ensemble Y,
  isOpen ys ->
  isOpen (preimage f ys)
.

Global Hint Unfold isContinuousMap : my_hints.

End GeneralTopology.

Module DomainTheory.

Import ListNotations.

Import MyStructures.

Import MyEnsemble.

Import GeneralTopology.

Definition isSupremum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
  fun sup_X : D =>
  fun X : ensemble D =>
  forall d : D,
  sup_X =< d <-> (forall x : D, member x X -> x =< d)
.

Global Hint Unfold isSupremum : my_hints.

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
  isSupremum sup_X2 X2 <-> sup_X1 = sup_X2.
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
  isSupremum sup2 X <-> sup1 = sup2.
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

Class isCompleteLattice (D : Type) : Type :=
  { CompleteLattice_requiresPoset :> isPoset D
  ; supremum_always_exists :
    forall X : ensemble D,
    {sup_X : D | isSupremum sup_X X}
  }
.

Global Hint Resolve supremum_always_exists : my_hints.

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
  ; supremum_always_exists :=
    fun Xs : ensemble (ensemble A) =>
    exist _ (unions Xs) (unions_isSupremum Xs)
  }
.

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
  destruct (supremum_always_exists empty) as [min_D H].
  exists min_D.
  intros x.
  apply H.
  intros x' H0.
  inversion H0; subst.
  inversion H1.
Defined.

Next Obligation.
  apply supremum_always_exists.
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

Definition U {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} : D -> ensemble D :=
  fun x : D =>
  fun z : D =>
  ~ z =< x
.

Global Hint Unfold U : my_hints.

Lemma U_x_isOpen {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} :
  forall x : D,
  isOpen (U x).
Proof with eauto with *.
  intros x.
  assert ( claim1 :
    forall y : D,
    forall z : D,
    member y (U x) ->
    y =< z ->
    member z (U x)
  ).
  { intros y z H H0 H1.
    contradiction H...
  }
  split...
  intros X H sup_X H0 H1.
  inversion H; subst.
  assert (claim2 : ~ (forall x0 : D, x0 =< x \/ ~ member x0 X)).
  { intros H4.
    contradiction H1.
    apply (proj2 (H0 x)).
    intros x0 H5.
    destruct (H4 x0); [apply H6 | contradiction].
  }
  apply not_all_ex_not in claim2.
  destruct claim2 as [x1 H4].
  exists x1.
  apply not_or_and in H4.
  destruct H4 as [H4 H5].
  apply NNPP in H5...
Qed.

Definition characterization_of_ContinuousMap_on_cpos {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D -> D') -> Prop :=
  fun f : D -> D' =>
  forall X : ensemble D,
  isDirected X ->
  let Y : ensemble D' := image f X in
  exists sup_X : D, exists sup_Y : D', isSupremum sup_X X /\ isSupremum sup_Y Y /\ f sup_X = sup_Y
.

Lemma ContinuousMaps_on_cpos_are_always_monotonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall f : D -> D',
  isContinuousMap f ->
  forall x1 : D,
  forall x2 : D,
  x1 =< x2 ->
  f x1 =< f x2.
Proof with eauto with *.
  intros f H x1 x2 H0.
  apply NNPP.
  intros H1.
  assert (H2 : member (f x1) (U (f x2))) by now unfold U.
  assert (H3 : member x1 (preimage f (U (f x2)))) by now constructor.
  assert (H4 : isOpen (preimage f (U (f x2)))) by now apply H, U_x_isOpen.
  assert (H5 : member x2 (preimage f (U (f x2)))) by now apply (proj1 H4 x1 x2).
  enough (H6 : member (f x2) (U (f x2)))...
  inversion H5...
Qed.

Lemma ContinuousMaps_preservesDirected {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall f : D -> D',
  isContinuousMap f ->
  forall X : ensemble D,
  isDirected X ->
  isDirected (image f X).
Proof with eauto with *.
  intros f H X H0.
  destruct H0 as [H0 H1].
  assert (H2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMaps_on_cpos_are_always_monotonic.
  split.
  - destruct H0 as [x0 H0]...
  - intros y1 H3 y2 H4.
    inversion H3; inversion H4; subst.
    rename x into x1, x0 into x2.
    destruct (H1 x1 H5 x2 H9) as [x3 [H6 [H7 H8]]].
    exists (f x3).
    repeat split...
Qed.

Lemma ContinuousMaps_preservesSupremum {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall f : D -> D',
  isContinuousMap f ->
  forall X : ensemble D,
  isDirected X ->
  forall sup_X : D,
  isSupremum sup_X X ->
  isDirected (image f X) ->
  {sup_Y : D' | isSupremum sup_Y (image f X) /\ f sup_X = sup_Y}.
Proof with eauto with *.
  intros f H X H0 sup_X H1 H2.
  set (Y := image f X).
  assert (H3 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMaps_on_cpos_are_always_monotonic.
  destruct (square_up_exists Y H2) as [sup_Y H4].
  exists sup_Y.
  assert (claim1 : sup_Y =< f sup_X).
  { apply H4.
    intros y H5.
    inversion H5; subst.
    apply H3, H1...
  }
  assert (claim2 : f sup_X =< sup_Y).
  { apply NNPP.
    intros H5.
    assert (H6 : member (f sup_X) (U sup_Y)) by now unfold U.
    assert (H7 : member sup_X (preimage f (U sup_Y))) by now constructor.
    assert (H8 : isOpen (preimage f (U sup_Y))) by now apply H, U_x_isOpen.
    destruct H8.
    destruct (H9 X H0 sup_X H1 H7) as [x1 H10].
    inversion H10; subst.
    inversion H12; subst.
    contradiction H13...
  }
  split...
Qed.

Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall f : D -> D',
  isContinuousMap f <-> characterization_of_ContinuousMap_on_cpos f.
Proof with eauto with *.
  assert (claim1 : forall f : D -> D', isContinuousMap f -> forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by apply ContinuousMaps_on_cpos_are_always_monotonic.
  split.
  - intros H X H0.
    inversion H0; subst.
    set (Y := image f X).
    assert (H3 : isDirected Y) by now apply ContinuousMaps_preservesDirected.
    destruct (square_up_exists X H0) as [sup_X H4].
    exists sup_X.
    destruct (ContinuousMaps_preservesSupremum f H X H0 sup_X H4 H3) as [sup_Y H5].
    exists sup_Y...
  - intros H.
    assert (claim2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2).
    { intros x1 x2 H0.
      set (X := finite [x1; x2]).
      set (Y := image f X).
      assert (H1 : isSupremum x2 X).
      { intros x.
        split.
        - intros H1 x' H2.
          inversion H2; subst.
          destruct H3 as [H3 | [H3 | []]]...
        - intros H1...
      }
      assert (H2 : isDirected X).
      { split.
        - exists x1...
        - intros x1' H2 x2' H3.
          exists x2.
          enough (x1' =< x2 /\ x2' =< x2)...
      }
      destruct (H X H2) as [sup_X H3].
      destruct H3 as [sup_Y [H3 [H4 H5]]].
      assert (H6 : sup_X = x2) by now apply (isSupremum_unique X).
      subst...
    }
    intros O H0.
    split.
    + intros x1 x2 H1 H2.
      inversion H1; subst.
      constructor.
      apply (proj1 H0 (f x1) (f x2))...
    + intros X H1 sup_X H2 H3.
      destruct (H X H1) as [sup_X' [sup_Y [H4 [H5 H6]]]].
      assert (H7 : sup_X = sup_X') by now apply (isSupremum_unique X).
      subst sup_X' sup_Y.
      assert (H8 : member (f sup_X) O) by now inversion H3; subst.
      assert (H9 : isDirected (image f X)).
      { destruct H1 as [[x1_0 H1] H6].
        split.
        - exists (f x1_0)...
        - intros y1 H10 y2 H11.
          inversion H10; subst.
          inversion H11; subst.
          rename x into x1, x0 into x2.
          destruct (H6 x1 H7 x2 H9) as [x3 [H12 [H13 H14]]].
          exists (f x3).
          repeat split...
      }
      assert (H10 : nonempty (intersection (image f X) O)).
      { apply (proj2 H0 (image f X) H9 (f sup_X))...
      }
      destruct H10 as [y1 H10].
      inversion H10; subst.
      inversion H6; subst.
      exists x...
Qed.

Local Program Instance DirectProductOfTwoPosets_isPoset {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isPoset (D * D') :=
  { leProp :=
    fun p1 : (D * D') =>
    fun p2 : (D * D') =>
    fst p1 =< fst p2 /\ snd p1 =< snd p2
  }
.

Next Obligation with eauto with *.
  split.
  - intros [x1 y1]...
  - intros [x1 y1] [x2 y2] [x3 y3] [H H0] [H1 H2]...
Qed.

Next Obligation with eauto with *.
  split.
  - intros H.
    subst.
    repeat red.
    repeat split...
  - intros [[H H0] [H1 H2]].
    apply injective_projections...
Qed.

Inductive getFsts {D : Type} {D' : Type} : ensemble (D * D') -> ensemble D :=
| in_getFsts {ps : ensemble (D * D')} :
  forall x : D,
  forall x' : D',
  member (x, x') ps ->
  member x (getFsts ps)
.

Global Hint Constructors getFsts : domain_theory_hints.

Inductive getSnds {D : Type} {D' : Type} : ensemble (D * D') -> ensemble D' :=
| in_getSnds {ps : ensemble (D * D')} :
  forall x : D,
  forall x' : D',
  member (x, x') ps ->
  member x' (getSnds ps)
.

Global Hint Constructors getSnds : domain_theory_hints.

Program Instance DirectProductOfTwoCompletePartialOrders_isCompletePartialOrder {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isCompletePartialOrder (D * D') :=
  { CompletePartialOrder_requiresPoset := DirectProductOfTwoPosets_isPoset (@CompletePartialOrder_requiresPoset D D_requiresCompletePartialOrder) (@CompletePartialOrder_requiresPoset D' D'_requiresCompletePartialOrder)
  }
.

Next Obligation.
  destruct (@bottom_exists D D_requiresCompletePartialOrder) as [bot_D H].
  destruct (@bottom_exists D' D'_requiresCompletePartialOrder) as [bot_D' H0].
  exists (bot_D, bot_D').
  intros [d d'].
  split; [apply H | apply H0].
Defined.

Next Obligation.
  assert (claim1 : isDirected (getFsts X)).
  { destruct H as [H H0].
    split.
    - destruct H as [[d0 d0'] H].
      exists d0.
      apply (in_getFsts d0 d0' H).
    - intros d1 H1 d2 H2.
      inversion H1; subst.
      inversion H2; subst.
      rename x' into d1', x'0 into d2'.
      destruct (H0 (d1, d1') H3 (d2, d2') H4) as [[d3 d3'] [H5 [[H6 H7] [H8 H9]]]].
      exists d3.
      split.
      + apply (in_getFsts d3 d3' H5).
      + split; [apply H6 | apply H8].
  }
  assert (claim2 : isDirected (getSnds X)).
  { destruct H as [H H0].
    split.
    - destruct H as [[d0 d0'] H].
      exists d0'.
      apply (in_getSnds d0 d0' H).
    - intros d1' H1 d2' H2.
      inversion H1; subst.
      inversion H2; subst.
      rename x into d1, x0 into d2.
      destruct (H0 (d1, d1') H3 (d2, d2') H4) as [[d3 d3'] [H5 [[H6 H7] [H8 H9]]]].
      exists d3'.
      split.
      + apply (in_getSnds d3 d3' H5).
      + split; [apply H7 | apply H9].
  }
  destruct (@square_up_exists D D_requiresCompletePartialOrder (getFsts X) claim1) as [sup_X1 H0].
  destruct (@square_up_exists D' D'_requiresCompletePartialOrder (getSnds X) claim2) as [sup_X2 H1].
  exists (sup_X1, sup_X2).
  intros [d d'].
  split.
  - intros H2 [x x'] H3.
    split.
    + apply H0.
      * apply (proj1 H2).
      * apply (in_getFsts x x' H3).
    + apply H1.
      * apply (proj2 H2).
      * apply (in_getSnds x x' H3).
  - intros H2.
    split.
    + apply H0.
      intros x H3.
      inversion H3; subst.
      apply (proj1 (H2 (x, x') H4)).
    + apply H1.
      intros x' H3.
      inversion H3; subst.
      apply (proj2 (H2 (x, x') H4)).
Defined.

Local Notation "D1 ~> D2" := ({f : D1 -> D2 | isContinuousMap f}) (at level 70, no associativity) : type_scope.

Definition ContinuousMap_is_continuous {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : forall f : D ~> D', isContinuousMap (proj1_sig f) :=
  fun f : D ~> D' => proj2_sig f
.

Global Hint Resolve ContinuousMap_is_continuous : my_hints.

Lemma squigarrows_are_the_same_iff {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall f1 : D ~> D',
  forall f2 : D ~> D',
  (forall x : D, proj1_sig f1 x = proj1_sig f2 x) ->
  f1 = f2.
Proof with eauto.
  intros f1 f2 H.
  enough (claim1 : proj1_sig f1 = proj1_sig f2) by apply (eq_sig f1 f2 claim1), proof_irrelevance.
  apply functional_extensionality...
Qed.

Global Hint Resolve squigarrows_are_the_same_iff : my_hints.

Global Program Instance squigarrow_isPoset {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isPoset (D ~> D') :=
  { leProp :=
    fun f1 : D ~> D' =>
    fun f2 : D ~> D' =>
    forall x : D,
    proj1_sig f1 x =< proj1_sig f2 x
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Next Obligation with eauto with *.
  split.
  - intros H.
    subst.
    split; intros x...
  - intros [H H0]...
Qed.

Lemma sup_of_squigarrow_is_well_defined {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall fs : ensemble (D ~> D'),
  isDirected fs ->
  forall x : D,
  isDirected (image (fun f : D ~> D' => proj1_sig f x) fs).
Proof with eauto with *.
  intros fs [H H0] x.
  split.
  - destruct H as [f0].
    exists (proj1_sig f0 x).
    apply (in_image (fun f : D ~> D' => proj1_sig f x))...
  - intros y1 H1 y2 H2.
    inversion H1; subst.
    inversion H2; subst.
    rename x0 into f1, x1 into f2.
    destruct (H0 f1 H3 f2 H4) as [f3 [H5 [H6 H7]]].
    exists (proj1_sig f3 x).
    repeat split...
    apply (in_image (fun f : D ~> D' => proj1_sig f x))...
Qed.

Lemma sup_of_set_of_squigarrows_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall fs : ensemble (D ~> D'),
  forall fs_isDirected : isDirected fs,
  let f : D -> D' := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs fs_isDirected x)) in
  isContinuousMap f.
Proof with eauto with *.
  intros fs H f.
  apply the_main_reason_for_introducing_ScottTopology.
  intros X H0 Y.
  destruct (square_up_exists X H0) as [sup_X H1].
  exists sup_X, (f sup_X).
  assert ( claim1 :
    forall f_i : D ~> D',
    member f_i fs ->
    isSupremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
  ).
  { intros f_i H2.
    assert (H3 : isContinuousMap (proj1_sig f_i))...
    assert (H4 : characterization_of_ContinuousMap_on_cpos (proj1_sig f_i)) by now apply the_main_reason_for_introducing_ScottTopology.
    destruct (H4 X H0) as [sup_X' [sup_Y' [H5 [H6 H7]]]].
    assert (H8 : sup_X' = sup_X) by now apply (isSupremum_unique X).
    subst...
  }
  assert (claim2 : isSupremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs) (sup_of_squigarrow_is_well_defined fs H sup_X))).
  assert (claim3 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs))).
  { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs.
    - intros ys H2.
      inversion H2; subst.
      rename x into f_i.
      exists (proj1_sig f_i sup_X)...
    - intros y.
      split.
      + intros H2 y' [ys [H3 H4]].
        inversion H3; subst.
        rename x into f_i.
        assert (H6 := claim1 f_i H5).
        assert (H7 : y' = proj1_sig f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X)).
        transitivity (proj1_sig f_i sup_X)...
        apply claim2...
        apply (in_image (fun f_i0 : D ~> D' => proj1_sig f_i0 sup_X))...
      + intros H2.
        apply claim2.
        intros y' H3.
        inversion H3; subst.
        rename x into f_i.
        apply H2.
        exists (image (fun x : D => proj1_sig f_i x) X).
        split...
        apply (in_image (fun f_i0 : D ~> D' => image (fun x : D => proj1_sig f_i0 x) X))...
  }
  assert (claim4 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
  { enough (H2 : forall x' : D', member x' (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs)) <-> member x' (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))) by now apply (proj2 (isSupremum_ext _ _ H2 _ claim3 _) eq_refl).
    intros y.
    split.
    - intros H2.
      inversion H2; subst.
      rename xs into ys.
      inversion H4; subst.
      rename x into f_i.
      inversion H3; subst.
      apply (in_unions (image (fun f_i' : D ~> D' => proj1_sig f_i' x) fs)).
      + apply (in_image (fun f_i' : D ~> D' => proj1_sig f_i' x))...
      + apply (in_image (fun x0 : D => image (fun f_i0 : D ~> D' => proj1_sig f_i0 x0) fs))...
    - intros H2.
      inversion H2; subst.
      rename xs into ys.
      inversion H4; subst.
      inversion H3; subst.
      rename x0 into f_i.
      apply (in_unions (image (fun x' : D => proj1_sig f_i x') X)).
      + apply (in_image (fun x' : D => proj1_sig f_i x'))...
      + apply (in_image (fun f_i0 : D ~> D' => image (fun x0 : D => proj1_sig f_i0 x0) X))...
  }
  assert (claim5 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
  { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
    intros ys H2.
    inversion H2; subst.
    exists (f x).
    intros y.
    split.
    - intros H4 y' H5.
      inversion H5; subst.
      rename x0 into f_i.
      apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x)))...
    - intros H4.
      assert (H5 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
      apply H5...
  }
  assert (claim6 : isSupremum (f sup_X) (image f X)).
  { intros y.
    split.
    - intros H2 y' H3.
      inversion H3; subst.
      apply claim5...
      exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs).
      split.
      + apply (in_image (fun x0 : D => image (fun f_i : D ~> D' => proj1_sig f_i x0) fs))...
      + apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
    - intros H2.
      apply claim5.
      intros y' [ys [H3 H4]].
      inversion H3; subst.
      assert (H6 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
      assert (H7 : y' = f x) by now apply (isSupremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)).
      transitivity (f x)...
  }
  split...
Qed.

Global Program Instance squigarrow_isCompletePartialOrder {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isCompletePartialOrder (D ~> D') :=
  { CompletePartialOrder_requiresPoset := squigarrow_isPoset D_requiresCompletePartialOrder D'_requiresCompletePartialOrder
  }
.

Next Obligation.
  set (bot := fun _ : D => proj1_sig bottom_exists).
  assert (claim1 : isContinuousMap bot).
  { intros Y [H H0].
    split.
    - intros x1 x2 H1 H2.
      inversion H1; subst.
      apply (in_preimage bot).
      apply (H (bot x1) (bot x2) H3 (Poset_refl (proj1_sig bottom_exists))).
    - intros X [[x_0 H1] H2] sup_X H3 H4.
      inversion H4; subst.
      exists x_0.
      constructor.
      + apply H1.
      + apply (in_preimage bot).
        apply (H (bot sup_X) (bot x_0) H5).
        apply Poset_refl.
  }
  exists (exist _ bot claim1).
  simpl.
  intros f x.
  apply (proj2_sig bottom_exists).
Defined.

Next Obligation.
  rename X into fs, H into fs_isDirected.
  set (sup_fs := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs fs_isDirected x))).
  exists (exist _ sup_fs (sup_of_set_of_squigarrows_exists_if_it_is_directed fs fs_isDirected)).
  assert (claim1 : forall x : D, isSupremum (sup_fs x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (fun x : D => proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs fs_isDirected x))).
  intros f.
  simpl.
  split.
  - intros H f' H0 x.
    apply (claim1 x).
    + apply H.
    + apply (in_image (fun f_i : D ~> D' => proj1_sig f_i x)).  
      apply H0.
  - intros H x.
    apply (claim1 x).
    intros f' H0.
    inversion H0; subst.
    rename x0 into f'.
    apply (H f').
    apply H1.
Defined.

Lemma separately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isCompletePartialOrder : isCompletePartialOrder D1} `{D2_isCompletePartialOrder : isCompletePartialOrder D2} `{D3_isCompletePartialOrder : isCompletePartialOrder D3} :
  forall f : D1 * D2 -> D3,
  ((forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2))) /\ (forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)))) <-> isContinuousMap f.
Proof with eauto with *.
  intros f.
  split.
  - intros [H H0].
    apply the_main_reason_for_introducing_ScottTopology.
    intros X H1 Y.
    destruct (square_up_exists X H1) as [[sup_X1 sup_X2] H2].
    set (X1 := getFsts X).
    set (X2 := getSnds X).
    exists (sup_X1, sup_X2), (f (sup_X1, sup_X2)).
    assert (claim1 : isDirected X1).
    { destruct H1 as [[[x1_0 x2_0] H1] H3].
      split.
      - exists x1_0.
        apply (in_getFsts x1_0 x2_0)...
      - intros x1_1 H4 x1_2 H5.
        inversion H4; subst.
        inversion H5; subst.
        rename x' into x2_1, x'0 into x2_2.
        destruct (H3 (x1_1, x2_1) H6 (x1_2, x2_2) H7) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
        exists x3_1.
        split...
        apply (in_getFsts x3_1 x3_2)...
    }
    assert (claim2 : isDirected X2).
    { destruct H1 as [[[x1_0 x2_0] H1] H3].
      split.
      - exists x2_0.
        apply (in_getSnds x1_0 x2_0)...
      - intros x2_1 H4 x2_2 H5.
        inversion H4; subst.
        inversion H5; subst.
        rename x into x1_1, x0 into x1_2.
        destruct (H3 (x1_1, x2_1) H6 (x1_2, x2_2) H7) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
        exists x3_2.
        split...
        apply (in_getSnds x3_1 x3_2)...
    }
    assert ( claim3 :
      forall x1 : D1,
      exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremum sup_X2_x1 X2 /\ isSupremum sup_f_X2_x1 (image (fun x2 : D2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) = sup_f_X2_x1
    ).
    { intros x1.
      apply (the_main_reason_for_introducing_ScottTopology (fun x2 : D2 => f (x1, x2)))...
    }
    assert ( claim4 :
      forall x2 : D2,
      exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremum sup_X1_x2 X1 /\ isSupremum sup_f_X1_x2 (image (fun x1 : D1 => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) = sup_f_X1_x2
    ).
    { intros x2.
      apply (the_main_reason_for_introducing_ScottTopology (fun x1 : D1 => f (x1, x2)))...
    }
    assert (XXX : isSupremum sup_X1 X1 /\ isSupremum sup_X2 X2).
    { destruct (square_up_exists X1 claim1) as [sup_X1' H3].
      destruct (square_up_exists X2 claim2) as [sup_X2' H4].
      assert (H5 : isSupremum (sup_X1', sup_X2') X).
      { intros [x1 x2].
        split.
        - intros [H5 H6] [x1' x2'] H7.
          simpl in *.
          split.
          + apply H3...
            apply (in_getFsts x1' x2')...
          + apply H4...
            apply (in_getSnds x1' x2')...
        - intros H5.
          split.
          + apply H3.
            intros x1' H6.
            inversion H6; subst.
            rename x' into x2'.
            apply (proj1 (H5 (x1', x2') H7)).
          + apply H4.
            intros x2' H6.
            inversion H6; subst.
            rename x into x1'.
            apply (proj2 (H5 (x1', x2') H7)).
        }
      assert (H6 : (sup_X1, sup_X2) = (sup_X1', sup_X2')) by now apply (isSupremum_unique X).
      inversion H6; subst.
      simpl in *.
      split...
    }
    destruct XXX as [claim5 claim6].
    assert (claim7 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
    { destruct (claim3 sup_X1) as [sup_X2_x1 [sup_f_X1_x2 [H3 [H4 H5]]]].
      assert (H6 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2) <-> sup_f_X1_x2 = f (sup_X1, sup_X2)) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder)).
      apply H6.
      transitivity (f (sup_X1, sup_X2_x1)).
      - symmetry...
      - enough (H7 : sup_X2_x1 = sup_X2) by congruence.
        apply (isSupremum_unique X2)...
    }
    assert ( claim8 :
      forall x2 : D2,
      member x2 X2 ->
      isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)
    ).
    { intros x2 H3.
      destruct (claim4 x2) as [sup_X1' [sup_f_X1_x2' [H4 [H5 H6]]]].
      assert (H7 : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1) <-> sup_f_X1_x2' = f (sup_X1, x2)) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder)).
      apply H7.
      transitivity (f (sup_X1', x2)).
      - symmetry...
      - enough (H8 : sup_X1' = sup_X1) by congruence.
        apply (isSupremum_unique X1)...
    }
    assert (claim9 : isSupremum (f (sup_X1, sup_X2)) (image_sup (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { intros y.
      split.
      - intros H3 y' [ys [H4 H5]].
        inversion H4; subst.
        rename x into x2.
        assert (H7 : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)) by now apply claim8.
        assert (H8 : y' = (f (sup_X1, x2))) by now apply (isSupremum_unique (image (fun x1 : D1 => f (x1, x2)) X1)).
        assert (H9 : f (sup_X1, x2) =< f (sup_X1, sup_X2)).
        { apply (ContinuousMaps_on_cpos_are_always_monotonic (fun x2' : D2 => f (sup_X1, x2')) (H sup_X1)).
          apply claim6...
        }
        transitivity (f (sup_X1, x2))...
      - intros H7.
        apply claim7.
        intros y' H8.
        inversion H8; subst.
        rename x into x2.
        apply H7...
        exists (image (fun x1 : D1 => f (x1, x2)) X1).
        split.
        + apply (in_image (fun x0 : D2 => image (fun x1 : D1 => f (x1, x0)) X1))...
        + apply claim8...
    }
    assert (claim10 : isSupremum (f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
      intros ys H3.
      inversion H3; subst.
      rename x into x2.
      exists (f (sup_X1, x2))...
    }
    assert (claim11 : isSupremum (f (sup_X1, sup_X2)) (image f X)).
    { intros y.
      split.
      - intros H3 y' H4.
        inversion H4; subst.
        apply claim10.
        + apply H3.
        + destruct x as [x1 x2].
          apply (in_unions (image (fun x1' : D1 => f (x1', x2)) X1)).
          * apply (in_image (fun x1' : D1 => f (x1', x2))).
            apply (in_getFsts x1 x2)...
          * apply (in_image (fun x0 : D2 => image (fun x3 : D1 => f (x3, x0)) X1)).
            apply (in_getSnds x1 x2)...
      - intros H3.
        apply claim10.
        intros y' H4.
        inversion H4; subst.
        rename xs into ys.
        inversion H6; subst.
        rename x into x2_2.
        inversion H5; subst.
        rename x into x1_1.
        inversion H8; subst.
        rename x' into x2_1.
        inversion H7; subst.
        rename x into x1_2.
        destruct H1 as [H1 H11].
        destruct (H11 (x1_1, x2_1) H9 (x1_2, x2_2) H10) as [[x3_1 x3_2] [H12 [[H13 H14] [H15 H16]]]].
        simpl in *.
        assert (H17 : f (x1_1, x2_2) =< f (x3_1, x3_2)).
        { transitivity (f (x1_1, x3_2)).
          - apply (ContinuousMaps_on_cpos_are_always_monotonic (fun x2 : D2 => f (x1_1, x2)))...
          - apply (ContinuousMaps_on_cpos_are_always_monotonic (fun x1 : D1 => f (x1, x3_2)))...
        }
        transitivity (f (x3_1, x3_2))...
    }
    split...
  - intros H.
    split.
    + intros x1.
      apply (the_main_reason_for_introducing_ScottTopology (fun x2 : D2 => f (x1, x2))).
      intros X2 H0 Y.
      destruct (square_up_exists X2 H0) as [sup_X2 H1].
      set (X := image (fun x2 : D2 => (x1, x2)) X2).
      assert (claim1 : isDirected X).
      { destruct H0 as [[x2_0 H0] H2].
        split.
        - exists (x1, x2_0).
          apply (in_image (fun x2 : D2 => (x1, x2)))...
        - intros [x1_1 x2_1] H3 [x1_2 x2_2] H4.
          inversion H3; subst x1_1; subst.
          inversion H4; subst x1_2; subst.
          rename H8 into H5, H9 into H6.
          destruct (H2 x2_1 H5 x2_2 H6) as [x3_2 [H7 [H8 H9]]].
          exists (x1, x3_2).
          repeat split...
      }
      destruct (square_up_exists X claim1) as [sup_X H2].
      exists sup_X2, (f sup_X).
      assert (claim2 : (x1, sup_X2) = sup_X).
      { apply (isSupremum_unique X)...
        intros [x_1 x_2].
        split.
        - intros [H3 H4] [x_1' x_2'] H5.
          inversion H5; subst x_1'; subst.
          simpl.
          split...
        - intros H3.
          simpl.
          split.
          + destruct H0 as [[x2_0 H0] H4].
            apply (H3 (x1, x2_0))...
          + apply H1.
            intros x_2' H4.
            apply (H3 (x1, x_2'))...
      }
      assert (claim3 : f (x1, sup_X2) = f sup_X) by congruence.
      assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' = sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
      destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
      assert (claim4 : isSupremum (f sup_X) Y).
      { assert (H6 : isSupremum (f sup_X) (image f X) <-> sup_Y' = f sup_X) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) (image f X)).
        assert (H7 : isSupremum (f sup_X) (image f X)).
        { apply H6.
          transitivity (f sup_X').
          - symmetry...
          - enough (H7 : sup_X' = sup_X) by congruence.
            apply (isSupremum_unique X)...
        }
        assert (H8 : forall y : D3, member y (image f X) <-> member y Y).
        { intros y.
          split.
          - intros H8.
            inversion H8; subst.
            inversion H9; subst.
            rename x0 into x2.
            apply (in_image (fun x2 : D2 => f (x1, x2)))...
          - intros H8.
            inversion H8; subst.
            rename x into x2.
            apply (in_image f)...
        }
        apply (proj2 (@isSupremum_ext D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) _ _ H8 _ H7 _) eq_refl).
      }
      split...
    + intros x2.
      apply (the_main_reason_for_introducing_ScottTopology (fun x1 : D1 => f (x1, x2))).
      intros X1 H0 Y.
      destruct (square_up_exists X1 H0) as [sup_X1 H1].
      set (X := image (fun x1 : D1 => (x1, x2)) X1).
      assert (YYY : forall x1 : D1, member x1 X1 -> member (x1, x2) X).
      { intros x1 H2.
        apply (in_image (fun x1 : D1 => (x1, x2))), H2.
      }
      assert (claim1 : isDirected X).
      { destruct H0 as [[x1_0 H0] H2].
        split.
        - exists (x1_0, x2).
          apply (in_image (fun x1 : D1 => (x1, x2)))...
        - intros [x1_1 x2_1] H3 [x1_2 x2_2] H4.
          inversion H3; subst x2_1; subst.
          inversion H4; subst x2_2; subst.
          rename H8 into H5, H9 into H6.
          destruct (H2 x1_1 H5 x1_2 H6) as [x3_1 [H7 [H8 H9]]].
          exists (x3_1, x2).
          repeat split...
      }
      destruct (square_up_exists X claim1) as [sup_X H2].
      exists sup_X1, (f sup_X).
      assert (claim2 : (sup_X1, x2) = sup_X).
      { apply (isSupremum_unique X)...
        intros [x_1 x_2].
        split.
        - intros [H3 H4] [x_1' x_2'] H5.
          inversion H5; subst x_1'; subst.
          simpl.
          split...
        - intros H3.
          simpl.
          split.
          + apply H1.
            intros x_1' H4.
            apply (H3 (x_1', x2))...
          + destruct H0 as [[x1_0 H0] H4].
            apply (H3 (x1_0, x2))...
      }
      assert (claim3 : f (sup_X1, x2) = f sup_X) by congruence.
      assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' = sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
      destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
      assert (claim4 : isSupremum (f sup_X) Y).
      { assert (H6 : isSupremum (f sup_X) (image f X) <-> sup_Y' = f sup_X) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) (image f X)).
        assert (H7 : isSupremum (f sup_X) (image f X)).
        { apply H6.
          transitivity (f sup_X').
          - symmetry...
          - enough (H7 : sup_X' = sup_X) by congruence.
            apply (isSupremum_unique X)...
        }
        assert (H8 : forall y : D3, member y (image f X) <-> member y Y).
        { intros y.
          split.
          - intros H8.
            inversion H8; subst.
            inversion H9; subst.
            rename x0 into x1.
            apply (in_image (fun x1 : D1 => f (x1, x2)))...
          - intros H8.
            inversion H8; subst.
            rename x into x1.
            apply (in_image f)...
        }
        apply (proj2 (@isSupremum_ext D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) _ _ H8 _ H7 _) eq_refl).
      }
      split...
Qed.

End DomainTheory.
