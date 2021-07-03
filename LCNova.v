Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.
Require Import Coq.Program.Basics.

Global Create HintDb my_hints.

Module MyStructures.

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
  intros x1.
  reflexivity.
Defined.

Global Hint Resolve Setoid_refl : my_hints.

Lemma Setoid_sym {A : Type} `{A_isSetoid : isSetoid A} :
  forall x1 : A,
  forall x2 : A,
  x1 == x2 ->
  x2 == x1.
Proof.
  intros x1 x2 H.
  symmetry.
  apply H.
Defined.

Global Hint Resolve Setoid_sym : my_hints.

Lemma Setoid_trans {A : Type} `{A_iSetoid : isSetoid A} :
  forall x1 : A,
  forall x2 : A,
  forall x3 : A,
  x1 == x2 ->
  x2 == x3 ->
  x1 == x3.
Proof.
  intros x1 x2 x3 H H0.
  transitivity x2.
  - apply H.
  - apply H0.
Defined.

Global Hint Resolve Setoid_trans : my_hints.

Global Program Instance Prop_isSetoid : isSetoid Prop :=
  { eqProp :=
    fun p : Prop =>
    fun q : Prop =>
    p <-> q
  }
.

Next Obligation with tauto.
  repeat split...
Qed.

Global Program Instance arrow_isSetoid {A : Type} {B : Type} (B_requiresSetoid : isSetoid B) : isSetoid (arrow A B) :=
  { eqProp :=
    fun f : A -> B =>
    fun g : A -> B =>
    forall x : A,
    f x == g x
  }
.

Next Obligation with eauto with *.
  split.
  - intros f1 x...
  - intros f1 f2 H x...
  - intros f1 f2 f3 H H0 x...
Qed.

Global Program Instance DirectProductOfTwoSetoids_isSetoid {A : Type} {B : Type} (A_requiresSetoid : isSetoid A) (B_requiresSetoid : isSetoid B) : isSetoid (A * B) :=
  { eqProp :=
    fun p1 : (A * B) =>
    fun p2 : (A * B) =>
    fst p1 == fst p2 /\ snd p1 == snd p2
  }
.

Next Obligation with eauto with *.
  split.
  - intros p1...
  - intros p1 p2 [H H0]...
  - intros p1 p2 p3 [H H0] [H1 H2]...
Qed.

Definition isSetoidHomomorphism {A : Type} {B : Type} : isSetoid A -> isSetoid B -> (A -> B) -> Prop :=
  fun A_requiresSetoid : isSetoid A =>
  fun B_requiresSetoid : isSetoid B =>
  fun f : A -> B =>
  forall x1 : A,
  forall x2 : A,
  @eqProp A A_requiresSetoid x1 x2 ->
  @eqProp B B_requiresSetoid (f x1) (f x2)
.

Global Hint Unfold isSetoidHomomorphism : my_hints.

Class WindBlowsBetweenSetoids {A : Type} {B : Type} (A_requiresSetoid : isSetoid A) (B_requiresSetoid : isSetoid B) : Prop :=
  { every_map_isSetoidHomomorphism :
    forall f : A -> B,
    isSetoidHomomorphism A_requiresSetoid B_requiresSetoid f
  }
.

Global Program Instance WindBlowsFrom_DirectProductOfTwoSetoids {A : Type} {B : Type} {C : Type} `{A_requiresSetoid : isSetoid A} `{B_requiresSetoid : isSetoid B} `{C_requiresSetoid : isSetoid C} (wind_from_A_to_C : WindBlowsBetweenSetoids A_requiresSetoid C_requiresSetoid) (wind_from_B_to_C : WindBlowsBetweenSetoids B_requiresSetoid C_requiresSetoid) : WindBlowsBetweenSetoids (DirectProductOfTwoSetoids_isSetoid A_requiresSetoid B_requiresSetoid) C_requiresSetoid :=
  {}
.

Next Obligation.
  intros [x1 y1] [x2 y2] [H H0].
  simpl in *.
  transitivity (f (x1, y2)).
  - apply (every_map_isSetoidHomomorphism (fun y : B => f (x1, y))), H0.
  - apply (every_map_isSetoidHomomorphism (fun x : A => f (x, y2))), H.
Defined.

Class isPoset (A : Type) : Type :=
  { leProp : A -> A -> Prop
  ; Poset_requiresSetoid :> isSetoid A
  ; Poset_requiresPreorder :> PreOrder leProp
  ; Poset_requiresPartialOrder :> PartialOrder eqProp leProp
  }
.

Global Notation "x1 =< x2" := (leProp x1 x2) (at level 70, no associativity) : type_scope.

Lemma Poset_refl {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  x1 =< x1.
Proof.
  intros x1.
  reflexivity.
Defined.

Global Hint Resolve Poset_refl : my_hints.

Lemma Poset_refl1 {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  forall x2 : A,
  x1 == x2 ->
  x1 =< x2.
Proof.
  destruct A_isPoset as [leProp_A A_isSetoid A_isPreOrder A_isPartialOrder].
  intros x1 x2 H.
  destruct (A_isPartialOrder x1 x2) as [H0 H1].
  destruct (H0 H) as [H2 H3].
  apply H2.
Defined.

Global Hint Resolve Poset_refl1 : my_hints.

Lemma Poset_refl2 {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  forall x2 : A,
  x1 == x2 ->
  x2 =< x1.
Proof.
  destruct A_isPoset as [leProp_A A_isSetoid A_isPreOrder A_isPartialOrder].
  intros x1 x2 H.
  destruct (A_isPartialOrder x1 x2) as [H0 H1].
  destruct (H0 H) as [H2 H3].
  apply H3.
Defined.

Global Hint Resolve Poset_refl2 : my_hints.

Lemma Poset_asym {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  forall x2 : A,
  x1 =< x2 ->
  x2 =< x1 ->
  x1 == x2.
Proof.
  intros x1 x2 H H0.
  apply antisymmetry.
  - apply H.
  - apply H0.
Defined.

Global Hint Resolve Poset_asym : my_hints.

Lemma Poset_trans {A : Type} `{A_isPoset : isPoset A} :
  forall x1 : A,
  forall x2 : A,
  forall x3 : A,
  x1 =< x2 ->
  x2 =< x3 ->
  x1 =< x3.
Proof.
  intros x1 x2 x3 H H0.
  transitivity x2.
  - apply H.
  - apply H0.
Defined.

Global Hint Resolve Poset_trans : my_hints.

End MyStructures.

Module MyEnsemble.

Import MyStructures.

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

Global Instance ensemble_is_Setoid {A : Type} : isSetoid (ensemble A) :=
  arrow_isSetoid Prop_isSetoid
.

Global Program Instance ensemble_is_Poset {A : Type} : isPoset (ensemble A) :=
  { leProp := isSubsetOf
  ; Poset_requiresSetoid := ensemble_is_Setoid
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Next Obligation with firstorder with my_hints.
  split...
Qed.

Inductive full {A : Type} : ensemble A :=
| in_full {x : A} :
  member x full
.

Global Hint Constructors full : my_hints.

Inductive finite_ensemble {A : Type} : list A -> ensemble A :=
| in_finite_ensemble {xs : list A} {x : A} :
  In x xs ->
  member x (finite_ensemble xs)
.

Global Hint Constructors finite_ensemble : my_hints.

Inductive unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
| in_unions {xss : ensemble (ensemble A)} {x : A} :
  forall xs : ensemble A,
  member x xs ->
  member xs xss ->
  member x (unions xss)
.

Global Hint Constructors unions : my_hints.

Inductive intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
| in_intersection {xs1 : ensemble A} {xs2 : ensemble A} {x : A} :
  member x xs1 ->
  member x xs2 ->
  member x (intersection xs1 xs2)
.

Global Hint Constructors intersection : my_hints.

Inductive image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
| in_image {xs : ensemble A} :
  forall x : A,
  forall f : A -> B,
  member x xs ->
  member (f x) (image f xs)
.

Global Hint Constructors image : my_hints.

Inductive preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
| in_preimage {ys : ensemble B} :
  forall x : A,
  forall f : A -> B,
  member (f x) ys ->
  member x (preimage f ys)
.

Global Hint Constructors preimage : my_hints.

Definition nonempty {A : Type} : ensemble A -> Prop :=
  fun xs : ensemble A =>
  exists x : A, member x xs
.

Global Hint Unfold nonempty : my_hints.

Definition empty {A : Type} : ensemble A :=
  finite_ensemble []
.

Global Hint Unfold empty : my_hints.

Definition singleton {A : Type} : A -> ensemble A :=
  fun x : A =>
  finite_ensemble [x]
.

Global Hint Unfold singleton : my_hints.

Definition union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
  fun xs1 : ensemble A =>
  fun xs2 : ensemble A =>
  unions (finite_ensemble [xs1; xs2])
.

Global Hint Unfold union : my_hints.

End MyEnsemble.

Module Supremum.

Import MyStructures.

Import MyEnsemble.

Definition isSupremum {A : Type} `{A_isPoset : isPoset A} : A -> ensemble A -> Prop :=
  fun sup : A =>
  fun X : ensemble A =>
  forall a : A,
  sup =< a <-> (forall x : A, member x X -> x =< a)
.

Global Hint Unfold isSupremum : my_hints.

Lemma isSupremum_isSubsetOf {A : Type} `{A_isPoset : isPoset A} :
  forall X1 : ensemble A,
  forall X2 : ensemble A,
  isSubsetOf X1 X2 ->
  forall sup1 : A,
  isSupremum sup1 X1 ->
  forall sup2 : A,
  isSupremum sup2 X2 ->
  sup1 =< sup2.
Proof with eauto with *.
  intros X1 X2 H sup1 H0 sup2 H1.
  apply H0...
  intros x H2.
  apply H1...
Qed.

Lemma isSupremum_ext {A : Type} `{A_isPoset : isPoset A} :
  forall X1 : ensemble A,
  forall X2 : ensemble A,
  X1 == X2 ->
  forall sup1 : A,
  isSupremum sup1 X1 ->
  forall sup2 : A,
  isSupremum sup2 X2 <-> sup1 == sup2.
Proof with eauto with *.
  intros X1 X2 H sup1 H0 sup2.
  assert (claim1 : X1 =< X2)...
  assert (claim2 : X2 =< X1)...
  split.
  - intros H1.
    apply Poset_asym; [apply (isSupremum_isSubsetOf X1 X2) | apply (isSupremum_isSubsetOf X2 X1)]...
  - intros H1 d.
    split.
    + intros H2 x H3.
      apply H0...
    + intros H2.
      transitivity sup1...
      apply H0...
Qed.

Lemma isSupremum_unique {A : Type} `{A_isPoset : isPoset A} :
  forall X : ensemble A,
  forall sup1 : A,
  isSupremum sup1 X ->
  forall sup2 : A,
  isSupremum sup2 X <-> sup1 == sup2.
Proof with eauto with *.
  intros X sup1 H sup2.
  apply (isSupremum_ext X X)...
Qed.

Definition image_sup {A : Type} `{A_isPoset : isPoset A} : ensemble (ensemble A) -> ensemble A :=
  fun Xs : ensemble (ensemble A) =>
  fun sup_X : A =>
  exists X : ensemble A, member X Xs /\ isSupremum sup_X X
.

Global Hint Unfold image_sup : my_hints.

Theorem sup_unions_Xs_is_sup_image_sup_Xs {A : Type} `{A_isPoset : isPoset A} :
  forall Xs : ensemble (ensemble A),
  (forall X : ensemble A, member X Xs -> exists sup_X : A, isSupremum sup_X X) ->
  forall sup1 : A,
  isSupremum sup1 (unions Xs) ->
  forall sup2 : A,
  isSupremum sup2 (image_sup Xs) <-> sup1 == sup2.
Proof with eauto with *.
  intros Xs H sup1 H0 sup2.
  split.
  - intros H1.
    apply Poset_asym.
    + apply NNPP.
      intros H2.
      assert (claim1 : isSupremum sup2 (unions Xs) -> sup1 =< sup2).
      { intros H3.
        apply Poset_refl1, (isSupremum_unique (unions Xs))...
      }
      assert (H3 : ~ isSupremum sup2 (unions Xs)) by tauto.
      apply not_all_ex_not in H3.
      destruct H3 as [d0 H3].
      apply not_and_or in H3.
      destruct H3.
      * apply imply_to_and in H3.
        destruct H3 as [H3 H4].
        apply not_all_ex_not in H4.
        destruct H4 as [x H4].
        apply imply_to_and in H4.
        destruct H4 as [H4 H5].
        inversion H4; subst.
        destruct (H xs H7) as [sup_xs H8].
        contradiction H5.
        transitivity sup_xs; [apply H8 | apply H1]...
      * apply imply_to_and in H3.
        destruct H3.
        contradiction H2. 
        apply H0.
        intros x H5.
        assert (H6 := H3 x H5).
        inversion H5; subst.
        destruct (H xs H8) as [sup_xs H9].
        enough (H10 : sup_xs =< d0).
        { transitivity sup_xs.
          - apply H9...
          - apply H1...
        }
        apply H9...
    + apply H1.
      intros x [X [H3 H4]].
      apply H4.
      intros x' H5.
      apply H0...
  - intros H1 d.
    split.
    + intros H2 x [X [H3 H4]].
      apply H4.
      intros x' H5.
      apply H0...
    + intros H2.
      transitivity sup1...
      apply H0...
      intros x' H3.
      inversion H3; subst.
      destruct (H xs H5) as [sup_xs H6].
      transitivity sup_xs; [apply H6 | apply H2]...
Qed.

Corollary sup_image_sup_Xs_is_sup_unions_Xs {A : Type} `{A_isPoset : isPoset A} :
  forall Xs : ensemble (ensemble A),
  (forall X : ensemble A, member X Xs -> exists sup_X : A, isSupremum sup_X X) ->
  forall sup1 : A,
  isSupremum sup1 (image_sup Xs) ->
  forall sup2 : A,
  isSupremum sup2 (unions Xs) <-> sup1 == sup2.
Proof with eauto with *.
  intros Xs H sup1 H0 sup2.
  split.
  - intros H1.
    symmetry.
    apply (sup_unions_Xs_is_sup_image_sup_Xs Xs)...
  - intros H1 d.
    split.
    + intros H2 x H3.
      inversion H3; subst.
      destruct (H xs H5) as [sup_xs H6].
      transitivity sup_xs; [apply H6 | apply H0]...
    + intros H2.
      transitivity sup1...
      apply H0...
      intros x [xs [H3 H4]].
      apply H4.
      intros x' H5.
      apply H2...
Qed.

End Supremum.

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

Import Supremum.

Import GeneralTopology.

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
  { CompleteLattice_requiresPoset := ensemble_is_Poset
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

Global Hint Resolve bottom_exists : my_hints.

Global Hint Resolve square_up_exists : my_hints.

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
    destruct (H11 x1 H12 x2 H17) as [x H14].
    destruct H14.
    destruct H15.
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
    contradiction H.
    transitivity z...
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
  destruct claim2 as [x1].
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
  exists sup_X : D, exists sup_Y : D', isSupremum sup_X X /\ isSupremum sup_Y Y /\ f sup_X == sup_Y
.

Global Hint Unfold characterization_of_ContinuousMap_on_cpos : my_hints.

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

Lemma property1_of_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
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
  - destruct H0 as [x0]...
  - intros y1 H3 y2 H4.
    inversion H3; inversion H4; subst.
    rename x into x1, x0 into x2.
    destruct (H1 x1 H5 x2 H9) as [x3].
    exists (f x3).
    destruct H6.
    destruct H7.
    repeat split...
Qed.

Lemma property2_of_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
  forall f : D -> D',
  isContinuousMap f ->
  forall X : ensemble D,
  isDirected X ->
  forall sup_X : D,
  isSupremum sup_X X ->
  isDirected (image f X) ->
  {sup_Y : D' | isSupremum sup_Y (image f X) /\ f sup_X == sup_Y}.
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
    destruct (H9 X H0 sup_X H1 H7) as [x1].
    inversion H10; subst.
    inversion H12; subst.
    contradiction H13.
    apply H4...
  }
  split...
Qed.

Definition substitutablity_on_cpos {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} `{wind_from_D_to_D' : @WindBlowsBetweenSetoids D D' (@Poset_requiresSetoid D (@CompletePartialOrder_requiresPoset D D_isCompletePartialOrder)) (@Poset_requiresSetoid D' (@CompletePartialOrder_requiresPoset D' D'_isCompletePartialOrder))} :
  forall x1 : D,
  forall x2 : D,
  x1 == x2 ->
  forall f : D -> D',
  f x1 == f x2.
Proof.
  intros x1 x2 H f.
  apply every_map_isSetoidHomomorphism, H.
Defined.

Global Hint Resolve substitutablity_on_cpos : my_hints.

Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} `{wind_from_D_to_D' : @WindBlowsBetweenSetoids D D' (@Poset_requiresSetoid D (@CompletePartialOrder_requiresPoset D D_isCompletePartialOrder)) (@Poset_requiresSetoid D' (@CompletePartialOrder_requiresPoset D' D'_isCompletePartialOrder))} :
  forall f : D -> D',
  isContinuousMap f <-> characterization_of_ContinuousMap_on_cpos f.
Proof with eauto with *.
  assert (claim1 : forall f : D -> D', isContinuousMap f -> forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by apply ContinuousMaps_on_cpos_are_always_monotonic.
  split; intros H.
  - intros X H0.
    inversion H0; subst.
    set (Y := image f X).
    assert (H3 : isDirected Y) by now apply property1_of_ScottTopology.
    destruct (square_up_exists X H0) as [sup_X H4].
    exists sup_X.
    destruct (property2_of_ScottTopology f H X H0 sup_X H4 H3) as [sup_Y H5].
    exists sup_Y...
  - assert (claim2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2).
    { intros x1 x2 H0.
      set (X := finite_ensemble [x1; x2]).
      set (Y := image f X).
      assert (H1 : isSupremum x2 X).
      { intros x.
        split.
        - intros H1 x' H2.
          inversion H2; subst.
          destruct H3 as [H3 | [H3 | []]].
          + subst.
            transitivity x2...
          + subst...
        - intros H1.
          apply H1...
      }
      assert (H2 : isDirected X).
      { split.
        - exists x1...
        - intros x1' H2 x2' H3.
          exists x2.
          enough (x1' =< x2 /\ x2' =< x2)...
          inversion H2; subst.
          inversion H3; subst.
          split; (destruct H4 as [H4 | [H4 | []]]; destruct H5 as [H5 | [H5 | []]]; subst)...
      }
      destruct (H X H2) as [sup_X H3].
      destruct H3 as [sup_Y [H3 [H4 H5]]].
      assert (H6 : sup_X == x2) by now apply (isSupremum_unique X).
      assert (H7 : sup_Y == f x2).
      { apply (isSupremum_unique Y)...
        intros y.
        split...
        intros H7 y' H8.
        transitivity (f x2)...
        apply H4...
      }
      apply H4...
    }
    intros O H0.
    split.
    + intros x1 x2 H1 H2.
      inversion H1; subst.
      constructor.
      apply (proj1 H0 (f x1) (f x2))...
    + intros X H1 sup_X H2 H3.
      destruct (H X H1) as [sup_X' [sup_Y [H4 [H5 H6]]]].
      assert (H7 : sup_X == sup_X') by now apply (isSupremum_unique X).
      assert (H8 : member (f sup_X) O) by now inversion H3; subst.
      assert (H9 : isDirected (image f X)).
      { destruct H1.
        split.
        - destruct H1 as [x1 H1].
          exists (f x1)...
        - intros y1 H10 y2 H11.
          inversion H10; subst.
          inversion H11; subst.
          rename x into x1, x0 into x2.
          destruct (H9 x1 H12 x2 H13) as [x3 [H14 [H15 H16]]].
          exists (f x3).
          repeat split...
      }
      assert (H10 : nonempty (intersection (image f X) O)).
      { apply (proj2 H0 (image f X) H9 (f sup_X))...
        intros y.
        split.
        - intros.
          apply H5...
          transitivity (f sup_X)...
        - intros.
          transitivity sup_Y...
          apply H5...
      }
      destruct H10 as [y1 H10].
      inversion H10; subst.
      inversion H11; subst...
Qed.

Program Instance DirectProductOfTwoPosets_isPoset {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isPoset (D * D') :=
  { leProp :=
    fun p1 : (D * D') =>
    fun p2 : (D * D') =>
    fst p1 =< fst p2 /\ snd p1 =< snd p2
  ; Poset_requiresSetoid := DirectProductOfTwoSetoids_isSetoid (@Poset_requiresSetoid D D_requiresPoset) (@Poset_requiresSetoid D' D'_requiresPoset)
  }
.

Next Obligation with eauto with *.
  split.
  - intros [x1 y1]...
  - intros [x1 y1] [x2 y2] [x3 y3] [H H0] [H1 H2]...
Qed.

Next Obligation with eauto with *.
  split.
  - intros [H H0].
    repeat split...
  - intros [[H H0] [H1 H2]]...
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
  destruct (@bottom_exists D D_requiresCompletePartialOrder) as [min_D H].
  destruct (@bottom_exists D' D'_requiresCompletePartialOrder) as [min_D' H0].
  exists (min_D, min_D').
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
      apply (in_getFsts d3 d3' H5).
      split.
      apply H6.
      apply H8.
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
      apply (in_getSnds d3 d3' H5).
      split.
      apply H7.
      apply H9.
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

Global Program Instance squigarrow_isSetoid {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isSetoid (D ~> D') :=
  { eqProp :=
    fun f1 : D ~> D' =>
    fun f2 : D ~> D' =>
    forall x : D,
    proj1_sig f1 x == proj1_sig f2 x
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Global Program Instance squigarrow_isPoset {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isPoset (D ~> D') :=
  { Poset_requiresSetoid := squigarrow_isSetoid D_requiresCompletePartialOrder D'_requiresCompletePartialOrder
  ; leProp :=
    fun f1 : D ~> D' =>
    fun f2 : D ~> D' =>
    forall x : D,
    proj1_sig f1 x =< proj1_sig f2 x
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Next Obligation with firstorder with my_hints.
  split.
  - intros H.
    split...
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
    apply (in_image f0)...
  - intros y1 H1 y2 H2.
    inversion H1; subst.
    inversion H2; subst.
    rename x0 into f1, x1 into f2.
    destruct (H0 f1 H3 f2 H4) as [f3 [H5 [H6 H7]]].
    exists (proj1_sig f3 x).
    repeat split...
    apply (in_image f3)...
Qed.

Lemma sup_of_set_of_squigarrows_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} `{wind_from_D_to_D' : @WindBlowsBetweenSetoids D D' (@Poset_requiresSetoid D (@CompletePartialOrder_requiresPoset D D_isCompletePartialOrder)) (@Poset_requiresSetoid D' (@CompletePartialOrder_requiresPoset D' D'_isCompletePartialOrder))} :
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
    assert (H8 : sup_X' == sup_X) by now apply (isSupremum_unique X).
    apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X) sup_Y')...
  }
  assert (claim2 : isSupremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) fs) (sup_of_squigarrow_is_well_defined fs H sup_X))).
  assert (claim3 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs))).
  { enough (H2 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs)) <-> f sup_X == f sup_X) by apply (proj2 H2 (Setoid_refl (f sup_X))).
    apply (@sup_image_sup_Xs_is_sup_unions_Xs D' (@CompletePartialOrder_requiresPoset D' D'_isCompletePartialOrder)).
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
        assert (H7 : y' == proj1_sig f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X)).
        transitivity (proj1_sig f_i sup_X)...
        apply claim2...
        apply (in_image f_i)...
      + intros H2.
        apply claim2.
        intros y' H3.
        inversion H3; subst.
        rename x into f_i.
        apply H2.
        exists (image (fun x : D => proj1_sig f_i x) X).
        split...
        apply (in_image f_i)...
  }
  assert (claim4 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
  { enough (H2 : (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) fs)) == (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
    { enough (H3 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X)) <-> f sup_X == f sup_X) by now apply (proj2 H3 (Setoid_refl (f sup_X))).
      apply (@isSupremum_ext D' (@CompletePartialOrder_requiresPoset D' D'_isCompletePartialOrder) _ _ H2)...
    }
    intros y.
    split.
    - intros H2.
      inversion H2; subst.
      rename xs into ys.
      inversion H4; subst.
      rename x into f_i.
      inversion H3; subst.
      apply (in_unions (image (fun f_i' : D ~> D' => proj1_sig f_i' x) fs)).
      + apply (in_image f_i)...
      + apply (in_image x)...
    - intros H2.
      inversion H2; subst.
      rename xs into ys.
      inversion H4; subst.
      inversion H3; subst.
      rename x0 into f_i.
      apply (in_unions (image (fun x' : D => proj1_sig f_i x') X)).
      + apply (in_image x)...
      + apply (in_image f_i)...
  }
  assert (claim5 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X))).
  { enough (H2 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) fs) X)) <-> f sup_X == f sup_X) by now apply (proj2 H2 (Setoid_refl (f sup_X))).
    apply (@sup_unions_Xs_is_sup_image_sup_Xs D' (@CompletePartialOrder_requiresPoset D' D'_isCompletePartialOrder))...
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
      + apply (in_image x)...
      + apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
    - intros H2.
      apply claim5.
      intros y' [ys [H3 H4]].
      inversion H3; subst.
      assert (H6 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_squigarrow_is_well_defined fs H x))).
      assert (H7 : y' == f x) by now apply (isSupremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)).
      transitivity (f x)...
  }
  split...
Qed.

Global Program Instance squigarrow_isCompletePartialOrder {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') (requires_wind_from_D_to_D' : @WindBlowsBetweenSetoids D D' (@Poset_requiresSetoid D (@CompletePartialOrder_requiresPoset D D_requiresCompletePartialOrder)) (@Poset_requiresSetoid D' (@CompletePartialOrder_requiresPoset D' D'_requiresCompletePartialOrder))) : isCompletePartialOrder (D ~> D') :=
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
      apply (in_preimage x2).
      apply (H (bot x1) (bot x2) H3 (Poset_refl (proj1_sig bottom_exists))).
    - intros X [[x_0 H1] H2] sup_X H3 H4.
      inversion H4; subst.
      exists x_0.
      constructor.
      + apply H1.
      + apply (in_preimage x_0).
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
    + apply (in_image f').  
      apply H0.
  - intros H x.
    apply (claim1 x).
    intros f' H0.
    inversion H0; subst.
    rename x0 into f'.
    apply (H f').
    apply H1.
Defined.

Lemma separately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isCompletePartialOrder : isCompletePartialOrder D1} `{D2_isCompletePartialOrder : isCompletePartialOrder D2} `{D3_isCompletePartialOrder : isCompletePartialOrder D3} `{wind_from_D1_to_D3 : @WindBlowsBetweenSetoids D1 D3 (@Poset_requiresSetoid D1 (@CompletePartialOrder_requiresPoset D1 D1_isCompletePartialOrder)) (@Poset_requiresSetoid D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder))} `{wind_from_D2_to_D3 : @WindBlowsBetweenSetoids D2 D3 (@Poset_requiresSetoid D2 (@CompletePartialOrder_requiresPoset D2 D2_isCompletePartialOrder)) (@Poset_requiresSetoid D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder))} :
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
      exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremum sup_X2_x1 X2 /\ isSupremum sup_f_X2_x1 (image (fun x2 : D2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) == sup_f_X2_x1
    ).
    { intros x1.
      apply (the_main_reason_for_introducing_ScottTopology (fun x2 : D2 => f (x1, x2)))...
    }
    assert ( claim4 :
      forall x2 : D2,
      exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremum sup_X1_x2 X1 /\ isSupremum sup_f_X1_x2 (image (fun x1 : D1 => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) == sup_f_X1_x2
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
      assert (H6 : (sup_X1, sup_X2) == (sup_X1', sup_X2')) by now apply (isSupremum_unique X).
      destruct H6 as [H6 H7].
      simpl in *.
      split.
      - assert (H8 : isSupremum sup_X1 X1 <-> sup_X1' == sup_X1) by now apply (@isSupremum_unique D1 (@CompletePartialOrder_requiresPoset D1 D1_isCompletePartialOrder)).
        apply H8...
      - assert (H8 : isSupremum sup_X2 X2 <-> sup_X2' == sup_X2) by now apply (@isSupremum_unique D2 (@CompletePartialOrder_requiresPoset D2 D2_isCompletePartialOrder)).
        apply H8...
    }
    destruct XXX as [claim5 claim6].
    assert (claim7 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
    { destruct (claim3 sup_X1) as [sup_X2_x1 [sup_f_X1_x2 [H3 [H4 H5]]]].
      assert (H6 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2) <-> sup_f_X1_x2 == f (sup_X1, sup_X2)) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder)).
      apply H6.
      transitivity (f (sup_X1, sup_X2_x1)).
      - symmetry...
      - apply substitutablity_on_cpos.
        split.
        + simpl...
        + simpl.
          apply (isSupremum_unique X2)...
    }
    assert ( claim8 :
      forall x2 : D2,
      member x2 X2 ->
      isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)
    ).
    { intros x2 H3.
      destruct (claim4 x2) as [sup_X1' [sup_f_X1_x2' [H4 [H5 H6]]]].
      assert (H7 : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1) <-> sup_f_X1_x2' == f (sup_X1, x2)) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder)).
      apply H7.
      transitivity (f (sup_X1', x2)).
      - symmetry...
      - apply substitutablity_on_cpos.
        split.
        + simpl.
          apply (isSupremum_unique X1)...
        + simpl...
    }
    assert (claim9 : isSupremum (f (sup_X1, sup_X2)) (image_sup (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { intros y.
      split.
      - intros H3 y' [ys [H4 H5]].
        inversion H4; subst.
        rename x into x2.
        assert (H7 : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)) by now apply claim8.
        assert (H8 : y' == (f (sup_X1, x2))) by now apply (isSupremum_unique (image (fun x1 : D1 => f (x1, x2)) X1)).
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
        + apply (in_image x2)...
        + apply claim8...
    }
    assert (claim10 : isSupremum (f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { enough (H3 : isSupremum (f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2)) <-> f (sup_X1, sup_X2) == f (sup_X1, sup_X2)) by apply (proj2 H3 (Setoid_refl (f (sup_X1, sup_X2)))).
      apply (@sup_image_sup_Xs_is_sup_unions_Xs D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder))...
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
          * apply (in_image x1).
            apply (in_getFsts x1 x2)...
          * apply (in_image x2).
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
          apply (in_image x2_0)...
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
      assert (claim2 : (x1, sup_X2) == sup_X).
      { apply (isSupremum_unique X)...
        intros [x_1 x_2].
        split.
        - intros [H3 H4] [x_1' x_2'] H5.
          inversion H5; subst x_1'; subst.
          simpl.
          split...
          apply H1...
        - intros H3.
          simpl.
          split.
          + destruct H0 as [[x2_0 H0] H4].
            apply (H3 (x1, x2_0))...
          + apply H1.
            intros x_2' H4.
            apply (H3 (x1, x_2'))...
      }
      assert (claim3 : f (x1, sup_X2) == f sup_X) by now apply (every_map_isSetoidHomomorphism f).
      assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' == sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
      destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
      assert (claim4 : isSupremum (f sup_X) Y).
      { assert (H6 : isSupremum (f sup_X) (image f X) <-> sup_Y' == f sup_X) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) (image f X)).
        assert (H7 : isSupremum (f sup_X) (image f X)).
        { apply H6.
          transitivity (f sup_X').
          - symmetry...
          - apply (every_map_isSetoidHomomorphism f).
            apply (isSupremum_unique X)...
        }
        assert (H8 : image f X == Y).
        { intros y.
          split.
          - intros H8.
            inversion H8; subst.
            inversion H9; subst.
            rename x0 into x2.
            apply (in_image x2)...
          - intros H8.
            inversion H8; subst.
            rename x into x2.
            apply (in_image (x1, x2))...
        }
        apply (proj2 (@isSupremum_ext D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) _ _ H8 _ H7 _) (Setoid_refl (f sup_X))).
      }
      split...
    + intros x2.
      apply (the_main_reason_for_introducing_ScottTopology (fun x1 : D1 => f (x1, x2))).
      intros X1 H0 Y.
      destruct (square_up_exists X1 H0) as [sup_X1 H1].
      set (X := image (fun x1 : D1 => (x1, x2)) X1).
      assert (YYY : forall x1 : D1, member x1 X1 -> member (x1, x2) X).
      { intros x1 H2.
        apply (in_image x1), H2.
      }
      assert (claim1 : isDirected X).
      { destruct H0 as [[x1_0 H0] H2].
        split.
        - exists (x1_0, x2).
          apply (in_image x1_0)...
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
      assert (claim2 : (sup_X1, x2) == sup_X).
      { apply (isSupremum_unique X)...
        intros [x_1 x_2].
        split.
        - intros [H3 H4] [x_1' x_2'] H5.
          inversion H5; subst x_1'; subst.
          simpl.
          split...
          apply H1...
        - intros H3.
          simpl.
          split.
          + apply H1.
            intros x_1' H4.
            apply (H3 (x_1', x2))...
          + destruct H0 as [[x1_0 H0] H4].
            apply (H3 (x1_0, x2))...
      }
      assert (claim3 : f (sup_X1, x2) == f sup_X) by now apply (every_map_isSetoidHomomorphism f).
      assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' == sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
      destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
      assert (claim4 : isSupremum (f sup_X) Y).
      { assert (H6 : isSupremum (f sup_X) (image f X) <-> sup_Y' == f sup_X) by now apply (@isSupremum_unique D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) (image f X)).
        assert (H7 : isSupremum (f sup_X) (image f X)).
        { apply H6.
          transitivity (f sup_X').
          - symmetry...
          - apply (every_map_isSetoidHomomorphism f).
            apply (isSupremum_unique X)...
        }
        assert (H8 : image f X == Y).
        { intros y.
          split.
          - intros H8.
            inversion H8; subst.
            inversion H9; subst.
            rename x0 into x1.
            apply (in_image x1)...
          - intros H8.
            inversion H8; subst.
            rename x into x1.
            apply (in_image (x1, x2))...
        }
        apply (proj2 (@isSupremum_ext D3 (@CompletePartialOrder_requiresPoset D3 D3_isCompletePartialOrder) _ _ H8 _ H7 _) (Setoid_refl (f sup_X))).
      }
      split...
Qed.

End DomainTheory.
