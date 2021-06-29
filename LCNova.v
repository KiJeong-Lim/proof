Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.
Require Import Coq.Program.Basics.

Global Create HintDb my_hints.

Module MyStructures.

Class Setoid (A : Type) : Type :=
  { eqProp : A -> A -> Prop
  ; Setoid_requiresEquivalence :> Equivalence eqProp
  }
.

Global Notation "x == y" := (eqProp x y) (at level 70, no associativity) : type_scope.

Lemma Setoid_refl {A : Type} `{A_requiresSetoid : Setoid A} :
  forall x1 : A,
  x1 == x1.
Proof.
  intros x1.
  reflexivity.
Defined.

Global Hint Resolve Setoid_refl : my_hints.

Lemma Setoid_sym {A : Type} `{A_requiresSetoid : Setoid A} :
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

Lemma Setoid_trans {A : Type} `{A_requiresSetoid : Setoid A} :
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

Global Program Instance Prop_isSetoid : Setoid Prop :=
  { eqProp := fun p : Prop => fun q : Prop => p <-> q
  }
.

Next Obligation with tauto.
  repeat split...
Qed.

Global Program Instance arrow_isSetoid {A : Type} {B : Type} (B_requiresSetoid : Setoid B) : Setoid (arrow A B) :=
  { eqProp := fun f : A -> B => fun g : A -> B => forall x : A, f x == g x
  }
.

Next Obligation with eauto with *.
  split.
  - intros f1 x...
  - intros f1 f2 H x...
  - intros f1 f2 f3 H H0 x...
Qed.

Definition isSetoidHomomorphism {A : Type} {B : Type} `{X : Setoid A} `{Y : Setoid B} : (A -> B) -> Prop :=
  fun f : A -> B =>
  forall x1 : A,
  forall x2 : A,
  x1 == x2 ->
  f x1 == f x2
.

Global Hint Unfold isSetoidHomomorphism : my_hints.

Class WindBlowsBetweenSetoids {A : Type} {B : Type} (X : Setoid A) (Y : Setoid B) : Prop :=
  { every_map_isSetoidHomomorphism :
    forall f : A -> B,
    isSetoidHomomorphism f
  }
.

Global Hint Resolve every_map_isSetoidHomomorphism : my_hints.

Class Poset (A : Type) : Type :=
  { leProp : A -> A -> Prop
  ; Poset_requiresSetoid :> Setoid A
  ; Poset_requiresPreorder :> PreOrder leProp
  ; Poset_requiresPartialOrder :> PartialOrder eqProp leProp
  }
.

Global Notation "x1 =< x2" := (leProp x1 x2) (at level 70, no associativity) : type_scope.

Lemma Poset_refl {A : Type} `{A_requiresPoset : Poset A} :
  forall x1 : A,
  x1 =< x1.
Proof.
  intros x1.
  reflexivity.
Defined.

Global Hint Resolve Poset_refl : my_hints.

Lemma Poset_refl1 {A : Type} `{A_requiresPoset : Poset A} :
  forall x1 : A,
  forall x2 : A,
  x1 == x2 ->
  x1 =< x2.
Proof.
  destruct A_requiresPoset as [leProp_A A_isSetoid A_isPreOrder A_isPartialOrder].
  intros x1 x2 H.
  destruct (A_isPartialOrder x1 x2) as [H0 H1].
  destruct (H0 H) as [H2 H3].
  apply H2.
Defined.

Global Hint Resolve Poset_refl1 : my_hints.

Lemma Poset_refl2 {A : Type} `{A_requiresPoset : Poset A} :
  forall x1 : A,
  forall x2 : A,
  x1 == x2 ->
  x2 =< x1.
Proof.
  destruct A_requiresPoset as [leProp_A A_isSetoid A_isPreOrder A_isPartialOrder].
  intros x1 x2 H.
  destruct (A_isPartialOrder x1 x2) as [H0 H1].
  destruct (H0 H) as [H2 H3].
  apply H3.
Defined.

Global Hint Resolve Poset_refl2 : my_hints.

Lemma Poset_asym {A : Type} `{A_requiresPoset : Poset A} :
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

Lemma Poset_trans {A : Type} `{A_requiresPoset : Poset A} :
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

Definition ensemble : Type -> Type :=
  fun A : Type => A -> Prop
.

Definition member {A : Type} : A -> ensemble A -> Prop :=
  fun x : A => fun xs : ensemble A => xs x
.

Global Hint Unfold member : my_hints.

Global Notation "x '\in' xs" := (member x xs) (at level 70, no associativity) : type_scope.

Definition isSubsetOf {A : Type} : ensemble A -> ensemble A -> Prop :=
  fun xs1 : ensemble A => fun xs2 : ensemble A => forall x : A, member x xs1 -> member x xs2
.

Global Hint Unfold isSubsetOf : my_hints.

Global Notation "xs1 '\subseteq' xs2" := (isSubsetOf xs1 xs2) (at level 70, no associativity) : type_scope.

Global Instance ensemble_is_Setoid {A : Type} : Setoid (ensemble A) :=
  arrow_isSetoid Prop_isSetoid
.

Global Program Instance ensemble_is_Poset {A : Type} : Poset (ensemble A) :=
  { leProp := isSubsetOf
  }
.

Next Obligation with eauto with *.
  split...
Qed.

Next Obligation with firstorder with my_hints.
  split...
Qed.

Inductive full {A : Type} : ensemble A :=
| mk1full {x : A} :
  member x full
.

Global Hint Constructors full : my_hints.

Inductive finiteensemble {A : Type} : list A -> ensemble A :=
| mk1finiteensemble {xs : list A} {x : A} :
  In x xs ->
  member x (finiteensemble xs)
.

Global Hint Constructors finiteensemble : my_hints.

Inductive union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
| mk1union {xs1 : ensemble A} {xs2 : ensemble A} {x : A} :
  member x xs1 ->
  member x (union xs1 xs2)
| mk2union {xs1 : ensemble A} {xs2 : ensemble A} {x : A} :
  member x xs2 ->
  member x (union xs1 xs2)
.

Global Hint Constructors union : my_hints.

Inductive unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
| mk1unions {xss : ensemble (ensemble A)} {x : A} :
  forall xs : ensemble A,
  member x xs ->
  member xs xss ->
  member x (unions xss)
.

Global Hint Constructors unions : my_hints.

Inductive intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
| mk1intersection {xs1 : ensemble A} {xs2 : ensemble A} {x : A} :
  member x xs1 ->
  member x xs2 ->
  member x (intersection xs1 xs2)
.

Global Hint Constructors intersection : my_hints.

Inductive image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
| mk1image {xs : ensemble A} :
  forall x : A,
  forall f : A -> B,
  member x xs ->
  member (f x) (image f xs)
.

Global Hint Constructors image : my_hints.

Inductive preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
| mk1preimage {ys : ensemble B} :
  forall x : A,
  forall f : A -> B,
  member (f x) ys ->
  member x (preimage f ys)
.

Global Hint Constructors preimage : my_hints.

Definition nonempty {A : Type} : ensemble A -> Prop :=
  fun xs : ensemble A => exists x : A, member x xs
.

Global Hint Unfold nonempty : my_hints.

Definition empty {A : Type} : ensemble A :=
  finiteensemble nil
.

Global Hint Unfold empty : my_hints.

Definition singleton {A : Type} : A -> ensemble A :=
  fun x : A => finiteensemble (cons x nil)
.

Global Hint Unfold singleton : my_hints.

Definition isSupremum {D : Type} `{D_isPoset : Poset D} : D -> ensemble D -> Prop :=
  fun sup : D => fun X : ensemble D => forall d : D, sup =< d <-> (forall x : D, member x X -> x =< d)
.

Global Hint Unfold isSupremum : my_hints.

Lemma isSupremum_isSubsetOf {D : Type} `{D_isPoset : Poset D} :
  forall X1 : ensemble D,
  forall X2 : ensemble D,
  isSubsetOf X1 X2 ->
  forall sup1 : D,
  isSupremum sup1 X1 ->
  forall sup2 : D,
  isSupremum sup2 X2 ->
  sup1 =< sup2.
Proof with eauto with *.
  intros X1 X2 H sup1 H0 sup2 H1.
  apply H0...
  intros x H2.
  apply H1...
Qed.

Lemma isSupremum_ext {D : Type} `{D_isPoset : Poset D} :
  forall X1 : ensemble D,
  forall X2 : ensemble D,
  X1 == X2 ->
  forall sup1 : D,
  isSupremum sup1 X1 ->
  forall sup2 : D,
  isSupremum sup2 X2 <-> sup1 == sup2.
Proof with eauto with *.
  intros X1 X2 H sup1 H0 sup2.
  split.
  - intros H1.
    apply Poset_asym.
    + apply (isSupremum_isSubsetOf X1 X2)...
      enough (X1 =< X2)...
    + apply (isSupremum_isSubsetOf X2 X1)...
      enough (X2 =< X1)...
  - intros H1 d.
    split.
    + intros H2 x H3.
      apply H0...
      enough (X2 =< X1)...
    + intros H2.
      transitivity sup1...
      apply H0...
      intros x H3.
      apply H2...
      enough (X1 =< X2)...
Qed.

Lemma isSupremum_unique {D : Type} `{D_isPoset : Poset D} :
  forall X : ensemble D,
  forall sup1 : D,
  isSupremum sup1 X ->
  forall sup2 : D,
  isSupremum sup2 X <-> sup1 == sup2.
Proof with eauto with *.
  intros X sup1 H sup2.
  apply (isSupremum_ext X X)...
Qed.

Lemma sup_unions_Xs_is_sup_image_sup_Xs {D : Type} `{D_isPoset : Poset D} :
  forall Xs : ensemble (ensemble D),
  (forall X : ensemble D, member X Xs -> exists sup_X : D, isSupremum sup_X X) ->
  forall sup1 : D,
  isSupremum sup1 (unions Xs) ->
  forall sup2 : D,
  isSupremum sup2 (fun sup_X : D => exists X : ensemble D, member X Xs /\ isSupremum sup_X X) <-> sup1 == sup2.
Proof with eauto with *.
  intros Xs H sup1 H0 sup2.
  set (sup_Xs := fun sup_X : D => exists X : ensemble D, member X Xs /\ isSupremum sup_X X).
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
      destruct H3 as [d0].
      apply not_and_or in H3.
      destruct H3.
      { apply imply_to_and in H3.
        destruct H3.
        apply not_all_ex_not in H4.
        destruct H4 as [x H4].
        apply imply_to_and in H4.
        destruct H4 as [H4 H5].
        inversion H4; subst.
        destruct (H xs H7) as [sup_xs H8].
        contradiction H5.
        transitivity sup_xs.
        - apply H8...
        - apply H1...
          exists xs...
      }
      { apply imply_to_and in H3.
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
            exists xs...
        }
        apply H9...
      }
    + apply H1.
      intros x [X [H3 H4]].
      apply H4.
      intros x' H5.
      apply H0...
  - intros H1.
    intros d.
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
      transitivity sup_xs.
      * apply H6...
      * apply H2...
        exists xs...
Qed.

End MyEnsemble.

Module DomainTheory.

Import MyStructures.

Import MyEnsemble.

Class TopologicalSpace (X : Set) : Type :=
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

Definition isContinuousMap {X : Set} {Y : Set} `{X_isTopologicalSpace : TopologicalSpace X} `{Y_isTopologicalSpace : TopologicalSpace Y} : (X -> Y) -> Prop :=
  fun f : X -> Y => forall ys : ensemble Y, isOpen ys -> isOpen (preimage f ys)
.

Global Hint Unfold isContinuousMap : my_hints.

Definition isDirected {D : Type} `{D_isPoset : Poset D} : ensemble D -> Prop :=
  fun X : ensemble D => nonempty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ x1 =< x3 /\ x2 =< x3)
.

Global Hint Unfold isDirected : my_hints.

Class CompletePartialOrder (D : Set) : Type :=
  { CompletePartialOrder_requiresPoset :> Poset D
  ; bottom : D
  ; bottom_least :
    forall x : D,
    bottom =< x
  ; supremum_exists :
    forall xs : ensemble D,
    isDirected xs ->
    {sup_xs : D | isSupremum sup_xs xs}
  }
.

Global Hint Resolve bottom_least : my_hints.

Global Hint Resolve supremum_exists : my_hints.

Class CompleteLattice (D : Set) : Type :=
  { CompleteLattice_requiresPoset :> Poset D
  ; supremum_always_exists :
    forall xs : ensemble D,
    {sup_xs : D | isSupremum sup_xs xs}
  }
.

Global Hint Resolve supremum_always_exists : my_hints.

Global Program Instance each_complete_lattice_is_a_cpo  {D : Set} (D_requiresCompleteLattice : CompleteLattice D) : CompletePartialOrder D :=
  { CompletePartialOrder_requiresPoset := CompleteLattice_requiresPoset
  ; bottom := supremum_always_exists empty
  }
.

Next Obligation with eauto with *.
  assert (H := proj2_sig (supremum_always_exists empty)).
  simpl in H.
  apply H.
  intros x' H0.
  inversion H0; subst.
  inversion H1.
Qed.

Next Obligation with eauto with *.
  apply supremum_always_exists.
Qed.

Global Program Instance ScottTopology {D : Set} (D_requiresCompletePartialOrder : CompletePartialOrder D) : TopologicalSpace D :=
  { isOpen := fun O : ensemble D => (forall x : D, forall y : D, member x O -> x =< y -> member y O) /\ (forall X : ensemble D, isDirected X -> forall sup_X : D, isSupremum sup_X X -> member sup_X O -> nonempty (intersection X O))
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
    apply (mk1unions xs)...
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

Definition U {D : Set} `{D_isCompletePartialOrder : CompletePartialOrder D} : D -> ensemble D :=
  fun x : D => fun z : D => ~ z =< x
.

Global Hint Unfold U : my_hints.

Lemma U_isOpen {D : Set} `{D_isCompletePartialOrder : CompletePartialOrder D} :
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
    destruct (H4 x0)...
    contradiction.
  }
  apply not_all_ex_not in claim2.
  destruct claim2 as [x1].
  exists x1.
  apply not_or_and in H4.
  destruct H4 as [H4 H5].
  apply NNPP in H5...
Qed.

End DomainTheory.
