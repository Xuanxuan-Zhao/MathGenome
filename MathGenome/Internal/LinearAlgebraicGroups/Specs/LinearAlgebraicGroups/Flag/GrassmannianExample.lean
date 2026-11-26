import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FlagSchemes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.PartialFlags
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Preorder.Finite
import Mathlib.SetTheory.Cardinal.Finite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj BigOperators TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.GrassmannianExample

noncomputable section

/-- The orbit map of a flag defined over the base field. -/
def orbitMap {k : Type u} [Field k] {X Y : SchemeOver k}
    (a : X ⨯ Y ⟶ Y) (z : Points Y (CommAlgCat.of k k)) : X ⟶ Y :=
  prod.lift (𝟙 X) (FlagSchemes.toBasePoint X ≫ z) ≫ a

/-- The actual right quotient by the scheme stabilizer of the coordinate flag,
with its projection, block equations, and left action on families. -/
def CoordinateFlagQuotientAt
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n m : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)
    (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
    (D : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    (G : GroupScheme k)
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G E)
    (S : FlagSchemes.CoordinateStabilizer β ranks P D G E A)
    (H : ClosedSubgroup G) : Prop :=
  Nonempty (QuotientEmbedding.Presentation H) ∧
  (∀ (T : SchemeOver k) (g : T ⟶ G.X),
    g ∈ SubgroupSections H T ↔
      g ≫ orbitMap A.onFlags S.point = FlagSchemes.toBasePoint T ≫ S.point) ∧
  (∀ (R : TestAlgebra k) (g : Points G.X R),
    g ∈ SubgroupSections H ((testSpec k).obj (op R)) ↔
      ∀ (a : Fin m) (i j : ULift.{u} (Fin n)),
        j.down.val < ranks a → ranks a ≤ i.down.val →
          (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0) ∧
  ∀ Q : QuotientEmbedding.Presentation H,
    ∃ e : Q.scheme ≅ D.scheme,
      Q.projection ≫ e.hom = orbitMap A.onFlags S.point ∧
      ∀ (T : SchemeOver k) (g : T ⟶ G.X) (x : T ⟶ Q.scheme),
        Q.quotientIso.hom.hom.app (op T)
          (actOnSection H g (Q.quotientIso.inv.hom.app (op T) (ULift.up x))) =
          ULift.up ((prod.lift g (x ≫ e.hom) ≫ A.onFlags) ≫ e.inv)

/-- The orbit of the locally transitive matrix action represents the right quotient. -/
def CoordinateFlagQuotient : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n m : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)
    (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
    (D : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    (G : GroupScheme k)
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G E)
    (S : FlagSchemes.CoordinateStabilizer β ranks P D G E A),
    FlagIncidence.HasLocalTransitivity ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G E A →
    ∃ H : ClosedSubgroup G, CoordinateFlagQuotientAt β ranks P D G E A S H

/-- Every sequence of allowed flag dimensions has the compatible quotient presentation. -/
def CoordinateFlagQuotientExists : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (β : Module.Basis (Fin n) k V) (m : ℕ) (ranks : Fin m → ℕ),
    StrictMono ranks → (∀ i, ranks i ≤ Module.finrank k V) →
    ∃ (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
      (D : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
        (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
      (G : GroupScheme k)
      (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
      (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β)
        (fun i ↦ (P i).charts) D.inclusion G E)
      (S : FlagSchemes.CoordinateStabilizer β ranks P D G E A)
      (H : ClosedSubgroup G),
      CoordinateFlagQuotientAt β ranks P D G E A S H

/-- Exponents count the chosen cuts lying strictly beyond a coordinate.
The decrease from a column to a later row detects exactly the cuts it crosses. -/
def blockExponent {n m : ℕ} (ranks : Fin m → ℕ) (i : Fin n) : ℤ :=
  ((Finset.univ.filter fun a ↦ i.val < ranks a).card : ℤ)

def BlockExponentOrder : Prop :=
  ∀ {n m : ℕ} (ranks : Fin m → ℕ) (i j : Fin n),
    blockExponent ranks i < blockExponent ranks j ↔
      ∃ a : Fin m, j.val < ranks a ∧ ranks a ≤ i.val

def earlierPivots {d n : ℕ} (I : Fin d ↪o Fin n) (j : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun r ↦ (I r).val < j

def pivotRank {d n : ℕ} (I : Fin d ↪o Fin n) (j : ℕ) : ℕ :=
  (earlierPivots I j).card

def EchelonVariable {d n : ℕ} (I : Fin d ↪o Fin n) :=
  {p : Fin n × Fin d // p.1 < I p.2 ∧ p.1 ∉ Set.range I}

/-- Incidence rank bounds compare increasing pivot positions componentwise. -/
def PivotRankOrder : Prop :=
  ∀ {d n : ℕ} (I J : Fin d ↪o Fin n),
    (∀ j ≤ n, pivotRank I j ≤ pivotRank J j) ↔ ∀ r, J r ≤ I r

/-- The empty and full pivot tuples are unique, with their intersection ranks. -/
def EndpointPivots : Prop :=
  ∀ n : ℕ,
    (∀ I : Fin 0 ↪o Fin n, I = Fin.castLEOrderEmb (Nat.zero_le n) ∧
      ∀ j ≤ n, pivotRank I j = 0) ∧
    (∀ I : Fin n ↪o Fin n, I = Fin.castLEOrderEmb (le_refl n) ∧
      ∀ j ≤ n, pivotRank I j = j)

/-- With zero-based indices the count i_r - r is unchanged. -/
def EchelonCoordinateCount : Prop :=
  ∀ {d n : ℕ} (I : Fin d ↪o Fin n),
    Nat.card (EchelonVariable I) = ∑ r, ((I r).val - r.val)

def laurentDiagonal {J : Type*} [Fintype J] [DecidableEq J] (R : Type*) [CommRing R] (w : J → ℤ) :
    Matrix.GeneralLinearGroup J (LaurentPolynomial R) where
  val := Matrix.diagonal (fun i ↦ LaurentPolynomial.T (w i))
  inv := Matrix.diagonal (fun i ↦ LaurentPolynomial.T (-w i))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, Matrix.diagonal_one]

/-- Conjugation by a diagonal Laurent matrix on invertible matrices. -/
def laurentConjugate {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]
    (w : J → ℤ) (g : Matrix.GeneralLinearGroup J R) :
    Matrix.GeneralLinearGroup J (LaurentPolynomial R) :=
  laurentDiagonal R w * Matrix.GeneralLinearGroup.map LaurentPolynomial.C g *
    (laurentDiagonal R w)⁻¹

def LaurentConjugateEntry : Prop :=
  ∀ {J R : Type u} [Fintype J] [DecidableEq J] [CommRing R]
    (w : J → ℤ) (g : Matrix.GeneralLinearGroup J R) (i j : J),
    laurentConjugate w g i j = LaurentPolynomial.C (g i j) * LaurentPolynomial.T (w i - w j)

def LaurentConjugateExtension : Prop :=
  ∀ {J R : Type u} [Fintype J] [DecidableEq J] [CommRing R]
    (w : J → ℤ) (g : Matrix.GeneralLinearGroup J R),
    (∃ f : Matrix.GeneralLinearGroup J (Polynomial R),
      Matrix.GeneralLinearGroup.map Polynomial.toLaurent f = laurentConjugate w g) ↔
    ∀ i j, w i < w j → g i j = 0

/-- The matrix calculation tests the actual dynamic parabolic on every test algebra.
Here the value of the cocharacter at the Laurent parameter is diagonal with
the displayed exponents. -/
def LimitGroupMatrixEquations : Prop :=
  ∀ {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J)
    (c : CharacterDescent.Cocharacter G) (w : J → ℤ),
    (∀ (R : TestAlgebra k),
      E.hom.app (CocharacterDynamics.laurentAlgebra R)
        (CocharacterDynamics.cocharacterPoint c (CocharacterDynamics.laurentAlgebra R)
          (CocharacterDynamics.laurentParameter R)) = laurentDiagonal R w) →
    ∀ (D : CocharacterDynamics.LimitDecomposition c)
      (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections D.parabolic ((testSpec k).obj (op R)) ↔
        ∀ i j, w i < w j →
          (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0

/-- The chosen block exponents identify the dynamic parabolic with the
coordinate flag equations on all commutative test algebras. -/
def BlockLimitEquations : Prop :=
  ∀ {k : Type u} [Field k] {n m : ℕ} {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (ranks : Fin m → ℕ) (c : CharacterDescent.Cocharacter G),
    (∀ (R : TestAlgebra k),
      E.hom.app (CocharacterDynamics.laurentAlgebra R)
        (CocharacterDynamics.cocharacterPoint c (CocharacterDynamics.laurentAlgebra R)
          (CocharacterDynamics.laurentParameter R)) =
        laurentDiagonal R (fun i : ULift.{u} (Fin n) ↦ blockExponent ranks i.down)) →
    ∀ (D : CocharacterDynamics.LimitDecomposition c)
      (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections D.parabolic ((testSpec k).obj (op R)) ↔
        ∀ (a : Fin m) (i j : ULift.{u} (Fin n)),
          j.down.val < ranks a → ranks a ≤ i.down.val →
            (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0

/-- Integral exponents define an actual cocharacter of the matrix group. -/
def DiagonalCocharacterExists : Prop :=
  ∀ {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J) (w : J → ℤ),
    ∃ c : CharacterDescent.Cocharacter G,
      ∀ (R : TestAlgebra k) (t : Rˣ),
        (E.hom.app R (CocharacterDynamics.cocharacterPoint c R t) :
          Matrix.GeneralLinearGroup J R).val =
          Matrix.diagonal (fun i ↦ ((t ^ w i : Rˣ) : R))

/-- The block cocharacter gives a genuine dynamic parabolic with the prescribed
matrix equations, including for the empty matrix group. -/
def BlockParabolicExists : Prop :=
  ∀ {k : Type u} [Field k] {n m : ℕ} (G : AffineAlgebraicGroup k)
    (E : (groupPointsFunctor k).obj G.val ≅
      StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))) (ranks : Fin m → ℕ),
    ∃ (c : CharacterDescent.Cocharacter G.val) (D : CocharacterDynamics.LimitDecomposition c),
      (∀ (R : TestAlgebra k) (t : Rˣ),
        (E.hom.app R (CocharacterDynamics.cocharacterPoint c R t) :
          Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val =
          Matrix.diagonal (fun i ↦ ((t ^ blockExponent ranks i.down : Rˣ) : R))) ∧
      ∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ∈ SubgroupSections D.parabolic ((testSpec k).obj (op R)) ↔
          ∀ (a : Fin m) (i j : ULift.{u} (Fin n)),
            j.down.val < ranks a → ranks a ≤ i.down.val →
              (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0

/-- The dynamic block parabolic itself represents the stabilizer, and its
right quotient is the incidence scheme with its matrix action. -/
def DynamicCoordinateFlagQuotient : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n m : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)
    (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
    (D : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    (G : AffineAlgebraicGroup k)
    (E : (groupPointsFunctor k).obj G.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G.val E)
    (S : FlagSchemes.CoordinateStabilizer β ranks P D G.val E A),
    FlagIncidence.HasLocalTransitivity ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G.val E A →
    ∃ (c : CharacterDescent.Cocharacter G.val) (L : CocharacterDynamics.LimitDecomposition c),
      (∀ (R : TestAlgebra k) (t : Rˣ),
        (E.hom.app R (CocharacterDynamics.cocharacterPoint c R t) :
          Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val =
          Matrix.diagonal (fun i ↦ ((t ^ blockExponent ranks i.down : Rˣ) : R))) ∧
      CoordinateFlagQuotientAt β ranks P D G.val E A S L.parabolic

/-- The displayed diagonal powers define cocharacters of the diagonal subgroup
itself, tested using the subgroup inclusion on every affine family. -/
def DiagonalCocharacterInTorus : Prop :=
  ∀ {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J)
    (T : ClosedSubgroup G),
    (∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0) →
    ∀ w : J → ℤ, ∃ c : CharacterDescent.Cocharacter T.group,
      ∀ (R : TestAlgebra k) (t : Rˣ),
        (E.hom.app R (CocharacterDynamics.cocharacterPoint (c ≫ T.inclusion) R t) :
          Matrix.GeneralLinearGroup J R).val = Matrix.diagonal (fun i ↦ ((t ^ w i : Rˣ) : R))

/-- Coordinates on the diagonal subgroup in its identified matrix representation. -/
def DiagonalTorusCoordinates : Prop :=
  ∀ {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J)
    (T : ClosedSubgroup G),
    (∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0) →
    ∃ e : (groupPointsFunctor k).obj T.group ≅ StandardGroups.multiplicativePowerPoints k J,
      ∀ (R : TestAlgebra k) (t : Points T.group.X R),
        (E.hom.app R (t ≫ T.inclusion.hom.hom) : Matrix.GeneralLinearGroup J R).val =
          Matrix.diagonal (fun i ↦ ((e.hom.app R t : J → Rˣ) i : R))

/-- The coordinate projections of the diagonal torus are scheme characters. -/
def DiagonalCoordinateCharacters : Prop :=
  ∀ {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J)
    (T : ClosedSubgroup G), IsAffine G.X.left →
    (∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0) →
    ∃ (e : (groupPointsFunctor k).obj T.group ≅ StandardGroups.multiplicativePowerPoints k J)
      (χ : J → CharacterDescent.Character T.group),
      (∀ (R : TestAlgebra k) (t : Points T.group.X R),
        (E.hom.app R (t ≫ T.inclusion.hom.hom) : Matrix.GeneralLinearGroup J R).val =
          Matrix.diagonal (fun i ↦ ((e.hom.app R t : J → Rˣ) i : R))) ∧
      ∀ (R : TestAlgebra k) (t : Points T.group.X R) (i : J),
        t ≫ (χ i).hom.hom = CocharacterDynamics.unitPoint R ((e.hom.app R t : J → Rˣ) i)

section EchelonCells

open GrassmannianCharts

variable {d n : ℕ}

/-- The pivot rows in the chart associated with the increasing tuple. -/
def pivotSet (I : Fin d ↪o Fin n) : Pivot (ULift.{u} (Fin n)) d :=
  ⟨Finset.univ.map ⟨fun r ↦ ULift.up (I r), fun _ _ h ↦ I.injective (ULift.up.inj h)⟩,
    by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩

abbrev ChartEntry (I : Fin d ↪o Fin n) :=
  Outside (pivotSet.{u} I) × Inside (pivotSet.{u} I)

/-- A free graph entry has its nonpivot row before its pivot column. -/
abbrev CellEntry (I : Fin d ↪o Fin n) :=
  {p : ChartEntry.{u} I // p.1.val.down < p.2.val.down}

abbrev echelonScheme (k : Type u) [Field k] (I : Fin d ↪o Fin n) : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial (CellEntry.{u} I) k)))

/-- In the pivot chart, set every forbidden variable to zero. -/
def echelonInChart (k : Type u) [Field k] (I : Fin d ↪o Fin n) :
    echelonScheme k I ⟶ chartScheme (k := k) (pivotSet.{u} I) :=
  (testSpec k).map (CommAlgCat.ofHom (MvPolynomial.aeval fun p : ChartEntry.{u} I ↦
    if h : p.1.val.down < p.2.val.down then MvPolynomial.X ⟨p, h⟩ else 0)).op

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  (β : Module.Basis (Fin n) k V)

def echelonCell (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d) (I : Fin d ↪o Fin n) :
    echelonScheme k I ⟶ C.scheme :=
  echelonInChart k I ≫ C.chart (pivotSet.{u} I)

/-- The locally closed echelon cell and its equations on all affine families. -/
def EchelonCellImmersion : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V) (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)
    (I : Fin d ↪o Fin n),
    IsClosedImmersion (echelonInChart k I).left ∧
    IsImmersion (echelonCell β C I).left ∧
    Nonempty (echelonScheme k I ≅ (testSpec k).obj (op
      (CommAlgCat.of k (MvPolynomial (ULift.{u} (Fin (∑ r, ((I r).val - r.val)))) k)))) ∧
    ∀ (R : TestAlgebra k) (p : Points C.scheme R),
      (∃ f : Points (echelonScheme k I) R, f ≫ echelonCell β C I = p) ↔
      ∃ f : Points (chartScheme (k := k) (pivotSet.{u} I)) R,
        f ≫ C.chart (pivotSet.{u} I) = p ∧
        ∀ (i : Outside (pivotSet.{u} I)) (j : Inside (pivotSet.{u} I)),
          ¬ i.val.down < j.val.down → matrixOfPoint (pivotSet.{u} I) R f i j = 0

/-- Intersection with the j-th coordinate subspace over a field extension. -/
def intersectionRank {k V F : Type u} [Field k] [AddCommGroup V] [Module k V]
    [Field F] [Algebra k F] {d n : ℕ} (β : Module.Basis (Fin n) k V)
    (L : Plane k V d (CommAlgCat.of k F)) (j : ℕ) : ℕ :=
  Module.finrank F (L.toSubmodule ⊓ FlagIncidence.prefixSubmodule β (CommAlgCat.of k F) j :
    Submodule F (F ⊗[k] V))

/-- Equalities of incidence ranks on the echelon locus. -/
def EchelonCellRank : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V) (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)
    (I : Fin d ↪o Fin n) {F : Type u} [Field F] [Algebra k F]
    (p : Points C.scheme (CommAlgCat.of k F)),
    (∃ f : Points (echelonScheme k I) (CommAlgCat.of k F), f ≫ echelonCell β C I = p) →
    ∀ j, intersectionRank β (C.affinePoints.hom.app (CommAlgCat.of k F) p) j = pivotRank I j

/-- On fields, the incidence ranks characterize the corresponding cell. -/
def EchelonCellRankCriterion : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V) (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)
    (I : Fin d ↪o Fin n) {F : Type u} [Field F] [Algebra k F]
    (p : Points C.scheme (CommAlgCat.of k F)),
    (∃ f : Points (echelonScheme k I) (CommAlgCat.of k F), f ≫ echelonCell β C I = p) ↔
    ∀ j, intersectionRank β (C.affinePoints.hom.app (CommAlgCat.of k F) p) j = pivotRank I j

/-- Every plane over a field extension has an echelon tuple. -/
def EchelonCellCoverage : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V) (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d),
    d ≤ n → ∀ {F : Type u} [Field F] [Algebra k F] (p : Points C.scheme (CommAlgCat.of k F)),
    ∃ (I : Fin d ↪o Fin n) (f : Points (echelonScheme k I) (CommAlgCat.of k F)),
      f ≫ echelonCell β C I = p

end EchelonCells

section ResiduePoints

variable {k : Type u} [Field k]

/-- The field of a scheme point with the algebra structure from the base. -/
abbrev residueBaseAlgebra (X : SchemeOver k) (x : X.left) :
    Algebra k (X.left.residueField x) :=
  (Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom)).hom.toAlgebra

abbrev residueTestAlgebra (X : SchemeOver k) (x : X.left) : TestAlgebra k :=
  letI := residueBaseAlgebra X x
  CommAlgCat.of k (X.left.residueField x)

def residuePoint (X : SchemeOver k) (x : X.left) : Points X (residueTestAlgebra X x) :=
  Over.homMk (X.left.fromSpecResidueField x) (by
    change X.left.fromSpecResidueField x ≫ X.hom =
      Spec.map (Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom))
    exact (Spec.map_preimage _).symm)

open GrassmannianCharts

variable {V : Type u} [AddCommGroup V] [Module k V] {n d : ℕ}
  (β : Module.Basis (Fin n) k V) (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)

/-- The intersection rank of the fiber at a scheme point. -/
def residueRank (x : C.scheme.left) (j : ℕ) : ℕ :=
  letI := residueBaseAlgebra C.scheme x
  intersectionRank β ((C.affinePoints.hom.app (residueTestAlgebra C.scheme x))
    (residuePoint C.scheme x)) j

def rankLocus (I : Fin d ↪o Fin n) : Set C.scheme.left :=
  {x | ∀ j ≤ n, pivotRank I j ≤ residueRank β C x j}

end ResiduePoints

/-- The rank conditions define a closed support and detect exactly the
allowed pivot tuples at scheme points. -/
def ClosedRankLocus : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (C : GrassmannianCharts.ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)
    (I : Fin d ↪o Fin n),
    IsClosed (rankLocus β C I) ∧
    rankLocus β C I =
      ⋃ (J : Fin d ↪o Fin n) (_ : ∀ r, J r ≤ I r), Set.range (echelonCell β C J).left

/-- For the endpoint dimensions the unique cell and its reduced closure are the point scheme. -/
def EchelonEndpointGeometry : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (C : GrassmannianCharts.ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d),
    d = 0 ∨ d = n → ∀ I : Fin d ↪o Fin n,
    Nonempty (C.scheme ≅ FlagSchemes.pointScheme k) ∧
    IsIso (echelonCell β C I) ∧
    IsIso (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range (echelonCell β C I).left))).subschemeι ∧
    rankLocus β C I = Set.univ

section TailRanks

open GrassmannianCharts

variable {k V F : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Field F] [Algebra k F] {d n : ℕ} (β : Module.Basis (Fin n) k V)

/-- Coordinate model for the quotient by the first j basis vectors. -/
def tailProjection (j : ℕ) :
    (F ⊗[k] V) →ₗ[F] ({i : ULift.{u} (Fin n) // j ≤ i.down.val} → F) :=
  (LinearMap.funLeft F F Subtype.val).comp
    (GrassmannianCharts.coordinates (FlagSchemes.liftedBasis β) (CommAlgCat.of k F)).toLinearMap

/-- The coordinate quotient is surjective with kernel the prescribed prefix. -/
def TailProjectionQuotient : Prop :=
  ∀ {k V F : Type u} [Field k] [AddCommGroup V] [Module k V] [Field F] [Algebra k F]
    {n : ℕ} (β : Module.Basis (Fin n) k V) (j : ℕ),
    LinearMap.ker (tailProjection (F := F) β j) = FlagIncidence.prefixSubmodule β (CommAlgCat.of k F) j ∧
    Function.Surjective (tailProjection (F := F) β j)

/-- The rank bound on the map of the plane to the coordinate quotient is the
intersection-dimension inequality. -/
def TailRankComparison : Prop :=
  ∀ {k V F : Type u} [Field k] [AddCommGroup V] [Module k V] [Field F] [Algebra k F]
    {n d : ℕ} (β : Module.Basis (Fin n) k V) (I : Fin d ↪o Fin n)
    (L : Plane k V d (CommAlgCat.of k F)) (j : ℕ),
    pivotRank I j ≤ intersectionRank β L j ↔
      Module.finrank F ((tailProjection β j).comp L.toSubmodule.subtype).range ≤ d - pivotRank I j

end TailRanks

/-- The reduced scheme-theoretic closure has precisely the prescribed incidence ranks. -/
def EchelonReducedClosure : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (C : GrassmannianCharts.ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)
    (I : Fin d ↪o Fin n),
    let D := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range (echelonCell β C I).left))
    AlgebraicGeometry.IsReduced D.subscheme ∧ Set.range D.subschemeι = rankLocus β C I

/-- The echelon graph is obtained by prescribing columns of an upper
unitriangular matrix on every test algebra. -/
def EchelonUpperUnitriangularOrbit : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (C : GrassmannianCharts.ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)
    (I : Fin d ↪o Fin n) (R : TestAlgebra k) (p : Points C.scheme R),
    (∃ f : Points (echelonScheme k I) R, f ≫ echelonCell β C I = p) →
    ∃ g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R,
      (∀ i j, j.down < i.down → g.val i j = 0) ∧ (∀ i, g.val i i = 1) ∧
      (C.affinePoints.hom.app R p).toSubmodule.map
        (GrassmannianCharts.coordinates (FlagSchemes.liftedBasis β) R).toLinearMap =
      (FlagSchemes.coordinateSubmodule R (↑(pivotSet.{u} I).val : Set (ULift.{u} (Fin n)))).map
        (Matrix.toLin' g.val)

/-- Advance one pivot into the next position, preserving all other pivots. -/
def AdvancesPivot {d n : ℕ} (J I : Fin d ↪o Fin n) (r : Fin d) : Prop :=
  (I r).val = (J r).val + 1 ∧ ∀ s, s ≠ r → I s = J s

/-- Componentwise comparison is generated by advances of one pivot. -/
def AdjacentPivotOrder : Prop :=
  ∀ {d n : ℕ} (I J : Fin d ↪o Fin n),
    (∀ r, J r ≤ I r) ↔
      Relation.ReflTransGen (fun K L : Fin d ↪o Fin n ↦ ∃ r, AdvancesPivot K L r) J I

/-- The advance is the transposition of the pivot and the next position. -/
def PivotAdvanceTransposition : Prop :=
  ∀ {d n : ℕ} (J I : Fin d ↪o Fin n) (r : Fin d),
    AdvancesPivot J I r → ∀ s, Equiv.swap (J r) (I r) (J s) = I s

open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots adjointWeightVectors pairing)


/-- The matrix entries of the torus and its coordinate characters on affine families. -/
structure DiagonalCharacters {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J)
    (T : ClosedSubgroup G) where
  coordinates : (groupPointsFunctor k).obj T.group ≅ StandardGroups.multiplicativePowerPoints k J
  character : J → Character T.group
  diagonal (R : TestAlgebra k) (t : Points T.group.X R) :
    (E.hom.app R (t ≫ T.inclusion.hom.hom) : Matrix.GeneralLinearGroup J R).val =
      Matrix.diagonal (fun i ↦ ((coordinates.hom.app R t : J → Rˣ) i : R))
  evaluates (R : TestAlgebra k) (t : Points T.group.X R) (i : J) :
    t ≫ (character i).hom.hom =
      CocharacterDynamics.unitPoint R ((coordinates.hom.app R t : J → Rˣ) i)

namespace DiagonalCharacters

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : GroupScheme k}
  {E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J}
  {T : ClosedSubgroup G}

def ratio (a : DiagonalCharacters E T) (i j : J) : Character T.group :=
  a.character i / a.character j

end DiagonalCharacters

/-- The actual absolute roots are the off-diagonal matrix weights, and the
positive ones for the upper triangular Borel are the upper entries. -/
def TypeAMatrixRoots : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ} (G : AffineAlgebraicGroup k)
    (E : (groupPointsFunctor k).obj G.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))) (T B : ClosedSubgroup G.val),
    GeometricRadicals.IsSplitTorus T.group →
    (∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0) →
    (∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections B ((testSpec k).obj (op R)) ↔
        ∀ (i j : ULift.{u} (Fin n)), j.down < i.down →
          (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0) →
    ∃ a : DiagonalCharacters E T,
      (∀ χ, χ ∈ absoluteRoots T ↔ ∃ i j, i ≠ j ∧ χ = a.ratio i j) ∧
      ∀ α : AbstractPairing.Root T, α ∈ BorelsAndChambers.subgroupRoots T B ↔
        ∃ (i j : ULift.{u} (Fin n)), i.down < j.down ∧ α.val = a.ratio i j

/-- The A03 matrix group with its diagonal torus and upper triangular Borel. -/
structure TypeAPair {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
    (E : GeneralLinearStructure.MatrixPoints G n) where
  torus : ClosedSubgroup G.val
  borel : ClosedSubgroup G.val
  reductive : GeometricRadicals.IsReductive G
  split : GeometricRadicals.IsSplitTorus torus.group
  maximal : RankOneFlag.IsGeometricallyMaximal torus
  isBorel : GeometricBorelConjugacy.IsKBorel borel
  torusInBorel : SchemeDerivedGroup.IsSubgroupOf torus borel
  diagonal (R : TestAlgebra k) (g : Points G.val.X R) :
    g ∈ SubgroupSections torus ((testSpec k).obj (op R)) ↔
      GeneralLinearStructure.IsDiagonal (E.hom.app R g)
  upper (R : TestAlgebra k) (g : Points G.val.X R) :
    g ∈ SubgroupSections borel ((testSpec k).obj (op R)) ↔
      ∀ (i j : ULift.{u} (Fin n)), j.down < i.down →
        (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0
  characters : DiagonalCharacters E torus
  absolute (χ : Character torus.group) :
    χ ∈ absoluteRoots torus ↔ ∃ i j, i ≠ j ∧ χ = characters.ratio i j
  positive (α : AbstractPairing.Root torus) :
    α ∈ BorelsAndChambers.subgroupRoots torus borel ↔
      ∃ (i j : ULift.{u} (Fin n)), i.down < j.down ∧ α.val = characters.ratio i j

/-- Existence for the canonical matrix realization, with its scheme arguments. -/
def CanonicalTypeAPair : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G : AffineAlgebraicGroup k) (E : GeneralLinearStructure.MatrixPoints G n), Nonempty (TypeAPair E)

section TypeABase

open AbstractPairing (Datum Root)
open BorelsAndChambers (positiveRoots subgroupRoots)
open SimpleRoots (IsBaseFor evaluate)
open StandardParabolicLevi (HasFace StandardParabolic)

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
  {E : GeneralLinearStructure.MatrixPoints G n} {T : ClosedSubgroup G.val}

/-- The subset of simple roots with both coordinates in the same block. -/
def uncutSimpleRoots (a : DiagonalCharacters E T) {m : ℕ} (ranks : Fin m → ℕ) : Set (Root T) :=
  {α | ∃ (i j : ULift.{u} (Fin n)), j.down.val = i.down.val + 1 ∧
    α.val = a.ratio i j ∧ ∀ r : Fin m, ranks r ≠ j.down.val}

/-- The roots of the actual based root datum are the indicated consecutive ratios. -/
def TypeASimpleRoots : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
    {E : GeneralLinearStructure.MatrixPoints G n} (M : TypeAPair E) [IsCommMonObj M.torus.group.X]
    (D : Datum M.torus) (c : Cocharacter M.torus.group) (b : D.rootDatum.Base),
    positiveRoots M.torus c = subgroupRoots M.torus M.borel → IsBaseFor D.rootDatum (evaluate D c) b →
    ∀ α : Root M.torus, α ∈ b.support ↔ ∃ (i j : ULift.{u} (Fin n)),
      j.down.val = i.down.val + 1 ∧ α.val = M.characters.ratio i j

/-- Every subset of the simple roots is obtained from a set of interior block cuts. -/
def TypeABlockCuts : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
    {E : GeneralLinearStructure.MatrixPoints G n} (M : TypeAPair E) [IsCommMonObj M.torus.group.X]
    (D : Datum M.torus) (c : Cocharacter M.torus.group) (b : D.rootDatum.Base),
    positiveRoots M.torus c = subgroupRoots M.torus M.borel → IsBaseFor D.rootDatum (evaluate D c) b →
    ∀ I : Set (Root M.torus), I ⊆ b.support → ∃ (m : ℕ) (ranks : Fin m → ℕ),
      StrictMono ranks ∧ (∀ r, 0 < ranks r ∧ ranks r < n) ∧ uncutSimpleRoots M.characters ranks = I

/-- The block powers give a cocharacter in the prescribed face. Every limit
parabolic in that face has exactly the same block equations on affine families. -/
def TypeABlockParabolics : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
    {E : GeneralLinearStructure.MatrixPoints G n} (M : TypeAPair E) [IsCommMonObj M.torus.group.X]
    (D : Datum M.torus) (c : Cocharacter M.torus.group) (b : D.rootDatum.Base),
    positiveRoots M.torus c = subgroupRoots M.torus M.borel → IsBaseFor D.rootDatum (evaluate D c) b →
    ∀ {m : ℕ} (ranks : Fin m → ℕ),
      uncutSimpleRoots M.characters ranks ⊆ b.support ∧
      (∃ lam : Cocharacter M.torus.group, HasFace b (uncutSimpleRoots M.characters ranks) lam ∧
        ∀ (R : TestAlgebra k) (t : Rˣ),
          (E.hom.app R (CocharacterDynamics.cocharacterPoint (lam ≫ M.torus.inclusion) R t) :
            Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val =
            Matrix.diagonal (fun i ↦ ((t ^ blockExponent ranks i.down : Rˣ) : R))) ∧
      ∀ lam : Cocharacter M.torus.group, HasFace b (uncutSimpleRoots M.characters ranks) lam →
        ∀ (L : CocharacterDynamics.LimitDecomposition (lam ≫ M.torus.inclusion))
          (R : TestAlgebra k) (g : Points G.val.X R),
          g ∈ SubgroupSections L.parabolic ((testSpec k).obj (op R)) ↔
          ∀ (r : Fin m) (i j : ULift.{u} (Fin n)), j.down.val < ranks r → ranks r ≤ i.down.val →
            (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0

/-- An actual standard parabolic of the canonical pair gives the equivariant
right quotient by the scheme stabilizer of the associated coordinate flag. -/
def StandardCoordinateFlagQuotient : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n m : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)
    (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
    (F : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    (G : AffineAlgebraicGroup k) (E : GeneralLinearStructure.MatrixPoints G n)
    (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β) (fun i ↦ (P i).charts) F.inclusion G.val E)
    (S : FlagSchemes.CoordinateStabilizer β ranks P F G.val E A)
    (M : TypeAPair E) [IsCommMonObj M.torus.group.X]
    (D : Datum M.torus) (c : Cocharacter M.torus.group) (b : D.rootDatum.Base),
    positiveRoots M.torus c = subgroupRoots M.torus M.borel → IsBaseFor D.rootDatum (evaluate D c) b →
    ∀ (U : OrderedRootProducts.RootSubgroupFamily M.torus)
      (H : StandardParabolic M.borel D b U (uncutSimpleRoots M.characters ranks)),
      FlagIncidence.HasLocalTransitivity ranks (FlagSchemes.liftedBasis β)
        (fun i ↦ (P i).charts) F.inclusion G.val E A →
      CoordinateFlagQuotientAt β ranks P F G.val E A S H.limitGroups.parabolic

end TypeABase

section TypeAWeylAction

open AbstractPairing (Datum Root)
open BruhatOrbitParametrization (IsRepresentative)
open DatumAndWeyl (Identification)
open CategoryTheory.CartesianMonoidalCategory

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
  {E : GeneralLinearStructure.MatrixPoints G n} (M : TypeAPair E) [IsCommMonObj M.torus.group.X]
  (D : Datum M.torus) (W : Identification D)

/-- Coordinate permutations realize the Weyl action of the scheme normalizer. -/
structure WeylPermutations where
  equiv : D.rootDatum.weylGroup ≃* Equiv.Perm (ULift.{u} (Fin n))
  characters (w : D.rootDatum.weylGroup) (i : ULift.{u} (Fin n)) :
    (W.labelEquiv w).val (M.characters.character i) = M.characters.character (equiv w i)
  reflection (α : Root M.torus) (i j : ULift.{u} (Fin n)) :
    i ≠ j → α.val = M.characters.ratio i j →
    equiv (RootPairing.weylGroup.ofIdx D.rootDatum α) = Equiv.swap i j
  matrices (w : D.rootDatum.weylGroup) (x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X) :
    IsRepresentative W w x → ∀ (i j : ULift.{u} (Fin n)), i ≠ equiv w j →
      (E.hom.app (CommAlgCat.of k k) (toUnit _ ≫ x ≫ W.normalizer.inclusion.hom.hom) :
        Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) k).val i j = 0

/-- The actual root-datum Weyl group is the full permutation group. -/
def TypeAWeylAction : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
    {E : GeneralLinearStructure.MatrixPoints G n} (M : TypeAPair E) [IsCommMonObj M.torus.group.X]
    (D : Datum M.torus) (W : Identification D),
    (∀ w, ∃ x, IsRepresentative W w x) → Nonempty (WeylPermutations M D W)

end TypeAWeylAction

section GrassmannianBruhat

open AbstractPairing (Datum Root)
open BorelsAndChambers (positiveRoots subgroupRoots)
open BruhatOrbitParametrization (IsRepresentative)
open DatumAndWeyl (Identification)
open SimpleRoots (IsBaseFor evaluate)
open CategoryTheory.CartesianMonoidalCategory

/-- The one-step flag quotient identifies the D07 orbit schemes and their
Bruhat order with the echelon cells and componentwise pivot order. -/
def GrassmannianBruhat : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n d : ℕ} (β : Module.Basis (Fin n) k V), 0 < n → d ≤ n →
    let ranks : Fin 1 → ℕ := fun _ ↦ d
    ∀ (P : ∀ i : Fin 1, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
      (F : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
        (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
      (G : AffineAlgebraicGroup k) (E : GeneralLinearStructure.MatrixPoints G n)
      (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β)
        (fun i ↦ (P i).charts) F.inclusion G.val E)
      (S : FlagSchemes.CoordinateStabilizer β ranks P F G.val E A),
      FlagIncidence.HasLocalTransitivity ranks (FlagSchemes.liftedBasis β)
        (fun i ↦ (P i).charts) F.inclusion G.val E A →
      ∃ (M : TypeAPair E) (h : IsCommMonObj M.torus.group.X), letI := h
        ∃ (D : Datum M.torus) (W : Identification D) (U : OrderedRootProducts.RootSubgroupFamily M.torus)
          (c : Cocharacter M.torus.group) (b : D.rootDatum.Base),
          positiveRoots M.torus c = subgroupRoots M.torus M.borel ∧ IsBaseFor D.rootDatum (evaluate D c) b ∧
          let I := uncutSimpleRoots M.characters ranks
          ∃ H : StandardParabolicLevi.StandardParabolic M.borel D b U I,
            CoordinateFlagQuotientAt β ranks P F G.val E A S H.limitGroups.parabolic ∧
            ∃ (R : QuotientEmbedding.Presentation H.limitGroups.parabolic)
              (e : R.scheme ≅ (P 0).charts.scheme) (W₀ : WeylPermutations M D W)
              (n₀ : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X))
              (a : ModObj G.val.X R.scheme)
              (O : D.rootDatum.weylGroup → SchemeOver k) (j : ∀ w, O w ⟶ R.scheme)
              (labels : {w // PartialFlags.IsMinimal D b I w} ≃ (Fin d ↪o Fin n)),
              (∀ w, IsRepresentative W w (n₀ w)) ∧
              R.projection ≫ e.hom = orbitMap A.onFlags S.point ≫ F.inclusion ≫ Pi.π _ 0 ∧
              lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ R.projection) ≫ a.smul =
                μ[G.val.X] ≫ R.projection ∧
              (∀ w, Set.range (j w).left = Set.range
                (lift M.borel.inclusion.hom.hom (toUnit M.borel.group.X ≫ n₀ w ≫
                  W.normalizer.inclusion.hom.hom ≫ R.projection) ≫ a.smul).left) ∧
              (∀ w : {w // PartialFlags.IsMinimal D b I w},
                ((pivotSet.{u} (labels w)).val : Set (ULift.{u} (Fin n))) =
                  (W₀.equiv w.val) '' {i | i.down.val < d} ∧
                ∃ f : O w.val ≅ echelonScheme k (labels w),
                  f.hom ≫ echelonCell β (P 0).charts (labels w) = j w.val ≫ e.hom) ∧
              (∀ v w : {w // PartialFlags.IsMinimal D b I w},
                SchubertClosures.SubwordLE D.rootDatum b v.val w.val ↔ ∀ r, labels v r ≤ labels w r) ∧
              ∀ (v w : {w // PartialFlags.IsMinimal D b I w}) (r : Fin d),
                AdvancesPivot (labels v) (labels w) r →
                ∃ α : Root M.torus, α ∈ b.support ∧
                  α.val = M.characters.ratio (ULift.up (labels v r)) (ULift.up (labels w r)) ∧
                  RootPairing.weylGroup.ofIdx D.rootDatum α * w.val = v.val ∧
                  SimpleRoots.wordLength D.rootDatum b w.val = SimpleRoots.wordLength D.rootDatum b v.val + 1

end GrassmannianBruhat

end

end LinearAlgebraicGroups.Specs.GrassmannianExample
