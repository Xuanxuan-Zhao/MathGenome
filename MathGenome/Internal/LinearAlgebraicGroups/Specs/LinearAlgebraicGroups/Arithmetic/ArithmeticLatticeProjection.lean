import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.Quotient

open Set Topology MeasureTheory
open scoped Pointwise RestrictedProduct

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

open AdelicGroups
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization RationalPoints)

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
variable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)

/-- The finite product of the actual local point groups. -/
abbrev FinitePoints (T : Finset D.Place) :=
  ∀ w : (↑T : Set D.Place), LocalPoints D i w.1

/-- Finite projection of rational points. -/
def rationalProjection (T : Finset D.Place) : RationalPoints G →* FinitePoints D i T where
  toFun g w := localPoint D i w.1 g
  map_one' := funext fun w => map_one (localPoint D i w.1)
  map_mul' g h := funext fun w => map_mul (localPoint D i w.1) g h

/-- Restrict a finite tuple to a subproduct. -/
def forgetPlaces {J T : Finset D.Place} (h : J ⊆ T) :
    FinitePoints D i T →* FinitePoints D i J where
  toFun x w := x ⟨w.1, h w.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The rational diagonal inside the full adelic point group. -/
def diagonalSubgroup : Subgroup (Adeles D i ∅) where
  carrier := Specs.DiscreteDiagonals.groupDiagonalImage D i
  one_mem' := ⟨1, fun w => (map_one (localPoint D i w.1)).symm⟩
  mul_mem' := by
    rintro x y ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g * h, fun w => by change x w * y w = _; rw [hg, hh, map_mul]⟩
  inv_mem' := by
    rintro x ⟨g, hg⟩
    exact ⟨g⁻¹, fun w => by change (x w)⁻¹ = _; rw [hg, map_inv]⟩

/-- Rational points lying in the chosen compact open subgroup away from T. -/
def arithmeticSubgroup (T : Finset D.Place) (U : Subgroup (Adeles D i T)) :
    Subgroup (RationalPoints G) where
  carrier := {g | ∃ x ∈ U, ∀ w : Outside D T, x w = localPoint D i w.1 g}
  one_mem' := ⟨1, U.one_mem, fun w => (map_one (localPoint D i w.1)).symm⟩
  mul_mem' := by
    rintro g h ⟨x, hx, hg⟩ ⟨y, hy, hh⟩
    exact ⟨x * y, U.mul_mem hx hy, fun w => by change x w * y w = _; rw [hg, hh, map_mul]⟩
  inv_mem' := by
    rintro g ⟨x, hx, hg⟩
    exact ⟨x⁻¹, U.inv_mem hx, fun w => by change (x w)⁻¹ = _; rw [hg, map_inv]⟩

/-- The arithmetic subgroup as a subgroup of the finite product. -/
def lattice (T : Finset D.Place) (U : Subgroup (Adeles D i T)) :
    Subgroup (FinitePoints D i T) :=
  (arithmeticSubgroup D i T U).map (rationalProjection D i T)

/-- The product of the integral groups away from T, with full archimedean factors. -/
def integralOutside (T : Finset D.Place) : Subgroup (Adeles D i T) where
  carrier := {x | ∀ w : Outside D T, x w ∈ localSubgroup D i w.1}
  one_mem' w := (localSubgroup D i w.1).one_mem
  mul_mem' hx hy w := (localSubgroup D i w.1).mul_mem (hx w) (hy w)
  inv_mem' hx w := (localSubgroup D i w.1).inv_mem (hx w)

/-- Unimodularity expressed by the existence of a Haar measure invariant on both sides. -/
def Unimodular (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  letI : MeasurableSpace P := borel P
  ∃ μ : Measure P, μ.IsHaarMeasure ∧ μ.IsMulRightInvariant

/-- A finite invariant Borel measure of full support on the space of left cosets. -/
def FiniteInvariantQuotientMeasure {P : Type*} [Group P] [TopologicalSpace P]
    (L : Subgroup P) : Prop :=
  letI : MeasurableSpace (P ⧸ L) := borel (P ⧸ L)
  ∃ μ : Measure (P ⧸ L), IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure ∧
    SMulInvariantMeasure P (P ⧸ L) μ

end LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

namespace LinearAlgebraicGroups.Specs.ArithmeticLatticeProjection

open Arithmetic Arithmetic.AdelicGroups Arithmetic.ArithmeticLatticeProjection
open Specs.IntegralModels (MatrixRealization RationalPoints)

/-- The usual outside product is compact open if every omitted archimedean group is compact. -/
def compactOpenOutside : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (T : Finset D.Place),
    (∀ w : D.InfinitePlace, Sum.inr w ∉ T → CompactSpace (LocalPoints D i (.inr w))) →
    IsCompact (integralOutside D i T : Set (Adeles D i T)) ∧
    IsOpen (integralOutside D i T : Set (Adeles D i T))

/-- The full adelic compactness assumption yields a cocompact discrete lattice in a finite
product, with finite invariant covolume. The topological argument works for every affine
algebraic group with compact full adelic quotient. -/
def latticeConstruction : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (T : Finset D.Place) (U : Subgroup (Adeles D i T)),
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
    T.Nonempty → IsCompact (U : Set (Adeles D i T)) → IsOpen (U : Set (Adeles D i T)) →
    let L := lattice D i T U
    (arithmeticSubgroup D i T U : Set (RationalPoints G)).InjOn (rationalProjection D i T) ∧
    IsClosed (L : Set (FinitePoints D i T)) ∧ IsDiscrete (L : Set (FinitePoints D i T)) ∧
    CompactSpace (FinitePoints D i T ⧸ L) ∧
    (∃ C : Set (FinitePoints D i T), IsCompact C ∧ C * (L : Set (FinitePoints D i T)) = univ) ∧
    Unimodular (FinitePoints D i T) ∧ FiniteInvariantQuotientMeasure L

/-- Every nonempty subproduct outside the noncompact S-product has a nondiscrete projected
arithmetic subgroup. Its closure is cocompact and the quotient has finite invariant measure. -/
def projectionProperties : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S T J : Finset D.Place) (U : Subgroup (Adeles D i T))
    (_hS : S ⊆ T) (hJ : J ⊆ T),
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
    ¬ CompactSpace (FinitePoints D i S) →
    J.Nonempty → Disjoint J S →
    IsCompact (U : Set (Adeles D i T)) → IsOpen (U : Set (Adeles D i T)) →
    let P := (lattice D i T U).map (forgetPlaces D i hJ)
    ¬ IsDiscrete (P : Set (FinitePoints D i J)) ∧
    ∃ H : Subgroup (FinitePoints D i J),
      (H : Set (FinitePoints D i J)) = closure (↑P : Set (FinitePoints D i J)) ∧
      CompactSpace (FinitePoints D i J ⧸ H) ∧ FiniteInvariantQuotientMeasure H

/-- The individual local groups are unimodular under the same adelic compactness hypothesis. -/
def localUnimodularity : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G),
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
    ∀ w : D.Place, Unimodular (LocalPoints D i w)

end LinearAlgebraicGroups.Specs.ArithmeticLatticeProjection
