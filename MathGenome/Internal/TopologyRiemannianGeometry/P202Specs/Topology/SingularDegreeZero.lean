import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import Mathlib.Topology.Connected.PathConnected

/-! Degree zero and the elementary spaces in paper.tex, §3.1.
The coefficients are an arbitrary module, so the case `R = ℤ` includes every
abelian group. Path components mean the quotient by `Joined`, without any
local connectedness or separation hypothesis. -/
noncomputable section
open CategoryTheory

namespace P202Specs.SingularDegreeZero
open P202Specs.SingularChains
universe u v w

/-- Finite sums of coefficients indexed by path components. -/
abbrev ComponentSums (M : Type v) [AddCommGroup M] (X : TopCat.{w}) :=
  ZerothHomotopy X →₀ M

/-- The sum of the coefficients of the path components. -/
def componentSum (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] (X : TopCat.{w}) : ComponentSums M X →ₗ[R] M :=
  sumCoefficients R M (ZerothHomotopy X)

/-- A point, in the same universe as the spaces under consideration. -/
abbrev point : TopCat.{w} := TopCat.of (PUnit.{w+1})

/-- The zero sphere as two discrete points. -/
abbrev zeroSphere : TopCat.{w} := TopCat.of (ULift.{w} (Fin 2))

namespace Expected

def degreeZero : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (X : TopCat.{w}), Nonempty (homology R M X 0 ≃ₗ[R] ComponentSums M X)

def reducedDegreeZero : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (X : TopCat.{w}),
    Nonempty (reducedHomology R M X 0 ≃ₗ[R] LinearMap.ker (componentSum R M X))

def emptyOrdinary : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (X : TopCat.{w}) [IsEmpty X] (n : ℤ), Limits.IsZero (homology R M X n)

def emptyReducedMinusOne : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (X : TopCat.{w}) [IsEmpty X], Nonempty (reducedHomology R M X (-1) ≃ₗ[R] M)

def emptyReducedOther : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (X : TopCat.{w}) [IsEmpty X] (n : ℤ), n ≠ -1 →
    Limits.IsZero (reducedHomology R M X n)

def pointOrdinaryZero : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Nonempty (homology R M point.{w} 0 ≃ₗ[R] M)

def pointOrdinaryOther : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℤ), n ≠ 0 → Limits.IsZero (homology R M point.{w} n)

def pointReduced : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℤ), Limits.IsZero (reducedHomology R M point.{w} n)

def sphereOrdinaryZero : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Nonempty (homology R M zeroSphere.{w} 0 ≃ₗ[R] (M × M))

def sphereOrdinaryOther : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℤ), n ≠ 0 → Limits.IsZero (homology R M zeroSphere.{w} n)

def sphereReducedZero : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Nonempty (reducedHomology R M zeroSphere.{w} 0 ≃ₗ[R] M)

def sphereReducedOther : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℤ), n ≠ 0 → Limits.IsZero (reducedHomology R M zeroSphere.{w} n)

end Expected
end P202Specs.SingularDegreeZero
