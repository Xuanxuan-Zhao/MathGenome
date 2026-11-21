import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.EulerPoincare

/-! The complete planar-region lemma, paper.tex 4760–4828.
The invariant is the canonical rational singular-homology Euler invariant;
no CW structure, triangulation, or homological finiteness is assumed. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace P202Specs.PlanarRegionEuler
open P202Specs.PlanarRegionTopology P202Specs.SingularChains
open P202Specs.EulerPoincare

abbrev rationalHomology (R : PlanarRegion) (n : ℕ) :=
  homology ℚ ℚ (TopCat.of R.carrier) (n : ℤ)

namespace Expected

def degreeZero : Prop := ∀ R : PlanarRegion,
  Nonempty (rationalHomology R 0 ≃ₗ[ℚ] ℚ)

def firstBettiNumber : Prop := ∀ R : PlanarRegion,
  FiniteDimensional ℚ (rationalHomology R 1) ∧
    Module.finrank ℚ (rationalHomology R 1) = R.boundaryCount - 1

def higherHomology : Prop := ∀ (R : PlanarRegion) (n : ℕ), 2 ≤ n →
  IsZero (rationalHomology R n)

def boundaryOrientation : Prop := ∀ R : PlanarRegion,
  ∃ S : ComplementData R, BoundaryOrientationConclusion R S.sides

/-- The full source conclusion, with its finite-type domain justified.
`BoundaryOrientationConclusion` includes the bounded side on the left for
exactly the outer curve, and on the right for every other curve, for every
choice of induced boundary orientation. -/
def planarRegionEuler : Prop := ∀ R : PlanarRegion,
  ∃ h : HomologyFiniteType ℚ R.carrier,
    topologicalEuler R.carrier h = 2 - (R.boundaryCount : ℤ) ∧
      ∃ S : ComplementData R, BoundaryOrientationConclusion R S.sides

/-- Algebraic assembly from the homology calculations and boundary orientation. -/
def assembly : Prop :=
  degreeZero → firstBettiNumber → higherHomology → boundaryOrientation → planarRegionEuler

/-- The two independent positive-degree homology calculations suffice; H₀ and
the complete orientation conclusion are supplied by the parent proof. -/
def eulerFromHomology : Prop := firstBettiNumber → higherHomology → planarRegionEuler

end Expected
end P202Specs.PlanarRegionEuler
