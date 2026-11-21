import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LefschetzRelativeCohomology

/-! Higher ordinary rational homology in the planar-region lemma,
paper.tex 4789–4809 and 4820–4825. The input is precisely the canonical
`PlanarRegion`, including reflex corners. No homological or orientation
certificate is part of that input. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace P202Specs.PlanarRegionHigherHomology
open P202Specs.PlanarRegionTopology P202Specs.SingularChains
open P202Specs.RelativeFundamentalClass P202Specs.CohomologyPairs P202Specs.LocalOrientation

/-- The actual boundary as a subset of the actual carrier. -/
def carrierBoundary (R : PlanarRegion) : Set R.carrier :=
  {x | x.val ∈ R.boundary}

namespace Expected

/-- The complete assigned conclusion, on the original integer-graded ordinary
singular groups. -/
def higherHomology : Prop := ∀ (R : PlanarRegion) (n : ℕ), 2 ≤ n →
  IsZero (homology ℚ ℚ (TopCat.of R.carrier) (n : ℤ))

/-- Geometric applicability of the actual upstream duality interface. -/
def dualityGeometry : Prop := ∀ R : PlanarRegion,
  ∃ A : SmoothManifolds.ModelData.TopologicalManifold 2 .halfSpace R.carrier,
    manifoldBoundary A = carrierBoundary R ∧
      Nonempty (Collar (manifoldBoundary A))

/-- Connectedness and a nonempty boundary force the genuine degree-zero
relative cohomology group to vanish. -/
def relativeDegreeZero : Prop := ∀ R : PlanarRegion,
  IsZero (relativeCohomology ℚ ℚ
    (boundaryPair R.carrier (carrierBoundary R)) 0)

/-- Rational orientability is a conclusion on the actual interior, for any
of its topological manifold atlases. It is not a region input certificate. -/
def interiorOrientable : Prop := ∀ (R : PlanarRegion) (B : Set R.carrier),
  B = carrierBoundary R → ∀ AI : Manifold 2 (Interior B), Nonempty (Orientation ℚ AI)

/-- Assembly through the first Lefschetz cap isomorphism and its
above-dimension consequence. The orientation premise is proved separately. -/
def vanishingFromOrientation : Prop := interiorOrientable → higherHomology

end Expected
end P202Specs.PlanarRegionHigherHomology
