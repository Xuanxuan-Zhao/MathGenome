import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization

/-!
Original target of paper.tex 5093–5137. The canonical intrinsic area,
curvature, boundary integrals, and regional geometry are shared with the
upstream localization Spec. No orientation, connectedness or nonemptiness
hypothesis is imposed; both surface model kinds are retained.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData

namespace P202Specs.GlobalGaussBonnet
open P202.MetricData P202.ConnectionData P202.CurvatureData
universe u

namespace Expected

/-- Full original Gauss–Bonnet theorem. The connection and its curvature
tensor are arbitrary representatives of the actual Levi–Civita geometry.
All boundary presentations give the formula with the intrinsic area measure
and the rational singular-homology Euler characteristic. -/
def globalGaussBonnet : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), P202.LeviCivitaData.IsLeviCivita g C →
    ∀ T : CurvatureTensor S, RepresentsCurvature C T →
      Nonempty (BoundaryPresentation g) ∧
      ∃ μ : @Measure M (borel M), IsAreaMeasure g μ ∧
        (letI : MeasurableSpace M := borel M
         Integrable (gaussianCurvature g T) μ) ∧
        ∀ B : BoundaryPresentation g,
          (∀ i, IntervalIntegrable (B.curvatureIntegrand C i) volume
            (B.arc i).left (B.arc i).right) ∧
          ∃ h : P202Specs.EulerPoincare.HomologyFiniteType ℚ M,
            totalCurvature g T μ + B.curvatureIntegral C =
              2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler M h : ℝ)

end Expected
end P202Specs.GlobalGaussBonnet
