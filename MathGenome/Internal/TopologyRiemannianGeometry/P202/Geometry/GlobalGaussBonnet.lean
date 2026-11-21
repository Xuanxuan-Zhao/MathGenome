import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnet
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetLocalization
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetBoundaryGluing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetCornerGluing

/-!
The global formula of paper.tex 5093–5137 follows by applying the local
formula to the actual chart regions, canceling their inward-normal edge
integrals, summing their metric exterior angles, and using the Euler
identity for their actual component closures. The area measure is the
canonical Riemannian density measure. No orientation, connectedness or
nonemptiness of the original surface is assumed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurvatureData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction

namespace P202.GlobalGaussBonnet
universe u

/-- Gauss–Bonnet for every compact Riemannian surface, with its intrinsic
inward-normal boundary integral and rational singular-homology Euler invariant. -/
theorem globalGaussBonnet :
    P202Specs.GlobalGaussBonnet.Expected.globalGaussBonnet.{u} := by
  intro kind M _ _ S g C hC T hT
  obtain ⟨hB, μ, hμ, hint, hboundaryInt⟩ := exists_global_integrals g C hC T hT
  refine ⟨hB, μ, hμ, hint, ?_⟩
  intro B
  refine ⟨hboundaryInt B, ?_⟩
  obtain ⟨D, _⟩ := P202.SurfaceRegionsEuler.surfaceRegionsEuler S
  let G : ∀ j, RegionalChartGeometry g D j :=
    fun j => Classical.choice (exists_regionalChartGeometry g D j)
  have hlocal (j : Fin D.regionCount) :=
    regionalChartGeometry_local_formula (G j) C hC T hT μ hμ
  let A : ∀ j i, P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i) :=
    fun j => Classical.choice (hlocal j).2.1
  let s : ∀ j, Fin (D.region j).boundaryCount → ℝ :=
    fun j => (hlocal j).1.choose
  have hs : ∀ j,
      P202Specs.PlanarRegionTopology.IsInducedBoundaryOrientation (D.region j) (s j) :=
    fun j => (hlocal j).1.choose_spec
  exact (assemble_regionalChartGeometry g C hC T hT μ hμ D B G A s hs
    (regional_boundary_gluing g C hC D G A s hs B)
    (CornerGluing.regionalExteriorAngleSum g D G A s hs)).2

end P202.GlobalGaussBonnet
