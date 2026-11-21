import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.OrientedPlanarDiskGeometry
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions

/-! The unsigned integral on the canonical embedded disk, paper.tex
`d04:12:local-meaning`. The affine map is arbitrary subject only to being
isometric and parametrizing the stated disk. Integrability and a genuine
chart partition are conclusions. -/
noncomputable section
open Set
open scoped RealInnerProductSpace ContDiff
namespace Specs.D04.C12.PlanarDiskIntegralBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.OrientedPlanarDiskGeometry.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C06.JordanRegions.Model

def disk_integralType : Prop :=
  ∀ (x N : E 3), ‖N‖ = 1 → ∀ A : E 2 →ₗᵢ[ℝ] E 3,
    (∀ r : ℝ, 0 < r → (fun u => x + A u) '' diskParameters r = planarDisk x N r) →
    ∀ (r : ℝ), 0 < r → ∀ g : E 3 → ℝ, ContinuousOn g (planarDisk x N r) →
      (∃ P : ChartPartition 1 2 (planarDisk x N r)
        (tsupport (fun y : planarDisk x N r => g y)),
        ∀ i, ProperIntegrable (localizedDensityCoefficient
          (fun y : planarDisk x N r => g y) (P.chart i) (P.weight i))) ∧
      RegionIntegrable (fun u : diskParameters r => g (x + A u)) ∧
      surfaceIntegral (planarDisk x N r) (fun y => g y) =
        regionIntegral (fun u : diskParameters r => g (x + A u))

/-- The same bridge gives the actual surface area and its positive
normalization, with no parametrization certificate among the hypotheses. -/
def disk_areaType : Prop :=
  ∀ (x N : E 3), ‖N‖ = 1 → ∀ (r : ℝ), 0 < r →
    surfaceIntegral (planarDisk x N r) (fun _ => 1) = Real.pi * r ^ 2 ∧
      0 < surfaceIntegral (planarDisk x N r) (fun _ => 1)

end Specs.D04.C12.PlanarDiskIntegralBridge
