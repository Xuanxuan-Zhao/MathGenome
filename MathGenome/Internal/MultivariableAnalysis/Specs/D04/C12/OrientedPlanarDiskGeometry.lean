import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SurfaceAssembly

/-! Pure geometry for the disks in paper.tex, d04:12:local-meaning.
The same linear isometry works for every positive radius. The boundary below
is the shared intrinsic manifold boundary, and normality refers to the shared
canonical tangent spaces. No integration or vector field is assumed. -/
noncomputable section
open Set
open scoped RealInnerProductSpace ContDiff
namespace Specs.D04.C12.OrientedPlanarDiskGeometry
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C10.SurfaceAssembly.Model
namespace Model

def diskParameters (r : ℝ) : Set (E 2) := {u | u 0 ^ 2 + u 1 ^ 2 ≤ r ^ 2}

def planarDisk (x N : E 3) (r : ℝ) : Set (E 3) :=
  {y | ⟪y - x, N⟫ = 0 ∧ dist y x ≤ r}

def planarCircle (x N : E 3) (r : ℝ) : Set (E 3) :=
  {y | ⟪y - x, N⟫ = 0 ∧ dist y x = r}

end Model
open Model
abbrev diskParametersType := ℝ → Set (E 2)
def diskParametersValue : diskParametersType := Model.diskParameters
abbrev planarDiskType := E 3 → E 3 → ℝ → Set (E 3)
def planarDiskValue : planarDiskType := Model.planarDisk
abbrev planarCircleType := E 3 → E 3 → ℝ → Set (E 3)
def planarCircleValue : planarCircleType := Model.planarCircle

def disk_geometryType : Prop :=
  ∀ x N : E 3, ‖N‖ = 1 → ∃ A : E 2 →ₗᵢ[ℝ] E 3,
    (∀ u, ⟪A u, N⟫ = 0) ∧
    (∀ v : E 3, ⟪v, N⟫ = 0 → ∃ u, A u = v) ∧
    ∀ r : ℝ, 0 < r →
      (fun u => x + A u) '' diskParameters r = planarDisk x N r ∧
      Compact (planarDisk x N r) ∧
      IsEmbeddedManifold 1 2 (planarDisk x N r) ∧
      intrinsicBoundary 1 2 (planarDisk x N r) = planarCircle x N r ∧
      ∃ ν : UnitNormalField (planarDisk x N r), ∀ y, ν.toFun y = N

end Specs.D04.C12.OrientedPlanarDiskGeometry
