import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.NegligibleSeams
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.RegularLevelsAndGraphs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Sphere example d04:10:sphere. All global integrals below are the canonical
Gram-density integrals of SurfaceAssembly. No sphere-area value is a definition. -/
noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
namespace Specs.D04.C10.SphereAreaFlux
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.AreaIntegral.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C10.NegligibleSeams.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
namespace Model

def sphere (R : ℝ) : Set (E 3) := {x | ‖x‖ = R}
def parameterDomain : Set (E 2) :=
  {u | 0 < u 0 ∧ u 0 < Real.pi ∧ 0 < u 1 ∧ u 1 < 2 * Real.pi}
def parametrization (R : ℝ) (u : E 2) : E 3 :=
  WithLp.toLp 2 ![R * Real.sin (u 0) * Real.cos (u 1),
    R * Real.sin (u 0) * Real.sin (u 1), R * Real.cos (u 0)]
def radialNormal (R : ℝ) (x : E 3) : E 3 := R⁻¹ • x
/-- This includes both poles and exactly the omitted half great circle. -/
def meridian (R : ℝ) : Set (E 3) :=
  (fun t : ℝ => parametrization R (WithLp.toLp 2 ![t, 0])) '' Icc 0 Real.pi
/-- Strictly interior regular compact rectangles; delta tends to zero. -/
def truncationDomain (j : ℕ) : Set (E 2) :=
  let δ := Real.pi / (j + 3 : ℝ)
  {u | δ ≤ u 0 ∧ u 0 ≤ Real.pi - δ ∧ δ ≤ u 1 ∧ u 1 ≤ 2 * Real.pi - δ}
end Model
open Model

def parametrization_smoothType : Prop :=
  ∀ R : ℝ, ContDiff ℝ ∞ (parametrization R)
def parametrization_normType : Prop :=
  ∀ R : ℝ, 0 < R → ∀ u : E 2, ‖parametrization R u‖ = R
def ordered_area_vectorType : Prop :=
  ∀ R : ℝ, 0 < R → ∀ u : E 2,
    areaVector (parametrization R) u =
      (R ^ 2 * Real.sin (u 0)) • radialNormal R (parametrization R u)
def regular_parametrizationType : Prop :=
  ∀ R : ℝ, 0 < R → RegularPatch parameterDomain (parametrization R)
def density_formulaType : Prop :=
  ∀ R : ℝ, 0 < R → ∀ u ∈ parameterDomain,
    patchJacobian (parametrization R) u = R ^ 2 * Real.sin (u 0)
def sphere_manifoldType : Prop :=
  ∀ R : ℝ, 0 < R → IsCompact (sphere R) ∧
    IsBoundarylessEmbeddedManifold 1 2 (sphere R)
def embedded_spherical_chartType : Prop :=
  ∀ R : ℝ, 0 < R → EmbeddedPatch parameterDomain (parametrization R) ∧
    parametrization R '' parameterDomain = sphere R \ meridian R ∧
    ∃ c : EmbeddedChart 1 2 3 (sphere R), c.half = false ∧
      c.source = parameterDomain ∧ c.toFun = parametrization R
/-- Normality refers to the canonical chart-independent tangent plane. -/
def outward_normalType : Prop :=
  ∀ R : ℝ, 0 < R →
    Continuous (fun x : sphere R => radialNormal R x) ∧
    ∀ x : sphere R,
      IsUnitNormal (tangentSpace 1 2 (sphere R) x) (radialNormal R x) ∧
      ⟪(x : E 3), radialNormal R x⟫ = R
def negligible_meridianType : Prop :=
  ∀ R : ℝ, 0 < R → FiniteSeam (meridian R) ∧
    meridian R ⊆ sphere R ∧ IsCompact (meridian R) ∧
    AreaNull (sphere R) (meridian R)
/-- Geometric cofinality and convergence, separated from the evaluation of the
Riemann chart-piece integrals. -/
def cofinal_truncationsType : Prop :=
  ∀ R : ℝ, 0 < R → ∃ T : ℕ → SurfaceTruncation (sphere R) (meridian R),
    (∀ j, (T j).count = 1 ∧
      ∀ i, ((T j).piece i).domain = truncationDomain j ∧
        ((T j).piece i).chart.toFun = parametrization R) ∧
    ExhaustsComplement T ∧
    Tendsto (fun j => truncationIntegral (T j) (fun _ => 1)) atTop
      (𝓝 (surfaceIntegral (sphere R) (fun _ => 1))) ∧
    Tendsto (fun j => truncationIntegral (T j)
      (fun x => ⟪(x : E 3), radialNormal R x⟫)) atTop
      (𝓝 (surfaceIntegral (sphere R) (fun x => ⟪(x : E 3), radialNormal R x⟫)))
def flux_area_relationType : Prop :=
  ∀ R : ℝ, 0 < R →
    surfaceIntegral (sphere R) (fun x => ⟪(x : E 3), radialNormal R x⟫) =
      R * surfaceIntegral (sphere R) (fun _ => 1)
/-- The existential constructs actual regular chart pieces, not assumed area
certificates. Their domains are the fixed rectangles and they exhaust every
compact subset away from the closed meridian. -/
def regular_truncationsType : Prop :=
  ∀ R : ℝ, 0 < R → ∃ T : ℕ → SurfaceTruncation (sphere R) (meridian R),
    (∀ j, (T j).count = 1 ∧
      ∀ i, ((T j).piece i).domain = truncationDomain j ∧
        ((T j).piece i).chart.toFun = parametrization R) ∧
    ExhaustsComplement T ∧
    (∀ j, truncationIntegral (T j) (fun _ => 1) =
      2 * R ^ 2 * (2 * Real.pi - 2 * (Real.pi / (j + 3 : ℝ))) *
        Real.cos (Real.pi / (j + 3 : ℝ))) ∧
    Tendsto (fun j => truncationIntegral (T j) (fun _ => 1)) atTop
      (𝓝 (surfaceIntegral (sphere R) (fun _ => 1))) ∧
    Tendsto (fun j => truncationIntegral (T j)
      (fun x => ⟪(x : E 3), radialNormal R x⟫)) atTop
      (𝓝 (surfaceIntegral (sphere R) (fun x => ⟪(x : E 3), radialNormal R x⟫)))
def sphere_areaType : Prop :=
  ∀ R : ℝ, 0 < R → surfaceIntegral (sphere R) (fun _ => 1) = 4 * Real.pi * R ^ 2
def sphere_fluxType : Prop :=
  ∀ R : ℝ, 0 < R →
    surfaceIntegral (sphere R) (fun x => ⟪(x : E 3), radialNormal R x⟫) =
      4 * Real.pi * R ^ 3
end Specs.D04.C10.SphereAreaFlux
