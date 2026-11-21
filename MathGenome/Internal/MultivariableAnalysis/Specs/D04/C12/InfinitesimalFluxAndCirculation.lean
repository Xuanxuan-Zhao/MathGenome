import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalIntegralCalibrations
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GaussDivergenceTheorem
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalSurfaceStokes
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.OrientedPlanarDiskGeometry

/-! Local densities, paper.tex d04:12:local-meaning. Values of the boundary
integrals are specified by the existing independent integral predicates.
The witnesses are their values as functions of radius, not assumed Gauss or
Stokes identities. All radii in the limits approach zero from above. -/
noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
namespace Specs.D04.C12.InfinitesimalFluxAndCirculation
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C12.ClassicalSurfaceStokes.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.GeneralizedStokes.Model

namespace Model
/-- The shared closed planar disk, retaining its center and chosen normal. -/
abbrev planarDisk := Specs.D04.C12.OrientedPlanarDiskGeometry.Model.planarDisk

/-- The boundary integral is the actual directed work integral with the
outward-first orientation of the disk with normal N. -/
def HasDiskCirculation (x N : E 3) (r : ℝ) (F : E 3 → E 3) (I : ℝ) : Prop :=
  ∃ (normal : UnitNormalField (planarDisk x N r))
    (o : PositiveManifoldOrientation 1 2 (planarDisk x N r))
    (bO : PositiveManifoldOrientation 1 1
      (intrinsicBoundary 1 2 (planarDisk x N r))),
    (∀ y, normal.toFun y = N) ∧ NormalCompatible normal o ∧
    OutwardFirst 1 o bO ∧ HasBoundaryWorkIntegral bO F I

/-- Pure geometry and unsigned integration in an isometrically parametrized
plane. This contains no field, curl, circulation, Stokes identity, or limit. -/
def DiskGeometry (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) : Prop :=
  ∀ r : ℝ, 0 < r →
    (fun u => x+A u) '' Specs.D04.C12.ClassicalIntegralCalibrations.Model.diskParameters r =
      planarDisk x N r ∧
    IsEmbeddedManifold 1 2 (planarDisk x N r) ∧ IsCompact (planarDisk x N r) ∧
    intrinsicBoundary 1 2 (planarDisk x N r) =
      {y | inner ℝ (y-x) N = 0 ∧ dist y x = r} ∧
    ∃ normal : UnitNormalField (planarDisk x N r), (∀ y, normal.toFun y = N) ∧
      ∀ g : E 3 → ℝ, ContinuousOn g (planarDisk x N r) →
        surfaceIntegral (planarDisk x N r) (fun y => g y) =
          regionIntegral
            (fun u : Specs.D04.C12.ClassicalIntegralCalibrations.Model.diskParameters r =>
              g (x+A u))
end Model
open Model

/-- Averaging a continuous scalar function over any positive-volume Jordan
regions that shrink into closed balls. Integrability is required only for
this general auxiliary statement and is proved in the applications. -/
def shrinking_averageType : Prop :=
  ∀ {n : ℕ} (g : E n → ℝ) (x : E n) (S : ℝ → Set (E n)), ContinuousAt g x →
    (∀ᶠ r in 𝓝[>] (0 : ℝ), Jordan (S r) ∧ 0 < volume (S r) ∧
      RegionIntegrable (fun y : S r => g y) ∧ S r ⊆ Metric.closedBall x r) →
    Tendsto (fun r => regionIntegral (fun y : S r => g y) / volume (S r))
      (𝓝[>] 0) (𝓝 (g x))

/-- Every positive ambient dimension, including n=1 via n=d+1. Flux uses
the positive d-dimensional Gram density and the radial outward unit normal.
All admissible closed balls are covered, and admissible radii form a full
right neighborhood of zero. -/
def local_fluxType : Prop :=
  ∀ {d : ℕ} (U : Set (E (d+1))) (F : E (d+1) → E (d+1))
    (x : E (d+1)), IsOpen U → x ∈ U → CrOn 1 U F →
    ∃ flux : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → Metric.closedBall x r ⊆ U →
        Jordan (Metric.ball x r) ∧ 0 < volume (Metric.ball x r) ∧
        HasDensityIntegral (d := d)
          (normalFlux F (fun y : frontier (Metric.ball x r) => r⁻¹ • (y.val-x)))
          (flux r)) ∧
      (∀ᶠ r in 𝓝[>] (0 : ℝ), Metric.closedBall x r ⊆ U) ∧
      Tendsto (fun r => flux r / volume (Metric.ball x r))
        (𝓝[>] 0) (𝓝 (divergence F x))

/-- The normal is arbitrary. Existence of the disk geometry and boundary
work integrals is part of the conclusion. The geometric flux of curl uses
the same constant normal and equals the boundary circulation. -/
def local_circulationType : Prop :=
  ∀ (U : Set (E 3)) (F : E 3 → E 3) (x N : E 3),
    IsOpen U → x ∈ U → CrOn 1 U F → ‖N‖ = 1 →
    ∃ circulation : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → Metric.closedBall x r ⊆ U →
        IsEmbeddedManifold 1 2 (planarDisk x N r) ∧
        IsCompact (planarDisk x N r) ∧
        intrinsicBoundary 1 2 (planarDisk x N r) =
          {y | inner ℝ (y-x) N = 0 ∧ dist y x = r} ∧
        HasDiskCirculation x N r F (circulation r) ∧
        circulation r = surfaceIntegral (planarDisk x N r)
          (fun y => inner ℝ (curl F y) N) ∧
        0 < Real.pi * r^2) ∧
      (∀ᶠ r in 𝓝[>] (0 : ℝ), Metric.closedBall x r ⊆ U) ∧
      Tendsto (fun r => circulation r / (Real.pi * r^2))
        (𝓝[>] 0) (𝓝 (inner ℝ (curl F x) N))
/-- Pure disk geometry together with its unsigned parameter integral formula. -/
def disk_geometryType : Prop :=
  ∀ x N : E 3, ‖N‖ = 1 → ∃ A : E 2 →ₗᵢ[ℝ] E 3, DiskGeometry x N A

/-- Assembly of the circulation limit from pure disk geometry. -/
def circulation_from_geometryType : Prop := disk_geometryType → local_circulationType

end Specs.D04.C12.InfinitesimalFluxAndCirculation
