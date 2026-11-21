import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.IntegrationByPartsAndGreenIdentities
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteManifoldBoundaryAssembly
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Independent interfaces for the real-plane Green bridge in
paper.tex:125–133 and the circular-exhaustion proof. BoundaryDisplay contains
only geometric chart, side/orientation and finite-overlap data. All integrals
are the original D04 density/Riemann objects or scalar Lebesgue intervals. -/
noncomputable section
set_option linter.unusedVariables false
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
namespace D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.GeneralizedStokes.Model

abbrev planeIsometry := Complex.orthonormalBasisOneI.repr

abbrev intervalIsometry := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

def planeOutwardNormal {D : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (p : frontier (planeIsometry '' D)) : ℂ :=
  planeIsometry.symm (outwardNormal hD p)

structure BoundaryDisplay {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (U : Set (E 2)) where
  orientation : PositiveManifoldOrientation 1 2 (closure D)
  ambient : IsAmbientOrientation orientation
  boundary_eq : intrinsicBoundary 1 2 (closure D) = frontier D
  boundaryOrientation : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D))
  outward : OutwardFirst 1 orientation boundaryOrientation
  count : ℕ
  patch : Fin count → Patch 1 U
  sign : Fin count → PointSign
  regular : ∀ j, RegularPiece boundaryOrientation (patch j) (sign j)
  seams : Seams 2
  seam_dimension : ∀ i, seams.dim i < 1
  self_intersections : ∀ j x, x ∈ (patch j).region → ∀ y, y ∈ (patch j).region →
    x ≠ y → (patch j).map x = (patch j).map y → (patch j).map x ∈ seams.carrier
  intersections : ∀ i j, i ≠ j →
    ((patch i).map '' (patch i).region) ∩ ((patch j).map '' (patch j).region) ⊆ seams.carrier
  cover : intrinsicBoundary 1 2 (closure D) ⊆
    (⋃ j, (patch j).map '' (patch j).region) ∪ seams.carrier

def patchNormal {D U : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (P : Patch 1 U) (x : E 1) : E 2 :=
  by
    classical
    exact if hx : P.map x ∈ frontier D then outwardNormal hD ⟨P.map x, hx⟩ else 0

def greenField (u v : ℂ → ℝ) (x : E 2) : E 2 :=
  u (planeIsometry.symm x) • scalarGradient (v ∘ planeIsometry.symm) x -
  v (planeIsometry.symm x) • scalarGradient (u ∘ planeIsometry.symm) x

def boundaryFlux {D : Set ℂ} (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (u v : ℂ → ℝ) (x : frontier (planeIsometry '' D)) : ℝ :=
  u (planeIsometry.symm x) * inner ℝ (gradient v (planeIsometry.symm x)) (planeOutwardNormal hD x) -
  v (planeIsometry.symm x) * inner ℝ (gradient u (planeIsometry.symm x)) (planeOutwardNormal hD x)

def arcIntegrand {D : Set ℂ} {U : Set (E 2)}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (P : Patch 1 U) (u v : ℂ → ℝ) (t : ℝ) : ℝ :=
  (u (planeIsometry.symm (P.map (intervalIsometry t))) *
      inner ℝ (gradient v (planeIsometry.symm (P.map (intervalIsometry t))))
        (planeIsometry.symm (patchNormal hD P (intervalIsometry t))) -
    v (planeIsometry.symm (P.map (intervalIsometry t))) *
      inner ℝ (gradient u (planeIsometry.symm (P.map (intervalIsometry t))))
        (planeIsometry.symm (patchNormal hD P (intervalIsometry t)))) *
    ‖deriv (fun s => planeIsometry.symm (P.map (intervalIsometry s))) t‖

def arcFlux {D : Set ℂ} {U : Set (E 2)}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (P : Patch 1 U) (u v : ℂ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, arcIntegrand hD P u v t

end D12Complex.ComplexGreenBridge

namespace Specs.D12Complex.Ch14.ComplexGreenBridge
open _root_.D12Complex _root_.D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.GeneralizedStokes.Model

def partial_zero_type : Prop :=
  ∀ (u : ℂ → ℝ) (z : ℂ),
    scalarPartialDerivative (u ∘ planeIsometry.symm) (planeIsometry z) 0 =
      D12Complex.partialX u z

def partial_one_type : Prop :=
  ∀ (u : ℂ → ℝ) (z : ℂ),
    scalarPartialDerivative (u ∘ planeIsometry.symm) (planeIsometry z) 1 =
      D12Complex.partialY u z

def contDiffOn_transport_type : Prop :=
  ∀ {n : ℕ∞ω} {U : Set ℂ} {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ n u U),
    ContDiffOn ℝ n (u ∘ planeIsometry.symm) (planeIsometry '' U)

def closure_image_type : Prop :=
  ∀ (D : Set ℂ),
    closure (planeIsometry '' D) = planeIsometry '' closure D

def frontier_image_type : Prop :=
  ∀ (D : Set ℂ),
    frontier (planeIsometry '' D) = planeIsometry '' frontier D

def laplacian_transport_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (z : ℂ) (hz : z ∈ U),
    laplacian (u ∘ planeIsometry.symm) (planeIsometry z) =
      D12Complex.coordinateLaplacian u z

def gradient_transport_type : Prop :=
  ∀ (u : ℂ → ℝ) (z : ℂ) (hu : DifferentiableAt ℝ u z),
    scalarGradient (u ∘ planeIsometry.symm) (planeIsometry z) =
      planeIsometry (gradient u z)

def normalDerivative_transport_type : Prop :=
  ∀ {D : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (u : ℂ → ℝ) (p : frontier (planeIsometry '' D))
    (hu : DifferentiableAt ℝ u (planeIsometry.symm p)),
    normalDerivative hD (u ∘ planeIsometry.symm) p =
      inner ℝ (gradient u (planeIsometry.symm p)) (planeOutwardNormal hD p)

def outwardNormal_defining_type : Prop :=
  ∀ {D V : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (p : frontier D) (ρ : E 2 → ℝ) (hρ : IsDefiningFunction D V ρ) (hp : (p : E 2) ∈ V),
    planeIsometry.symm (outwardNormal hD p) =
      ‖gradient (ρ ∘ planeIsometry) (planeIsometry.symm p)‖⁻¹ •
        gradient (ρ ∘ planeIsometry) (planeIsometry.symm p)

def second_green_type : Prop :=
  ∀ (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U),
    let A := fun x : planeIsometry '' D =>
      u (planeIsometry.symm x) * coordinateLaplacian v (planeIsometry.symm x) -
      v (planeIsometry.symm x) * coordinateLaplacian u (planeIsometry.symm x)
    let B := fun x : frontier (planeIsometry '' D) =>
      u (planeIsometry.symm x) * inner ℝ (gradient v (planeIsometry.symm x))
        (planeOutwardNormal hD x) -
      v (planeIsometry.symm x) * inner ℝ (gradient u (planeIsometry.symm x))
        (planeOutwardNormal hD x)
    RegionIntegrable A ∧ HasDensityIntegral (d := 1) B (regionIntegral A) ∧
      regionIntegral A = boundaryIntegral B

def harmonic_second_green_type : Prop :=
  ∀ (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hLu : ∀ z ∈ D, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ D, coordinateLaplacian v z = 0),
    let B := fun x : frontier (planeIsometry '' D) =>
      u (planeIsometry.symm x) * inner ℝ (gradient v (planeIsometry.symm x))
        (planeOutwardNormal hD x) -
      v (planeIsometry.symm x) * inner ℝ (gradient u (planeIsometry.symm x))
        (planeOutwardNormal hD x)
    HasDensityIntegral (d := 1) B 0 ∧ boundaryIntegral B = 0

def normalFromDefining_deleted_disk_type : Prop :=
  ∀ (c : ℂ) (r : ℝ) (_hr : 0 < r)
    (z : ℂ) (hz : ‖z - c‖ = r),
    ‖gradient (fun w : ℂ => r ^ 2 - ‖w - c‖ ^ 2) z‖⁻¹ •
      gradient (fun w : ℂ => r ^ 2 - ‖w - c‖ ^ 2) z =
        -(r⁻¹ • (z - c))

def circle_speed_type : Prop :=
  ∀ (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (t : ℝ),
    ‖deriv (circleMap c r) t‖ = r

def circle_inward_radial_type : Prop :=
  ∀ (c : ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ),
    -(r⁻¹ • (circleMap c r t - c)) = -Complex.exp ((t : ℂ) * Complex.I)

def riemann_interval_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (f : E 1 → ℝ)
    (hf : RegionIntegrable (fun x : intervalIsometry '' Icc a b => f x)),
    regionIntegral (fun x : intervalIsometry '' Icc a b => f x) =
      ∫ t in a..b, f (intervalIsometry t)

def riemann_interval_integrable_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (f : E 1 → ℝ)
    (hf : RegionIntegrable (fun x : intervalIsometry '' Icc a b => f x)),
    IntervalIntegrable (fun t => f (intervalIsometry t)) MeasureTheory.volume a b

def density_boundary_display_type : Prop :=
  ∀ {D U : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U) (B : BoundaryDisplay hD U),
    HasDensityIntegral (d := 1) (normalFlux F (outwardNormal hD))
      (∑ j, (B.sign j).val * patchIntegral (B.patch j) (fun _ => 1) (fluxForm F))

def patch_interval_flux_type : Prop :=
  ∀ {D U : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hU : IsOpen U) (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U)
    (P : Patch 1 U) (s : PointSign) (a b : ℝ) (hab : a ≤ b)
    (hregion : P.region = intervalIsometry '' Icc a b)
    (hframe : ∀ x ∈ P.region,
      ‖patchNormal hD P x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD P x) (fderiv ℝ P.map x (standardBasis 1 i)) = 0) ∧
      0 < s.val * omega 2 (Fin.cons (patchNormal hD P x)
        (fun i => fderiv ℝ P.map x (standardBasis 1 i)))),
    s.val * patchIntegral P (fun _ => 1) (fluxForm F) =
      ∫ t in a..b, inner ℝ (F (P.map (intervalIsometry t)))
        (patchNormal hD P (intervalIsometry t)) *
          ‖fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)‖

def patch_interval_integrable_type : Prop :=
  ∀ {D U : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hU : IsOpen U) (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U)
    (P : Patch 1 U) (s : PointSign) (a b : ℝ) (hab : a ≤ b)
    (hregion : P.region = intervalIsometry '' Icc a b)
    (hframe : ∀ x ∈ P.region,
      ‖patchNormal hD P x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD P x) (fderiv ℝ P.map x (standardBasis 1 i)) = 0) ∧
      0 < s.val * omega 2 (Fin.cons (patchNormal hD P x)
        (fun i => fderiv ℝ P.map x (standardBasis 1 i)))),
    IntervalIntegrable (fun t => inner ℝ (F (P.map (intervalIsometry t)))
        (patchNormal hD P (intervalIsometry t)) *
          ‖fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)‖)
      MeasureTheory.volume a b

def density_interval_display_type : Prop :=
  ∀ {D U : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U) (B : BoundaryDisplay hD U)
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))),
    let J := ∑ j, ∫ t in (a j)..(b j),
      inner ℝ (F ((B.patch j).map (intervalIsometry t)))
        (patchNormal hD (B.patch j) (intervalIsometry t)) *
      ‖fderiv ℝ (B.patch j).map (intervalIsometry t) (standardBasis 1 0)‖
    HasDensityIntegral (d := 1) (normalFlux F (outwardNormal hD)) J ∧
      boundaryIntegral (normalFlux F (outwardNormal hD)) = J

def parametrization_speed_type : Prop :=
  ∀ {U : Set (E 2)} (P : Patch 1 U) (t : ℝ)
    (ht : intervalIsometry t ∈ P.domain),
    ‖deriv (fun s => planeIsometry.symm (P.map (intervalIsometry s))) t‖ =
      ‖fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)‖

def outwardNormal_deleted_disk_type : Prop :=
  ∀ {D V : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (p : frontier D) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hρ : IsDefiningFunction D V (fun x => r ^ 2 - ‖planeIsometry.symm x - c‖ ^ 2))
    (hp : (p : E 2) ∈ V),
    planeIsometry.symm (outwardNormal hD p) =
      -(r⁻¹ • (planeIsometry.symm p - c))

def complex_boundary_display_type : Prop :=
  ∀ (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (B : BoundaryDisplay hD (planeIsometry '' U))
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))),
    HasDensityIntegral (d := 1) (boundaryFlux hD u v)
      (∑ j, arcFlux hD (B.patch j) u v (a j) (b j)) ∧
    boundaryIntegral (boundaryFlux hD u v) =
      ∑ j, arcFlux hD (B.patch j) u v (a j) (b j)

def complex_boundary_integrable_type : Prop :=
  ∀ (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (B : BoundaryDisplay hD (planeIsometry '' U))
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))),
    ∀ j, IntervalIntegrable (arcIntegrand hD (B.patch j) u v) MeasureTheory.volume (a j) (b j)

def harmonic_boundary_display_type : Prop :=
  ∀ (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hLu : ∀ z ∈ D, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ D, coordinateLaplacian v z = 0)
    (B : BoundaryDisplay hD (planeIsometry '' U))
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))),
    (∑ j, arcFlux hD (B.patch j) u v (a j) (b j)) = 0 ∧
      HasDensityIntegral (d := 1) (boundaryFlux hD u v) 0

def deleted_circle_normal_speed_type : Prop :=
  ∀ {D V : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (c : ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (p : frontier D) (he : (p : E 2) = planeIsometry (circleMap c r t))
    (hρ : IsDefiningFunction D V (fun x => r ^ 2 - ‖planeIsometry.symm x - c‖ ^ 2))
    (hp : (p : E 2) ∈ V),
    planeIsometry.symm (outwardNormal hD p) = -Complex.exp ((t : ℂ) * Complex.I) ∧
      ‖deriv (circleMap c r) t‖ = r

def region_integral_transport_type : Prop :=
  ∀ {D : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D)) (f : ℂ → ℝ)
    (hf : RegionIntegrable (fun x : planeIsometry '' D => f (planeIsometry.symm x))),
    MeasureTheory.IntegrableOn f D ∧
      regionIntegral (fun x : planeIsometry '' D => f (planeIsometry.symm x)) =
        ∫ z in D, f z

def second_green_lebesgue_type : Prop :=
  ∀ (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U),
    let f := fun z => u z * coordinateLaplacian v z - v z * coordinateLaplacian u z
    MeasureTheory.IntegrableOn f D ∧
      HasDensityIntegral (d := 1) (boundaryFlux hD u v) (∫ z in D, f z) ∧
      (∫ z in D, f z) = boundaryIntegral (boundaryFlux hD u v)

def planeIsometry_type := ℂ ≃ₗᵢ[ℝ] E 2
def planeIsometry_value : planeIsometry_type := @_root_.D12Complex.ComplexGreenBridge.planeIsometry

def intervalIsometry_type := ℝ ≃ₗᵢ[ℝ] E 1
def intervalIsometry_value : intervalIsometry_type := @_root_.D12Complex.ComplexGreenBridge.intervalIsometry

def planeOutwardNormal_type := {D : Set ℂ} → IsClassicalRegularDomain (planeIsometry '' D) → frontier (planeIsometry '' D) → ℂ
def planeOutwardNormal_value : planeOutwardNormal_type := @_root_.D12Complex.ComplexGreenBridge.planeOutwardNormal

def BoundaryDisplay_type := {D : Set (E 2)} → IsClassicalRegularDomain D → Set (E 2) → Type
def BoundaryDisplay_value : BoundaryDisplay_type := @_root_.D12Complex.ComplexGreenBridge.BoundaryDisplay

def patchNormal_type := {D U : Set (E 2)} → IsClassicalRegularDomain D → Patch 1 U → E 1 → E 2
def patchNormal_value : patchNormal_type := @_root_.D12Complex.ComplexGreenBridge.patchNormal

def greenField_type := (ℂ → ℝ) → (ℂ → ℝ) → E 2 → E 2
def greenField_value : greenField_type := @_root_.D12Complex.ComplexGreenBridge.greenField

def boundaryFlux_type := {D : Set ℂ} → IsClassicalRegularDomain (planeIsometry '' D) → (ℂ → ℝ) → (ℂ → ℝ) → frontier (planeIsometry '' D) → ℝ
def boundaryFlux_value : boundaryFlux_type := @_root_.D12Complex.ComplexGreenBridge.boundaryFlux

def arcIntegrand_type := {D : Set ℂ} → {U : Set (E 2)} → IsClassicalRegularDomain (planeIsometry '' D) → Patch 1 U → (ℂ → ℝ) → (ℂ → ℝ) → ℝ → ℝ
def arcIntegrand_value : arcIntegrand_type := @_root_.D12Complex.ComplexGreenBridge.arcIntegrand

def arcFlux_type := {D : Set ℂ} → {U : Set (E 2)} → IsClassicalRegularDomain (planeIsometry '' D) → Patch 1 U → (ℂ → ℝ) → (ℂ → ℝ) → ℝ → ℝ → ℝ
def arcFlux_value : arcFlux_type := @_root_.D12Complex.ComplexGreenBridge.arcFlux

end Specs.D12Complex.Ch14.ComplexGreenBridge
