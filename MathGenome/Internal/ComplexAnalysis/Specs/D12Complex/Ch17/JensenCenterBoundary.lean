import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.PoissonJensen

/-! Independent statements for paper.tex:2893–2922, d12:17-02.
The local factorization is punctured, so negative center orders are allowed.
All divisor weights reuse the canonical closed-disk divisor from Poisson–Jensen.
The formula explicitly restricts its sums to nonzero interior points. -/
noncomputable section
open Complex Metric Set Filter
open scoped Topology Classical

namespace Specs.D12Complex.Ch17.JensenCenterBoundary
open _root_.D12Complex _root_.D12Complex.PoissonJensen

def elementary_log_mean_type : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ a : ℂ,
    IntervalIntegrable (fun t => Real.log ‖circleMap 0 R t - a‖)
      MeasureTheory.volume 0 (2 * Real.pi) ∧
    (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi,
      Real.log ‖circleMap 0 R t - a‖) = Real.log (max R ‖a‖)

/-- Finiteness, and the exact signed order and positive/negative multiplicities,
including boundary points. A locally zero center germ is excluded. -/
def finite_divisor_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    ¬ scalarZeroGerm F 0 →
    (Function.support (zeroMultiplicity F R)).Finite ∧
    (Function.support (poleMultiplicity F R)).Finite ∧
    ∀ a ∈ closedBall (0 : ℂ) R,
      scalarSignedOrder F a = some (diskDivisor F R a) ∧
      (0 < zeroMultiplicity F R a ↔ F a = sphereFinite 0) ∧
      (0 < poleMultiplicity F R a ↔ F a = sphereInfty)

/-- No boundary exclusion: logarithmic singularities are integrable. -/
def boundary_integrable_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    IntervalIntegrable (fun t => Real.log ‖scalarFinitePart F (circleMap 0 R t)‖)
      MeasureTheory.volume 0 (2 * Real.pi)

/-- The center term is the actual value g(0) of the holomorphic local factor.
V need only be a neighborhood of zero, not the whole disk. -/
def jensen_center_boundary_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    ∀ (V : Set ℂ) (g : ℂ → ℂ) (m : ℤ),
      0 ∈ V → HolomorphicOn V g → g 0 ≠ 0 →
      scalarFinitePart F =ᶠ[𝓝[≠] 0] (fun z => z ^ m * g z) →
      boundaryMean F R = Real.log ‖g 0‖ + (m : ℝ) * Real.log R +
        (∑ᶠ a : ℂ, if a ∈ ball 0 R ∧ a ≠ 0 then
          (zeroMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) else 0) -
        (∑ᶠ a : ℂ, if a ∈ ball 0 R ∧ a ≠ 0 then
          (poleMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) else 0)

def boundary_divisor_terms_zero_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (R : ℝ) (a : ℂ), 0 < R →
    a ∈ sphere (0 : ℂ) R →
    (zeroMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) = 0 ∧
    (poleMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) = 0

/-- Arbitrary real values at the finite set of boundary zeros and poles have
no effect on integrability or the mean. -/
def boundary_redefinition_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    ¬ scalarZeroGerm F 0 → ∀ φ : ℂ → ℝ,
    (∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty → F ζ ≠ sphereFinite 0 →
      φ ζ = Real.log ‖scalarFinitePart F ζ‖) →
    IntervalIntegrable (fun t => φ (circleMap 0 R t))
      MeasureTheory.volume 0 (2 * Real.pi) ∧
    (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi, φ (circleMap 0 R t)) =
      boundaryMean F R

end Specs.D12Complex.Ch17.JensenCenterBoundary
