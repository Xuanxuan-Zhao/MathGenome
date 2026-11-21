import MathGenome.Internal.LinearPDE.P201Specs.Heat.DistributionRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent specification of the full `pde:heat-local` estimate.
The common Euclidean model has time coordinate zero. The cylinder and
iterated integral below use the equivalent space × time coordinates.
Spatial multi-indices are the common multisets of coordinate directions;
`iteratedDeriv` takes the ordinary time derivatives after the spatial ones.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201Specs.Heat.LocalEstimate

/-- Closed backward parabolic cylinder, including its top time face. -/
def closedCylinder {n : ℕ} (z : Space n × ℝ) (r : ℝ) : Set (Space n × ℝ) :=
  closedBall z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2

/-- The source hypothesis, expressed without imposing values outside the domain. -/
def CylinderIn {n : ℕ} (Ω : Domain (n + 1)) (z : Space n × ℝ) (r : ℝ) : Prop :=
  closedCylinder z r ⊆ (spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n + 1)))

/-- Exactly ∂ₜʲDₓᵅf(x,t), in the manuscript's order of differentiation. -/
def mixedDerivative {n : ℕ} (f : Space (n + 1) → ℝ)
    (α : MultiIndex n) (j : ℕ) (z : Space n × ℝ) : ℝ :=
  iteratedDeriv j (fun t =>
    multiPartial (fun x => f ((spaceTimeCoordinates n).symm (x, t))) α z.1) z.2

/-- The L¹ integral over the backward cylinder; the spatial ball is open. -/
def cylinderMass {n : ℕ} (f : Space (n + 1) → ℝ) (z : Space n × ℝ) (r : ℝ) : ℝ :=
  ∫ s in Icc (z.2 - r ^ 2) z.2, ∫ y in ball z.1 r,
    |f ((spaceTimeCoordinates n).symm (y, s))| ∂spatialMeasure n

/-- Explicit integrability, to exclude the nonintegrable Bochner default. -/
def MassIntegrable {n : ℕ} (f : Space (n + 1) → ℝ) (z : Space n × ℝ) (r : ℝ) : Prop :=
  (∀ s ∈ Icc (z.2 - r ^ 2) z.2,
    IntegrableOn (fun y => |f ((spaceTimeCoordinates n).symm (y, s))|)
      (ball z.1 r) (spatialMeasure n)) ∧
  IntegrableOn (fun s => ∫ y in ball z.1 r,
    |f ((spaceTimeCoordinates n).symm (y, s))| ∂spatialMeasure n)
    (Icc (z.2 - r ^ 2) z.2)

/-- The radius power is the reciprocal of r^(n+2+|α|+2j).
The constant is chosen before the domain, function, radius, and center. -/
def Bound {n : ℕ} (C : ℝ) (α : MultiIndex n) (j : ℕ)
    (f : Space (n + 1) → ℝ) (z : Space n × ℝ) (r : ℝ) : Prop :=
  |mixedDerivative f α j z| ≤
    C * (r ^ (n + 2 + α.card + 2 * j))⁻¹ * cylinderMass f z r

/-- Classical special case: smoothness and the pointwise heat equation suffice. -/
def classicalEstimateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (α : MultiIndex n) (j : ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Domain (n + 1)) (f : Space (n + 1) → ℝ),
      ContDiffOn ℝ ∞ f Ω → IsCaloric Ω f →
      ∀ (z : Space n × ℝ) (r : ℝ), 0 < r → CylinderIn Ω z r →
        MassIntegrable f z r ∧ Bound C α j f z r

/-- Fixed-scale analytic obligation. This is an auxiliary Prop type, not a
certificate: the original theorem requires proving this uniform unit bound. -/
def unitClassicalEstimateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (α : MultiIndex n) (j : ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Domain (n + 1)) (f : Space (n + 1) → ℝ),
      ContDiffOn ℝ ∞ f Ω → IsCaloric Ω f → CylinderIn Ω (0, 0) 1 →
        |mixedDerivative f α j (0, 0)| ≤ C * cylinderMass f (0, 0) 1

/-- Every compact subset admits one positive radius for all its centers.
In particular this applies to any smaller closed cylinder contained in a larger
cylinder contained in the domain; no boundary regularity is required. -/
def commonRadiusStatement : Prop :=
  ∀ (n : ℕ) (Ω : Domain (n + 1)) (K : Set (Space n × ℝ)),
    IsCompact K → K ⊆ (spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n + 1))) →
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K, CylinderIn Ω z r

/-- Full distributional conclusion, with a single representative used in all
integrals and derivatives. Its bounds include a common radius on compact subsets.
Constants depend only on n, α and j, and hold for all admissible cylinders. -/
def interiorEstimateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : MultiIndex n → ℕ → ℝ, (∀ α j, 0 < C α j) ∧
    ∀ (Ω : Domain (n + 1)) (u : Distribution ℝ Ω), distributionHeat u = 0 →
      ∃ f : Space (n + 1) → ℝ,
        ContDiffOn ℝ ∞ f Ω ∧ regularDistribution Ω f = u ∧ IsCaloric Ω f ∧
        (∀ (α : MultiIndex n) (j : ℕ) (z : Space n × ℝ) (r : ℝ),
          0 < r → CylinderIn Ω z r →
          MassIntegrable f z r ∧ Bound (C α j) α j f z r) ∧
        (∀ K : Set (Space n × ℝ), IsCompact K →
          K ⊆ (spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n + 1))) →
          ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K,
            CylinderIn Ω z r ∧ MassIntegrable f z r ∧
              ∀ α j, Bound (C α j) α j f z r)

/-- Integrability requires only smoothness and the source's closed containment. -/
def massIntegrableStatement : Prop :=
  ∀ (n : ℕ) (Ω : Domain (n + 1)) (f : Space (n + 1) → ℝ),
    ContDiffOn ℝ ∞ f Ω → ∀ (z : Space n × ℝ) (r : ℝ),
      CylinderIn Ω z r → MassIntegrable f z r

end P201Specs.Heat.LocalEstimate
