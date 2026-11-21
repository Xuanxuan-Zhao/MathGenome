import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPolarReduction

/-!
Independent specification for paper.tex, Lemma d13:16:hopf-return-expansion
(lines 3656–3695), including the smooth division used immediately afterwards.
The field, normal coordinates, and cubic coefficient are the canonical ones
from the preceding normal-form construction. No periodic orbit is assumed.
-/
noncomputable section

namespace Specs.D13Unified.Ch16.HopfReturnExpansion

open Complex Set
open scoped ComplexConjugate
open CubicHomologicalElimination CubicNormalForm

def turnAngle : ℝ := 2 * Real.pi

def linearReturnFactor (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℝ :=
  Real.exp (turnAngle * angularLinear F μ)

def returnError (F : ℝ × ℂ → ℂ) (P : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  P q - linearReturnFactor F q.2 * q.1 - cubicReturnCoefficient F q.2 * q.1 ^ 3

/-- Coordinates here and below are (initial signed radius, parameter). -/
def returnBox (δ ε : ℝ) : Set (ℝ × ℝ) := {q | |q.1| < δ ∧ |q.2| < ε}

/-- A genuine first turn, built in angular time on [0,2π], with a strictly
increasing physical clock and an actual solution in physical time. The
no-earlier-intersection clause makes this a first return, without appealing
to a return-map theorem based at a preexisting periodic orbit. -/
def FullAngularTurn (F : ℝ × ℂ → ℂ) (ω μ r p ρ : ℝ) : Prop :=
  ∃ (u clock : ℝ → ℝ) (z : ℝ → ℂ),
    u 0 = r ∧ u turnAngle = p ∧ clock 0 = 0 ∧
    0 < clock turnAngle ∧
    StrictMonoOn clock (Icc 0 turnAngle) ∧
    BijOn clock (Icc 0 turnAngle) (Icc 0 (clock turnAngle)) ∧
    (∀ θ ∈ Icc 0 turnAngle,
      0 < u θ ∧ u θ < ρ ∧
      ω / 2 < angularVelocity F θ (u θ) μ ∧
      HasDerivWithinAt u (angularField F θ (u θ) μ) (Icc 0 turnAngle) θ ∧
      HasDerivWithinAt clock (1 / angularVelocity F θ (u θ) μ)
        (Icc 0 turnAngle) θ ∧
      z (clock θ) = polarPoint (u θ) θ) ∧
    z 0 = (r : ℂ) ∧ z (clock turnAngle) = (p : ℂ) ∧
    (∀ t ∈ Icc 0 (clock turnAngle),
      ‖z t‖ < ρ ∧
      HasDerivWithinAt z (transformedField F (μ, z t))
        (Icc 0 (clock turnAngle)) t) ∧
    (∀ t ∈ Ioo 0 (clock turnAngle), ¬ positiveRay (z t))

def CoefficientAtZero : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ),
    spectralReal F 0 = 0 → spectralImag F 0 = ω →
      cubicReturnCoefficient F 0 = turnAngle * firstLyapunovCoefficient F / ω

def PolarVelocityIdentity : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (μ r θ : ℝ), r ≠ 0 →
    conj (direction θ) * transformedField F (μ, polarPoint r θ) =
      (radialVelocity F θ r μ : ℂ) + I * (r * angularVelocity F θ r μ)

def UniformAngularPositivity : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω ε ρ C : ℝ),
    0 < ω → 0 < ε → 0 < ρ → 0 < C →
    UniformRemainderBounds F ε ρ C →
    ContinuousAt (spectralImag F) 0 → spectralImag F 0 = ω →
    ContinuousAt (coefficient F) 0 →
    ∃ ε' > 0, ∃ ρ' > 0, ε' ≤ ε ∧ ρ' ≤ ρ ∧
      ∀ μ r θ : ℝ, |μ| < ε' → |r| < ρ' →
        ω / 2 < angularVelocity F θ r μ

def PolarNeighborhood : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∃ ρ > 0, CoordinateValidity F ε ρ ∧
      ∀ μ r θ : ℝ, |μ| < ε → |r| < ρ →
        ω / 2 < angularVelocity F θ r μ

/-- Full original conclusion, uniformly on a fixed local neighborhood.
The error is estimated on signed radii, a harmless stronger conclusion
which makes the smooth extension explicit. At positive radii P is the
first return of the actual field. At zero P=0 and Q is C² jointly.
Coordinate validity connects this very same field to the input family.
There is no crossing hypothesis a'(0)≠0 and no assumption ℓ≠0. -/
def ReturnExpansion : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    cubicReturnCoefficient F 0 = turnAngle * firstLyapunovCoefficient F / ω ∧
    ∃ ε > 0, ∃ ρ > 0, ∃ δ > 0, ∃ C > 0,
      ∃ P Q : ℝ × ℝ → ℝ,
        δ < ρ ∧ CoordinateValidity F ε ρ ∧
        ContDiffOn ℝ 2 P (returnBox δ ε) ∧
        ContDiffOn ℝ 2 Q (returnBox δ ε) ∧
        ContDiffOn ℝ 1 (returnError F P) (returnBox δ ε) ∧
        (∀ μ : ℝ, |μ| < ε →
          P (0, μ) = 0 ∧ Q (0, μ) = linearReturnFactor F μ - 1) ∧
        (∀ q ∈ returnBox δ ε,
          P q = q.1 * (1 + Q q) ∧
          |returnError F P q| ≤ C * |q.1| ^ 4 ∧
          |deriv (fun r => returnError F P (r, q.2)) q.1| ≤ C * |q.1| ^ 3 ∧
          |deriv (fun μ => returnError F P (q.1, μ)) q.2| ≤ C * |q.1| ^ 4) ∧
        (∀ μ r : ℝ, |μ| < ε → 0 < r → r < δ →
          FullAngularTurn F ω μ r (P (r, μ)) ρ)

end Specs.D13Unified.Ch16.HopfReturnExpansion
