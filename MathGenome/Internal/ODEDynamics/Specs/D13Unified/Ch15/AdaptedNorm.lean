import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.MatrixPowerCriteria
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The basis is arbitrary, so these statements apply to every finite-dimensional
operator, including the zero space. For a real operator the spectral conditions
are imposed on the complexification of its matrix, not on its real spectrum.
A seminorm with the two positive comparison constants below is a genuine norm
and induces exactly the original topology. The pointwise upper estimate is the
induced-operator-norm bound. -/
noncomputable section
open Module
namespace D13Unified.Ch15.AdaptedNorm

/-- Explicit two-sided norm equivalence, also implying positive definiteness. -/
def Equivalent {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (p : Seminorm 𝕜 E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
    ∀ v : E, ‖v‖ ≤ C * p v ∧ p v ≤ D * ‖v‖

/-- The induced norm, as a supremum on the closed unit ball. -/
def inducedNorm {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (p : Seminorm 𝕜 E) (A : Module.End 𝕜 E) : ℝ :=
  sSup {r : ℝ | ∃ v : E, p v ≤ 1 ∧ r = p (A v)}

end D13Unified.Ch15.AdaptedNorm
namespace Specs.D13Unified.Ch15.AdaptedNorm
open _root_.D13Unified.Ch15.AdaptedNorm
open _root_.D13Unified.Ch08.MatrixPowerCriteria
open scoped Matrix.Norms.Operator

/-- Upper bound over the complex field, in any coordinates. -/
def upperComplex : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {d : ℕ} (b : Basis (Fin d) ℂ E)
    (A : Module.End ℂ E) (a : ℝ),
    spectralRadius ℂ (LinearMap.toMatrix b b A) < ENNReal.ofReal a →
    ∃ p : Seminorm ℂ E, Equivalent p ∧ (∀ v, p (A v) ≤ a * p v) ∧
      inducedNorm p A ≤ a

/-- A real norm, with the spectral radius computed after complexification. -/
def upperReal : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (b : Basis (Fin d) ℝ E)
    (A : Module.End ℝ E) (a : ℝ),
    spectralRadius ℂ (complexify (LinearMap.toMatrix b b A)) < ENNReal.ofReal a →
    ∃ p : Seminorm ℝ E, Equivalent p ∧ (∀ v, p (A v) ≤ a * p v) ∧
      inducedNorm p A ≤ a

/-- A unit is precisely an invertible endomorphism. Finite complex spectrum
is the set of eigenvalues, as established in the matrix-power prerequisite. -/
def lowerComplex : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {d : ℕ} (b : Basis (Fin d) ℂ E)
    (A : (Module.End ℂ E)ˣ) (a : ℝ), 0 < a →
    (∀ z ∈ spectrum ℂ (LinearMap.toMatrix b b (A : Module.End ℂ E)), a < ‖z‖) →
    ∃ p : Seminorm ℂ E, Equivalent p ∧ ∀ v, a * p v ≤ p ((A : Module.End ℂ E) v)

/-- Real expansion retains all nonreal conjugate pairs via complexification. -/
def lowerReal : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (b : Basis (Fin d) ℝ E)
    (A : (Module.End ℝ E)ˣ) (a : ℝ), 0 < a →
    (∀ z ∈ spectrum ℂ (complexify (LinearMap.toMatrix b b (A : Module.End ℝ E))),
      a < ‖z‖) →
    ∃ p : Seminorm ℝ E, Equivalent p ∧ ∀ v, a * p v ≤ p ((A : Module.End ℝ E) v)

/-- Positive definiteness of the norm represented by our bundled seminorm. -/
def normRepresentation : Prop :=
  ∀ {𝕜 E : Type} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : Seminorm 𝕜 E), Equivalent p → ∀ v, p v = 0 ↔ v = 0

end Specs.D13Unified.Ch15.AdaptedNorm
