import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing
import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Finite-measure part of paper.tex:5707–5718. The scalar pairing is the
already shared bilinear pairing, on ordinary measurable a.e. classes.
The final statement includes existence, uniqueness, integrability of every
pairing and exact norm, with no nonzero-mass or nonzero-functional hypothesis.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch20.LpDualFiniteMeasure

/-- An auxiliary consequence of the two upstream pairing norm theorems. -/
def pairing_norm : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    ∀ g : Lp 𝕜 q μ, ‖IntegralPairing.pairing_value μ p q g‖ = ‖g‖

/-- Once a representative is found, its norm and a.e.-class uniqueness follow
from isometry of the already fixed pairing. This is only an assembly helper. -/
def representation_unique_norm : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) (g : Lp 𝕜 q μ),
    (∀ f : Lp 𝕜 p μ, ℓ f = ∫ x, f x * g x ∂μ) →
    ‖g‖ = ‖ℓ‖ ∧ ∀ k : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, ℓ f = ∫ x, f x * k x ∂μ) → k = g

/-- The scalar measure is constructed, rather than assumed, from the values
of the functional on measurable indicators. Its variation is finite before RN. -/
def scalar_measure_exists : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ∞ → ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃ ν : VectorMeasure X 𝕜,
      (∀ (A : Set X) (hA : MeasurableSet A),
        ν A = ℓ (indicatorConstLp p hA (measure_ne_top μ A) 1)) ∧
      IsFiniteMeasure ν.variation ∧
      (∀ A, MeasurableSet A → μ A = 0 → ν A = 0)

/-- The signed/complex RN step, with an integrable, genuinely measurable
representative on the original measurable space. -/
def integrable_density_exists : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ∞ → ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃ h : X → 𝕜, Measurable h ∧ Integrable h μ ∧
      ∀ (A : Set X) (hA : MeasurableSet A),
        ℓ (indicatorConstLp p hA (measure_ne_top μ A) 1) = ∫ x in A, h x ∂μ

/-- Full assigned finite-measure theorem. The exponent p=1 has q=∞ by the
conjugacy condition. The witnesses are ordinary Lq classes, not local-null
classes; `Integrable` is included before the totalized Bochner integral. -/
def finite_measure_duality : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ → ∀ ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃! g : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        ℓ f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖ℓ‖

end Specs.D11.Ch20.LpDualFiniteMeasure
