import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Independent specification of the regularity assertion of Theorem
`thm:integral-conjugacy`, paper.tex:4354–4385. The extended energy is the
upstream Lebesgue integral convention, and the real energy is on native `Lp`
a.e. classes. The general statements apply to arbitrary measure spaces and
second-countable real normed fibers. The last statement specializes explicitly
to Ω ⊆ ℝᵈ, induced Lebesgue measure, Euclidean norm, and real 1 < p < ∞.
No positivity of domain measure, boundary regularity or derivative growth is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u_1 u_2

namespace VariationalNotes.Flux.IntegralRegularitySpecs
open VariationalNotes.Sobolev.CaratheodorySpecs

def TwoSidedPGrowth_type : Type _ :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E],
    Measure S → ℝ≥0∞ → (S → E → ℝ) → Prop

/-- The growth constants and the integrable lower-order term are existential data.
The bounds hold simultaneously for every z outside one common null set. -/
def TwoSidedPGrowth : TwoSidedPGrowth_type :=
  fun {S} {E} [MeasurableSpace S] [NormedAddCommGroup E] μ p F =>
    ∃ (a₀ a₁ : ℝ) (a : S → ℝ), 0 < a₀ ∧ 0 ≤ a₁ ∧ Integrable a μ ∧
      (∀ᵐ x ∂μ, 0 ≤ a x) ∧
      ∀ᵐ x ∂μ, ∀ z, a₀ * ‖z‖ ^ p.toReal - a x ≤ F x z ∧
        F x z ≤ a x + a₁ * ‖z‖ ^ p.toReal

def integralFunctional_type : Type _ :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (μ : Measure S), (S → E → ℝ) → Lp E p μ → ℝ

def integralFunctional : integralFunctional_type :=
  fun {S} {E} [MeasurableSpace S] [NormedAddCommGroup E] {p} μ F v =>
    ∫ x, F x (v x) ∂μ

/-- Genuine integrability for every representative, prior to taking a real integral. -/
def integrable_substitution_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ},
    p ≠ 0 → p ≠ ∞ → Caratheodory μ F → TwoSidedPGrowth μ p F →
    ∀ {v : S → E}, MemLp v p μ → Integrable (fun x => F x (v x)) μ

/-- The integral descends to the canonical a.e. class with its prescribed value. -/
def integralFunctional_toLp_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E]
    {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ} {v : S → E} (hv : MemLp v p μ),
    integralFunctional μ F (hv.toLp v) = ∫ x, F x (v x) ∂μ

/-- Finiteness in the extended-real convention, with the precise finite real value. -/
def lpIntegralEnergy_eq_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ},
    p ≠ 0 → p ≠ ∞ → Caratheodory μ F → TwoSidedPGrowth μ p F →
    ∀ v : Lp E p μ, lpIntegralEnergy μ F v = (integralFunctional μ F v : EReal)

def convex_integralFunctional_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ} [Fact (1 ≤ p)],
    p ≠ ∞ → Caratheodory μ F → TwoSidedPGrowth μ p F →
    (∀ᵐ x ∂μ, ConvexOn ℝ univ (F x)) →
    ConvexOn ℝ univ (integralFunctional (p := p) μ F)

def continuous_integralFunctional_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ} [Fact (1 ≤ p)],
    p ≠ ∞ → Caratheodory μ F → TwoSidedPGrowth μ p F →
    (∀ᵐ x ∂μ, ConvexOn ℝ univ (F x)) →
    Continuous (integralFunctional (p := p) μ F)

/-- Exact original Euclidean applicability, including d=1 and null domains.
The subtype measure is the pullback of Lebesgue measure by the inclusion. -/
def euclidean_integral_regularity_type : Prop :=
  ∀ {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))), volume Ω < ∞ →
  ∀ (p : ℝ) (hp : 1 < p) (F : Ω → EuclideanSpace ℝ (Fin d) → ℝ),
    Caratheodory (volume.comap Subtype.val) F →
  ∀ (a₀ a₁ : ℝ) (a : Ω → ℝ), 0 < a₀ → 0 ≤ a₁ →
    Integrable a (volume.comap Subtype.val) →
    (∀ᵐ x ∂(volume.comap Subtype.val), 0 ≤ a x) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p) →
    (∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (F x)) →
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    (∀ v : Lp (EuclideanSpace ℝ (Fin d)) (ENNReal.ofReal p) (volume.comap Subtype.val),
      Integrable (fun x => F x (v x)) (volume.comap Subtype.val) ∧
      lpIntegralEnergy (volume.comap Subtype.val) F v =
        (integralFunctional (volume.comap Subtype.val) F v : EReal)) ∧
    ConvexOn ℝ univ (integralFunctional (p := ENNReal.ofReal p)
      (volume.comap Subtype.val) F) ∧
    Continuous (integralFunctional (p := ENNReal.ofReal p) (volume.comap Subtype.val) F)

end VariationalNotes.Flux.IntegralRegularitySpecs
