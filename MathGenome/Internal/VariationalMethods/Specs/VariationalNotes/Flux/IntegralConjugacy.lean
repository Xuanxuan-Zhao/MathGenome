import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.IntegralRegularity
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.LpDuality
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Independent specification of paper.tex, Theorem `thm:integral-conjugacy`,
4354–4404. The supremum is extended-real, with its finite real value used for
Bochner integration only after finiteness has been asserted. The global conjugate
is the previously specified continuous-dual conjugate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
universe u v
namespace VariationalNotes.Flux.IntegralConjugacySpecs

/-- The source's pointwise Fenchel conjugate, retaining possible infinities. -/
def pointwiseConjugate {S : Type u} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : S → E → ℝ) (x : S) (w : E) : EReal :=
  ⨆ z : E, ((inner ℝ w z - F x z : ℝ) : EReal)

def pointwiseConjugate_type : Type _ :=
  ∀ {S : Type u} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (S → E → ℝ) → S → E → EReal

/-- This also identifies the pointwise definition with the shared conjugation. -/
def pointwise_conjugate_eq_type : Prop :=
  ∀ {S : Type u} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : S → E → ℝ) (x : S) (w : E),
    pointwiseConjugate F x w = ConvexAnalysis.Specs.conjugate
      (fun z => (F x z : WithTop ℝ)) (innerSL ℝ w)

/-- A.e. measurability accommodates the common exceptional null set in the
Carathéodory convention. On the complete Lebesgue measure this is ordinary
measurability. Integrability is a separate assertion about the finite real value. -/
def conjugate_integrable_type : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} (p : ℝ) (hp : 1 < p)
    (F : S → E → ℝ),
    Sobolev.CaratheodorySpecs.Caratheodory μ F →
    IntegralRegularitySpecs.TwoSidedPGrowth μ (ENNReal.ofReal p) F →
    ∀ σ : Lp E (ENNReal.ofReal (p / (p - 1))) μ,
      AEMeasurable (fun x => pointwiseConjugate F x (σ x)) μ ∧
      (∀ᵐ x ∂μ, pointwiseConjugate F x (σ x) ≠ ⊤ ∧
        pointwiseConjugate F x (σ x) ≠ ⊥) ∧
      Integrable (fun x => (pointwiseConjugate F x (σ x)).toReal) μ

/-- Ordinary measurability on complete measure spaces, in particular completed
Lebesgue measure. The other results also work before completing the measure. -/
def conjugate_measurable_type : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} [μ.IsComplete]
    (p : ℝ) (hp : 1 < p) (F : S → E → ℝ),
    Sobolev.CaratheodorySpecs.Caratheodory μ F →
    IntegralRegularitySpecs.TwoSidedPGrowth μ (ENNReal.ofReal p) F →
    ∀ σ : Lp E (ENNReal.ofReal (p / (p - 1))) μ,
      Measurable (fun x => pointwiseConjugate F x (σ x))

/-- The equality holds for the actual continuous functional with the integral
pairing formula. No independently postulated conjugate functional is used. -/
def integral_conjugate_eq_type : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} [IsFiniteMeasure μ]
    (p : ℝ) (hp : 1 < p) (F : S → E → ℝ),
    Sobolev.CaratheodorySpecs.Caratheodory μ F →
    IntegralRegularitySpecs.TwoSidedPGrowth μ (ENNReal.ofReal p) F →
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∀ (σ : Lp E (ENNReal.ofReal (p / (p - 1))) μ)
      (L : Lp E (ENNReal.ofReal p) μ →L[ℝ] ℝ),
      (∀ v, L v = ∫ x, inner ℝ (σ x) (v x) ∂μ) →
      ConvexAnalysis.Specs.conjugate
        (fun v => (IntegralRegularitySpecs.integralFunctional μ F v : WithTop ℝ)) L =
      ((∫ x, (pointwiseConjugate F x (σ x)).toReal ∂μ : ℝ) : EReal)

/-- Exact original Euclidean applicability, under the accepted Lp duality
identification. Restricting Lebesgue measure retains null domains. -/
def euclidean_integral_conjugacy_type : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (Ω : Set (EuclideanSpace ℝ (Fin d))),
    MeasurableSet Ω → volume Ω < ∞ → ∀ (p : ℝ) (hp : 1 < p)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ),
    let μ := volume.restrict Ω
    Sobolev.CaratheodorySpecs.Caratheodory μ F →
    IntegralRegularitySpecs.TwoSidedPGrowth μ (ENNReal.ofReal p) F →
    (∀ᵐ x ∂μ, ConvexOn ℝ univ (F x)) →
    let P := ENNReal.ofReal p
    let Q := ENNReal.ofReal (p / (p - 1))
    letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    letI : Fact (1 ≤ Q) := ⟨ENNReal.one_le_ofReal.mpr
      (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩
    (∀ v : Lp (EuclideanSpace ℝ (Fin d)) P μ,
      Integrable (fun x => F x (v x)) μ) ∧
    ConvexOn ℝ univ (IntegralRegularitySpecs.integralFunctional (p := P) μ F) ∧
    Continuous (IntegralRegularitySpecs.integralFunctional (p := P) μ F) ∧
    ∃ T : Lp (EuclideanSpace ℝ (Fin d)) Q μ ≃ₗᵢ[ℝ]
        (Lp (EuclideanSpace ℝ (Fin d)) P μ →L[ℝ] ℝ),
      (∀ σ v, T σ v = ∫ x, inner ℝ (σ x) (v x) ∂μ) ∧
      ∀ σ, AEMeasurable (fun x => pointwiseConjugate F x (σ x)) μ ∧
        (∀ᵐ x ∂μ, pointwiseConjugate F x (σ x) ≠ ⊤ ∧
          pointwiseConjugate F x (σ x) ≠ ⊥) ∧
        Integrable (fun x => (pointwiseConjugate F x (σ x)).toReal) μ ∧
        ConvexAnalysis.Specs.conjugate
          (fun v => (IntegralRegularitySpecs.integralFunctional μ F v : WithTop ℝ)) (T σ) =
          ((∫ x, (pointwiseConjugate F x (σ x)).toReal ∂μ : ℝ) : EReal)

/-- The subtype-domain interface used by integral regularity, with the canonical
continuous integral pairing. The preceding ambient-domain statement identifies
this pairing with the accepted isometric Lp duality map. -/
def euclidean_subtype_integral_conjugacy_type : Prop :=
  ∀ {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))), volume Ω < ∞ →
  ∀ (p : ℝ) (hp : 1 < p) (F : Ω → EuclideanSpace ℝ (Fin d) → ℝ),
    let μ : Measure Ω := volume.comap Subtype.val
    Sobolev.CaratheodorySpecs.Caratheodory μ F →
    IntegralRegularitySpecs.TwoSidedPGrowth μ (ENNReal.ofReal p) F →
    (∀ᵐ x ∂μ, ConvexOn ℝ univ (F x)) →
    let P := ENNReal.ofReal p
    let Q := ENNReal.ofReal (p / (p - 1))
    letI : ENNReal.HolderConjugate P Q :=
      (Real.HolderConjugate.conjExponent hp).ennrealOfReal
    letI : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
    letI : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
    (∀ v : Lp (EuclideanSpace ℝ (Fin d)) P μ,
      Integrable (fun x => F x (v x)) μ ∧
      Sobolev.CaratheodorySpecs.lpIntegralEnergy μ F v =
        (IntegralRegularitySpecs.integralFunctional μ F v : EReal)) ∧
    ConvexOn ℝ univ (IntegralRegularitySpecs.integralFunctional (p := P) μ F) ∧
    Continuous (IntegralRegularitySpecs.integralFunctional (p := P) μ F) ∧
    ∀ σ : Lp (EuclideanSpace ℝ (Fin d)) Q μ,
      AEMeasurable (fun x => pointwiseConjugate F x (σ x)) μ ∧
      (∀ᵐ x ∂μ, pointwiseConjugate F x (σ x) ≠ ⊤ ∧
        pointwiseConjugate F x (σ x) ≠ ⊥) ∧
      Integrable (fun x => (pointwiseConjugate F x (σ x)).toReal) μ ∧
      ConvexAnalysis.Specs.conjugate
        (fun v => (IntegralRegularitySpecs.integralFunctional μ F v : WithTop ℝ))
          ((innerSL ℝ).lpPairing μ Q P σ) =
        ((∫ x, (pointwiseConjugate F x (σ x)).toReal ∂μ : ℝ) : EReal)

end VariationalNotes.Flux.IntegralConjugacySpecs
