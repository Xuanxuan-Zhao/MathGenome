import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.CompactDiniRiemannElementary
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.GeneratedRingAlgebra
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent statements of paper.tex:6322–6324. The Riemann functional
is the upstream proper Darboux functional on all continuous functions.
The interval carries its relative topology and native Borel sigma-algebra.
Ordinary completion is the upstream sandwich completion, not an arbitrary
larger extension. Ordered endpoints include a singleton interval. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch23.RiemannLebesgueBridge.Model

/-- The usual Borel restriction of one-dimensional Lebesgue measure to [a,b],
viewed on the interval itself. The subtype measurable structure is Borel. -/
def intervalLebesgue (a b : ℝ) : Measure (Icc a b) :=
  (volume : Measure ℝ).comap Subtype.val

/-- Actual absolute integrability and the identity with the classical functional. -/
def RepresentsRiemann {a b : ℝ} (hab : a ≤ b) (μ : Measure (Icc a b)) : Prop :=
  ∀ f : D11.Ch23.Specs.continuousFunctions (Icc a b),
    Integrable f.val μ ∧ (∫ x, f.val x ∂μ) = D11.Ch23.Specs.riemannFunctional hab f

end D11.Ch23.RiemannLebesgueBridge.Model

namespace Specs.D11.Ch23.RiemannLebesgueBridge
open _root_.D11.Ch23.Specs
open _root_.D11.Ch23.RiemannLebesgueBridge.Model

/-- The generated sigma-algebra is exactly Borel, including degenerate intervals. -/
def generated_eq_borel : Prop :=
  ∀ (a b : ℝ), positiveLevelMeasurableSpace (continuousFunctions (Icc a b)) =
    borel (Icc a b)

/-- The classical Lebesgue restriction really represents the Darboux functional. -/
def lebesgue_represents : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b),
    IsFiniteMeasure (intervalLebesgue a b) ∧ RepresentsRiemann hab (intervalLebesgue a b)

/-- Every representing Borel measure is the usual one; finiteness is a conclusion. -/
def representing_measure_eq : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) (μ : Measure (Icc a b)), RepresentsRiemann hab μ →
    IsFiniteMeasure μ ∧ μ = intervalLebesgue a b

/-- Applying Daniell–Stone, after the proved Borel identification, gives this
finite representing measure and full uniqueness. -/
def daniell_riemann_lebesgue : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b), ∃ μ : Measure (Icc a b),
    RepresentsRiemann hab μ ∧ IsFiniteMeasure μ ∧ μ = intervalLebesgue a b ∧
      ∀ ν : Measure (Icc a b), RepresentsRiemann hab ν → ν = μ

/-- Equality of the ordinary completed sigma-algebras and of the completed
values on every set (in particular on every common measurable set). -/
def completions_agree : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) (μ : Measure (Icc a b)), RepresentsRiemann hab μ →
    D11.Ch02.Completion.completedSpace_value μ =
      D11.Ch02.Completion.completedSpace_value (intervalLebesgue a b) ∧
    ∀ A : Set (Icc a b),
      D11.Ch02.Completion.completedMeasure_value μ A =
        D11.Ch02.Completion.completedMeasure_value (intervalLebesgue a b) A

/-- Nonnegative integrals agree on the common completion, including infinite values. -/
def completed_nonnegative_integrals : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) (μ : Measure (Icc a b)), RepresentsRiemann hab μ →
    ∀ f : Icc a b → ℝ≥0∞,
      (∫⁻ x, f x ∂D11.Ch02.Completion.completedMeasure_value μ) =
        ∫⁻ x, f x ∂D11.Ch02.Completion.completedMeasure_value (intervalLebesgue a b)

/-- Scalar integrability is the same on both completions and the integrals
agree. The Banach-valued formulation includes both real and complex scalars. -/
def completed_scalar_integrals : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) (μ : Measure (Icc a b)), RepresentsRiemann hab μ →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Icc a b → E),
      (Integrable f (D11.Ch02.Completion.completedMeasure_value μ) ↔
        Integrable f (D11.Ch02.Completion.completedMeasure_value (intervalLebesgue a b))) ∧
      (Integrable f (D11.Ch02.Completion.completedMeasure_value μ) →
        (∫ x, f x ∂D11.Ch02.Completion.completedMeasure_value μ) =
          ∫ x, f x ∂D11.Ch02.Completion.completedMeasure_value (intervalLebesgue a b))

end Specs.D11.Ch23.RiemannLebesgueBridge
