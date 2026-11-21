import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Monotone AC substitution, paper.tex:3218–3248.

`NullMeasurable h (volume.restrict (Icc A B))` means measurable for the
completion of Lebesgue measure restricted to the displayed interval. It
places no condition on values outside that interval. Integrals against the
Borel measure of these completed-measurable functions are the same Lebesgue
integrals. The target interval is allowed to be a singleton.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch09.MonotoneAcSubstitution

/-- A zero derivative, including a totalized undefined derivative, kills
infinite target values by the ENNReal convention `0 * ∞ = 0`. -/
def weightedNonnegative (F : ℝ → ℝ) (h : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (deriv F x) * h (F x)

/-- The pointwise scalar convention, including all exceptional points. -/
def weightedScalar {K : Type*} [RCLike K]
    (F : ℝ → ℝ) (h : ℝ → K) (x : ℝ) : K :=
  if 0 < deriv F x then deriv F x • h (F x) else 0

/-- Nonnegative substitution, with no finiteness condition on the integral. -/
def nonnegative_substitution : Prop :=
  ∀ (F : ℝ → ℝ) {a b : ℝ}, a < b →
    MonotoneOn F (Icc a b) →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue F a b →
    ∀ (h : ℝ → ℝ≥0∞), NullMeasurable h (volume.restrict (Icc (F a) (F b))) →
      NullMeasurable (weightedNonnegative F h) (volume.restrict (Icc a b)) ∧
      (∫⁻ x in Icc a b, weightedNonnegative F h x) =
        ∫⁻ y in Icc (F a) (F b), h y

/-- Weighted scalar measurability does not require integrability of `h`. -/
def scalar_weight_measurable : Prop :=
  ∀ {K : Type*} [RCLike K] [MeasurableSpace K] [BorelSpace K]
    (F : ℝ → ℝ) {a b : ℝ}, a < b →
    MonotoneOn F (Icc a b) →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue F a b →
    ∀ (h : ℝ → K), NullMeasurable h (volume.restrict (Icc (F a) (F b))) →
      NullMeasurable (weightedScalar F h) (volume.restrict (Icc a b))

/-- Scalar substitution includes absolute integrability before integral equality.
`RCLike` covers both real and complex scalars. -/
def scalar_substitution : Prop :=
  ∀ {K : Type*} [RCLike K] [MeasurableSpace K] [BorelSpace K]
    (F : ℝ → ℝ) {a b : ℝ}, a < b →
    MonotoneOn F (Icc a b) →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue F a b →
    ∀ (h : ℝ → K), NullMeasurable h (volume.restrict (Icc (F a) (F b))) →
      IntegrableOn h (Icc (F a) (F b)) →
      NullMeasurable (weightedScalar F h) (volume.restrict (Icc a b)) ∧
      IntegrableOn (weightedScalar F h) (Icc a b) ∧
      ((∫⁻ x in Icc a b, ENNReal.ofReal ‖weightedScalar F h x‖) =
        ∫⁻ y in Icc (F a) (F b), ENNReal.ofReal ‖h y‖) ∧
      (∫ x in Icc a b, weightedScalar F h x) =
        ∫ y in Icc (F a) (F b), h y

end Specs.D11.Ch09.MonotoneAcSubstitution
