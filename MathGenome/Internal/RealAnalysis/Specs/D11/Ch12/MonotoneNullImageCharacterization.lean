import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Independent statements for paper.tex:4265–4307. Ambient functions represent
functions on the closed interval. `NullMeasurableSet` means measurability in
the ordinary completion of Borel Lebesgue measure, and zero outer volume tests
all subsets of null sets. No measurability is assumed for those subsets. -/

open Set MeasureTheory

namespace D11.Ch12.MonotoneNullImageCharacterization

/-- The null-image property tests arbitrary subsets of the indicated domain. -/
def NullImagesOn (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ N : Set ℝ, N ⊆ s → volume N = 0 → volume (F '' N) = 0

/-- Images of all completed Lebesgue measurable subsets are completed
Lebesgue measurable. This does not assert Borel measurability of the images. -/
def MeasurableImagesOn (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ E : Set ℝ, E ⊆ s → NullMeasurableSet E volume →
    NullMeasurableSet (F '' E) volume

end D11.Ch12.MonotoneNullImageCharacterization

namespace Specs.D11.Ch12.MonotoneNullImageCharacterization

open _root_.D11.Ch12.MonotoneNullImageCharacterization

/-- Full three-way equivalence; monotonicity need only hold on the domain.
Constant maps and both endpoints are included. -/
def characterization : Prop :=
  ∀ (F : ℝ → ℝ) {a b : ℝ}, a < b → ContinuousOn F (Icc a b) →
    MonotoneOn F (Icc a b) →
    (absolutelyContinuousOnIntervalValue F a b ↔ NullImagesOn F (Icc a b)) ∧
      (NullImagesOn F (Icc a b) ↔ MeasurableImagesOn F (Icc a b))

/-- The AC equivalence retains precisely the original continuity and
nondecreasing hypotheses, with no injectivity or nonconstant assumption. -/
def ac_iff_nullImages : Prop :=
  ∀ (F : ℝ → ℝ) {a b : ℝ}, a < b → ContinuousOn F (Icc a b) →
    MonotoneOn F (Icc a b) →
      (absolutelyContinuousOnIntervalValue F a b ↔ NullImagesOn F (Icc a b))

/-- This direction holds for any function and any domain: completeness, not
measurability of the inverse image of an arbitrary target subset, is used. -/
def measurableImages_implies_nullImages : Prop :=
  ∀ (F : ℝ → ℝ) (s : Set ℝ), MeasurableImagesOn F s → NullImagesOn F s

/-- Compact approximation gives the converse for continuous maps on an interval;
monotonicity is unnecessary for this part. -/
def nullImages_implies_measurableImages : Prop :=
  ∀ (F : ℝ → ℝ) (a b : ℝ), ContinuousOn F (Icc a b) →
    NullImagesOn F (Icc a b) → MeasurableImagesOn F (Icc a b)

def nullImages_iff_measurableImages : Prop :=
  ∀ (F : ℝ → ℝ) (a b : ℝ), ContinuousOn F (Icc a b) →
    (NullImagesOn F (Icc a b) ↔ MeasurableImagesOn F (Icc a b))

/-- The constant case is included without an injectivity or positive-range
hypothesis. The constant value need only be fixed on the interval. -/
def constant_case : Prop :=
  ∀ (F : ℝ → ℝ) (a b c : ℝ), (∀ x ∈ Icc a b, F x = c) →
    absolutelyContinuousOnIntervalValue F a b ∧
      NullImagesOn F (Icc a b) ∧ MeasurableImagesOn F (Icc a b)

end Specs.D11.Ch12.MonotoneNullImageCharacterization
