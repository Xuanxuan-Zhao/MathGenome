import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.AbsoluteConvergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for `d04:06:measure-bridge`.
`NullMeasurable` means measurable for the completion of ordinary Borel
Lebesgue volume (`NullMeasurable.measurable'`). This is essential: a Riemann
function need not be Borel measurable on its exceptional null set. Integrals
below use the ordinary volume measure and its a.e. Bochner integral, which
ignores precisely these null modifications. All Riemann objects come from
the independent upstream construction. No comparison is assumed here. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D04.C06.MeasureBridge
open DarbouxIntegral.Model JordanRegions.Model ImproperExhaustions.Model
open AbsoluteConvergence.Model

def null_measure_zeroType : Prop := ∀ {n} {S : Set (E n)},
  NullCovers.Model.Null S → MeasureTheory.volume S = 0

def box_bridgeType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n) (hf : Integrable f Q),
  NullMeasurable ((carrier Q).indicator f) MeasureTheory.volume ∧
  MeasureTheory.Integrable ((carrier Q).indicator f) MeasureTheory.volume ∧
  integral f Q hf = ∫ x in carrier Q, f x

def region_bridgeType : Prop := ∀ {n} {S : Set (E n)} (f : S → ℝ),
  RegionIntegrable f →
  NullMeasurable (zeroExtension f) MeasureTheory.volume ∧
  MeasureTheory.Integrable (zeroExtension f) MeasureTheory.volume ∧
  regionIntegral f = ∫ x, zeroExtension f x

def jordan_measureType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  NullMeasurableSet S MeasureTheory.volume ∧
  MeasureTheory.volume S = ENNReal.ofReal (volume S)

def improper_bridgeType : Prop := ∀ {n} {Ω : Set (E n)} {f : E n → ℝ},
  IsOpen Ω → AbsolutelyConvergent Ω f →
  NullMeasurable (Ω.indicator f) MeasureTheory.volume ∧
  MeasureTheory.Integrable (Ω.indicator f) MeasureTheory.volume ∧
  improperIntegral Ω f = ∫ x, Ω.indicator f x

end Specs.D04.C06.MeasureBridge
