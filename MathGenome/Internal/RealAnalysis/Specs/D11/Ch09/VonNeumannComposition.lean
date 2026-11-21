import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.MonotoneNullImageCharacterization
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

/-! Independent statements for paper.tex:3267–3288. The domain sigma-algebra
is the trace of completed Lebesgue measure, not the Borel trace. Functions
on closed intervals are actual subtype functions; no extension hypothesis
is imposed. The inverse is extended arbitrarily off its domain solely to
use the shared compact-interval absolute-continuity definition. -/

noncomputable section
open Set MeasureTheory

namespace D11.Ch09.VonNeumannComposition

/-- Trace of the ordinary completion of real Borel Lebesgue measure. -/
def intervalSigma (a b : ℝ) : MeasurableSpace (Icc a b) :=
  (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ volume)).comap Subtype.val

/-- Exact completed Lebesgue measurability of a function on a closed interval. -/
def IntervalMeasurable {K : Type*} [MeasurableSpace K] {a b : ℝ}
    (g : Icc a b → K) : Prop :=
  @Measurable _ K (intervalSigma a b) _ g

/-- The genuine inverse of a strictly increasing onto interval map, with
value zero off the target interval. Off-domain values do not enter AC. -/
def inverseExtension {a b c d : ℝ} (h : Icc a b → Icc c d)
    (hm : StrictMono h) (hs : Function.Surjective h) (y : ℝ) : ℝ :=
  if hy : y ∈ Icc c d then
    ((hm.orderIsoOfSurjective h hs).symm ⟨y, hy⟩ : ℝ)
  else 0

/-- Preservation of all real (or complex) measurable functions on the target. -/
def PreservesComposition (K : Type*) [MeasurableSpace K] {a b c d : ℝ}
    (h : Icc a b → Icc c d) : Prop :=
  ∀ g : Icc c d → K, IntervalMeasurable g → IntervalMeasurable (g ∘ h)

/-- Equivalent test class consisting of functions on the whole real line. -/
def PreservesWholeLineComposition (K : Type*) [MeasurableSpace K] {a b c d : ℝ}
    (h : Icc a b → Icc c d) : Prop :=
  ∀ g : ℝ → K, NullMeasurable g volume →
    IntervalMeasurable (fun x => g (h x))

end D11.Ch09.VonNeumannComposition

namespace Specs.D11.Ch09.VonNeumannComposition
open _root_.D11.Ch09.VonNeumannComposition

/-- von Neumann's real composition criterion, including both endpoints. -/
def real_criterion : Prop :=
  ∀ {a b c d : ℝ}, a < b → c < d →
    ∀ (h : Icc a b → Icc c d) (_hc : Continuous h)
      (hm : StrictMono h) (hs : Function.Surjective h),
      PreservesComposition ℝ h ↔
        Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (inverseExtension h hm hs) c d

/-- The full complex criterion with the same hypotheses. -/
def complex_criterion : Prop :=
  ∀ {a b c d : ℝ}, a < b → c < d →
    ∀ (h : Icc a b → Icc c d) (_hc : Continuous h)
      (hm : StrictMono h) (hs : Function.Surjective h),
      PreservesComposition ℂ h ↔
        Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (inverseExtension h hm hs) c d

/-- Restriction and zero extension identify the two real formulations. -/
def real_wholeLine_iff_interval : Prop :=
  ∀ {a b c d : ℝ} (h : Icc a b → Icc c d),
    PreservesWholeLineComposition ℝ h ↔ PreservesComposition ℝ h

/-- Restriction and zero extension identify the two complex formulations. -/
def complex_wholeLine_iff_interval : Prop :=
  ∀ {a b c d : ℝ} (h : Icc a b → Icc c d),
    PreservesWholeLineComposition ℂ h ↔ PreservesComposition ℂ h

/-- The equivalent criterion for real functions on all of R. -/
def real_wholeLine_criterion : Prop :=
  ∀ {a b c d : ℝ}, a < b → c < d →
    ∀ (h : Icc a b → Icc c d) (_hc : Continuous h)
      (hm : StrictMono h) (hs : Function.Surjective h),
      PreservesWholeLineComposition ℝ h ↔
        Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (inverseExtension h hm hs) c d

/-- The equivalent criterion for complex functions on all of R. -/
def complex_wholeLine_criterion : Prop :=
  ∀ {a b c d : ℝ}, a < b → c < d →
    ∀ (h : Icc a b → Icc c d) (_hc : Continuous h)
      (hm : StrictMono h) (hs : Function.Surjective h),
      PreservesWholeLineComposition ℂ h ↔
        Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (inverseExtension h hm hs) c d

end Specs.D11.Ch09.VonNeumannComposition
