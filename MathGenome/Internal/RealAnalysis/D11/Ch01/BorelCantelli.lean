import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.BorelCantelli
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# First Borel--Cantelli lemma

The library's outer-measure theorem applies to the canonical positive
measure, with no size assumptions. Its proof bounds the limsup by every
tail union, uses countable subadditivity, and lets the summable tails tend
to zero, as in paper.tex:363–368. The measurable-set hypotheses retain
the source's domain of evaluation.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch01.BorelCantelli

theorem first_borel_cantelli {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (E : ℕ → Set α) (_hE : ∀ n, MeasurableSet (E n))
    (hsum : (∑' n, μ (E n)) < ∞) :
    μ (Filter.limsup E Filter.atTop) = 0 :=
  MeasureTheory.measure_limsup_atTop_eq_zero hsum.ne

end D11.Ch01.BorelCantelli
