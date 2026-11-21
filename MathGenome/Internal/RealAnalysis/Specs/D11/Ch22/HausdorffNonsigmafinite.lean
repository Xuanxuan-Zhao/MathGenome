import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.OuterVolume
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Independent statements for paper.tex:6119–6125.

`Point n` is Euclidean l2 space. Exponents are nonnegative, including zero.
The agreement hypothesis below identifies a Borel measure with the shared
coefficient-one diameter-cover construction on Borel sets. It imposes no
finiteness assumption. Such a measure exists by the upstream Borel restriction
theorem. The second statement gives the native Hausdorff measure formulation;
its agreement with the shared construction is checked in the implementation.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace Specs.D11.Ch22.HausdorffNonsigmafinite

open _root_.D11.Ch03

def borelRestrictionStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (s : ℝ≥0), s < (n : ℝ≥0) →
    ∀ μ : Measure (Point n),
      (∀ E : Set (Point n), MeasurableSet E →
        μ E = HausdorffOuterMeasure.outerMeasureValue s E) →
      ¬ SigmaFinite μ

def nativeStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (s : ℝ≥0), s < (n : ℝ≥0) →
    ¬ SigmaFinite (Measure.hausdorffMeasure (s : ℝ) : Measure (Point n))

end Specs.D11.Ch22.HausdorffNonsigmafinite
