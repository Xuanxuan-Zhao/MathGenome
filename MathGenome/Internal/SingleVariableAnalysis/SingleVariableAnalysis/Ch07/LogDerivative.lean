import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Inverse
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogDerivative

/-!
The derivative part of K03.07.log_derivative, paper.tex:1610–1626.
Apply the reciprocal difference-quotient argument for a continuous inverse to
the series exponential at `seriesLog x`. Its derivative there is `x`, which
is nonzero. This uses neither a logarithmic derivative from Mathlib nor an
integral representation of the logarithm.
-/
namespace SingleVariableAnalysis

open Set
open scoped Topology

theorem seriesLog_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch07.LogDerivative.derivative := by
  intro x hx
  change HasDerivAt seriesLog (1 / x) x
  have he : realSeriesExp (seriesLog x) = x := expSeries_seriesLog x hx
  have hImage : realSeriesExp '' univ = Ioi 0 :=
    real_expSeries_bijOn_positive.image_eq
  have hg : RelativeContinuousAt seriesLog (realSeriesExp '' univ)
      (realSeriesExp (seriesLog x)) := by
    rw [hImage, he]
    exact (relativeContinuousAt_within_iff _ _ _).mpr (seriesLog_continuousOn x hx)
  have hExp : HasDerivAt realSeriesExp (realSeriesExp (seriesLog x)) (seriesLog x) :=
    real_expSeries_derivative (seriesLog x)
  rw [he] at hExp
  have hd : HasRealIncrementDerivativeWithin realSeriesExp x univ (seriesLog x) :=
    (withinDerivative_interior_iff _ _ _ _ (by simp)).mpr hExp
  have hInv := inverse_incrementDerivativeWithin realSeriesExp seriesLog univ
    (seriesLog x) x hg (seriesLog_expSeries (seriesLog x))
    (fun _ _ => mem_univ _) (fun y hy => by
      rw [hImage] at hy
      exact expSeries_seriesLog y hy) hd (ne_of_gt hx)
  have hInterior : realSeriesExp (seriesLog x) ∈ interior (realSeriesExp '' univ) := by
    rw [hImage, he, isOpen_Ioi.interior_eq]
    exact hx
  simpa only [he] using (withinDerivative_interior_iff _ _ _ _ hInterior).mp hInv

end SingleVariableAnalysis
