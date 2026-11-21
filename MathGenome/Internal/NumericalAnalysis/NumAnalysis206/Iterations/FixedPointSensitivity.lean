import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.FixedPointSensitivity
import Mathlib.Tactic.Linarith

namespace NumAnalysis206.Iterations

/-- Proposition p206:W68, using only the perturbation at the fixed point of S. -/
theorem fixedPointSensitivityAtPoint :
    Specs.NumAnalysis206.Iterations.FixedPointSensitivityAtPoint := by
  intro X _ T S p ptilde q δ _hq_nonneg hq hT hp hptilde hδ
  have htriangle : dist p ptilde ≤ dist (T p) (T ptilde) +
      dist (T ptilde) (S ptilde) := by
    simpa only [hp, hptilde] using dist_triangle p (T ptilde) ptilde
  have hbound : dist p ptilde ≤ q * dist p ptilde + δ :=
    htriangle.trans (add_le_add (hT p ptilde) hδ)
  apply (le_div_iff₀ (sub_pos.mpr hq)).2
  linarith

/-- Proposition p206:W68 for a perturbation bounded throughout the space. -/
theorem fixedPointSensitivityUniform :
    Specs.NumAnalysis206.Iterations.FixedPointSensitivityUniform := by
  intro X _ T S p ptilde q δ hq_nonneg hq hT hp hptilde hδ
  exact fixedPointSensitivityAtPoint T S p ptilde q δ hq_nonneg hq hT hp hptilde
    (hδ ptilde)

end NumAnalysis206.Iterations
