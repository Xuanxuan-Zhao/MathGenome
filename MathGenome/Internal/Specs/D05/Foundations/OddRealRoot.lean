import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic

/-!
Independent statement of the odd-degree real-root claim in paper.tex:417.
`Polynomial ℝ` is the formal coefficient polynomial, rather than a value function.
The positive natural degree excludes the zero and constant cases explicitly.
-/

namespace D05.Specs.OddRealRoot

/-- Every real polynomial of positive odd degree has a real zero. -/
def existsRealRoot : Prop :=
  ∀ (p : Polynomial ℝ), 0 < p.natDegree → Odd p.natDegree →
    ∃ x : ℝ, p.eval x = 0

end D05.Specs.OddRealRoot
