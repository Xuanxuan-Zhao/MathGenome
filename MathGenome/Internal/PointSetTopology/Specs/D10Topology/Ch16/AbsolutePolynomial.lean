import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Independent statements for paper.tex, d10:16:absolute-polynomial.
The approximants are actual real polynomials, evaluated on the entire
closed interval [-1,1]. Uniform convergence includes both endpoints.
-/

open Filter Set

namespace Specs.D10Topology.Ch16.AbsolutePolynomial

def absolute_polynomial : Prop :=
  ∃ p : ℕ → Polynomial ℝ,
    TendstoUniformlyOn (fun n t => (p n).eval t) (fun t : ℝ => |t|)
      atTop (Icc (-1) 1)

def absolute_polynomial_epsilon : Prop :=
  ∃ p : ℕ → Polynomial ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (-1 : ℝ) 1, abs ((p n).eval t - |t|) < ε

end Specs.D10Topology.Ch16.AbsolutePolynomial
