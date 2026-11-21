import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.LimitsCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
The factorial series, its entire holomorphy, algebra, real restriction,
polar formula, and exact equality criterion (paper.tex:367–424).

Mathlib's complex exponential is itself constructed from factorial partial
sums. The first theorem identifies its value with the actual scalar tsum
in the independent definition; subsequent results are transported through
that equality. No holomorphy or convergence certificate is assumed.
-/

noncomputable section

namespace D12Complex.Exponential

/-- Candidate export of the shared series definition. -/
abbrev E : Specs.D12Complex.Ch02.Exponential.E_type := _root_.D12Complex.E

theorem E_eq_exp : Specs.D12Complex.Ch02.Exponential.E_eq_exp_type := by
  funext z
  change (∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ)) = Complex.exp z
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp z).tsum_eq

theorem hasSum_E : Specs.D12Complex.Ch02.Exponential.hasSum_E_type := by
  intro z
  rw [E_eq_exp, Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem summable_norm_E : Specs.D12Complex.Ch02.Exponential.summable_norm_E_type := by
  intro z
  exact NormedSpace.norm_expSeries_div_summable z

theorem hasDerivAt_E : Specs.D12Complex.Ch02.Exponential.hasDerivAt_E_type := by
  intro z
  rw [E_eq_exp]
  exact Complex.hasDerivAt_exp z

theorem holomorphicOn_E : Specs.D12Complex.Ch02.Exponential.holomorphicOn_E_type := by
  exact ⟨isOpen_univ, fun z _ => (hasDerivAt_E z).differentiableAt⟩

theorem hasComplexDerivativeAt_E :
    Specs.D12Complex.Ch02.Exponential.hasComplexDerivativeAt_E_type := by
  intro z
  exact (hasComplexDerivativeAt_iff E (E z) z).mpr (hasDerivAt_E z)

theorem deriv_E : Specs.D12Complex.Ch02.Exponential.deriv_E_type := by
  funext z
  exact (hasDerivAt_E z).deriv

theorem E_add : Specs.D12Complex.Ch02.Exponential.E_add_type := by
  intro z w
  rw [E_eq_exp]
  exact Complex.exp_add z w

theorem E_zero : Specs.D12Complex.Ch02.Exponential.E_zero_type := by
  rw [Specs.D12Complex.Ch02.Exponential.E_zero_type, E_eq_exp]
  exact Complex.exp_zero

theorem E_ne_zero : Specs.D12Complex.Ch02.Exponential.E_ne_zero_type := by
  intro z
  rw [E_eq_exp]
  exact Complex.exp_ne_zero z

theorem E_ofReal : Specs.D12Complex.Ch02.Exponential.E_ofReal_type := by
  intro x
  rw [E_eq_exp]
  exact (Complex.ofReal_exp x).symm

theorem E_polar : Specs.D12Complex.Ch02.Exponential.E_polar_type := by
  intro x y
  rw [E_eq_exp, mul_comm Complex.I (y : ℂ), Complex.exp_add_mul_I,
    ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [mul_comm (Real.sin y : ℂ) Complex.I]

theorem E_eq_E_iff : Specs.D12Complex.Ch02.Exponential.E_eq_E_iff_type := by
  intro z w
  rw [E_eq_exp, Complex.exp_eq_exp_iff_exp_sub_eq_one, Complex.exp_eq_one_iff]
  simp only [mul_comm]

end D12Complex.Exponential
