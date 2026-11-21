import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Regulated
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RegulatedApproximation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.UniformStability
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Regulated scalar functions are properly Riemann integrable. We use the
prerequisite's finite-step approximants, retaining the original function at
every partition node, with errors tending uniformly to zero. Step integrability
allows arbitrary node values; uniform stability is for the proper Darboux
integral, rather than a measure-integrability substitute. -/

namespace SingleVariableAnalysis
open Set

namespace RegulatedApproximation

/-- A sequence of the prerequisite's step approximants, with a single error
bound at each index for the entire interval. All assigned node values are
retained, including both endpoints and the singleton-interval case. -/
theorem exists_step_sequence {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : RegulatedOn f a b) :
    ∃ P : ℕ → Riemann.Partition a b, ∃ s : ℕ → ℝ → E,
      (∀ n, Riemann.IsStepOn (P n) (s n)) ∧
      (∀ n j, s n ((P n).point j) = f ((P n).point j)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        ∀ x ∈ Icc a b, ‖s n x - f x‖ < ε) := by
  classical
  have hpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) :=
    one_div_pos.mpr (by positivity)
  choose P s hs hn he using
    (fun n : ℕ => exists_step_pointwise hab hf (hpos n))
  refine ⟨P, s, hs, hn, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn x hx => ?_⟩
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  calc
    ‖s n x - f x‖ = ‖f x - s n x‖ := norm_sub_rev _ _
    _ < 1 / ((n : ℝ) + 1) := he n x hx
    _ ≤ 1 / ((N : ℝ) + 1) := hle
    _ < ε := hN

end RegulatedApproximation

namespace Riemann

theorem real_integrable_of_regulated {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : RegulatedOn f a b) : RealIntegrable f a b := by
  obtain ⟨P, s, hs, _, hu⟩ := RegulatedApproximation.exists_step_sequence hab hf
  apply realIntegrable_uniform_limit hab (fun n => real_step_integrable (s n) (P n) (hs n))
  intro ε hε
  obtain ⟨N, hN⟩ := hu ε hε
  refine ⟨N, fun n hn x => ?_⟩
  simpa only [Real.norm_eq_abs] using hN n hn x.val x.property

theorem complex_integrable_of_regulated {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : RegulatedOn f a b) : ComplexIntegrable f a b := by
  obtain ⟨P, s, hs, _, hu⟩ := RegulatedApproximation.exists_step_sequence hab hf
  have hF (n : ℕ) : ComplexIntegrable (s n) a b :=
    complex_step_integrable (s n) (P n) (hs n)
  apply (complex_uniform_stability s f hab hF ?_).choose
  intro ε hε
  obtain ⟨N, hN⟩ := hu ε hε
  exact ⟨N, fun n hn x => hN n hn x.val x.property⟩

end Riemann

theorem real_regulated_riemann :
    Specs.SingleVariableAnalysis.Ch15.Regulated.realRegulatedRiemann := by
  intro a b hab f hf
  exact ⟨real_regulated_bounded hab f hf, Riemann.real_integrable_of_regulated hab hf⟩

theorem complex_regulated_riemann :
    Specs.SingleVariableAnalysis.Ch15.Regulated.complexRegulatedRiemann := by
  intro a b hab f hf
  exact ⟨complex_regulated_bounded hab f hf, Riemann.complex_integrable_of_regulated hab hf⟩

end SingleVariableAnalysis
