import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.Alteration
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace P205.Probability.FiniteModel

variable {Ω : Type*} [Fintype Ω]

/-- A finite weighted mean is attained or exceeded on positive support. -/
theorem exists_expectation_le (M : FiniteModel Ω) (Z : Ω → ℝ) :
    ∃ ω, ω ∈ M.positiveSupport ∧ M.expectation Z ≤ Z ω := by
  classical
  by_contra h
  have hlt : ∀ ω, 0 < M.weight ω → Z ω < M.expectation Z := by
    intro ω hp
    exact lt_of_not_ge (fun hz => h ⟨ω, hp, hz⟩)
  have hle : ∀ ω ∈ Finset.univ,
      M.weight ω * Z ω ≤ M.weight ω * M.expectation Z := by
    intro ω _
    by_cases hp : 0 < M.weight ω
    · exact mul_le_mul_of_nonneg_left (hlt ω hp).le (M.weight_nonneg ω)
    · have hz : M.weight ω = 0 :=
        le_antisymm (le_of_not_gt hp) (M.weight_nonneg ω)
      simp [hz]
  obtain ⟨ω, hp⟩ := M.support_nonempty
  have hsum := Finset.sum_lt_sum hle
    ⟨ω, Finset.mem_univ ω, mul_lt_mul_of_pos_left (hlt ω hp) hp⟩
  rw [← Finset.sum_mul, M.weight_sum, one_mul] at hsum
  exact (lt_irrefl (M.expectation Z)) hsum

/-- The finite alteration principle. The subtraction is in ℝ, so large defect
counts are not truncated to zero. No independence or positivity of all weights
is required, and the procedure is only required on positive support. -/
theorem finite_alteration (M : FiniteModel Ω) (S D : Ω → ℕ)
    {Object : Type*} (size : Object → ℕ) (defectFree : Object → Prop)
    (repair : M.positiveSupport → Object)
    (hclear : ∀ ω, defectFree (repair ω))
    (hsize : ∀ ω, (S ω.val : ℝ) - (D ω.val : ℝ) ≤ (size (repair ω) : ℝ)) :
    ∃ ω : M.positiveSupport, defectFree (repair ω) ∧
      M.expectation (fun v => (S v : ℝ) - (D v : ℝ)) ≤ (size (repair ω) : ℝ) := by
  obtain ⟨ω, hp, hω⟩ := M.exists_expectation_le (fun v => (S v : ℝ) - (D v : ℝ))
  exact ⟨⟨ω, hp⟩, hclear ⟨ω, hp⟩, hω.trans (hsize ⟨ω, hp⟩)⟩

/-- A repair by deleting at most D items satisfies the alteration bound.
Clearance is an application-specific hypothesis, not an assumed final witness. -/
theorem finite_set_alteration (M : FiniteModel Ω)
    {α : Type*} [DecidableEq α] (sample : Ω → Finset α) (D : Ω → ℕ)
    (defectFree : Finset α → Prop) (repair : M.positiveSupport → Finset α)
    (hsub : ∀ ω, repair ω ⊆ sample ω.val)
    (hremoved : ∀ ω, ((sample ω.val) \ repair ω).card ≤ D ω.val)
    (hclear : ∀ ω, defectFree (repair ω)) :
    ∃ ω : M.positiveSupport, defectFree (repair ω) ∧
      M.expectation (fun v => ((sample v).card : ℝ) - (D v : ℝ)) ≤
        ((repair ω).card : ℝ) := by
  apply M.finite_alteration (fun v => (sample v).card) D Finset.card defectFree repair hclear
  intro ω
  have hc := Finset.card_sdiff_add_card_eq_card (hsub ω)
  have hd := hremoved ω
  have hc' : (((sample ω.val) \ repair ω).card : ℝ) + ((repair ω).card : ℝ) =
      ((sample ω.val).card : ℝ) := by exact_mod_cast hc
  have hd' : (((sample ω.val) \ repair ω).card : ℝ) ≤ (D ω.val : ℝ) := by
    exact_mod_cast hd
  linarith

end P205.Probability.FiniteModel
