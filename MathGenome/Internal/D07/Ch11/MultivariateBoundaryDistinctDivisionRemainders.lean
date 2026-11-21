import MathGenome.Internal.Specs.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The explicit two-variable nonuniqueness example, paper.tex:2860–2872. -/

universe u

namespace D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders

open MvPolynomial
open Specs.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders
open scoped MonomialOrder

theorem lexVariableOrder : LexVariableOrder := by
  change toLex (Finsupp.single (1 : Fin 2) 1) < toLex (Finsupp.single (0 : Fin 2) 1)
  use 0
  simp

private lemma degree_xy (F : Type u) [Field F] :
    lexOrder.degree (x F * y F) = Finsupp.single 0 1 + Finsupp.single 1 1 := by
  rw [lexOrder.degree_mul (X_ne_zero _) (X_ne_zero _),
    lexOrder.degree_X, lexOrder.degree_X]

private lemma degree_y_squared (F : Type u) [Field F] :
    lexOrder.degree (y F ^ 2) = Finsupp.single 1 2 := by
  rw [pow_two, lexOrder.degree_mul (X_ne_zero _) (X_ne_zero _), lexOrder.degree_X]
  rw [← Finsupp.single_add]

theorem leadingMonomials : LeadingMonomials.{u} := by
  intro F _
  have hxy : lexOrder.degree (1 : MvPolynomial (Fin 2) F) ≺[lexOrder]
      lexOrder.degree (x F * y F) := by
    rw [lexOrder.degree_one, degree_xy]
    rw [map_zero, MonomialOrder.toSyn_lt_iff_ne_zero (m := lexOrder)]
    apply lexOrder.toSyn.injective.ne
    change _ ≠ (0 : Fin 2 →₀ ℕ)
    intro h
    have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    norm_num at this
  have hy : lexOrder.degree (1 : MvPolynomial (Fin 2) F) ≺[lexOrder]
      lexOrder.degree (y F ^ 2) := by
    rw [lexOrder.degree_one, degree_y_squared]
    rw [map_zero, MonomialOrder.toSyn_lt_iff_ne_zero (m := lexOrder)]
    apply lexOrder.toSyn.injective.ne
    change _ ≠ (0 : Fin 2 →₀ ℕ)
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (lexOrder.degree_sub_of_lt hxy).trans (degree_xy F)
  · exact (lexOrder.degree_sub_of_lt hy).trans (degree_y_squared F)
  · unfold g₁
    rw [lexOrder.leadingCoeff_sub_of_lt hxy, lexOrder.leadingCoeff_mul,
      lexOrder.leadingCoeff_X, lexOrder.leadingCoeff_X, one_mul]
  · unfold g₂
    rw [lexOrder.leadingCoeff_sub_of_lt hy, lexOrder.leadingCoeff_pow,
      lexOrder.leadingCoeff_X, one_pow]

theorem cancellationIdentities : CancellationIdentities.{u} := by
  intro F _
  constructor <;> dsimp [dividend, g₁, g₂] <;> ring

theorem terminalRemainders : TerminalRemainders.{u} := by
  intro F _
  obtain ⟨h₁, h₂, _, _⟩ := leadingMonomials F
  have hx : Terminal (x F) := by
    intro e he
    simp only [x, support_X, Finset.mem_singleton] at he
    subst e
    rw [h₁, h₂]
    constructor
    · intro h
      have := h (1 : Fin 2)
      norm_num at this
    · intro h
      have := h (1 : Fin 2)
      norm_num at this
  have hy : Terminal (y F) := by
    intro e he
    simp only [y, support_X, Finset.mem_singleton] at he
    subst e
    rw [h₁, h₂]
    constructor
    · intro h
      have := h (0 : Fin 2)
      norm_num at this
    · intro h
      have := h (1 : Fin 2)
      norm_num at this
  exact ⟨hx, hy, fun h => (by decide : (0 : Fin 2) ≠ 1) (X_injective h)⟩

theorem idealDifference : IdealDifference.{u} := by
  intro F _
  have hid : x F - y F = y F * g₁ F - x F * g₂ F := by
    dsimp [g₁, g₂]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  apply Ideal.sub_mem
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem divisionSteps : DivisionSteps.{u} := by
  intro F _
  obtain ⟨h₁, h₂, hc₁, hc₂⟩ := leadingMonomials F
  have hp : lexOrder.degree (dividend F) = Finsupp.single 0 1 + Finsupp.single 1 2 := by
    unfold dividend
    rw [lexOrder.degree_mul (X_ne_zero _) (pow_ne_zero _ (X_ne_zero _)),
      lexOrder.degree_X, degree_y_squared]
  have hcp : lexOrder.leadingCoeff (dividend F) = 1 := by
    simp [dividend, x, y, lexOrder.leadingCoeff_mul, lexOrder.leadingCoeff_pow]
  constructor
  · refine ⟨by rw [hc₁]; exact one_ne_zero, Finsupp.single 1 1, 1, one_ne_zero, ?_, ?_, ?_⟩
    · rw [h₁, hp]
      ext i
      fin_cases i <;> norm_num
    · rw [hc₁, hcp, one_mul]
    · exact (cancellationIdentities F).1.symm
  · refine ⟨by rw [hc₂]; exact one_ne_zero, Finsupp.single 0 1, 1, one_ne_zero, ?_, ?_, ?_⟩
    · rw [h₂, hp]
    · rw [hc₂, hcp, one_mul]
    · exact (cancellationIdentities F).2.symm

theorem distinctDivisionRemainders : DistinctDivisionRemainders.{u} := by
  intro F _
  obtain ⟨hx, hy, hne⟩ := terminalRemainders F
  obtain ⟨hfirst, hsecond⟩ := divisionSteps F
  exact ⟨y F, x F, ⟨Or.inl hfirst, hy⟩, ⟨Or.inr hsecond, hx⟩, Ne.symm hne⟩

end D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders
