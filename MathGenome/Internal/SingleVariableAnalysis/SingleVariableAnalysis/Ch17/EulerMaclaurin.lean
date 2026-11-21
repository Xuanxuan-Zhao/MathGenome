import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.EmRecursion

/-! Euler–Maclaurin with the paper's actual proper Riemann remainder.
The upstream recursion supplies all integrability facts. Pairing its steps
eliminates odd Bernoulli boundary terms; a finite induction then telescopes.
No convergence of an infinite Euler–Maclaurin series is asserted or used. -/
noncomputable section
namespace SingleVariableAnalysis.EulerMaclaurin
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch17.EmRecursion
open Specs.SingleVariableAnalysis.Ch17.Bernoulli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Finite algebra for the paired odd/even recursion. -/
theorem sum_even_corrections (m : ℕ) (hm : 1 ≤ m) (T A : ℕ → E)
    (hodd : ∀ r : ℕ, 1 ≤ r → r ≤ m → T (2 * r - 1) = A r - T (2 * r))
    (heven : ∀ r : ℕ, 1 ≤ r → r < m → T (2 * r) = -T (2 * r + 1)) :
    T 1 = (∑ r ∈ Finset.range m, A (r + 1)) - T (2 * m) := by
  have hprefix : ∀ n : ℕ, 1 ≤ n → n ≤ m →
      T 1 = (∑ r ∈ Finset.range n, A (r + 1)) - T (2 * n) := by
    intro n hn hnm
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hzero : n = 0
      · subst n
        simpa using hodd 1 (by omega) (by omega)
      · have hp := ih (by omega) (by omega)
        have he := heven n (by omega) (by omega)
        have ho := hodd (n + 1) (by omega) hnm
        have hind : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [hind] at ho
        rw [Finset.sum_range_succ, hp, he, ho]
        abel
  exact hprefix m hm le_rfl

/-- Derive the finite formula from the proved integral recursion. This helper
is generic only to share the identical real and complex finite algebra. -/
theorem formula_of_recursion
    {I : (ℝ → E) → ℝ → ℝ → Prop}
    {J : (f : ℝ → E) → {a b : ℝ} → I f a b → E}
    (hrec : recursion I J) :
    Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin.formula I J := by
  intro a b hab m hm f D hD
  obtain ⟨hf, hB, hfirst, hstep⟩ := hrec a b hab m hm f D hD
  let T : ℕ → E := fun j => if h : 1 ≤ j ∧ j ≤ 2 * m then
    term J j D (hB j h.1 h.2) else 0
  have hT (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ 2 * m) :
      T j = term J j D (hB j hj hjm) := by
    simp [T, hj, hjm]
  let A : ℕ → E := fun r =>
    (bernoulliNumberValue (2 * r) / ((2 * r).factorial : ℝ)) •
      (D (2 * r - 1) b - D (2 * r - 1) a)
  have hodd (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) :
      T (2 * r - 1) = A r - T (2 * r) := by
    have hs := hstep (2 * r - 1) (by omega) (by omega)
    have hind : 2 * r - 1 + 1 = 2 * r := by omega
    have hs' : T (2 * r - 1) =
        (bernoulliNumberValue (2 * r - 1 + 1) /
          ((2 * r - 1 + 1).factorial : ℝ)) •
            (D (2 * r - 1) b - D (2 * r - 1) a) - T (2 * r - 1 + 1) := by
      rw [hT _ (by omega) (by omega), hT _ (by omega) (by omega)]
      exact hs
    simpa only [hind] using hs' 
  have heven (r : ℕ) (hr : 1 ≤ r) (hrm : r < m) :
      T (2 * r) = -T (2 * r + 1) := by
    have hs := hstep (2 * r) (by omega) (by omega)
    have hz : bernoulliNumberValue (2 * r + 1) = 0 :=
      bernoulli_odd_number (2 * r + 1) (by omega) ⟨r, by omega⟩
    rw [hz, zero_div, zero_smul, zero_sub] at hs
    rw [hT _ (by omega) (by omega), hT _ (by omega) (by omega)]
    exact hs
  have he := sum_even_corrections m hm T A hodd heven
  rw [hT 1 (by omega) (by omega), hT (2 * m) (by omega) le_rfl] at he
  refine ⟨hf, hB (2 * m) (by omega) le_rfl, ?_⟩
  rw [← hfirst] at he
  change trapezoid f a b = J f hf + (∑ r ∈ Finset.range m, A (r + 1)) - _
  calc
    trapezoid f a b = ((∑ r ∈ Finset.range m, A (r + 1)) -
        term J (2 * m) D (hB (2 * m) (by omega) le_rfl)) + J f hf :=
      sub_eq_iff_eq_add.mp he
    _ = _ := by abel

end SingleVariableAnalysis.EulerMaclaurin

namespace SingleVariableAnalysis

theorem euler_maclaurin_real :
    Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin.realFormula :=
  EulerMaclaurin.formula_of_recursion em_real_recursion

theorem euler_maclaurin_complex :
    Specs.SingleVariableAnalysis.Ch17.EulerMaclaurin.complexFormula :=
  EulerMaclaurin.formula_of_recursion em_complex_recursion

end SingleVariableAnalysis
