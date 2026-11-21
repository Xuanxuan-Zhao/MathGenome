import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticSurdRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace P203

noncomputable abbrev surdNextP : P203Specs.SurdUpdateType := P203Specs.surdNextP
noncomputable abbrev surdNextQ : P203Specs.SurdUpdateType := P203Specs.surdNextQ

/-- The source recurrence works for both signs of the denominator. -/
theorem surd_recurrence : P203Specs.SurdRecurrence := by
  intro P Q D hD hns hQ hdiv
  let a : ℤ := ⌊((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ)⌋
  let R : ℤ := surdNextP P Q D
  let S : ℤ := surdNextQ P Q D
  have hR : R = a * Q - P := rfl
  have hdiv' : Q ∣ D - R ^ 2 := by
    have hid : D - R ^ 2 = (D - P ^ 2) + Q * (2 * a * P - a ^ 2 * Q) := by
      rw [hR]
      ring
    rw [hid]
    exact dvd_add hdiv (dvd_mul_right _ _)
  have hexact : Q * S = D - R ^ 2 := by
    change Q * ((D - R ^ 2) / Q) = D - R ^ 2
    exact Int.mul_ediv_cancel' hdiv'
  have hn : D - R ^ 2 ≠ 0 := by
    intro hz
    apply hns
    exact ⟨R, by nlinarith [hz]⟩
  have hS : S ≠ 0 := by
    intro hz
    apply hn
    rw [← hexact, hz, mul_zero]
  refine ⟨hS, hexact, ?_, ?_⟩
  · rw [← hexact]
    exact dvd_mul_left _ _
  · have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
    have hSr : (S : ℝ) ≠ 0 := by exact_mod_cast hS
    have hsqrt : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast le_of_lt hD)
    have hprod : (Q : ℝ) * (S : ℝ) = (D : ℝ) - (R : ℝ) ^ 2 := by
      exact_mod_cast hexact
    have hRr : (R : ℝ) = (a : ℝ) * (Q : ℝ) - (P : ℝ) := by
      exact_mod_cast hR
    have hden : Real.sqrt (D : ℝ) - (R : ℝ) ≠ 0 := by
      intro hz
      have he : Real.sqrt (D : ℝ) = (R : ℝ) := sub_eq_zero.mp hz
      have hz' : (D : ℝ) - (R : ℝ) ^ 2 = 0 := by rw [← he, hsqrt]; ring
      exact hn (by exact_mod_cast hz')
    change 1 / (((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ) - (a : ℝ)) =
      ((R : ℝ) + Real.sqrt (D : ℝ)) / (S : ℝ)
    have hsub : ((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ) - (a : ℝ) =
        (Real.sqrt (D : ℝ) - (R : ℝ)) / (Q : ℝ) := by
      rw [hRr]
      field_simp [hQr]
      ring
    rw [hsub, one_div_div]
    apply (div_eq_div_iff hden hSr).mpr
    nlinarith [hprod, hsqrt]

end P203
