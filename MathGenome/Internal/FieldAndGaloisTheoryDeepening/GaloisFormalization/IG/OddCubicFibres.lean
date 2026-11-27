import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.CubicGaloisCriterion
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.OddCubicFibres
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Linarith

open Polynomial
open scoped Polynomial

namespace GaloisFormalization.IG

noncomputable section

/-- The specialization of the cubic at the integer parameter `a`. -/
def oddCubicFibre (a : ℤ) : ℚ[X] :=
  X ^ 3 - X - C (a : ℚ)

private theorem fibre_isMonicOfDegree {R : Type*} [Ring R] [Nontrivial R] (a : R) :
    IsMonicOfDegree (X ^ 3 - X - C a) 3 :=
  ((isMonicOfDegree_X_pow R 3).sub (by simp)).sub (by simp)

theorem odd_cubic_fibre_isMonicOfDegree (a : ℤ) :
    IsMonicOfDegree (oddCubicFibre a) 3 :=
  fibre_isMonicOfDegree (a : ℚ)

private theorem odd_cubic_no_integer_root {a : ℤ} (ha : Odd a) (x : ℤ) :
    x ^ 3 - x - a ≠ 0 := by
  have noRootModTwo : ∀ y : ZMod 2, y ^ 3 - y - 1 ≠ 0 := by decide
  intro h
  apply noRootModTwo (x : ZMod 2)
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_zero, ha.intCast_zmod_two]
    using congrArg (Int.cast : ℤ → ZMod 2) h

theorem odd_cubic_fibre_irreducible (a : ℤ) (ha : Odd a) :
    Irreducible (oddCubicFibre a) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [(odd_cubic_fibre_isMonicOfDegree a).natDegree_eq]
  intro x hx
  let p : ℤ[X] := X ^ 3 - X - C a
  have hp : p.Monic := (fibre_isMonicOfDegree a).monic
  have hx' : aeval x p = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    simpa [p, oddCubicFibre, IsRoot.def] using hx
  obtain ⟨b, hb⟩ := isInteger_of_is_root_of_monic hp hx'
  rw [← hb] at hx'
  have hq : (b : ℚ) ^ 3 - (b : ℚ) - (a : ℚ) = 0 := by
    simpa [p] using hx'
  exact odd_cubic_no_integer_root ha b (by exact_mod_cast hq)

theorem odd_cubic_fibre_separable (a : ℤ) (ha : Odd a) :
    (oddCubicFibre a).Separable :=
  (odd_cubic_fibre_irreducible a ha).separable

theorem odd_cubic_fibre_discriminant (a : ℤ) :
    cubicDiscriminant (oddCubicFibre a) = 4 - 27 * (a : ℚ) ^ 2 := by
  simp only [cubicDiscriminant, Cubic.discr, oddCubicFibre, coeff_sub, coeff_X_pow,
    coeff_X, coeff_C]
  norm_num

theorem odd_cubic_fibre_discriminant_neg (a : ℤ) (ha : Odd a) :
    cubicDiscriminant (oddCubicFibre a) < 0 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact Int.not_odd_zero ha
  have hs : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
  have hs' : (1 : ℚ) ≤ (a : ℚ) ^ 2 := by
    exact_mod_cast (show (1 : ℤ) ≤ a ^ 2 by omega)
  rw [odd_cubic_fibre_discriminant]
  linarith

theorem odd_cubic_fibre_discriminant_nonsquare (a : ℤ) (ha : Odd a) :
    ¬ IsSquare (cubicDiscriminant (oddCubicFibre a)) := by
  rintro ⟨x, hx⟩
  exact (not_lt_of_ge (hx ▸ mul_self_nonneg x)) (odd_cubic_fibre_discriminant_neg a ha)

theorem odd_cubic_fibre_galois_equiv (a : ℤ) {L : Type*} [Field L] [Algebra ℚ L]
    [(oddCubicFibre a).IsSplittingField ℚ L] (ha : Odd a) :
    ∃ (e : CubicRootOrdering (oddCubicFibre a) L) (φ : (L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)),
      φ.toMonoidHom = cubicRootAction e :=
  cubic_galois_equiv_of_nonsquare (odd_cubic_fibre_isMonicOfDegree a).monic
    (odd_cubic_fibre_isMonicOfDegree a).natDegree_eq (odd_cubic_fibre_separable a ha)
    (odd_cubic_fibre_irreducible a ha) (odd_cubic_fibre_discriminant_nonsquare a ha)

end
end GaloisFormalization.IG
