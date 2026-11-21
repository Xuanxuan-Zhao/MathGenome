import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Recurrence.InitialValues
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.MultiplicativeInverse
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.RationalSeries
import Lean.Elab.Tactic.Omega

/-! Rational ordinary generating functions, paper.tex p204:W14. -/
noncomputable section
open scoped BigOperators
universe u
namespace FiniteCombinatorics.Recurrence

def denominator {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) : Polynomial R :=
  1 - ∑ j : Fin r, Polynomial.C (c j) * Polynomial.X ^ (r - (j : ℕ))

def numerator {R : Type u} [CommRing R] {r : ℕ} (c init : Fin r → R) : Polynomial R :=
  PowerSeries.trunc r ((denominator c : PowerSeries R) * Series.ogf (sequence c init))

lemma denominator_coe {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) :
    (denominator c : PowerSeries R) =
      1 - ∑ j : Fin r, PowerSeries.C (c j) * PowerSeries.X ^ (r - (j : ℕ)) := by
  change Polynomial.coeToPowerSeries.ringHom
    (1 - ∑ j : Fin r, Polynomial.C (c j) * Polynomial.X ^ (r - (j : ℕ))) = _
  simp only [map_sub, map_one, map_sum, map_mul, map_pow,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

theorem denominator_constant {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) :
    PowerSeries.constantCoeff (denominator c : PowerSeries R) = 1 := by
  rw [denominator_coe]
  simp only [map_sub, map_one, map_sum, map_mul, PowerSeries.constantCoeff_C,
    map_pow, PowerSeries.constantCoeff_X]
  have hz (j : Fin r) : 0 ^ (r - (j : ℕ)) = (0 : R) :=
    zero_pow (by have := j.isLt; omega)
  simp [hz]

theorem numerator_degree {R : Type u} [CommRing R] {r : ℕ} (c init : Fin r → R) :
    (numerator c init).degree < (r : WithBot ℕ) :=
  PowerSeries.degree_trunc_lt _ _

/-- Coefficient cancellation is exactly the recurrence equation. -/
lemma coeff_denominator_mul_ogf {R : Type u} [CommRing R] {r : ℕ}
    (c : Fin r → R) (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff (n + r) ((denominator c : PowerSeries R) * Series.ogf a) =
      a (n + r) - ∑ j : Fin r, c j * a (n + (j : ℕ)) := by
  rw [denominator_coe, sub_mul, one_mul, Finset.sum_mul, map_sub, map_sum,
    Series.coeff_ogf]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have hj := j.isLt
  have hle : r - (j : ℕ) ≤ n + r := by omega
  have heq : n + r - (r - (j : ℕ)) = n + (j : ℕ) := by omega
  simp [hle, heq]

theorem product_coefficients_vanish {R : Type u} [CommRing R] {r : ℕ}
    (c : Fin r → R) (a : ℕ → R) (ha : IsSolution c a)
    (n : ℕ) (hn : r ≤ n) :
    PowerSeries.coeff n ((denominator c : PowerSeries R) * Series.ogf a) = 0 := by
  change ∀ m, a (m + r) = ∑ j : Fin r, c j * a (m + (j : ℕ)) at ha
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm, coeff_denominator_mul_ogf, ha, sub_self]

/-- A series with no coefficients from r onward is its polynomial truncation. -/
lemma eq_coe_trunc_of_coeff_vanish {R : Type u} [CommRing R]
    (F : PowerSeries R) (r : ℕ)
    (hF : ∀ n, r ≤ n → PowerSeries.coeff n F = 0) :
    F = (PowerSeries.trunc r F : PowerSeries R) := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · exact hF n (Nat.le_of_not_gt h)

theorem rational_product {R : Type u} [CommRing R] {r : ℕ}
    (c : Fin r → R) (_hr : 1 ≤ r) (init : Fin r → R) (a : ℕ → R)
    (ha : IsSolution c a) (hi : ∀ i : Fin r, a i = init i) :
    (denominator c : PowerSeries R) * Series.ogf a =
      (numerator c init : PowerSeries R) := by
  have heq : a = sequence c init :=
    (recurrence c).eq_mk_of_is_sol_of_eq_init' ha hi
  unfold numerator
  rw [← heq]
  exact eq_coe_trunc_of_coeff_vanish _ r (product_coefficients_vanish c a ha)

theorem unique_numerator {R : Type u} [CommRing R] {r : ℕ}
    (c : Fin r → R) (hr : 1 ≤ r) (a : ℕ → R) (ha : IsSolution c a) :
    ∃! P : Polynomial R, P.degree < (r : WithBot ℕ) ∧
      (denominator c : PowerSeries R) * Series.ogf a = (P : PowerSeries R) := by
  refine ⟨numerator c (fun i => a i),
    ⟨numerator_degree _ _, rational_product c hr _ a ha (fun _ => rfl)⟩, ?_⟩
  intro P hP
  apply Polynomial.coe_injective R
  exact hP.2.symm.trans (rational_product c hr _ a ha (fun _ => rfl))

theorem rational_quotient {R : Type u} [CommRing R] {r : ℕ}
    (c : Fin r → R) (hr : 1 ≤ r) (init : Fin r → R) (a : ℕ → R)
    (ha : IsSolution c a) (hi : ∀ i : Fin r, a i = init i) :
    Series.ogf a = (numerator c init : PowerSeries R) *
      PowerSeries.invOfUnit (denominator c : PowerSeries R) (1 : Rˣ) := by
  have hinv := (Series.invOfUnit_two_sided (denominator c : PowerSeries R)
    (1 : Rˣ) (denominator_constant c)).1
  rw [← rational_product c hr init a ha hi, mul_comm (denominator c : PowerSeries R),
    mul_assoc, hinv, mul_one]

theorem numerator_initial_dependence {R : Type u} [CommRing R] {r : ℕ}
    (c : Fin r → R) (a b : ℕ → R) (h : ∀ i : Fin r, a i = b i) :
    numerator c (fun i => a i) = numerator c (fun i => b i) := by
  rw [show (fun i : Fin r => a i) = (fun i : Fin r => b i) from funext h]

end FiniteCombinatorics.Recurrence
