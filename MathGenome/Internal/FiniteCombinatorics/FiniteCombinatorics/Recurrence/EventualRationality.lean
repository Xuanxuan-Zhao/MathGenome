import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Recurrence.RationalSeries
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.EventualRationality

/-! The first assertion of paper.tex, p204:W16: eventual recurrence and
rationality of the ordinary generating series, over an arbitrary field. -/
noncomputable section
open scoped BigOperators
universe u
namespace FiniteCombinatorics.Recurrence

/-- Any normalized polynomial denominator has recurrence form. The order may
exceed its degree, which permits constant denominators without an order-zero
exception. -/
lemma normalized_polynomial_eq_denominator {R : Type u} [CommRing R]
    (Q : Polynomial R) (hQ : Q.coeff 0 = 1) :
    Q = denominator (fun j : Fin (Q.natDegree + 1) =>
      -Q.coeff (Q.natDegree + 1 - (j : ℕ))) := by
  classical
  let r := Q.natDegree + 1
  let c : Fin r → R := fun j => -Q.coeff (r - (j : ℕ))
  change Q = denominator c
  apply Polynomial.ext
  intro n
  simp only [denominator, Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n = 0
  · subst n
    rw [hQ]
    have hz : ∀ j : Fin r, ¬0 = r - (j : ℕ) := by
      intro j; have := j.isLt; omega
    simp [hz]
  · rw [Polynomial.coeff_one, ite_eq_right hn]
    by_cases hnr : n ≤ r
    · let j : Fin r := ⟨r - n, by omega⟩
      have heq : r - (j : ℕ) = n := by dsimp [j]; omega
      rw [Finset.sum_eq_single j]
      · simp [heq, c]
      · intro k _ hkj
        have hk : n ≠ r - (k : ℕ) := by
          intro hk
          apply hkj
          apply Fin.ext
          dsimp [j]
          have := k.isLt
          omega
        simp [hk]
      · simp
    · have hz : ∀ j : Fin r, ¬n = r - (j : ℕ) := by
        intro j; omega
      simp only [hz, ite_false, Finset.sum_const_zero, sub_zero]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      dsimp [r] at hnr
      omega

/-- A recurrence need hold only eventually for its denominator product to have
finite support. -/
lemma eventual_recurrence_product {R : Type u} [CommRing R]
    {r : ℕ} (c : Fin r → R) (a : ℕ → R) (N : ℕ)
    (ha : ∀ n, N ≤ n → a (n + r) = ∑ j : Fin r, c j * a (n + (j : ℕ))) :
    (denominator c : PowerSeries R) * Series.ogf a =
      (PowerSeries.trunc (N + r)
        ((denominator c : PowerSeries R) * Series.ogf a) : PowerSeries R) := by
  apply eq_coe_trunc_of_coeff_vanish
  intro m hm
  have hmr : m = (m - r) + r := by omega
  rw [hmr, coeff_denominator_mul_ogf, ha (m - r) (by omega), sub_self]

/-- Normalized rational generating functions are exactly eventual homogeneous
constant-coefficient recurrences, with positive order in all cases. -/
theorem eventual_rationality {K : Type u} [Field K] (a : ℕ → K) :
    (∃ P Q : Polynomial K, Q.coeff 0 = 1 ∧
      Series.ogf a = (P : PowerSeries K) *
        PowerSeries.invOfUnit (Q : PowerSeries K) (1 : Kˣ)) ↔
    ∃ (r : ℕ) (_hr : 1 ≤ r) (c : Fin r → K) (N : ℕ),
      ∀ n : ℕ, N ≤ n → a (n + r) = ∑ j : Fin r, c j * a (n + (j : ℕ)) := by
  constructor
  · rintro ⟨P, Q, hQ, ha⟩
    -- For Q = 1 this is order one, with coefficient -[z]Q = 0.
    let r := Q.natDegree + 1
    let c : Fin r → K := fun j => -Q.coeff (r - (j : ℕ))
    have hden : Q = denominator c := normalized_polynomial_eq_denominator Q hQ
    have hconst : PowerSeries.constantCoeff (Q : PowerSeries K) = (↑(1 : Kˣ) : K) := by
      simpa using hQ
    have hprod : (Q : PowerSeries K) * Series.ogf a = (P : PowerSeries K) := by
      rw [ha, mul_left_comm, (Series.invOfUnit_two_sided _ _ hconst).1, mul_one]
    refine ⟨r, by dsimp [r]; omega, c, P.natDegree + 1, ?_⟩
    intro n hn
    have hz : PowerSeries.coeff (n + r)
        ((denominator c : PowerSeries K) * Series.ogf a) = 0 := by
      rw [← hden, hprod, Polynomial.coeff_coe]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    rw [coeff_denominator_mul_ogf] at hz
    exact sub_eq_zero.mp hz
  · rintro ⟨r, _hr, c, N, ha⟩
    let Q := denominator c
    let P := PowerSeries.trunc (N + r) ((Q : PowerSeries K) * Series.ogf a)
    have hprod : (Q : PowerSeries K) * Series.ogf a = (P : PowerSeries K) :=
      eventual_recurrence_product c a N ha
    refine ⟨P, Q, ?_, ?_⟩
    · have := denominator_constant c
      simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe] using this
    · rw [← hprod, mul_comm (Q : PowerSeries K), mul_assoc,
        (Series.invOfUnit_two_sided _ (1 : Kˣ) (denominator_constant c)).1, mul_one]

end FiniteCombinatorics.Recurrence
