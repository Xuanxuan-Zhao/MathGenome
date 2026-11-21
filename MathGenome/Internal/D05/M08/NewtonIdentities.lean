import MathGenome.Internal.Specs.D05.M08.NewtonIdentities
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M04.Trace
import MathGenome.Internal.D05.M08.NewtonIdentities.Series
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Ring

noncomputable section
open Finset
namespace D05.M08.NewtonIdentities

variable {K : Type*} [Field K]

/-- The formal determinant series is the polynomial reverse, included in series. -/
theorem determinantSeries_eq_reverse {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    determinantSeries A = (A.charpoly.reverse : PowerSeries K) := by
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, determinantSeries,
    D05.M05.DetDefinition.matrix_det_bridge]
  change (pencil A).det = Polynomial.coeToPowerSeries.ringHom
    (Matrix.det (1 - (Polynomial.X : Polynomial K) • A.map Polynomial.C))
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [pencil, constantMatrix, h] <;> ring

theorem coefficient_zero : Specs.D05.M08.NewtonIdentities.coefficient_zero := by
  intro K V _ _ _ _ T
  simp only [elementaryCoeff, pow_zero, one_mul, Nat.sub_zero]
  change T.charpoly.coeff (Module.finrank K V) = 1
  rw [← LinearMap.charpoly_natDegree T]
  exact (LinearMap.charpoly_monic T).coeff_natDegree

private theorem signed_coefficient {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V) (k : ℕ) :
    (-1 : K)^k * elementaryCoeff T k = T.charpoly.coeff (Module.finrank K V - k) := by
  simp [elementaryCoeff, Specs.D05.M08.Charpoly.charpoly_value, ← mul_assoc,
    ← mul_pow]

theorem characteristic_expansion :
    Specs.D05.M08.NewtonIdentities.characteristic_expansion := by
  intro K V _ _ _ _ T
  simp_rw [signed_coefficient]
  change T.charpoly = _
  have h := T.charpoly.as_sum_range
  rw [LinearMap.charpoly_natDegree] at h
  refine h.trans ?_
  simpa only [Nat.add_sub_cancel, Polynomial.C_mul_X_pow_eq_monomial] using
    (Finset.sum_range_reflect
      (fun j => Polynomial.monomial j (T.charpoly.coeff j))
      (Module.finrank K V + 1)).symm

theorem determinant_coefficients :
    Specs.D05.M08.NewtonIdentities.determinant_coefficients := by
  intro K V _ _ _ _ b T k hk
  rw [signed_coefficient, determinantSeries_eq_reverse, Polynomial.coeff_coe,
    LinearMap.charpoly_toMatrix, Polynomial.coeff_reverse,
    LinearMap.charpoly_natDegree, Polynomial.revAt_le hk]

private theorem sign_cancel (m j : ℕ) :
    (-1 : K)^(m+j+1) * -((-1)^m) = (-1)^j := by
  calc
    _ = (-1)^j * ((-1 : K)^m * (-1)^m) := by simp only [pow_add, pow_one]; ring
    _ = _ := by rw [← mul_pow]; simp

theorem newton_identity : Specs.D05.M08.NewtonIdentities.newton_identity := by
  intro K V _ _ _ _ T k hk hkn
  let b := Module.finBasis K V
  let A := LinearMap.toMatrix b b T
  have hs := Series.finite_coefficients A (k-1)
  have hsucc : k - 1 + 1 = k := by omega
  rw [← Nat.cast_add_one, hsucc] at hs
  have hreindex : (∑ p ∈ antidiagonal (k-1),
      PowerSeries.coeff p.1 (determinantSeries A) * Matrix.trace (A^(p.2+1))) =
      ∑ j ∈ range k, PowerSeries.coeff (k-1-j) (determinantSeries A) *
        Matrix.trace (A^(j+1)) := by
    rw [← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Prod.swap, hsucc, Nat.succ_eq_add_one]
  rw [hreindex, determinant_coefficients b T k hkn] at hs
  have hcoef : ∀ j ∈ range k,
      PowerSeries.coeff (k-1-j) (determinantSeries A) =
        (-1 : K)^(k-1-j) * elementaryCoeff T (k-(j+1)) := by
    intro j hj
    rw [determinant_coefficients b T (k-1-j) (by omega)]
    congr 2; omega
  have htrace : ∀ j, Matrix.trace (A^(j+1)) = LinearMap.trace K V (T^(j+1)) := by
    intro j
    rw [LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace K b]
  simp_rw [htrace] at hs
  have hsum := Finset.sum_congr rfl (fun j hj =>
    congrArg (fun x : K => x * LinearMap.trace K V (T^(j+1))) (hcoef j hj))
  rw [hsum] at hs
  have hm := congrArg (fun x : K => (-1)^k * x) hs
  have hleft : (-1 : K)^k * (((-1)^k * elementaryCoeff T k) * (k : K)) =
      (k : K) * elementaryCoeff T k := by
    calc
      _ = ((-1 : K)^k * (-1)^k) * ((k : K) * elementaryCoeff T k) := by ring
      _ = _ := by rw [← mul_pow]; simp
  rw [hleft, ← Finset.sum_neg_distrib, Finset.mul_sum] at hm
  refine hm.trans (Finset.sum_congr rfl ?_)
  intro j hj
  have hjk := Finset.mem_range.mp hj
  have hsign : (-1 : K)^k * -((-1)^(k-1-j)) = (-1)^j := by
    convert sign_cancel (K := K) (k-1-j) j using 1
    congr 2
    omega
  calc
    _ = ((-1 : K)^k * -((-1)^(k-1-j))) *
      elementaryCoeff T (k-(j+1)) * LinearMap.trace K V (T^(j+1)) := by ring
    _ = _ := by rw [hsign]

theorem newton_for_expansion : Specs.D05.M08.NewtonIdentities.newton_for_expansion := by
  intro K V _ _ _ _ T e hexp
  have he : ∀ k, k ≤ Module.finrank K V → e k = elementaryCoeff T k := by
    intro k hk
    have h := congrArg (fun p : Polynomial K => p.coeff (Module.finrank K V - k)) hexp
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at h
    rw [Finset.sum_eq_single k] at h
    · simp only [ite_true] at h
      rw [elementaryCoeff, h]
      simp only [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    · intro j hj hjk
      have hjn := Finset.mem_range.mp hj
      rw [ite_eq_right (by omega)]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  refine ⟨(he 0 (by omega)).trans (coefficient_zero T), ?_⟩
  intro k hk hkn
  rw [he k hkn, newton_identity T k hk hkn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he (k-(j+1)) (by omega)]

theorem recursive_formula : Specs.D05.M08.NewtonIdentities.recursive_formula := by
  intro K V _ _ _ _ _ T k hk hkn
  rw [← newton_identity T k hk hkn, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega)), one_mul]

theorem recursive_uniqueness : Specs.D05.M08.NewtonIdentities.recursive_uniqueness := by
  intro K V _ _ _ _ _ T e he0 he k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkn
    by_cases hk0 : k = 0
    · subst k
      rw [he0, coefficient_zero T]
    · have hk : 1 ≤ k := by omega
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hk0 : (k : K) ≠ 0)
      rw [he k hk hkn, newton_identity T k hk hkn]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (k-(j+1)) (by omega) (by omega)]

theorem zero_dimension : Specs.D05.M08.NewtonIdentities.zero_dimension := by
  intro K V _ _ _ _ T h
  exact ⟨D05.M08.Charpoly.zero_dimensional T h, coefficient_zero T, by omega⟩

end D05.M08.NewtonIdentities
