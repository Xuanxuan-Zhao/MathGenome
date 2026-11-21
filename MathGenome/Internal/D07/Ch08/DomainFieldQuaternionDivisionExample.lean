import MathGenome.Internal.Specs.D07.Ch08.DomainFieldQuaternionDivisionExample
import MathGenome.Internal.D07.Ch08.MatrixRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! K07.08.domain_field: the associative real quaternion division algebra,
with the source's explicit two-by-two complex matrix realization. -/

noncomputable section

namespace D07.Ch08.DomainFieldQuaternionDivisionExample

open Specs.D07.Ch08.DomainFieldQuaternionDivisionExample
open scoped Quaternion

theorem coordinateExpansion : CoordinateExpansion := by
  intro a b c d
  ext <;> simp [iH, jH, kH]

private theorem matrixMap_add (p q : H) : matrixMap (p + q) = matrixMap p + matrixMap q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMap, coordinates] <;> ring

private theorem matrixMap_mul (p q : H) : matrixMap (p * q) = matrixMap p * matrixMap q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMap, coordinates, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

private theorem matrixMap_one : matrixMap 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixMap, coordinates]

private theorem matrixMap_real (r : ℝ) :
    matrixMap (algebraMap ℝ H r) = algebraMap ℝ M r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixMap, coordinates, Algebra.algebraMap_eq_smul_one]

/-- The coordinates define an algebra homomorphism, not merely a set map. -/
def matrixEmbedding : H →ₐ[ℝ] M where
  toFun := matrixMap
  map_one' := matrixMap_one
  map_mul' := matrixMap_mul
  map_zero' := by simpa using matrixMap_real 0
  map_add' := matrixMap_add
  commutes' := matrixMap_real

private theorem matrixEmbedding_injective : Function.Injective matrixEmbedding := by
  intro p q h
  have h00 := congrArg (fun A : M => A 0 0) h
  have h01 := congrArg (fun A : M => A 0 1) h
  have ha := congrArg Complex.re h00
  have hb := congrArg Complex.im h00
  have hc := congrArg Complex.re h01
  have hd := congrArg Complex.im h01
  apply Quaternion.ext
  · simpa [matrixEmbedding, matrixMap, coordinates] using ha
  · simpa [matrixEmbedding, matrixMap, coordinates] using hb
  · simpa [matrixEmbedding, matrixMap, coordinates] using hc
  · simpa [matrixEmbedding, matrixMap, coordinates] using hd

theorem matrixRealization : MatrixRealization :=
  ⟨matrixEmbedding, fun _ => rfl, matrixEmbedding_injective⟩

theorem matrixAlgebraEquivalence : MatrixAlgebraEquivalence := by
  refine ⟨matrixEmbedding.range, ?_,
    AlgEquiv.ofInjective matrixEmbedding matrixEmbedding_injective, fun _ => rfl⟩
  intro A
  change (∃ q : H, matrixMap q = A) ↔ ∃ a b c d : ℝ, coordinates a b c d = A
  constructor
  · rintro ⟨q, h⟩
    exact ⟨q.re, q.imI, q.imJ, q.imK, h⟩
  · rintro ⟨a, b, c, d, h⟩
    exact ⟨⟨a, b, c, d⟩, h⟩

theorem matrixClosure : MatrixClosure := by
  obtain ⟨S, hS, _⟩ := matrixAlgebraEquivalence
  refine ⟨(hS 0).mp S.zero_mem, (hS 1).mp S.one_mem, ?_, ?_, ?_⟩
  · intro A B hA hB
    exact ⟨(hS _).mp (S.add_mem ((hS _).mpr hA) ((hS _).mpr hB)),
      (hS _).mp (S.mul_mem ((hS _).mpr hA) ((hS _).mpr hB))⟩
  · intro A hA
    exact (hS _).mp (S.neg_mem ((hS _).mpr hA))
  · intro r A hA
    exact (hS _).mp (S.smul_mem ((hS _).mpr hA) r)

theorem ringLaws : RingLaws := by
  intro p q r
  exact ⟨mul_assoc p q r, one_mul p, mul_one p, mul_add p q r, add_mul p q r⟩

theorem unitRelations : UnitRelations := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext <;> norm_num [iH, jH, kH]

private theorem conjugate_eq_star (q : H) : conjugate q = star q := by
  ext <;> simp [conjugate]

private theorem denominator_eq_normSq (q : H) : denominator q = Quaternion.normSq q :=
  (Quaternion.normSq_def' q).symm

theorem conjugateProducts : ConjugateProducts := by
  intro q
  rw [conjugate_eq_star, denominator_eq_normSq]
  exact ⟨Quaternion.self_mul_star q, Quaternion.star_mul_self q⟩

theorem positiveDenominator : PositiveDenominator := by
  intro q hq
  rw [denominator_eq_normSq]
  exact lt_of_le_of_ne Quaternion.normSq_nonneg (Ne.symm (Quaternion.normSq_ne_zero.mpr hq))

theorem inverseFormula : InverseFormula := by
  intro q hq
  have h : q⁻¹ = inverseCandidate q := by
    simp only [inverseCandidate, denominator_eq_normSq, conjugate_eq_star, Quaternion.inv_def]
  exact ⟨h, h ▸ mul_inv_cancel₀ hq, h ▸ inv_mul_cancel₀ hq⟩

theorem divisionRingExample : DivisionRingExample := by
  refine ⟨zero_ne_one, fun q hq => isUnit_iff_ne_zero.mpr hq, ?_⟩
  intro hcomm
  have h := congrArg QuaternionAlgebra.imK (hcomm iH jH)
  norm_num [iH, jH] at h

end D07.Ch08.DomainFieldQuaternionDivisionExample
