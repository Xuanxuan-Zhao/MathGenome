import MathGenome.Internal.Specs.D07.Ch23.QuaternionAlgebra
import MathGenome.Internal.D07.Ch08.DomainFieldQuaternionDivisionExample
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace D07.Ch23.QuaternionAlgebra

open Specs.D07.Ch23.QuaternionAlgebra

/-- Complex-pair coordinates of the canonical Hamilton algebra. -/
def pairEquiv : Pair ≃ₗ[ℝ] H where
  toFun := toH
  invFun := fromH
  left_inv u := by
    apply Prod.ext <;> apply Complex.ext <;> simp [toH, fromH]
  right_inv q := by ext <;> simp [toH, fromH]
  map_add' u v := by ext <;> simp [toH]
  map_smul' r u := by ext <;> simp [toH]

@[simp] theorem pairEquiv_apply (u : Pair) : pairEquiv u = toH u := rfl
@[simp] theorem pairEquiv_symm_apply (q : H) : pairEquiv.symm q = fromH q := rfl

@[simp] theorem toH_fromH (q : H) : toH (fromH q) = q :=
  pairEquiv.apply_symm_apply q

theorem toH_mul (u v : Pair) : toH (pairMul u v) = toH u * toH v := by
  ext <;> simp [toH, pairMul] <;> ring

@[simp] theorem toH_one : toH (1, 0) = 1 := by ext <;> simp [toH]
@[simp] theorem toH_zero : toH 0 = 0 := by ext <;> simp [toH]

@[simp] theorem toH_add (u v : Pair) : toH (u + v) = toH u + toH v := by
  ext <;> simp [toH]

theorem pairCoordinates : PairCoordinates :=
  ⟨pairEquiv, fun _ => rfl, fun _ => rfl, toH_mul, toH_one⟩

theorem matrixRepresentation : MatrixRepresentation := by
  obtain ⟨f, hf, hinj⟩ := D07.Ch08.DomainFieldQuaternionDivisionExample.matrixRealization
  refine ⟨f, hinj, ?_⟩
  intro u
  rw [hf]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.matrixMap,
      Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.coordinates, toH, pairMatrix]

theorem pairMatrixLaws : PairMatrixLaws := by
  obtain ⟨f, hinj, hf⟩ := matrixRepresentation
  have hi : Function.Injective pairMatrix := by
    intro u v h
    apply pairEquiv.injective
    exact hinj (by simpa only [pairEquiv_apply, hf] using h)
  refine ⟨hi, ?_, ?_⟩
  · intro u v
    rw [← hf, toH_mul, map_mul, hf, hf]
  · rw [← hf, toH_one, map_one]

theorem pairRingLaws : PairRingLaws := by
  intro u v w
  have hi : Function.Injective toH := pairEquiv.injective
  refine ⟨hi ?_, hi ?_, hi ?_, hi ?_, hi ?_⟩
  · simp only [toH_mul, mul_assoc]
  · simp only [toH_mul, toH_one, one_mul]
  · simp only [toH_mul, toH_one, mul_one]
  · change pairEquiv (pairMul u (v + w)) = pairEquiv (pairMul u v + pairMul u w)
    simp only [map_add, pairEquiv_apply, toH_mul, toH_add, mul_add]
  · change pairEquiv (pairMul (u + v) w) = pairEquiv (pairMul u w + pairMul v w)
    simp only [map_add, pairEquiv_apply, toH_mul, toH_add, add_mul]

theorem unitCoordinates : UnitCoordinates := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;>
    simp [toH, iH, jH, kH, Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH,
      Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.jH,
      Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.kH]

theorem unitRelations : UnitRelations :=
  D07.Ch08.DomainFieldQuaternionDivisionExample.unitRelations

theorem conjugationCoordinates : ConjugationCoordinates := by
  intro u
  ext <;> simp [toH, pairConj]

theorem normIdentification : NormIdentification := by
  intro u
  have h : pairNorm u = Quaternion.normSq (toH u) := by
    simp only [pairNorm, Quaternion.normSq_def', toH, Complex.normSq_apply]
    ring
  refine ⟨h, ?_, ?_⟩
  · simp only [pairNorm, Complex.normSq_eq_norm_sq]
  · rw [h, Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem conjugateProducts : ConjugateProducts := by
  intro u
  have h := (normIdentification u).1
  have hr : toH ((pairNorm u : ℂ), 0) = (pairNorm u : H) := by
    ext <;> simp [toH]
  constructor <;> apply pairEquiv.injective <;> change toH _ = toH _
  · rw [toH_mul, conjugationCoordinates, hr, h, Quaternion.self_mul_star]
  · rw [toH_mul, conjugationCoordinates, hr, h, Quaternion.star_mul_self]

theorem positiveNorm : PositiveNorm := by
  intro u
  have hz : toH u = 0 ↔ u = 0 := by
    rw [← toH_zero]
    exact pairEquiv.injective.eq_iff
  have he : pairNorm u = 0 ↔ u = 0 := by
    rw [(normIdentification u).1, Quaternion.normSq_eq_zero, hz]
  have hn : 0 ≤ pairNorm u := by
    rw [(normIdentification u).1]
    exact Quaternion.normSq_nonneg
  exact ⟨hn, he, fun hu => lt_of_le_of_ne hn (Ne.symm (he.not.mpr hu))⟩

theorem inverseFormula : InverseFormula := by
  intro u
  have hinv : toH (pairInv u) = (toH u)⁻¹ := by
    change pairEquiv ((pairNorm u)⁻¹ • pairConj u) = _
    rw [map_smul, pairEquiv_apply, conjugationCoordinates,
      (normIdentification u).1, Quaternion.inv_def]
  refine ⟨hinv, ?_⟩
  intro hu
  have hq : toH u ≠ 0 := by
    intro h
    apply hu
    exact pairEquiv.injective (h.trans toH_zero.symm)
  constructor <;> apply pairEquiv.injective <;> change toH _ = toH _
  · rw [toH_mul, hinv, toH_one, mul_inv_cancel₀ hq]
  · rw [toH_mul, hinv, toH_one, inv_mul_cancel₀ hq]

theorem divisionAlgebra : DivisionAlgebra := by
  obtain ⟨hn, hu, hc⟩ := D07.Ch08.DomainFieldQuaternionDivisionExample.divisionRingExample
  exact ⟨⟨inferInstance, rfl⟩, hn, hu, hc⟩

theorem determinantNorm : DeterminantNorm := by
  intro u
  simp only [pairMatrix, Matrix.det_fin_two]
  apply Complex.ext <;> simp [pairNorm, Complex.normSq_apply]
  ring

theorem normMultiplicative : NormMultiplicative := by
  intro u v
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, ← determinantNorm, ← determinantNorm, ← determinantNorm,
    (pairMatrixLaws).2.1, Matrix.det_mul]

theorem fourSquareNorm : FourSquareNorm := by
  intro a b c d
  rw [← D07.Ch08.DomainFieldQuaternionDivisionExample.coordinateExpansion a b c d,
    Quaternion.normSq_def']

theorem centralizerCoordinates : CentralizerCoordinates := by
  intro q
  have hi : q * iH = iH * q ↔ q.imJ = 0 ∧ q.imK = 0 := by
    constructor
    · intro h
      have hj := congrArg QuaternionAlgebra.imJ h
      have hk := congrArg QuaternionAlgebra.imK h
      simp [iH, Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH] at hj hk
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hc, hd⟩
      ext <;> simp [iH, Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH, hc, hd]
  refine ⟨hi, ?_⟩
  constructor
  · rintro ⟨hI, hJ⟩
    obtain ⟨hc, hd⟩ := hi.mp hI
    have hk := congrArg QuaternionAlgebra.imK hJ
    simp [jH, Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.jH] at hk
    exact ⟨by linarith, hc, hd⟩
  · rintro ⟨hb, hc, hd⟩
    refine ⟨hi.mpr ⟨hc, hd⟩, ?_⟩
    ext <;> simp [jH, Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.jH, hb, hc, hd]

@[simp] theorem toH_real (r : ℝ) : toH ((r : ℂ), 0) = algebraMap ℝ H r := by
  ext <;> simp [toH]

theorem centerReal : CenterReal := by
  have hc : ∀ q : H, (∀ p : H, q * p = p * q) ↔ ∃ r : ℝ, q = algebraMap ℝ H r := by
    intro q
    constructor
    · intro h
      obtain ⟨hb, hj, hk⟩ := (centralizerCoordinates q).2.mp ⟨h iH, h jH⟩
      refine ⟨q.re, ?_⟩
      ext <;> simp [hb, hj, hk]
    · rintro ⟨r, rfl⟩ p
      exact Algebra.commutes r p
  refine ⟨hc, ?_⟩
  intro u
  constructor
  · intro h
    have hh : ∀ q : H, toH u * q = q * toH u := by
      intro q
      have ht := congrArg pairEquiv (h (pairEquiv.symm q))
      change toH (pairMul u (pairEquiv.symm q)) =
        toH (pairMul (pairEquiv.symm q) u) at ht
      rw [toH_mul, toH_mul] at ht
      change pairEquiv u * pairEquiv (pairEquiv.symm q) =
        pairEquiv (pairEquiv.symm q) * pairEquiv u at ht
      simpa only [LinearEquiv.apply_symm_apply, pairEquiv_apply] using ht
    obtain ⟨r, hr⟩ := (hc (toH u)).mp hh
    refine ⟨r, pairEquiv.injective ?_⟩
    change toH u = toH ((r : ℂ), 0)
    rw [hr, toH_real]
  · rintro ⟨r, rfl⟩ v
    apply pairEquiv.injective
    change toH (pairMul _ _) = toH (pairMul _ _)
    rw [toH_mul, toH_mul, toH_real]
    exact Algebra.commutes r (toH v)

theorem realBasis : RealBasis := by
  let b : Module.Basis (Fin 4) ℝ H := QuaternionAlgebra.basisOneIJK (R := ℝ) (-1) 0 (-1)
  have hb : ∀ t, b t = ![1, iH, jH, kH] t := by
    intro t
    apply b.repr.injective
    rw [Module.Basis.repr_self]
    ext s
    fin_cases t <;> fin_cases s <;>
      simp [b, iH, jH, kH, Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH,
        Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.jH,
        Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.kH]
  refine ⟨⟨b, hb⟩, ⟨b.map pairEquiv.symm, ?_⟩, Quaternion.finrank_eq_four⟩
  intro t
  rw [Module.Basis.map_apply, hb]
  fin_cases t <;>
    apply pairEquiv.injective <;>
    simp [unitCoordinates.1, unitCoordinates.2.1, unitCoordinates.2.2]

end D07.Ch23.QuaternionAlgebra
