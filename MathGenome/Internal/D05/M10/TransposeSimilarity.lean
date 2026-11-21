import MathGenome.Internal.Specs.D05.M10.TransposeSimilarity
import MathGenome.Internal.D05.M10.JordanExistence
import MathGenome.Internal.D05.Foundations.Fta

noncomputable section
open scoped Classical
open Matrix
namespace D05.M10.TransposeSimilarity
open Specs.D05.M10.TransposeSimilarity
open Specs.D05.M10.JordanExistence (jordanMatrix)

lemma blockReversal_involutive {r : ℕ} (a : Fin r → ℕ) :
    Function.Involutive (blockReversal a) := by
  rintro ⟨i, j⟩
  simp [blockReversal]

lemma blockReversal_symm {r : ℕ} (a : Fin r → ℕ) :
    (blockReversal a).symm = blockReversal a := by
  apply Equiv.ext
  intro x
  apply (blockReversal a).injective
  rw [Equiv.apply_symm_apply, blockReversal_involutive a x]

theorem reversal_squared : Specs.D05.M10.TransposeSimilarity.reversal_squared := by
  intro K _ r a
  rw [reversalMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_some_iff, Matrix.one_apply,
    blockReversal_involutive a x]

theorem reversal_inverse : Specs.D05.M10.TransposeSimilarity.reversal_inverse := by
  intro K _ r a
  have h := reversal_squared (K := K) a
  exact ⟨⟨⟨reversalMatrix a, reversalMatrix a, h, h⟩, rfl⟩, Matrix.inv_eq_left_inv h⟩

lemma jordan_reversal_entries {K : Type*} [Field K] {r : ℕ}
    (a : Fin r → ℕ) (μ : Fin r → K) :
    (jordanMatrix a μ).submatrix (blockReversal a) (blockReversal a) =
      (jordanMatrix a μ).transpose := by
  ext ⟨i, u⟩ ⟨j, v⟩
  change (if i = j then
    if u.rev.val = v.rev.val then μ j else
      if u.rev.val + 1 = v.rev.val then 1 else 0
    else 0) =
    (if j = i then if v.val = u.val then μ i else
      if v.val + 1 = u.val then 1 else 0 else 0)
  by_cases hij : i = j
  · subst j
    have hd : (a i - (u.val + 1) = a i - (v.val + 1)) ↔ v.val = u.val := by
      have hu := u.isLt
      have hv := v.isLt
      omega
    have hs : (a i - (u.val + 1) + 1 = a i - (v.val + 1)) ↔
        v.val + 1 = u.val := by
      have hu := u.isLt
      have hv := v.isLt
      omega
    simp only [Fin.val_rev, ite_true, hd, hs]
  · simp [hij, Ne.symm hij]

theorem jordan_transpose : Specs.D05.M10.TransposeSimilarity.jordan_transpose := by
  intro K _ r a μ
  rw [(reversal_inverse (K := K) a).2]
  simp only [reversalMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, blockReversal_symm, Matrix.submatrix_submatrix]
  exact jordan_reversal_entries a μ

/-- Coordinate transfer of an involutory reversal. P and Q are rectangular
coordinate matrices between two finite index types. -/
lemma similar_transpose_of_reversal {K : Type*} [Field K] {n : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin n) (Fin n) K) (J F : Matrix ι ι K)
    (P : Matrix (Fin n) ι K) (Q : Matrix ι (Fin n) K)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hA : A = P * J * Q) (hF : F * F = 1)
    (hJF : F * J * F = J.transpose) :
    Specs.D05.M04.Similarity.similar_value A A.transpose := by
  have ht₁ : P.transpose * Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  have ht₂ : Q.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  let X := P * F * P.transpose
  let Y := Q.transpose * F * Q
  have hYX : Y * X = 1 := by
    calc
      Y * X = Q.transpose * F * (Q * P) * F * P.transpose := by
        simp only [X, Y, Matrix.mul_assoc]
      _ = Q.transpose * (F * F) * P.transpose := by
        rw [hQP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hF, Matrix.mul_one, ht₂]
  have hXY : X * Y = 1 := by
    calc
      X * Y = P * F * (P.transpose * Q.transpose) * F * Q := by
        simp only [X, Y, Matrix.mul_assoc]
      _ = P * (F * F) * Q := by
        rw [ht₁]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hF, Matrix.mul_one, hPQ]
  refine ⟨X, ⟨⟨X, Y, hXY, hYX⟩, rfl⟩, ?_⟩
  rw [Matrix.inv_eq_left_inv hYX, hA]
  calc
    (P * J * Q).transpose = Q.transpose * (F * J * F) * P.transpose := by
      rw [hJF]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Y * (P * J * Q) * X := by
      dsimp only [X, Y]
      calc
        Q.transpose * (F * J * F) * P.transpose =
            Q.transpose * F * (Q * P) * J * (Q * P) * F * P.transpose := by
          rw [hQP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]

theorem complex_transpose_similarity :
    Specs.D05.M10.TransposeSimilarity.complex_transpose_similarity := by
  intro n A
  let c := Pi.basisFun ℂ (Fin n)
  let T : Module.End ℂ (Fin n → ℂ) := Matrix.toLin c c A
  obtain ⟨r, a, μ, _ha, b, hJ, _hdim⟩ :=
    JordanExistence.jordan_form T (Foundations.Fta.splits T.charpoly)
  let P := LinearMap.toMatrix b c LinearMap.id
  let Q := LinearMap.toMatrix c b LinearMap.id
  have hPQ : P * Q = 1 := by
    rw [← LinearMap.toMatrix_comp c b c, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hQP : Q * P = 1 := by
    rw [← LinearMap.toMatrix_comp b c b, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hA : A = P * jordanMatrix a μ * Q := by
    rw [← hJ]
    simp only [P, Q, ← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.comp_id]
    exact (LinearMap.toMatrix_toLin c c A).symm
  apply similar_transpose_of_reversal A (jordanMatrix a μ) (reversalMatrix a) P Q
    hPQ hQP hA (reversal_squared a)
  simpa only [(reversal_inverse (K := ℂ) a).2] using jordan_transpose a μ

end D05.M10.TransposeSimilarity
