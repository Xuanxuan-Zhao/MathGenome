import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer

/-! The signed centralizer in the complex symplectic Lie algebra (LA-J07). -/

namespace LieAlgebrasAndRepresentations.SymplecticSignedCentralizer

open Matrix
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
open Specs.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

private abbrev Indices (n : ℕ) := Fin n ⊕ Fin n

private def cut {n p : ℕ} (hp : p ≤ n) : Fin p ⊕ Fin (n - p) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hp))

private def groupedIndices {n p : ℕ} (hp : p ≤ n) :
    Indices p ⊕ Indices (n - p) ≃ Indices n :=
  (Equiv.sumSumSumComm _ _ _ _).trans ((cut hp).sumCongr (cut hp))

private abbrev regroup {n p : ℕ} (hp : p ≤ n) :
    Mat n ≃ₐ[ℂ] Matrix (Indices p ⊕ Indices (n - p)) (Indices p ⊕ Indices (n - p)) ℂ :=
  reindexAlgEquiv ℂ ℂ (groupedIndices hp).symm

private abbrev join {a b : Type*} (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    Matrix (a ⊕ b) (a ⊕ b) ℂ :=
  fromBlocks A 0 0 B

private theorem join_mul {a b : Type*} [Fintype a] [Fintype b]
    (A C : Matrix a a ℂ) (B D : Matrix b b ℂ) :
    join A B * join C D = join (A * C) (B * D) := by
  simp [fromBlocks_multiply]

private theorem regroup_J {n p : ℕ} (hp : p ≤ n) :
    regroup hp (J (Fin n) ℂ) = join (J (Fin p) ℂ) (J (Fin (n - p)) ℂ) := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [coe_reindexAlgEquiv, reindex_apply, submatrix_apply, groupedIndices,
      J, Matrix.one_apply]

private theorem regroup_signature {n p : ℕ} (hp : p ≤ n) :
    regroup hp (signatureMatrix n p) =
      join (1 : Mat p) (-1 : Mat (n - p)) := by
  change regroup hp (signatureMatrix n p) = fromBlocks (1 : Mat p) 0 0 (-1 : Mat (n - p))
  have hneg : (-1 : Mat (n - p)) = Matrix.diagonal (fun _ => (-1 : ℂ)) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_neg]
  rw [hneg, ← Matrix.diagonal_one]
  simp only [signatureMatrix, signatureDiagonal, fromBlocks_diagonal,
    coe_reindexAlgEquiv, reindex_apply, Equiv.symm_symm, submatrix_diagonal_equiv]
  congr 1
  funext i
  rcases i with ((i | i) | (i | i)) <;> simp [groupedIndices, cut]

private theorem regroup_transpose {n p : ℕ} (hp : p ≤ n) (X : Mat n) :
    regroup hp Xᵀ = (regroup hp X)ᵀ := rfl

private theorem sp_iff {n : ℕ} (X : Mat n) :
    X ∈ sp n ↔ Xᵀ * J (Fin n) ℂ = -(J (Fin n) ℂ * X) := by
  simp only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]

private theorem regroup_commute_iff {n p : ℕ} (hp : p ≤ n) (X : Mat n) :
    Commute (signatureMatrix n p) X ↔
      Commute (join (1 : Mat p) (-1 : Mat (n - p))) (regroup hp X) := by
  change signatureMatrix n p * X = X * signatureMatrix n p ↔ _
  rw [← (regroup hp).injective.eq_iff]
  simp only [map_mul, regroup_signature]
  rfl

private theorem regroup_mem_iff {n p : ℕ} (hp : p ≤ n) (X : Mat n)
    (A : Mat p) (B : Mat (n - p)) (h : regroup hp X = join A B) :
    X ∈ sp n ↔ A ∈ sp p ∧ B ∈ sp (n - p) := by
  rw [sp_iff, sp_iff, sp_iff, ← (regroup hp).injective.eq_iff]
  simp only [map_mul, map_neg, regroup_transpose, regroup_J, h,
    fromBlocks_transpose, Matrix.transpose_zero, join_mul, fromBlocks_neg, neg_zero,
    fromBlocks_inj, true_and]

private theorem commute_join {p q : ℕ} (A : Mat p) (B : Mat q) :
    Commute (join (1 : Mat p) (-1 : Mat q)) (join A B) := by
  change join (1 : Mat p) (-1 : Mat q) * join A B =
    join A B * join (1 : Mat p) (-1 : Mat q)
  simp [join_mul]

private theorem eq_join_of_commute {p q : ℕ}
    (X : Matrix (Indices p ⊕ Indices q) (Indices p ⊕ Indices q) ℂ)
    (h : Commute (join (1 : Mat p) (-1 : Mat q)) X) :
    X = join X.toBlocks₁₁ X.toBlocks₂₂ := by
  change join (1 : Mat p) (-1 : Mat q) * X = X * join (1 : Mat p) (-1 : Mat q) at h
  conv at h => rw [← X.fromBlocks_toBlocks]
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, fromBlocks_inj] at h
  have h₁₂ : X.toBlocks₁₂ = 0 := by
    ext i j
    exact CharZero.neg_eq_self_iff.mp (congr($(h.2.1.symm) i j))
  have h₂₁ : X.toBlocks₂₁ = 0 := by
    ext i j
    exact CharZero.neg_eq_self_iff.mp (congr($(h.2.2.1) i j))
  calc
    X = fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ :=
      X.fromBlocks_toBlocks.symm
    _ = join X.toBlocks₁₁ X.toBlocks₂₂ := by rw [h₁₂, h₂₁]

/-- Restricting to the two sign eigenspaces identifies the full complex
centralizer with the product of the two symplectic Lie algebras. -/
theorem signedCentralizerEquiv : signedCentralizerEquivType := by
  intro n p hp
  let e := regroup hp
  let f : (sp p × sp (n - p)) →ₗ⁅ℂ⁆ signedCentralizer n p :=
    { toFun := fun z =>
        let M := join (z.1 : Mat p) (z.2 : Mat (n - p))
        have hM : e (e.symm M) = M := e.apply_symm_apply M
        have hcomm : Commute (join (1 : Mat p) (-1 : Mat (n - p))) (e (e.symm M)) := by
          rw [hM]
          exact commute_join (z.1 : Mat p) (z.2 : Mat (n - p))
        ⟨⟨e.symm M, (regroup_mem_iff hp _ _ _ hM).2 ⟨z.1.property, z.2.property⟩⟩,
          (regroup_commute_iff hp (e.symm M)).2 hcomm⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        change e.symm (join ((x.1 : Mat p) + y.1) ((x.2 : Mat (n - p)) + y.2)) =
          e.symm (join x.1 x.2) + e.symm (join y.1 y.2)
        rw [← map_add]
        simp [fromBlocks_add]
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Subtype.ext
        change e.symm (join (c • (x.1 : Mat p)) (c • (x.2 : Mat (n - p)))) =
          c • e.symm (join x.1 x.2)
        rw [← map_smul]
        simp [fromBlocks_smul]
      map_lie' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        change e.symm (join ⁅(x.1 : Mat p), (y.1 : Mat p)⁆
          ⁅(x.2 : Mat (n - p)), (y.2 : Mat (n - p))⁆) =
            ⁅e.symm (join x.1 x.2), e.symm (join y.1 y.2)⁆
        simp only [Ring.lie_def, ← map_mul, ← map_sub, join_mul]
        congr 1
        simp [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add] }
  refine ⟨(LieEquiv.ofBijective f ⟨?_, ?_⟩).symm⟩
  · intro x y h
    have hm : join (x.1 : Mat p) (x.2 : Mat (n - p)) = join y.1 y.2 :=
      e.symm.injective (congrArg (fun z : signedCentralizer n p => (z.val : Mat n)) h)
    have hxy := fromBlocks_inj.mp hm
    exact Prod.ext (Subtype.ext hxy.1) (Subtype.ext hxy.2.2.2)
  · intro X
    let M := e (X.val : Mat n)
    have hM : M = join M.toBlocks₁₁ M.toBlocks₂₂ :=
      eq_join_of_commute M ((regroup_commute_iff hp _).1 X.property)
    have hm := (regroup_mem_iff hp (X.val : Mat n) _ _ hM).1 X.val.property
    refine ⟨(⟨M.toBlocks₁₁, hm.1⟩, ⟨M.toBlocks₂₂, hm.2⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change e.symm (join M.toBlocks₁₁ M.toBlocks₂₂) = (X.val : Mat n)
    rw [← hM]
    exact e.symm_apply_apply _

end
end LieAlgebrasAndRepresentations.SymplecticSignedCentralizer
