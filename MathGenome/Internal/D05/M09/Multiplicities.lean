import MathGenome.Internal.Specs.D05.M09.Multiplicities
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M09.Eigenspace
import Mathlib.LinearAlgebra.Projection

noncomputable section
namespace D05.M09.Multiplicities

open Module Polynomial

def algebraicMultiplicity : Specs.D05.M09.Multiplicities.algebraicMultiplicity_type :=
  Specs.D05.M09.Multiplicities.algebraicMultiplicity_value

def geometricMultiplicity : Specs.D05.M09.Multiplicities.geometricMultiplicity_type :=
  Specs.D05.M09.Multiplicities.geometricMultiplicity_value

theorem exponent_characterization : Specs.D05.M09.Multiplicities.exponent_characterization := by
  intro K V _ _ _ _ T μ k
  exact Polynomial.le_rootMultiplicity_iff (LinearMap.charpoly_monic T).ne_zero

/-- A scalar identity block has the expected characteristic polynomial,
including the empty block. -/
theorem charpoly_scalar_identity {K : Type*} [Field K] (r : ℕ) (μ : K) :
    Matrix.charpoly (μ • (1 : Matrix (Fin r) (Fin r) K)) = (X - C μ) ^ r := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

theorem basis_block_factorization : Specs.D05.M09.Multiplicities.basis_block_factorization := by
  intro K V _ _ _ _ T μ e
  classical
  let U := T.eigenspace μ
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  let c := Module.finBasis K W
  let b := (e.prod c).map (U.prodEquivOfIsCompl W hW)
  have hb (i) : b (Sum.inl i) = (e i : V) := by
    simp [b, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  let A := LinearMap.toMatrix b b T
  let B := A.submatrix Sum.inl Sum.inr
  let C₀ := A.submatrix Sum.inr Sum.inr
  have hcol (j) : T (b (Sum.inl j)) = μ • b (Sum.inl j) := by
    rw [hb]
    exact Module.End.mem_eigenspace_iff.mp (e j).property
  have hA : A = Matrix.fromBlocks (μ • 1) B 0 C₀ := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [A, LinearMap.toMatrix_apply, hcol, Module.Basis.repr_self,
          Matrix.one_apply, Finsupp.single_apply, eq_comm]
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        simp [A, LinearMap.toMatrix_apply, hcol, Module.Basis.repr_self]
      | inr j => rfl
  refine ⟨Module.finrank K W, b, B, C₀, hb, hA, ?_⟩
  change T.charpoly = _
  rw [← LinearMap.charpoly_toMatrix T b]
  change A.charpoly = _
  rw [hA, Matrix.charpoly_fromBlocks_zero₂₁, charpoly_scalar_identity,
    D05.M05.DetDefinition.matrix_det_bridge]
  rfl

theorem geometric_le_algebraic : Specs.D05.M09.Multiplicities.geometric_le_algebraic := by
  intro K V _ _ _ _ T μ
  apply (exponent_characterization T μ _).mpr
  obtain ⟨s, b, B, C₀, _, _, h⟩ := basis_block_factorization T μ
    (Module.finBasis K (T.eigenspace μ))
  exact ⟨_, h⟩

theorem geometric_pos_of_hasEigenvalue :
    Specs.D05.M09.Multiplicities.geometric_pos_of_hasEigenvalue := by
  intro K V _ _ _ _ T μ h
  have hU : T.eigenspace μ ≠ ⊥ := Module.End.hasEigenvalue_iff.mp h
  change 0 < Module.finrank K (T.eigenspace μ)
  have : Nontrivial (T.eigenspace μ) := Submodule.nontrivial_iff_ne_bot.mpr hU
  exact Module.finrank_pos

end D05.M09.Multiplicities
