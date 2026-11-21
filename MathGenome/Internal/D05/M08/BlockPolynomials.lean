import MathGenome.Internal.Specs.D05.M08.BlockPolynomials
import MathGenome.Internal.D05.M06.InvariantDecomposition
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M08.Minpoly
import Mathlib.Algebra.DirectSum.LinearMap

/-! Invariant direct sums, their characteristic polynomials and their minimal
polynomials (K05.08.block_polynomials). All scalar fields and empty cases are retained. -/
noncomputable section

namespace D05.M08.BlockPolynomials

open scoped BigOperators
open Specs.D05.M06.DirectSum (UniqueDecomposition)
open Specs.D05.M06.Invariant (invariant_value restriction_value)
open Specs.D05.M08.Minpoly (minimalPolynomial_value)
open Specs.D05.M08.Evaluation (evaluation_value)

theorem block_diagonal_matrix : Specs.D05.M08.BlockPolynomials.block_diagonal_matrix := by
  intro K V ι _ _ _ _ _ U hU T hT n b
  have h : _root_.DirectSum.IsInternal U :=
    (D05.M06.DirectSum.internal_iff_mathlib U).mp hU
  refine ⟨h.collectedBasis b, ?_, ?_⟩
  · intro i j
    exact congrFun (h.collectedBasis_coe b) ⟨i, j⟩
  · exact LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hT

/-- The determinant of a dependent block diagonal matrix is the product of the
block determinants. Fibres may be empty, so zero-dimensional blocks are included. -/
theorem det_blockDiagonal {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (A : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' A).det = ∏ i, (A i).det := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' A).det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e : κ i ≃ {x : Σ i, κ i // x.1 = i} :=
    { toFun := fun a => ⟨⟨i, a⟩, rfl⟩
      invFun := fun x => x.property ▸ x.val.2
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨j, a⟩, rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext a b
  exact Matrix.blockDiagonal'_apply_eq A i a b

/-- Applying xI minus a block diagonal matrix leaves the same block pattern. -/
theorem charpoly_blockDiagonal {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (A : ∀ i, Matrix (κ i) (κ i) K) :
    (Matrix.blockDiagonal' A).charpoly = ∏ i, (A i).charpoly := by
  classical
  have hc : (Matrix.blockDiagonal' A).charmatrix =
      Matrix.blockDiagonal' (fun i => (A i).charmatrix) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst j
      simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal'_apply]
    · have hsig : (Sigma.mk i a) ≠ ⟨j, b⟩ := fun he => h (congrArg Sigma.fst he)
      simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal,
        Matrix.blockDiagonal'_apply, h, hsig]
  change (Matrix.blockDiagonal' A).charmatrix.det = _
  rw [hc, det_blockDiagonal]
  rfl

theorem charpoly_product : Specs.D05.M08.BlockPolynomials.charpoly_product := by
  intro K V ι _ _ _ _ _ U hU T hT
  classical
  let n := fun i => Module.finrank K (U i)
  let b := fun i => Module.finBasis K (U i)
  obtain ⟨B, _, hB⟩ := block_diagonal_matrix U hU T hT n b
  change T.charpoly = ∏ i, (restriction_value K V (U i) T (hT i)).charpoly
  rw [← LinearMap.charpoly_toMatrix T B, hB, charpoly_blockDiagonal]
  simp only [LinearMap.charpoly_toMatrix]

theorem evaluation_on_summand : Specs.D05.M08.BlockPolynomials.evaluation_on_summand := by
  intro K V _ _ _ U T hT p u
  have hp (j : ℕ) (x : U) :
      ((restriction_value K V U T hT ^ j) x : V) = (T ^ j) (x : V) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply]
      exact congrArg T ih
  rw [Evaluation.eval_apply, Evaluation.eval_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, hp]

theorem evaluation_zero_iff : Specs.D05.M08.BlockPolynomials.evaluation_zero_iff := by
  intro K V ι _ _ _ _ U hU T hT p
  constructor
  · intro hp i
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (evaluation_value K (U i) (restriction_value K V (U i) T (hT i)) p u : V) = 0
    rw [evaluation_on_summand, hp]
    rfl
  · intro hp
    ext v
    obtain ⟨c, hc, _⟩ := hU v
    rw [← hc, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [← evaluation_on_summand (U i) T (hT i) p (c i), hp i]
    rfl

theorem annihilates_iff_all_divide :
    Specs.D05.M08.BlockPolynomials.annihilates_iff_all_divide := by
  intro K V ι _ _ _ _ _ U hU T hT p
  rw [evaluation_zero_iff U hU T hT p]
  apply forall_congr'
  intro i
  exact minpoly.dvd_iff.symm

theorem lcm_monic : Specs.D05.M08.BlockPolynomials.lcm_monic := by
  intro K V ι _ _ _ _ _ U T hT
  classical
  have hn : (Finset.univ.lcm fun i =>
      minimalPolynomial_value K (U i) (restriction_value K V (U i) T (hT i))) ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro i _
    exact Minpoly.ne_zero _
  rw [← Finset.normalize_lcm]
  exact Polynomial.monic_normalize hn

theorem annihilates_iff_lcm_divides :
    Specs.D05.M08.BlockPolynomials.annihilates_iff_lcm_divides := by
  intro K V ι _ _ _ _ _ U hU T hT p
  classical
  rw [annihilates_iff_all_divide U hU T hT p, Finset.lcm_dvd_iff]
  simp

theorem minpoly_lcm : Specs.D05.M08.BlockPolynomials.minpoly_lcm := by
  intro K V ι _ _ _ _ _ U hU T hT
  classical
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (Minpoly.monic T) (lcm_monic U T hT)
  · apply minpoly.dvd_iff.mpr
    exact (annihilates_iff_lcm_divides U hU T hT _).mpr dvd_rfl
  · apply Polynomial.natDegree_le_of_dvd
    · exact (annihilates_iff_lcm_divides U hU T hT _).mp (Minpoly.annihilates T)
    · exact Minpoly.ne_zero T

theorem empty_decomposition : Specs.D05.M08.BlockPolynomials.empty_decomposition := by
  intro K V ι _ _ _ _ _ _ U hU T hT
  rw [charpoly_product U hU T hT, minpoly_lcm U hU T hT]
  simp

end D05.M08.BlockPolynomials
