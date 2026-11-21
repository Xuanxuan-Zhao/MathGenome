import MathGenome.Internal.Specs.D05.M11.Nondegenerate
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M04.RankBridge
import MathGenome.Internal.D05.M04.InverseMatrix
import MathGenome.Internal.D05.M11.Radicals

/-! Nondegeneracy and rank for arbitrary bilinear forms, K05.11.nondegenerate.
The transpose in the dual-map matrix is essential; no symmetry is assumed. -/
namespace D05.M11.Nondegenerate

open Module Matrix
open Specs.D05.M11.Nondegenerate
open Specs.D05.M11.Radicals Specs.D05.M11.FormMatrix

/-- Rank of the first-slot map into the algebraic dual. -/
noncomputable def rank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) : ℕ :=
  Specs.D05.M03.Image.rank_value K V (Module.Dual K V) B

/-- Both separation conditions, also meaningful on arbitrary spaces. -/
def nondegenerate {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : Prop := LinearMap.Nondegenerate B

theorem toDual_matrix : Specs.D05.M11.Nondegenerate.toDual_matrix := by
  intro K V _ _ _ n b B
  ext i j
  simp [LinearMap.toMatrix_apply, formMatrix_value]

theorem rank_eq_transpose_rank : Specs.D05.M11.Nondegenerate.rank_eq_transpose_rank := by
  intro K V _ _ _ _ n b B
  change Module.finrank K (LinearMap.range B) = _
  rw [← toDual_matrix b B]
  exact (D05.M04.RankBridge.matrixOfMap_rank b b.dualBasis B).symm

theorem rank_eq_matrix_rank : Specs.D05.M11.Nondegenerate.rank_eq_matrix_rank := by
  intro K V _ _ _ _ n b B
  rw [rank_eq_transpose_rank b B, D05.M04.RankBridge.rank_transpose]

theorem basis_independent_rank : Specs.D05.M11.Nondegenerate.basis_independent_rank := by
  intro K V _ _ _ n m b c B
  have := Module.Finite.of_basis b
  exact (rank_eq_matrix_rank b B).symm.trans (rank_eq_matrix_rank c B)

theorem rank_flip : Specs.D05.M11.Nondegenerate.rank_flip := by
  intro K V _ _ _ _ B
  let b := Module.finBasis K V
  rw [rank_eq_matrix_rank b B.flip, rank_eq_matrix_rank b B]
  change (formMatrix_value b B)ᵀ.rank = (formMatrix_value b B).rank
  exact D05.M04.RankBridge.rank_transpose _

theorem rank_nullity_left : Specs.D05.M11.Nondegenerate.rank_nullity_left := by
  intro K V _ _ _ _ B
  exact D05.M03.RankNullity.rank_nullity B

theorem rank_nullity_right : Specs.D05.M11.Nondegenerate.rank_nullity_right := by
  intro K V _ _ _ _ B
  have h := rank_nullity_left B.flip
  rw [rank_flip] at h
  exact h

theorem rank_eq_sub_left : Specs.D05.M11.Nondegenerate.rank_eq_sub_left := by
  intro K V _ _ _ _ B
  rw [rank_nullity_left B, Nat.add_sub_cancel_left]

theorem rank_eq_sub_right : Specs.D05.M11.Nondegenerate.rank_eq_sub_right := by
  intro K V _ _ _ _ B
  rw [rank_nullity_right B, Nat.add_sub_cancel_left]

theorem radical_dimensions : Specs.D05.M11.Nondegenerate.radical_dimensions := by
  intro K V _ _ _ _ B
  exact Nat.add_right_cancel ((rank_nullity_left B).symm.trans (rank_nullity_right B))

theorem rank_eq_dim_iff_left : Specs.D05.M11.Nondegenerate.rank_eq_dim_iff_left := by
  intro K V _ _ _ _ B
  rw [rank_nullity_left B, eq_comm, Nat.add_eq_right, Submodule.finrank_eq_zero]

theorem left_iff_right : Specs.D05.M11.Nondegenerate.left_iff_right := by
  intro K V _ _ _ _ B
  rw [← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, radical_dimensions B]

theorem matrix_full_rank_iff_ker_bot :
    Specs.D05.M11.Nondegenerate.matrix_full_rank_iff_ker_bot := by
  intro K _ n A
  have h : A.rank = n ↔ Function.Surjective A.mulVec := by
    simpa only [Fintype.card_fin] using
      (Matrix.mulVec_surjective_iff_rank_eq_card (M := A)).symm
  rw [h, LinearMap.ker_eq_bot]
  exact (LinearMap.injective_iff_surjective (f := A.mulVecLin)).symm

theorem matrix_ker_bot_iff_isUnit :
    Specs.D05.M11.Nondegenerate.matrix_ker_bot_iff_isUnit := by
  intro K _ n A
  rw [LinearMap.ker_eq_bot]
  exact Matrix.mulVec_injective_iff_isUnit

theorem matrix_isUnit_iff_inverse :
    Specs.D05.M11.Nondegenerate.matrix_isUnit_iff_inverse := by
  intro K _ n A
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, u.inv_val, u.val_inv⟩
  · rintro ⟨C, hCA, hAC⟩
    exact ⟨⟨A, C, hAC, hCA⟩, rfl⟩

theorem left_iff_matrix_isUnit : Specs.D05.M11.Nondegenerate.left_iff_matrix_isUnit := by
  intro K V _ _ _ n b B
  have := Module.Finite.of_basis b
  rw [← rank_eq_dim_iff_left B, rank_eq_matrix_rank b B,
    Module.finrank_eq_card_basis b, Fintype.card_fin,
    matrix_full_rank_iff_ker_bot, matrix_ker_bot_iff_isUnit]

theorem nondegenerate_iff_radicals :
    Specs.D05.M11.Nondegenerate.nondegenerate_iff_radicals := by
  intro K V _ _ _ B
  exact and_congr LinearMap.separatingLeft_iff_ker_eq_bot
    LinearMap.separatingRight_iff_flip_ker_eq_bot

theorem nondegenerate_iff_left : Specs.D05.M11.Nondegenerate.nondegenerate_iff_left := by
  intro K V _ _ _ _ B
  rw [nondegenerate_iff_radicals B, ← left_iff_right B, and_self]

theorem nondegenerate_iff_right : Specs.D05.M11.Nondegenerate.nondegenerate_iff_right := by
  intro K V _ _ _ _ B
  exact (nondegenerate_iff_left B).trans (left_iff_right B)

theorem nondegenerate_iff_rank : Specs.D05.M11.Nondegenerate.nondegenerate_iff_rank := by
  intro K V _ _ _ _ B
  exact (nondegenerate_iff_left B).trans (rank_eq_dim_iff_left B).symm

theorem nondegenerate_iff_matrix : Specs.D05.M11.Nondegenerate.nondegenerate_iff_matrix := by
  intro K V _ _ _ n b B
  have := Module.Finite.of_basis b
  exact (nondegenerate_iff_left B).trans (left_iff_matrix_isUnit b B)

theorem pairing_left_iff : Specs.D05.M11.Nondegenerate.pairing_left_iff := by
  intro K V W _ _ _ _ _ B
  exact LinearMap.separatingLeft_iff_ker_eq_bot

theorem pairing_right_iff : Specs.D05.M11.Nondegenerate.pairing_right_iff := by
  intro K V W _ _ _ _ _ B
  exact LinearMap.separatingRight_iff_flip_ker_eq_bot

theorem pairing_equal_dimensions : Specs.D05.M11.Nondegenerate.pairing_equal_dimensions := by
  intro K V W _ _ _ _ _ _ _ B hdim
  rw [pairing_left_iff B, pairing_right_iff B, LinearMap.ker_eq_bot, LinearMap.ker_eq_bot,
    LinearMap.flip_injective_iff₁]
  apply LinearMap.injective_iff_surjective_of_finrank_eq_finrank
  exact hdim.trans Subspace.dual_finrank_eq.symm

end D05.M11.Nondegenerate
