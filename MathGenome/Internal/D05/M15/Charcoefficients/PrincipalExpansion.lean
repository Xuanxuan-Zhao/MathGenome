import MathGenome.Internal.Specs.D05.M15.Charcoefficients.PrincipalExpansion
import MathGenome.Internal.D05.M05.DetDefinition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The principal-minor expansion uses multilinearity and identity rows.
No division, eigenvalues, or splitting assumptions enter the proof. -/

noncomputable section

namespace D05.M15.Charcoefficients.PrincipalExpansion

open scoped BigOperators

set_option backward.isDefEq.respectTransparency.types false in
/-- Expand a determinant by choosing a matrix row or an identity row in each slot. -/
theorem det_smul_one_add_smul {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (t u : R) :
    Matrix.det (t • (1 : Matrix ι ι R) + u • A) =
      ∑ I : Finset ι, u ^ I.card * t ^ (Fintype.card ι - I.card) *
        Matrix.det (A.submatrix (Subtype.val : I → ι) (Subtype.val : I → ι)) := by
  let D := (Matrix.detRowAlternating : AlternatingMap R (ι → R) R ι)
  rw [add_comm]
  change D ((fun i => (u • A) i) + (fun i => (t • (1 : Matrix ι ι R)) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro I _
  have hrows : I.piecewise (fun i => (u • A) i) (fun i => (t • (1 : Matrix ι ι R)) i) =
      fun i => (if i ∈ I then u else t) •
        I.piecewise (fun i => A i) (fun i => (1 : Matrix ι ι R) i) i := by
    funext i j
    by_cases hi : i ∈ I <;> simp [Finset.piecewise, hi]
  rw [hrows, D.map_smul_univ]
  have hprod : (∏ i : ι, if i ∈ I then u else t) =
      u ^ I.card * t ^ (Fintype.card ι - I.card) := by
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.prod_const, ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset
        (Finset.subset_univ I), Finset.card_univ]
  rw [hprod, smul_eq_mul]
  exact congrArg (fun x => (u ^ I.card * t ^ (Fintype.card ι - I.card)) * x)
    (Matrix.det_piecewise_one_eq_submatrix_det A I)

set_option backward.isDefEq.respectTransparency.types false in
theorem polynomial_expansion :
    D05.Specs.Charcoefficients.PrincipalExpansion.polynomial_expansion := by
  intro R _ n A
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  have h := det_smul_one_add_smul (A.map Polynomial.C) (Polynomial.X : Polynomial R) (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg, Fintype.card_fin] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  rw [Matrix.submatrix_map]
  exact (Polynomial.C.map_det _).symm

theorem scalar_expansion :
    D05.Specs.Charcoefficients.PrincipalExpansion.scalar_expansion := by
  intro R _ n A t
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  simpa only [neg_one_smul, sub_eq_add_neg, Fintype.card_fin] using
    det_smul_one_add_smul A t (-1)

theorem empty_minor : D05.Specs.Charcoefficients.PrincipalExpansion.empty_minor := by
  intro R _ n A
  exact Matrix.det_isEmpty

end D05.M15.Charcoefficients.PrincipalExpansion
