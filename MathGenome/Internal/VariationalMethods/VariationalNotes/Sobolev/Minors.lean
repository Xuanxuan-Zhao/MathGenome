import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Minors
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace
namespace VariationalNotes.Sobolev.Minors

namespace Definitions
abbrev index : Expected.IndexType := Index
abbrev determinant : Expected.MinorType := @minor
abbrev vector : Expected.MinorsType := @minors
abbrev firstRowCofactor : Expected.CofactorType := @cofactor
abbrev independentCoordinates : Expected.CoordinatesType := Coordinates
abbrev fullVector : Expected.AllMinorsType := @allMinors
abbrev polyconvexRepresentation : Expected.RepresentationType := @IsPolyconvexRepresentation
abbrev lift : Expected.LiftType := @convexLift
end Definitions

/-- Increasing one-element lists are exactly single entries. -/
def entryEquiv (m d : ℕ) : (Fin m × Fin d) ≃ Index m d 1 where
  toFun := entryIndex
  invFun a := (a.1.val 0, a.2.val 0)
  left_inv _ := rfl
  right_inv a := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [entryIndex, singletonSelection, Fin.eq_zero i]
    · apply Subtype.ext
      funext i
      simp [entryIndex, singletonSelection, Fin.eq_zero i]

/-- The first-order minor vector is simply Euclidean reindexing of the matrix. -/
def firstIsometry (m d : ℕ) : Gradient m d ≃ₗᵢ[ℝ] MinorVector m d 1 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (entryEquiv m d)

theorem firstIsometry_eq {m d : ℕ} (Z : Gradient m d) :
    firstIsometry m d Z = minors 1 Z := by
  apply PiLp.ext
  intro a
  change Z (a.1.val 0, a.2.val 0) = Matrix.det (submatrix a Z)
  rw [Matrix.det_fin_one]
  rfl

theorem first_identification : Expected.FirstIdentification := by
  intro m d
  refine ⟨firstIsometry m d, firstIsometry_eq, ?_⟩
  intro Z W
  rw [← firstIsometry_eq Z, ← firstIsometry_eq W]
  exact (firstIsometry m d).inner_map_map Z W

theorem first_entries : Expected.FirstEntries := by
  intro m d Z ik
  change Matrix.det (submatrix (entryIndex ik) Z) = Z ik
  rw [Matrix.det_fin_one]
  rfl

theorem first_norm : Expected.FirstNorm := by
  intro m d Z
  have hn : ‖minors 1 Z‖ = ‖Z‖ := by
    rw [← firstIsometry_eq]
    exact (firstIsometry m d).norm_map Z
  exact ⟨hn, hn.trans (gradient_norm_eq Z)⟩

theorem cofactor_one : Expected.CofactorOne := by
  intro m d a Z
  simp [cofactor, Matrix.det_fin_zero]

theorem first_row_expansion : Expected.FirstRowExpansion := by
  intro m d n a Z
  rw [minor, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro l _
  simp only [cofactor, submatrix]
  ring

theorem all_orders : Expected.AllOrders := by
  intro m d Z k a
  rfl

theorem matrix_recovery : Expected.MatrixRecovery := by
  intro m d hm hd Z
  apply PiLp.ext
  intro ik
  exact first_entries Z ik

theorem convex_implies_polyconvex : Expected.ConvexImpliesPolyconvex := by
  intro m d hm hd F hF
  constructor
  · intro x s Z
    change F x s Z = F x s (firstMatrix hm hd (allMinors Z))
    rw [matrix_recovery hm hd Z]
  · intro x s
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ a b ha hb hab
    have hproj : firstMatrix hm hd (a • z + b • w) =
        a • firstMatrix hm hd z + b • firstMatrix hm hd w := by
      apply PiLp.ext
      intro ik
      rfl
    change F x s (firstMatrix hm hd (a • z + b • w)) ≤ _
    rw [hproj]
    exact (hF x s).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

end VariationalNotes.Sobolev.Minors
