import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PositiveQuadraticEstimates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Positive-form estimates for `paper.tex` 7432–7435.

The form b(y,x) = ⟪y,Dx⟫ is Hermitian and positive semidefinite.
We apply Mathlib's Cauchy–Schwarz theorem for a semidefinite core,
without installing any new norm, topology, or inner product on H.
Applying that inequality with y = Dx, bounding b(Dx,Dx), and
cancelling ‖Dx‖² when it is positive proves the norm estimate.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.PositiveQuadraticEstimates
universe u v

theorem positive_diagonal_real : Spec.DiagonalNonnegativeReal.{u, v} := by
  intro 𝕜 H _ _ _ _ D hD hpos x
  change D.adjoint = D at hD
  refine ⟨RCLike.conj_eq_iff_re.mp ?_, hpos x⟩
  rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hD]

theorem positive_quadratic_cauchy_schwarz : Spec.QuadraticCauchySchwarz.{u, v} := by
  intro 𝕜 H _ _ _ _ D hD hpos x y
  change D.adjoint = D at hD
  have hsym (z w : H) : ⟪D z, w⟫_𝕜 = ⟪z, D w⟫_𝕜 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hD]
  let c : PreInnerProductSpace.Core 𝕜 H :=
    { inner := fun z w => ⟪z, D w⟫_𝕜
      conj_inner_symm := fun z w => by rw [inner_conj_symm, hsym]
      re_inner_nonneg := hpos
      add_left := fun z w t => inner_add_left z w (D t)
      smul_left := fun z w r => inner_smul_left z (D w) r }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 H _ _ _ c y x
  change ‖⟪y, D x⟫_𝕜‖ * ‖⟪x, D y⟫_𝕜‖ ≤
    RCLike.re ⟪y, D y⟫_𝕜 * RCLike.re ⟪x, D x⟫_𝕜 at h
  have hs : ‖⟪x, D y⟫_𝕜‖ = ‖⟪y, D x⟫_𝕜‖ := by
    rw [← hsym, norm_inner_symm]
  simpa only [hs, pow_two] using h

/-- An arbitrary quadratic value is bounded using the native operator norm. -/
private theorem re_quadratic_le_opNorm_mul_sq {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (D : H →L[𝕜] H) (x : H) :
    RCLike.re ⟪x, D x⟫_𝕜 ≤ ‖D‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖⟪x, D x⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ ‖x‖ * ‖D x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖D‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (D.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

theorem positive_norm_quadratic_estimate : Spec.NormQuadraticEstimate.{u, v} := by
  intro 𝕜 H _ _ _ _ D hD hpos x
  by_cases hx : D x = 0
  · simp [hx]
  have hn : 0 < ‖D x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hcs := positive_quadratic_cauchy_schwarz 𝕜 H D hD hpos x (D x)
  have hmul : ‖D x‖ ^ 2 * ‖D x‖ ^ 2 ≤
      ‖D x‖ ^ 2 * (‖D‖ * RCLike.re ⟪x, D x⟫_𝕜) := by
    calc
      _ = ‖⟪D x, D x⟫_𝕜‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      _ ≤ _ := hcs
      _ ≤ (‖D‖ * ‖D x‖ ^ 2) * RCLike.re ⟪x, D x⟫_𝕜 :=
        mul_le_mul_of_nonneg_right (re_quadratic_le_opNorm_mul_sq D (D x)) (hpos x)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hn).mp (by nlinarith only [hmul])

end ExpandedFA.Hilbert.PositiveQuadraticEstimates
