import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.OrthonormalExpansion

/-!
The matrix sum is defined for every bounded operator, before imposing either
compactness or finiteness. Parseval and the unconditional ENNReal double-sum
identity give basis independence, even when the value is infinite. Real norms
are taken only on the finite-square-sum subtype. No enumeration is used.
-/
noncomputable section
namespace ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions
universe u v w a b c
open scoped InnerProductSpace ENNReal

abbrev basisSquareSum : Spec.BasisSquareSumType.{u, v, w, a} :=
  Spec.BasisSquareSumValue
abbrev matrixSquareSum : Spec.MatrixSquareSumType.{u, v, w, a, b} :=
  Spec.MatrixSquareSumValue
abbrev hilbertSchmidtSquare : Spec.HilbertSchmidtSquareType.{u, v, w} :=
  Spec.HilbertSchmidtSquareValue
abbrev IsHilbertSchmidt : Spec.IsHilbertSchmidtType.{u, v, w} :=
  Spec.IsHilbertSchmidtValue
abbrev HilbertSchmidtMap : Spec.HilbertSchmidtMapType.{u, v, w} :=
  @Spec.HilbertSchmidtMapValue
abbrev hilbertSchmidtNorm : Spec.HilbertSchmidtNormType.{u, v, w} :=
  Spec.HilbertSchmidtNormValue
abbrev singularSquareSum : Spec.SingularSquareSumType.{u, v, w} :=
  Spec.SingularSquareSumValue

theorem finiteSum_supremum : Spec.FiniteSumSupremum.{u, v, w, a} := by
  intro 𝕜 _ H K _ _ _ _ ι T e
  exact ENNReal.tsum_eq_iSup_sum

/-- Parseval converted to an extended nonnegative sum. The real coefficient
series is summable for each vector, without a countable basis assumption. -/
lemma parseval_ennreal {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {ι : Type a}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H) (he : Spec.IsBasis (𝕜 := 𝕜) e) (x : H) :
    ENNReal.ofReal (‖x‖ ^ 2) = ∑' i, ENNReal.ofReal (‖inner 𝕜 (e i) x‖ ^ 2) := by
  obtain ⟨hs, hp⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.parseval 𝕜 H ι e he x
  rw [hp]
  exact ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable

theorem matrix_identity : Spec.MatrixIdentity.{u, v, w, a, b} := by
  intro 𝕜 _ H K _ _ _ _ _ _ ι κ T e f hf
  exact tsum_congr (fun i => parseval_ennreal f hf (T (e i)))

theorem adjoint_basis_identity : Spec.AdjointBasisIdentity.{u, v, w, a, b} := by
  intro 𝕜 _ H K _ _ _ _ _ _ ι κ T e f he hf
  calc
    basisSquareSum T e = matrixSquareSum T e f := matrix_identity T e f hf
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner 𝕜 (f j) (T (e i))‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = ∑' j, ∑' i,
        ENNReal.ofReal (‖inner 𝕜 (e i) (ContinuousLinearMap.adjoint T (f j))‖ ^ 2) := by
      apply tsum_congr
      intro j
      apply tsum_congr
      intro i
      rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ = basisSquareSum (ContinuousLinearMap.adjoint T) f :=
      (matrix_identity (ContinuousLinearMap.adjoint T) f e he).symm

theorem basis_independence : Spec.BasisIndependence.{u, v, w, a, b} := by
  intro 𝕜 _ H K _ _ _ _ _ _ ι ι' T e e' he he'
  obtain ⟨S, hS⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 K
  exact (adjoint_basis_identity T e (Subtype.val : S → K) he hS).trans
    (adjoint_basis_identity T e' (Subtype.val : S → K) he' hS).symm

theorem squareSum_in_basis : Spec.SquareSumInBasis.{u, v, w, a} := by
  intro 𝕜 _ H K _ _ _ _ _ _ ι T e he
  apply le_antisymm
  · apply iSup_le
    intro S
    apply iSup_le
    intro hS
    exact (basis_independence T (Subtype.val : S → H) e hS he).le
  · obtain ⟨S, hS⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
    rw [← basis_independence T (Subtype.val : S → H) e hS he]
    exact le_iSup_of_le S (le_iSup_of_le hS le_rfl)

theorem finiteness_in_basis : Spec.FinitenessInBasis.{u, v, w, a} := by
  intro 𝕜 _ H K _ _ _ _ _ _ ι T e he
  change Spec.HilbertSchmidtSquareValue T < ∞ ↔ _
  rw [squareSum_in_basis T e he]
  constructor
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hs
  · intro hs
    exact hs.tsum_ofReal_lt_top

theorem normSquare_in_basis : Spec.NormSquareInBasis.{u, v, w, a} := by
  intro 𝕜 _ H K _ _ _ _ _ _ ι T e he
  have hs := (finiteness_in_basis T.val e he).mp T.property
  change 0 ≤ Real.sqrt (Spec.HilbertSchmidtSquareValue T.val).toReal ∧
    Real.sqrt (Spec.HilbertSchmidtSquareValue T.val).toReal ^ 2 = _
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, squareSum_in_basis T.val e he]
  change (∑' i, ENNReal.ofReal (‖T.val (e i)‖ ^ 2)).toReal = _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs,
    ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _))]

theorem zero_square : Spec.ZeroSquare.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  have hz : hilbertSchmidtSquare (0 : H →L[𝕜] K) = 0 := by
    simp [hilbertSchmidtSquare, Spec.HilbertSchmidtSquareValue, Spec.BasisSquareSumValue]
  refine ⟨hz, ?_⟩
  change hilbertSchmidtSquare (0 : H →L[𝕜] K) < ∞
  rw [hz]
  exact ENNReal.zero_lt_top

end ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions
