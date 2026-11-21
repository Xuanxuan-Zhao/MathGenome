import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.IsometryBoundaries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
The sine graph preserves distance since sine is 1-Lipschitz and the first
coordinate already realizes the distance in the sup norm. Its values at
0, π/2, π violate preservation of affine combinations. Conjugation is the
standard real linear isometry; its values at 1 and i exclude complex linearity.
-/

namespace ExpandedFA.Supplements.IsometryBoundaries

open IsometryBoundariesSpec

theorem plane_norm_is_sup : SupNormConclusion := by
  intro p
  simp only [Prod.norm_def, Real.norm_eq_abs]

theorem sineGraph_isometry : SineGraphIsometryConclusion := by
  apply Isometry.of_dist_eq
  intro x y
  change max (dist x y) (dist (Real.sin x) (Real.sin y)) = dist x y
  apply max_eq_left
  simpa only [Real.dist_eq] using Real.abs_sin_sub_sin_le x y

theorem sineGraph_not_affine : SineGraphNotAffineConclusion := by
  rintro ⟨A, hA⟩
  have h := A.apply_lineMap 0 Real.pi (1 / 2 : ℝ)
  have hs := congrArg Prod.snd h
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
    sub_zero, add_zero, one_div, inv_mul_eq_div] at hs
  rw [hA, hA, hA] at hs
  norm_num [sineGraph, Real.sin_pi, Real.sin_pi_div_two, Real.sin_zero] at hs

theorem sineGraph_not_surjective : SineGraphNotSurjectiveConclusion := by
  intro h
  obtain ⟨t, ht⟩ := h (0, 1)
  have ht0 : t = 0 := congrArg Prod.fst ht
  have ht1 := congrArg Prod.snd ht
  simp [sineGraph, ht0] at ht1

theorem conjugation_real_linear_surjective_isometry : ConjugationRealConclusion := by
  refine ⟨Complex.isometry_conj, Complex.conjLIE.surjective, ?_⟩
  exact ⟨Complex.conjLIE.toLinearEquiv.toLinearMap, fun _ => rfl⟩

theorem conjugation_not_complex_linear : ConjugationNotComplexLinearConclusion := by
  rintro ⟨L, hL⟩
  have h := L.map_smul Complex.I (1 : ℂ)
  rw [hL, hL] at h
  have hi := congrArg Complex.im h
  norm_num at hi

end ExpandedFA.Supplements.IsometryBoundaries
