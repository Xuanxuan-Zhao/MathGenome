import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UcExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HilbertUniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LpUniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces

/-! Hilbert and Lᵖ uniform convexity and the two endpoint counterexamples,
`fa2:p1:c14:uc-examples`, paper.tex:2894–2942. -/
noncomputable section
open scoped ENNReal

namespace ExpandedFA.P1.C14UcExamples
universe u v

theorem hilbert_modulus : Spec.HilbertModulus.{u,v} :=
  HilbertUniformConvexity.hilbert_uniform_convexity_modulus

theorem hilbert_uniformly_convex : Spec.HilbertUniformConvexity.{u,v} :=
  HilbertUniformConvexity.hilbert_uniform_convexity

theorem lp_uniformly_convex : Spec.LpUniformConvexity.{u,v} :=
  LpUniformConvexity.measure_lp_uniformly_convex

/-- An exactly flat separated pair in the closed unit ball obstructs uniform
convexity. This applies directly to the manuscript definition. -/
lemma not_uniformlyConvex_of_flat_pair (𝕜 : Type u) (E : Type v)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hsep : 2 ≤ ‖x - y‖) (hmid : 1 ≤ ‖(2 : 𝕜)⁻¹ • (x + y)‖) :
    ¬ C14UniformConvexity.UniformlyConvex 𝕜 E := by
  intro h
  obtain ⟨δ, hδ, hδxy⟩ := h 2 (by norm_num) le_rfl
  have := hδxy x y hx hy hsep
  linarith

/-- The ℓ¹ norm of a vector supported in the first two coordinates. -/
lemma l1_norm_two_coordinates (𝕜 : Type u) [RCLike 𝕜] (a b : 𝕜) :
    ‖lp.single (E := fun _ : ℕ => 𝕜) 1 0 a + lp.single 1 1 b‖ = ‖a‖ + ‖b‖ := by
  have h := lp.norm_sum_single (E := fun _ : ℕ => 𝕜) (p := 1)
    (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    (fun n : ℕ => if n = 0 then a else b) ({0, 1} : Finset ℕ)
  simpa using h

/-- e₁ and e₂ have distance two but their midpoint still has norm one. -/
theorem l1_not_uniformly_convex : Spec.L1NotUniformlyConvex.{u} := by
  intro 𝕜 _
  let x : C01SequenceSpaces.SequenceLp 𝕜 1 := lp.single 1 0 1
  let y : C01SequenceSpaces.SequenceLp 𝕜 1 := lp.single 1 1 1
  have hx : ‖x‖ = 1 := by simp [x]
  have hy : ‖y‖ = 1 := by simp [y]
  have hsum : ‖x + y‖ = 2 := by
    simpa [x, y, one_add_one_eq_two] using l1_norm_two_coordinates 𝕜 1 1
  have hsub : ‖x - y‖ = 2 := by
    simpa [x, y, sub_eq_add_neg, ← lp.single_neg, one_add_one_eq_two] using l1_norm_two_coordinates 𝕜 1 (-1)
  apply not_uniformlyConvex_of_flat_pair 𝕜 _ x y hx.le hy.le hsub.ge
  rw [C14UniformConvexity.norm_midpoint_eq_half, hsum]
  norm_num

/-- The supremum norm of a vector supported in the first two coordinates. -/
lemma linfty_norm_two_coordinates (𝕜 : Type u) [RCLike 𝕜] (a b : 𝕜) :
    ‖lp.single (E := fun _ : ℕ => 𝕜) ∞ 0 a + lp.single ∞ 1 b‖ = max ‖a‖ ‖b‖ := by
  let z : C01SequenceSpaces.SequenceLInfinity 𝕜 :=
    lp.single ∞ 0 a + lp.single ∞ 1 b
  change ‖z‖ = max ‖a‖ ‖b‖
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (le_trans (norm_nonneg a) (le_max_left _ _))
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [z]
    · by_cases hn1 : n = 1
      · subst n
        simp [z]
      · simp [z, hn0, hn1]
  · apply max_le
    · simpa [z] using lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) z 0
    · simpa [z] using lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) z 1

/-- (1,1,0,…) and (1,−1,0,…) have distance two and midpoint e₁. -/
theorem linfty_not_uniformly_convex : Spec.LInfinityNotUniformlyConvex.{u} := by
  intro 𝕜 _
  let e : C01SequenceSpaces.SequenceLInfinity 𝕜 := lp.single ∞ 0 1
  let f : C01SequenceSpaces.SequenceLInfinity 𝕜 := lp.single ∞ 1 1
  let x := e + f
  let y := e - f
  have hx : ‖x‖ = 1 := by
    simpa [x, e, f] using linfty_norm_two_coordinates 𝕜 1 1
  have hy : ‖y‖ = 1 := by
    simpa [y, e, f, sub_eq_add_neg, ← lp.single_neg] using
      linfty_norm_two_coordinates 𝕜 1 (-1)
  have hsum : x + y = (2 : 𝕜) • e := by
    dsimp [x, y]
    rw [two_smul]
    abel
  have hsub : x - y = (2 : 𝕜) • f := by
    dsimp [x, y]
    rw [two_smul]
    abel
  have hsep : 2 ≤ ‖x - y‖ := by
    rw [hsub, norm_smul]
    norm_num [f]
  apply not_uniformlyConvex_of_flat_pair 𝕜 _ x y hx.le hy.le hsep
  rw [hsum, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : 𝕜) ≠ 0), one_smul]
  simp [e]

end ExpandedFA.P1.C14UcExamples
