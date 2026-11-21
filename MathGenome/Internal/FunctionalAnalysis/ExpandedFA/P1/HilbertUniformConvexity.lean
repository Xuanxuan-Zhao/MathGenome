import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HilbertUniformConvexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The Hilbert clause of `fa2:p1:c14:uc-examples` (paper.tex:2894–2903).
The parallelogram identity bounds the squared midpoint norm by
`1 - ε ^ 2 / 4`. Its nonnegative square root gives the stated modulus.
The proof applies without completeness and includes the zero space.
-/

namespace ExpandedFA.P1.HilbertUniformConvexity

universe u v

/-- The exact Hilbert modulus, including the endpoint ε = 2. -/
theorem hilbert_uniform_convexity_modulus : Spec.ExplicitModulus.{u,v} := by
  intro 𝕜 H _ _ _ ε hε hε₂
  have hεsq : ε ^ 2 ≤ (2 : ℝ) ^ 2 :=
    (sq_le_sq₀ hε.le (by norm_num)).mpr hε₂
  have hrad : 0 ≤ 1 - ε ^ 2 / 4 := by nlinarith
  refine ⟨?_, ?_⟩
  · apply sub_pos.mpr
    apply (Real.sqrt_lt' zero_lt_one).mpr
    nlinarith [sq_pos_of_pos hε]
  · intro x y hx hy hsep
    rw [C14UniformConvexity.norm_midpoint_eq_half, sub_sub_cancel]
    apply (Real.le_sqrt (by positivity) hrad).mpr
    have hx₂ : ‖x‖ ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (norm_nonneg x) zero_le_one).mpr hx
    have hy₂ : ‖y‖ ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (norm_nonneg y) zero_le_one).mpr hy
    have hsep₂ : ε ^ 2 ≤ ‖x - y‖ ^ 2 :=
      (sq_le_sq₀ hε.le (norm_nonneg (x - y))).mpr hsep
    have hp := parallelogram_law_with_norm 𝕜 x y
    nlinarith

/-- Every real or complex Hilbert space satisfies the shared uniform-convexity
predicate, witnessed by exactly the modulus stated in the paper. -/
theorem hilbert_uniform_convexity : Spec.UniformConvexity.{u,v} := by
  intro 𝕜 H _ _ _ ε hε hε₂
  obtain ⟨hδ, hmid⟩ := hilbert_uniform_convexity_modulus 𝕜 H ε hε hε₂
  exact ⟨1 - Real.sqrt (1 - ε ^ 2 / 4), hδ, hmid⟩

end ExpandedFA.P1.HilbertUniformConvexity
