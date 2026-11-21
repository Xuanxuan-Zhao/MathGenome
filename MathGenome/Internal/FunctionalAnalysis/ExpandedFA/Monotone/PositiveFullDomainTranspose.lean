import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.PositiveFullDomainTranspose
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.PositiveGraphQuadratic
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
namespace ExpandedFA.Monotone

/-- The already established graph-domain clause, with its original hypotheses. -/
theorem positive_graph_estimate : PositiveFullDomainSpec.GraphEstimate :=
  positive_graph_quadratic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The dual norm estimate and its sharp quadratic lower bound are equivalent.
The reverse implication uses scalar tests and the operator norm, without
assuming that a functional attains its norm. -/
lemma full_domain_norm_iff_lower_bound
    (B : X →L[ℝ] (X →L[ℝ] ℝ)) (hpositive : ∀ y, 0 ≤ B y y)
    (α : ℝ) (hα : 0 < α) :
    (∀ y, ‖B y‖ ^ 2 ≤ α * B y y) ↔
      ∀ x y, -α * ‖x‖ ^ 2 / 4 ≤ B y y - B y x := by
  constructor
  · intro h x y
    have hb : (B y x) ^ 2 ≤ (α * ‖x‖ ^ 2) * B y y := by
      have hn := (B y).le_opNorm x
      have hs := (sq_le_sq₀ (norm_nonneg (B y x))
        (mul_nonneg (norm_nonneg (B y)) (norm_nonneg x))).mpr hn
      rw [Real.norm_eq_abs, sq_abs, mul_pow] at hs
      have hm := mul_le_mul_of_nonneg_right (h y) (sq_nonneg ‖x‖)
      nlinarith
    have hlow := quadratic_lower_bound_of_square_le
      (mul_nonneg hα.le (sq_nonneg ‖x‖)) (hpositive y) hb
    nlinarith
  · intro h y
    have hscalar (x : X) : (B y x) ^ 2 ≤ α * ‖x‖ ^ 2 * B y y := by
      have ht (t : ℝ) : -(B y y) ≤
          t ^ 2 * (α * ‖x‖ ^ 2 / 4) - t * B y x := by
        have hh := h (t • x) y
        simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs] at hh
        nlinarith
      have hd := square_le_of_quadratic_lower_bound ht
      nlinarith
    have hn : ‖B y‖ ≤ Real.sqrt (α * B y y) := by
      apply (B y).opNorm_le_bound (Real.sqrt_nonneg _)
      intro x
      apply (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
      rw [Real.norm_eq_abs, sq_abs, mul_pow,
        Real.sq_sqrt (mul_nonneg hα.le (hpositive y))]
      nlinarith [hscalar x]
    have hsq := Real.sq_sqrt (mul_nonneg hα.le (hpositive y))
    nlinarith [norm_nonneg (B y), Real.sqrt_nonneg (α * B y y)]

/-- The substitution y ↦ x-y exchanges the two slots of a real bilinear
form in the lower-bound condition. This is valid for nonsymmetric forms. -/
lemma full_domain_lower_bound_flip
    (B : X →L[ℝ] (X →L[ℝ] ℝ)) (α : ℝ) :
    (∀ x y, -α * ‖x‖ ^ 2 / 4 ≤ B y y - B y x) ↔
      ∀ x y, -α * ‖x‖ ^ 2 / 4 ≤ B.flip y y - B.flip y x := by
  have forward (C : X →L[ℝ] (X →L[ℝ] ℝ))
      (h : ∀ x y, -α * ‖x‖ ^ 2 / 4 ≤ C y y - C y x) :
      ∀ x y, -α * ‖x‖ ^ 2 / 4 ≤ C.flip y y - C.flip y x := by
    intro x y
    have ht := h x (x - y)
    simp only [ContinuousLinearMap.flip_apply]
    have hid : C (x - y) (x - y) - C (x - y) x = C y y - C x y := by
      simp only [map_sub, sub_apply]
      ring
    rwa [hid] at ht
  exact ⟨forward B, fun h => by simpa using forward B.flip h⟩

/-- A closed, everywhere-defined positive real operator has the two sharp
quadratic equivalences, including its canonical transpose with the same α. -/
theorem positive_full_domain_estimates : PositiveFullDomainSpec.FullDomainEstimates := by
  intro X _ _ _ A hclosed hpositive
  have hcontinuous : Continuous A := A.continuous_of_isClosed_graph hclosed
  let B : X →L[ℝ] (X →L[ℝ] ℝ) := ⟨A, hcontinuous⟩
  refine ⟨B, rfl, ?_, ?_⟩
  · intro x y
    rfl
  · intro α hα
    have hp : ∀ y, 0 ≤ B y y := hpositive
    have hpf : ∀ y, 0 ≤ B.flip y y := hpositive
    exact ⟨full_domain_norm_iff_lower_bound B hp α hα,
      (full_domain_norm_iff_lower_bound B hp α hα).trans
        ((full_domain_lower_bound_flip B α).trans
          (full_domain_norm_iff_lower_bound B.flip hpf α hα).symm)⟩

end ExpandedFA.Monotone
