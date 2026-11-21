import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.LaxMilgramSolvability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.ClosedRangeEquivalences

/-!
The representing operator is bounded below by α, hence has closed range.
A vector orthogonal to that range has zero diagonal form value, so coercivity
forces it to vanish. Orthogonal decomposition then gives surjectivity.
Riesz representation of the antidual and the same lower bound give the solution
and its estimate. No division by the norm of a vector is used at zero.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.LaxMilgramSolvability
universe u v

section Helpers
variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Conjugating a continuous antidual produces a linear dual with the same norm;
ordinary Riesz representation then gives the antidual representation. -/
theorem antidual_representation (F : H →L⋆[𝕜] 𝕜) :
    ∃ f : H, (∀ x, F x = ⟪x, f⟫_𝕜) ∧ ‖F‖ = ‖f‖ := by
  let G : H →L[𝕜] 𝕜 :=
    { toFun := fun x => conj (F x)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp
      cont := RCLike.continuous_conj.comp F.continuous }
  have hnorm : ‖G‖ = ‖F‖ := by
    apply ContinuousLinearMap.opNorm_ext
    intro x
    exact RCLike.norm_conj (F x)
  obtain ⟨f, hf, hfnorm, _⟩ :=
    RieszRepresentation.functional_representation 𝕜 H G
  refine ⟨f, ?_, hnorm.symm.trans hfnorm⟩
  intro x
  have h := congrArg conj (hf x)
  change conj (conj (F x)) = conj ⟪f, x⟫_𝕜 at h
  simpa only [RCLike.conj_conj, inner_conj_symm] using h

omit [CompleteSpace H] in
/-- The coercive diagonal inequality implies a lower norm bound for the
representing operator, at every vector including zero. -/
theorem operator_lower_bound (A : H →L[𝕜] H) {α : ℝ}
    (hc : ∀ x : H, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_𝕜) :
    ∀ x : H, α * ‖x‖ ≤ ‖A x‖ := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h := (hc x).trans (re_inner_le_norm x (A x))
    nlinarith

/-- A coercive representing operator is bijective on the whole Hilbert space. -/
theorem operator_bijective (A : H →L[𝕜] H) {α : ℝ} (hα : 0 < α)
    (hc : ∀ x : H, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_𝕜) :
    Function.Bijective A := by
  have hb := operator_lower_bound A hc
  have hclosed : IsClosed (A.range : Set H) :=
    ClosedRangeEquivalences.isClosed_range_of_kernelComplement_lower_bound A hα
      (fun x _ => hb x)
  let : CompleteSpace A.range := hclosed.completeSpace_coe
  have hrange : A.range = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply le_antisymm
    · intro z hz
      have hz' : ⟪A z, z⟫_𝕜 = 0 := hz (A z) (A.mem_range_self z)
      have hz'' : ⟪z, A z⟫_𝕜 = 0 := by rw [← inner_conj_symm, hz', map_zero]
      have h := hc z
      rw [hz'', map_zero] at h
      have hn : ‖z‖ = 0 := by
        have hs : ‖z‖ ^ 2 ≤ 0 :=
          (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_zero] using h)
        exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
      exact norm_eq_zero.mp hn
    · exact bot_le
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hzero : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h := hb (x - y)
    rw [hzero, norm_zero] at h
    have hn : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact norm_eq_zero.mp hn
  · intro f
    have hf : f ∈ A.range := by rw [hrange]; trivial
    exact hf

end Helpers

theorem solvability : Spec.Solvability.{u, v} := by
  intro 𝕜 H _ _ _ _ a α ha F
  obtain ⟨A, hA, _, _⟩ := RieszRepresentation.form_representation 𝕜 H a
  have hc : ∀ x : H, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_𝕜 := by
    intro x
    rw [← hA]
    exact ha.2 x
  have hbij := operator_bijective A ha.1 hc
  obtain ⟨f, hf, hnorm⟩ := antidual_representation F
  obtain ⟨u, hu⟩ := hbij.2 f
  refine ⟨u, ?_, ?_, ?_⟩
  · intro v
    rw [hA, hu, hf]
  · apply (le_div_iff₀ ha.1).mpr
    have hb := operator_lower_bound A hc u
    rw [hu, ← hnorm] at hb
    simpa only [mul_comm] using hb
  · intro w hw
    apply hbij.1
    apply ext_inner_left 𝕜
    intro v
    rw [← hA, hw, hf, hu]

theorem real_solvability : Spec.RealSolvability.{v} := by
  intro H _ _ _ a α hα hc F
  exact solvability ℝ H a α ⟨hα, hc⟩ F

end ExpandedFA.Hilbert.LaxMilgramSolvability
