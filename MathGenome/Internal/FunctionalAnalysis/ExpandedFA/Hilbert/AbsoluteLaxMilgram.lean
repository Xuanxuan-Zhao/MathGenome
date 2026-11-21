import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.AbsoluteLaxMilgram
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.TwoSpaceForms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.ClosedRangeEquivalences

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.AbsoluteLaxMilgram
universe u v

section Helpers
variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Riesz representation in the conjugate-linear testing convention. -/
theorem antidual_representation (F : H →L⋆[𝕜] 𝕜) :
    ∃ f : H, ∀ v : H, F v = ⟪v, f⟫_𝕜 := by
  let g : H →L[𝕜] 𝕜 :=
    { toFun := fun v => conj (F v)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp
      cont := RCLike.continuous_conj.comp F.continuous }
  obtain ⟨f, hf, _, _⟩ := RieszRepresentation.functional_representation 𝕜 H g
  refine ⟨f, fun v => ?_⟩
  calc
    F v = conj (g v) := by simp [g]
    _ = conj ⟪f, v⟫_𝕜 := congrArg conj (hf v)
    _ = ⟪v, f⟫_𝕜 := inner_conj_symm v f

/-- The diagonal modulus bound makes the representing operator surjective.
Closedness follows from the lower bound; orthogonality to the range forces zero. -/
theorem representing_operator_surjective
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (A : H →L[𝕜] H)
    (hA : ∀ x y : H, a x y = ⟪x, A y⟫_𝕜)
    {b : ℝ} (hb : 0 < b) (ha : ∀ x : H, b * ‖x‖ ^ 2 ≤ ‖a x x‖) :
    Function.Surjective A := by
  have hlower (x : H) : b * ‖x‖ ≤ ‖A x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h : b * ‖x‖ ^ 2 ≤ ‖x‖ * ‖A x‖ := calc
      _ ≤ ‖a x x‖ := ha x
      _ = ‖⟪x, A x⟫_𝕜‖ := congrArg norm (hA x x)
      _ ≤ _ := norm_inner_le_norm x (A x)
    nlinarith
  have hclosed : IsClosed (A.range : Set H) :=
    ClosedRangeEquivalences.isClosed_range_of_kernelComplement_lower_bound A hb
      (fun x _ => hlower x)
  have hortho : A.range.orthogonal = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    have hi : ⟪A w, w⟫_𝕜 = 0 := (Submodule.mem_orthogonal _ _).mp hw (A w)
      (A.mem_range_self w)
    have hi' : a w w = 0 := by
      rw [hA]
      exact inner_eq_zero_symm.mp hi
    have hzero : ‖w‖ = 0 := by
      have h := ha w
      rw [hi', norm_zero] at h
      have hs : ‖w‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right h hb
      nlinarith [norm_nonneg w, sq_nonneg ‖w‖]
    exact norm_eq_zero.mp hzero
  have htop : A.range = ⊤ := by
    have h := A.range.topologicalClosure_eq_top_iff.mpr hortho
    rwa [hclosed.submodule_topologicalClosure_eq] at h
  exact LinearMap.range_eq_top.mp htop

end Helpers

/-- The source theorem, including the continuous scalar-linear solution map. -/
theorem absolute_lax_milgram : Spec.AbsoluteLaxMilgram.{u, v} := by
  intro 𝕜 H _ _ _ _ a b hb ha
  obtain ⟨T, _, hT, _, _⟩ := TwoSpaceForms.form_representation 𝕜 H H a
  let A : H →L[𝕜] H := T.adjoint
  have hA (x y : H) : a x y = ⟪x, A y⟫_𝕜 := hT x y
  have hsurj := representing_operator_surjective a A hA hb ha
  have hbound (x : H) : ‖x‖ ≤ (1 / b) * ‖a.flip x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h := (ha x).trans ((a.flip x).le_opNorm x)
    change b * ‖x‖ ^ 2 ≤ ‖a.flip x‖ * ‖x‖ at h
    have h' : b * ‖x‖ ≤ ‖a.flip x‖ := by nlinarith
    exact (le_div_iff₀ hb).mpr (by simpa [mul_comm] using h') |>.trans_eq
      (by ring)
  have hbij : Function.Bijective a.flip := by
    constructor
    · intro x y hxy
      apply sub_eq_zero.mp
      have hzero : a.flip (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h := hbound (x - y)
      rw [hzero, norm_zero, mul_zero] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    · intro F
      obtain ⟨f, hf⟩ := antidual_representation F
      obtain ⟨x, hx⟩ := hsurj f
      refine ⟨x, ?_⟩
      ext v
      change a v x = F v
      rw [hA, hx, hf]
  let e : H ≃ₗ[𝕜] (H →L⋆[𝕜] 𝕜) := LinearEquiv.ofBijective a.flip.toLinearMap hbij
  let S : (H →L⋆[𝕜] 𝕜) →L[𝕜] H := e.symm.toLinearMap.mkContinuous (1 / b)
    (fun F => by
      change ‖e.symm F‖ ≤ (1 / b) * ‖F‖
      have h := hbound (e.symm F)
      change ‖e.symm F‖ ≤ (1 / b) * ‖e (e.symm F)‖ at h
      simpa only [e.apply_symm_apply] using h)
  have hsolve (F : H →L⋆[𝕜] 𝕜) : a.flip (S F) = F := e.apply_symm_apply F
  refine ⟨S, S.opNorm_le_bound (by positivity) ?_, ?_⟩
  · intro F
    simpa only [hsolve] using hbound (S F)
  · intro F
    refine ⟨fun v => congrArg (fun g : H →L⋆[𝕜] 𝕜 => g v) (hsolve F), ?_, ?_⟩
    · have h := hbound (S F)
      rw [hsolve] at h
      convert h using 1; ring
    · intro x hx
      apply hbij.1
      rw [hsolve]
      ext v
      exact hx v

end ExpandedFA.Hilbert.AbsoluteLaxMilgram
