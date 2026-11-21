import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ReducedMinimumModulus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.ClosedRangeEquivalences
import Mathlib.Analysis.Normed.Module.RCLike.Basic

noncomputable section
open scoped ENNReal NNReal
universe u v w
namespace ExpandedFA.Hilbert.ReducedMinimumModulus
open scoped InnerProductSpace

/-- Infimum over the unit sphere of the kernel complement, in [0,∞]. -/
def reducedMinimumModulus : Spec.ReducedMinimumModulusType.{u,v,w} :=
  Spec.ReducedMinimumModulusValue

section Helpers
variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]

/-- Normalization turns bounds on the unit sphere into homogeneous bounds. -/
theorem le_modulus_iff (T : H →L[𝕜] K) (c : ℝ≥0) :
    (c : ℝ≥0∞) ≤ reducedMinimumModulus 𝕜 H K T ↔
      ∀ x : H, x ∈ T.ker.orthogonal → (c : ℝ) * ‖x‖ ≤ ‖T x‖ := by
  change (c : ℝ≥0∞) ≤ (⨅ (x : H) (_ : x ∈ T.ker.orthogonal)
    (_ : ‖x‖ = 1), (‖T x‖₊ : ℝ≥0∞)) ↔ _
  simp only [le_iInf_iff, ENNReal.coe_le_coe]
  constructor
  · intro h x hx
    by_cases hzero : x = 0
    · simp [hzero]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hzero
    have hb := h ((‖x‖⁻¹ : 𝕜) • x)
      (T.ker.orthogonal.smul_mem _ hx) (norm_smul_inv_norm hzero)
    have hb' : (c : ℝ) ≤ ‖T ((‖x‖⁻¹ : 𝕜) • x)‖ := hb
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hn.le] at hb'
    rw [← div_eq_inv_mul] at hb'
    exact (le_div_iff₀ hn).mp hb'
  · intro h x hx hn
    change (c : ℝ) ≤ ‖T x‖
    simpa only [hn, mul_one] using h x hx

variable [CompleteSpace H] [CompleteSpace K]

/-- A positive lower bound transfers to the adjoint with the same constant. -/
theorem adjoint_lower_bound (T : H →L[𝕜] K) {c : ℝ} (hc : 0 < c)
    (hb : ∀ x : H, x ∈ T.ker.orthogonal → c * ‖x‖ ≤ ‖T x‖) :
    ∀ y : K, y ∈ T.adjoint.ker.orthogonal → c * ‖y‖ ≤ ‖T.adjoint y‖ := by
  have hclosed := ClosedRangeEquivalences.isClosed_range_of_kernelComplement_lower_bound T hc hb
  have hrange := (ClosedRangeEquivalences.closed_range_kernel_range_identities 𝕜 H K T hclosed).1
  intro y hy
  have hym : y ∈ T.range := by rw [hrange]; exact hy
  obtain ⟨x, hx⟩ := (ClosedRangeEquivalences.kernelComplementMap_bijective T).2 ⟨y, hym⟩
  have hTx : T (x : H) = y := congrArg Subtype.val hx
  have h1 := hb x x.property
  rw [hTx] at h1
  have h2 : ‖y‖ * ‖y‖ ≤ ‖(x : H)‖ * ‖T.adjoint y‖ := by
    calc
      ‖y‖ * ‖y‖ = ‖⟪y, y⟫_𝕜‖ := by
        rw [← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm]
      _ = ‖⟪(x : H), T.adjoint y⟫_𝕜‖ := by rw [T.adjoint_inner_right, hTx]
      _ ≤ ‖(x : H)‖ * ‖T.adjoint y‖ := norm_inner_le_norm _ _
  by_cases hy0 : y = 0
  · simp [hy0]
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (T.adjoint y))
  have h4 := mul_le_mul_of_nonneg_left h2 hc.le
  nlinarith

/-- Comparison uses all finite nonnegative lower bounds, including when
one or both infima are infinite. -/
theorem modulus_le_adjoint (T : H →L[𝕜] K) :
    reducedMinimumModulus 𝕜 H K T ≤ reducedMinimumModulus 𝕜 K H T.adjoint := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro c hc
  apply (le_modulus_iff T.adjoint c).mpr
  by_cases hc0 : c = 0
  · simp [hc0]
  · exact adjoint_lower_bound T (by exact_mod_cast (pos_iff_ne_zero.mpr hc0))
      ((le_modulus_iff T c).mp hc.le)
end Helpers

theorem adjoint_equality : Spec.AdjointEquality.{u,v,w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  apply le_antisymm (modulus_le_adjoint T)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using modulus_le_adjoint T.adjoint

theorem zero_modulus : Spec.ZeroModulus.{u,v,w} := by
  intro 𝕜 H K _ _ _ _ _
  change (⨅ (x : H) (_ : x ∈ (0 : H →L[𝕜] K).ker.orthogonal)
    (_ : ‖x‖ = 1), (‖(0 : H →L[𝕜] K) x‖₊ : ℝ≥0∞)) = ⊤
  apply top_unique
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun hn => ?_
  have hx0 : x = 0 := by simpa using hx
  simp [hx0] at hn

theorem closed_range_iff_lower_bound : Spec.ClosedRangeIffLowerBound.{u,v,w} :=
  ClosedRangeEquivalences.closed_range_iff_lower_bound

theorem closed_range_iff_adjoint_range_closed : Spec.ClosedRangeAdjointIff.{u,v,w} :=
  ClosedRangeEquivalences.closed_range_iff_adjoint_range_closed

theorem closed_range_kernel_range_identities : Spec.ClosedRangeIdentities.{u,v,w} :=
  ClosedRangeEquivalences.closed_range_kernel_range_identities
end ExpandedFA.Hilbert.ReducedMinimumModulus
