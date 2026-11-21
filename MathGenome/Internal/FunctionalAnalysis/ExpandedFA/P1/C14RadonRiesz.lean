import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14RadonRiesz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Radon–Riesz without a completeness assumption. -/
namespace ExpandedFA.P1.C14RadonRiesz

universe u v
open Filter
open scoped Topology
noncomputable section

variable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Scalar tests suffice on the unit ball when the weak limit has norm one.
A norming functional forces midpoint norms arbitrarily near one; uniform
convexity then forces the original vectors arbitrarily near the limit. -/
private theorem tendsto_of_scalar_unit (huc : C14UniformConvexity.UniformlyConvex 𝕜 E)
    (s : ℕ → E) (x : E) (hs : ∀ n, ‖s n‖ ≤ 1) (hx : ‖x‖ = 1)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) :
    Tendsto s atTop (𝓝 x) := by
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
  have hmid : (2 : 𝕜)⁻¹ • (x + x) = x := by
    rw [← two_smul 𝕜 x, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : 𝕜) ≠ 0),
      one_smul]
  have hm : Tendsto (fun n => ‖f ((2 : 𝕜)⁻¹ • (s n + x))‖) atTop (𝓝 1) := by
    have h : Tendsto (fun n => f ((2 : 𝕜)⁻¹ • (s n + x))) atTop
        (𝓝 (f ((2 : 𝕜)⁻¹ • (x + x)))) := by
      simpa only [map_smul, map_add, smul_eq_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : 𝕜)⁻¹) atTop
          (𝓝 ((2 : 𝕜)⁻¹))).mul ((hw f).add tendsto_const_nhds)
    have hnorm : ‖f x‖ = 1 := by
      rw [hfx, hx]
      norm_num
    simpa only [hmid, hnorm] using h.norm
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hconv⟩ := huc (min ε 1) (lt_min hε zero_lt_one)
    ((min_le_right ε 1).trans (by norm_num))
  have hnear := hm.eventually (lt_mem_nhds (show 1 - δ < (1 : ℝ) by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnear
  refine ⟨N, fun n hn => ?_⟩
  have hsep : ‖s n - x‖ < min ε 1 := by
    by_contra h
    have hupper := hconv (s n) x (hs n) hx.le (le_of_not_gt h)
    have hnorm := (f.le_opNorm ((2 : 𝕜)⁻¹ • (s n + x))).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hf (norm_nonneg ((2 : 𝕜)⁻¹ • (s n + x))))
    have := hN n hn
    linarith
  rw [dist_eq_norm]
  exact hsep.trans_le (min_le_left ε 1)

/-- The limsup bound and weak lower semicontinuity first give convergence
of norms. Normalize by max(‖s n‖, ‖x‖), use the unit-ball result, and
rescale. The zero limit is handled before division. -/
theorem radon_riesz : Spec.RadonRiesz.{u,v} := by
  intro 𝕜 E _ _ _ huc s x hw hsup
  obtain ⟨C, _, hC⟩ := C12BoundedSequences.weak_sequence_bounded 𝕜 E s x hw
  have hn : Tendsto (fun n => ‖s n‖) atTop (𝓝 ‖x‖) :=
    tendsto_of_le_liminf_of_limsup_le
      (C12BoundedSequences.weak_sequence_norm_liminf 𝕜 E s x hw) hsup
      (isBoundedUnder_of ⟨C, hC⟩)
      (isBoundedUnder_of ⟨0, fun n => norm_nonneg (s n)⟩)
  by_cases hx : x = 0
  · subst x
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa using hn)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let r : ℕ → ℝ := fun n => max ‖s n‖ ‖x‖
  have hrpos (n : ℕ) : 0 < r n := hxpos.trans_le (le_max_right _ _)
  have hr : Tendsto r atTop (𝓝 ‖x‖) := by
    simpa only [r, max_self] using hn.max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))
  have hcast : Tendsto (fun n => (r n : 𝕜)) atTop (𝓝 (‖x‖ : 𝕜)) :=
    (RCLike.continuous_ofReal.tendsto ‖x‖).comp hr
  have hxcast : (‖x‖ : 𝕜) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hrcast (n : ℕ) : (r n : 𝕜) ≠ 0 := by exact_mod_cast (hrpos n).ne'
  let a : ℕ → E := fun n => (r n : 𝕜)⁻¹ • s n
  let y : E := (‖x‖ : 𝕜)⁻¹ • x
  have haunit (n : ℕ) : ‖a n‖ ≤ 1 := by
    dsimp [a]
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos (hrpos n),
      ← div_eq_inv_mul]
    exact (div_le_one (hrpos n)).mpr (le_max_left _ _)
  have hyunit : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hxpos,
      inv_mul_cancel₀ hxpos.ne']
  have haw : ∀ f : E →L[𝕜] 𝕜,
      Tendsto (fun n => f (a n)) atTop (𝓝 (f y)) := by
    intro f
    simpa only [a, y, map_smul, smul_eq_mul] using
      (hcast.inv₀ hxcast).mul (C12BoundedSequences.weak_evaluation_tendsto 𝕜 E s x hw f)
  have ha := tendsto_of_scalar_unit 𝕜 E huc a y haunit hyunit haw
  have hrescale (n : ℕ) : (r n : 𝕜) • a n = s n := by
    dsimp [a]
    rw [smul_smul, mul_inv_cancel₀ (hrcast n), one_smul]
  have hyrescale : (‖x‖ : 𝕜) • y = x := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hxcast, one_smul]
  simpa only [hrescale, hyrescale] using hcast.smul ha

theorem radon_riesz_of_norm_convergence :
    Spec.RadonRieszOfNormConvergence.{u,v} := by
  intro 𝕜 E _ _ _ huc s x hw hn
  apply radon_riesz 𝕜 E huc s x hw
  exact hn.limsup_eq.le

end
end ExpandedFA.P1.C14RadonRiesz
