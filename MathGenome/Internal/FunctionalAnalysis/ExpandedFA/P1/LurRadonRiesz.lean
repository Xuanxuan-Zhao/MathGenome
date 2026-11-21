import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LurRadonRiesz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences

/-! Local uniform convexity implies Radon–Riesz without completeness.
A norming functional at the normalized limit squeezes the normalized
midpoint norms to one. Zero sequence terms are replaced by the normalized
limit before applying the unit-sphere definition. -/
namespace ExpandedFA.P1.LurRadonRiesz
universe u v
open Filter
open scoped Topology
noncomputable section

theorem locallyUniformlyConvex_radonRiesz :
    Spec.LocallyUniformlyConvexRadonRiesz.{u,v} := by
  classical
  intro 𝕜 E _ _ _ hluc s x hw hn
  by_cases hx : x = 0
  · subst x
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa using hn)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxcast : (‖x‖ : 𝕜) ≠ 0 := by exact_mod_cast hxpos.ne'
  let u : E := (‖x‖ : 𝕜)⁻¹ • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hxpos,
      inv_mul_cancel₀ hxpos.ne']
  let y : ℕ → E := fun n => if s n = 0 then u else (‖s n‖ : 𝕜)⁻¹ • s n
  have hy (n : ℕ) : ‖y n‖ = 1 := by
    dsimp [y]
    split_ifs with h
    · exact hu
    · have hp : 0 < ‖s n‖ := norm_pos_iff.mpr h
      rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hp,
        inv_mul_cancel₀ hp.ne']
  have hcast : Tendsto (fun n => (‖s n‖ : 𝕜)) atTop (𝓝 (‖x‖ : 𝕜)) :=
    (RCLike.continuous_ofReal.tendsto ‖x‖).comp hn
  have hnonzero : ∀ᶠ n in atTop, s n ≠ 0 := by
    filter_upwards [hn.eventually (lt_mem_nhds hxpos)] with n hn
    exact norm_pos_iff.mp hn
  obtain ⟨f, hf, hfu⟩ := C05Norming.norming_functional 𝕜 E u
  have hfuone : f u = 1 := by simpa only [hu, RCLike.ofReal_one] using hfu
  have hyf : Tendsto (fun n => f (y n)) atTop (𝓝 (f u)) := by
    have h := (hcast.inv₀ hxcast).mul
      (C12BoundedSequences.weak_evaluation_tendsto 𝕜 E s x hw f)
    have heq : (‖x‖ : 𝕜)⁻¹ * f x = f u := by simp [u]
    rw [heq] at h
    apply h.congr'
    filter_upwards [hnonzero] with n hn
    simp [y, hn]
  let m : ℕ → E := fun n => (2 : 𝕜)⁻¹ • (u + y n)
  have hfm : Tendsto (fun n => ‖f (m n)‖) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (2 : 𝕜)⁻¹)).mul
      ((tendsto_const_nhds (x := f u)).add hyf)).norm
    have hmone : (2 : 𝕜)⁻¹ * (f u + f u) = 1 := by
      rw [hfuone]
      norm_num
    simpa only [m, map_smul, map_add, smul_eq_mul, hmone, norm_one] using h
  have hm : Tendsto (fun n => ‖m n‖) atTop (𝓝 1) := by
    apply hfm.squeeze tendsto_const_nhds
    · intro n
      exact (f.le_opNorm (m n)).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (norm_nonneg (m n)))
    · intro n
      dsimp [m]
      rw [C14UniformConvexity.norm_midpoint_eq_half]
      have h := norm_add_le u (y n)
      rw [hu, hy] at h
      linarith
  have hyconv : Tendsto y atTop (𝓝 u) := (hluc u hu).2 y hy hm
  have hrescale (n : ℕ) : (‖s n‖ : 𝕜) • y n = s n := by
    dsimp [y]
    split_ifs with h
    · simp [h]
    · have hc : (‖s n‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hurescale : (‖x‖ : 𝕜) • u = x := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hxcast, one_smul]
  simpa only [hrescale, hurescale] using hcast.smul hyconv

end
end ExpandedFA.P1.LurRadonRiesz
