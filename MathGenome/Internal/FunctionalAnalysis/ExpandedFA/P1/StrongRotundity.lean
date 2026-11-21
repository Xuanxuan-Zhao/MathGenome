import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.StrongRotundity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.StrongRotundityCriteria
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.StrictApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14WeakSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LurRadonRiesz
import Batteries.Tactic.OpenPrivate

namespace ExpandedFA.P1.StrongRotundity
universe u v
open Filter Metric
open scoped Topology
noncomputable section

/-- The diameter-limit definition of strong rotundity. -/
def StrongRotund : Spec.StrongRotundType.{u,v} := Spec.StrongRotundValue

theorem strong_rotundity_criteria : Spec.Criteria.{u,v} := by
  intro 𝕜 E _ _ _
  obtain ⟨h12, h23⟩ := StrongRotundityCriteria.strong_rotundity_criteria 𝕜 E
  exact ⟨h12, h12.trans h23⟩

open private exposing_functional from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.StrictApproximation

theorem strongRotund_strictConvex : Spec.StrictConvexity.{u,v} := by
  intro 𝕜 E _ _ _ h
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  apply (RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E).mpr
  apply StrictConvexSpace.of_norm_add_ne_two
  intro x y hx hy hne hxy
  obtain ⟨f, hf, hfx, hfy⟩ := exposing_functional 𝕜 hx hy hxy
  have hd := StrongRotundityCriteria.shrinkingSlices_iff_smallSliceDiameters.mp h
  obtain ⟨δ, hδ, hd⟩ := hd f hf (dist x y) (dist_pos.mpr hne)
  have hxmem : x ∈ StrongRotundityCriteria.Spec.slice 𝕜 E f δ :=
    ⟨hx.le, by linarith⟩
  have hymem : y ∈ StrongRotundityCriteria.Spec.slice 𝕜 E f δ :=
    ⟨hy.le, by linarith⟩
  exact (not_lt_of_ge (dist_le_diam_of_mem
    (StrongRotundityCriteria.slice_bounded f δ) hxmem hymem)) hd

/-- A norm-Cauchy sequence with a weak limit converges to that limit, even
when the ambient space is incomplete. Scalar norming tests suffice. -/
lemma tendsto_of_cauchySeq_of_weak {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : ℕ → E} {x : E}
    (hc : CauchySeq s)
    (hw : Tendsto s atTop (@nhds E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) x)) : Tendsto s atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E (s n - x)
  have hlim : Tendsto (fun m => ‖f (s n - s m)‖) atTop (𝓝 ‖s n - x‖) := by
    have ht := ((tendsto_const_nhds (x := f (s n))).sub
      (C12BoundedSequences.weak_evaluation_tendsto 𝕜 E s x hw f)).norm
    simpa [← map_sub, hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] using ht
  have hle : ‖s n - x‖ ≤ ε / 2 := le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => by
    calc
      ‖f (s n - s m)‖ ≤ ‖f‖ * ‖s n - s m‖ := f.le_opNorm _
      _ ≤ ‖s n - s m‖ := by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg _)
      _ ≤ ε / 2 := by simpa [dist_eq_norm] using (hN n hn m hm).le⟩)
  rw [dist_eq_norm]
  linarith

theorem strongRotund_radonRiesz : Spec.RadonRiesz.{u,v} := by
  classical
  intro 𝕜 E _ _ _ h s x hw hn
  by_cases hx : x = 0
  · subst x
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa using hn)
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxcast : (‖x‖ : 𝕜) ≠ 0 := by exact_mod_cast hxpos.ne'
  let u : E := (‖x‖ : 𝕜)⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ hxpos.ne']
  let y : ℕ → E := fun n => if s n = 0 then u else (‖s n‖ : 𝕜)⁻¹ • s n
  have hy (n : ℕ) : ‖y n‖ = 1 := by
    dsimp [y]
    split_ifs with hz
    · exact hu
    · have hp := norm_pos_iff.mpr hz
      simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hcast : Tendsto (fun n => (‖s n‖ : 𝕜)) atTop (𝓝 (‖x‖ : 𝕜)) :=
    (RCLike.continuous_ofReal.tendsto ‖x‖).comp hn
  have hnonzero : ∀ᶠ n in atTop, s n ≠ 0 := by
    filter_upwards [hn.eventually (lt_mem_nhds hxpos)] with n hn
    exact norm_pos_iff.mp hn
  obtain ⟨f, hf, hfu⟩ := C05Norming.norming_functional_nonzero 𝕜 E u
    (norm_ne_zero_iff.mp (by rw [hu]; norm_num))
  have hfuone : f u = 1 := by simpa [hu] using hfu
  have hyf : Tendsto (fun n => f (y n)) atTop (𝓝 (f u)) := by
    have ht := (hcast.inv₀ hxcast).mul
      (C12BoundedSequences.weak_evaluation_tendsto 𝕜 E s x hw f)
    have heq : (‖x‖ : 𝕜)⁻¹ * f x = f u := by simp [u]
    rw [heq] at ht
    apply ht.congr'
    filter_upwards [hnonzero] with n hn
    simp [y, hn]
  have heval : Tendsto (fun n => RCLike.re (f (y n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, hfuone, RCLike.one_re] using
      (RCLike.continuous_re.tendsto (f u)).comp hyf
  have hyc : CauchySeq y := (strong_rotundity_criteria 𝕜 E).1.mp h f hf y hy heval
  have hrec (n : ℕ) : (‖s n‖ : 𝕜) • y n = s n := by
    dsimp [y]
    split_ifs with hz
    · simp [hz]
    · have hp : (‖s n‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
      simp [smul_smul, mul_inv_cancel₀ hp]
  have hyc' : CauchySeq (fun n => (‖x‖ : 𝕜) • y n) :=
    (uniformContinuous_const_smul (‖x‖ : 𝕜)).comp_cauchySeq hyc
  have hs : CauchySeq s := by
    apply StrongRotundityCriteria.cauchySeq_of_norm_sub_tendsto_zero hyc'
    have heq : (fun n => ‖s n - (‖x‖ : 𝕜) • y n‖) =
        (fun n => |‖s n‖ - ‖x‖|) := by
      funext n
      conv_lhs => rw [← hrec n]
      rw [← sub_smul, norm_smul, hy n, mul_one, ← RCLike.ofReal_sub,
        RCLike.norm_ofReal]
    rw [heq]
    simpa using (hn.sub_const ‖x‖).abs
  exact tendsto_of_cauchySeq_of_weak hs hw

theorem strongRotund_banach_minimizers_converge : Spec.BanachMinimizersConverge.{u,v} := by
  intro 𝕜 E _ _ _ _ h C hC hc p x hx hlim
  exact cauchySeq_tendsto_of_complete ((strong_rotundity_criteria 𝕜 E).2.mp h C hC hc p x hx hlim)

/-- Reflexivity extracts a norm-convergent subsequence of a unit maximizing
sequence: its weak limit lies on the same supporting sphere, and Radon–Riesz
upgrades weak convergence because all the norms equal one. -/
lemma maximizing_subsequence {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (href : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E)
    (hrr : RotundDefinitions.Spec.RadonRieszValue 𝕜 E)
    (f : E →L[𝕜] 𝕜) (hf : ‖f‖ = 1) (s : ℕ → E) (hs : ∀ n, ‖s n‖ = 1)
    (hfs : Tendsto (fun n => RCLike.re (f (s n))) atTop (𝓝 1)) :
    ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ z : E, ‖z‖ = 1 ∧ RCLike.re (f z) = 1 ∧
      Tendsto (s ∘ k) atTop (𝓝 z) := by
  have hb : Bornology.IsBounded (Set.range s) := isBounded_iff_forall_norm_le.2
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hs n).le⟩
  obtain ⟨k, hk, z, hw⟩ := C14WeakSubsequence.reflexive_weak_subsequence 𝕜 E href s hb
  have hfz : RCLike.re (f z) = 1 := tendsto_nhds_unique
    ((RCLike.continuous_re.tendsto (f z)).comp
      (C12BoundedSequences.weak_evaluation_tendsto 𝕜 E (s ∘ k) z hw f))
    (hfs.comp hk.tendsto_atTop)
  have hzle : ‖z‖ ≤ 1 := by
    have hl := C12BoundedSequences.weak_sequence_norm_liminf 𝕜 E (s ∘ k) z hw
    simpa only [Function.comp_apply, hs, liminf_const] using hl
  have hzn : ‖z‖ = 1 := le_antisymm hzle (by
    simpa [hfz] using StrongRotundityCriteria.realPart_le_norm f hf z)
  refine ⟨k, hk, z, hzn, hfz, hrr (s ∘ k) z hw ?_⟩
  simpa only [Function.comp_apply, hs, hzn] using
    (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))

/-- Unique support contact makes all extracted norm limits equal. The
subsequence criterion then gives convergence of the entire maximizing sequence. -/
theorem reflexive_strictConvex_radonRiesz_strongRotund : Spec.ReflexiveConverse.{u,v} := by
  intro 𝕜 E _ _ _ href hrot hrr
  letI : CompleteSpace E := C14Reflexive.reflexive_completeSpace 𝕜 E href
  apply (strong_rotundity_criteria 𝕜 E).1.mpr
  intro f hf s hs hfs
  obtain ⟨k, hk, z, hzn, hfz, _hzconv⟩ := maximizing_subsequence href hrr f hf s hs hfs
  have hsupport : StrictApproximation.Spec.SupportsUnitBall 𝕜 E f 1 := by
    refine ⟨?_, ?_, z, hzn.le, hfz⟩
    · intro hz
      simp [hz] at hf
    · intro w hw
      exact (StrongRotundityCriteria.realPart_le_norm f hf w).trans hw
  have hconv : Tendsto s atTop (𝓝 z) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, _, w, hwn, hfw, hwconv⟩ := maximizing_subsequence href hrr f hf
      (s ∘ ns) (fun n => hs (ns n)) (hfs.comp hns)
    have heq : w = z :=
      (StrictApproximation.rotund_iff_supporting_hyperplanes_unique 𝕜 E).mp hrot
        f 1 hsupport w z hwn hzn hfw hfz
    exact ⟨ms, by simpa [Function.comp_def, heq] using hwconv⟩
  exact hconv.cauchySeq

/-- Local uniform convexity also forces strict convexity, without completeness. -/
lemma locallyUniformlyConvex_rotund (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hluc : RotundDefinitions.Spec.LocallyUniformlyConvexValue 𝕜 E) :
    RotundDefinitions.Spec.RotundValue 𝕜 E := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  apply (RotundDefinitions.rotund_iff_strictConvexSpace 𝕜 E).mpr
  apply StrictConvexSpace.of_norm_add_ne_two
  intro x y hx hy hne hxy
  have hm : ‖(2 : 𝕜)⁻¹ • (x + y)‖ = 1 := by
    rw [C14UniformConvexity.norm_midpoint_eq_half, hxy]
    norm_num
  have hconv : Tendsto (fun _ : ℕ => y) atTop (𝓝 x) :=
    (hluc x hx).2 (fun _ => y) (fun _ => hy) (by
      simpa only [hm] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)))
  exact hne (tendsto_nhds_unique hconv tendsto_const_nhds)

theorem reflexive_locallyUniformlyConvex_strongRotund :
    Spec.ReflexiveLocallyUniformlyConvex.{u,v} := by
  intro 𝕜 E _ _ _ href hluc
  exact reflexive_strictConvex_radonRiesz_strongRotund 𝕜 E href
    (locallyUniformlyConvex_rotund 𝕜 E hluc)
    (LurRadonRiesz.locallyUniformlyConvex_radonRiesz 𝕜 E hluc)

end
end ExpandedFA.P1.StrongRotundity
