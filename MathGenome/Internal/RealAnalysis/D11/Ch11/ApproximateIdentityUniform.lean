import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ApproximateIdentityUniform
import MathGenome.Internal.RealAnalysis.D11.Ch11.ConvolutionYoung
import MathGenome.Internal.RealAnalysis.D11.Ch09.LinearJacobian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! The completed linear Jacobian formula gives the normalized integral
`∫ z, φ z * f (x - t • z)`. Its difference from `(∫ φ) * f x` is dominated
by `‖φ z‖ * (B+B)`. Apply dominated convergence along `(𝓝 0) ×ˢ 𝓟 S`:
the second coordinate ranges freely over S, retaining uniform convergence.
Uniform continuity supplies the translation control for S = univ; continuity
at a compact subset of an open set supplies the same ambient control there.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace D11.Ch11.ApproximateIdentityUniform
open D11.Ch03 Specs.D11.Ch03.LebesgueMeasures
open D11.Ch09.LinearJacobian
open D11.Ch11.ConvolutionBound (convolution)

abbrev scaledKernel : Specs.D11.Ch11.ApproximateIdentityUniform.scaledKernel_type :=
  Specs.D11.Ch11.ApproximateIdentityUniform.scaledKernel_value

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- A scalar dilation, as a linear equivalence on the original Euclidean space. -/
def dilationEquiv (t : ℝ) (ht : t ≠ 0) : Point d ≃ₗ[ℝ] Point d :=
  LinearEquiv.smulOfNeZero ℝ (Point d) t ht

lemma dilation_det (t : ℝ) (ht : t ≠ 0) :
    LinearMap.det (dilationEquiv (d := d) t ht : Point d →ₗ[ℝ] Point d) = t ^ d := by
  change LinearMap.det (t • (LinearMap.id : Point d →ₗ[ℝ] Point d)) = _
  simp [LinearMap.det_smul, finrank_euclideanSpace]

lemma completed_measurable_of_continuous {f : Point d → 𝕜} (hf : Continuous f) :
    @Measurable _ _ (lebesgueSpace_value d) _ f :=
  hf.measurable.mono (D11.Ch03.LebesgueMeasures.native_borel_le d) le_rfl

section Completed
local instance : MeasurableSpace (Point d) := lebesgueSpace_value d

lemma measurable_dilation (t : ℝ) : Measurable (fun z : Point d => t • z) := by
  by_cases ht : t = 0
  · simp only [ht, zero_smul]; exact measurable_const
  · exact completed_measurable d (dilationEquiv t ht)

lemma measurable_shift_dilation (x : Point d) (t : ℝ) :
    Measurable (fun z : Point d => x - t • z) :=
  (ConvolutionBound.measurePreserving_const_sub x).measurable.comp (measurable_dilation t)

lemma map_dilation (t : ℝ) (ht : t ≠ 0) :
    Measure.map (dilationEquiv t ht) (lebesgue_value d) =
      ENNReal.ofReal |(t ^ d)⁻¹| • lebesgue_value d := by
  have hm := map_lebesgue d (dilationEquiv t ht)
  change Measure.map (dilationEquiv t ht) (lebesgue_value d) =
    ENNReal.ofReal |(LinearMap.det (dilationEquiv (d := d) t ht : Point d →ₗ[ℝ] Point d))⁻¹| •
      lebesgue_value d at hm
  rwa [dilation_det] at hm

lemma integral_dilation (H : Point d → 𝕜) {t : ℝ} (ht : 0 < t) :
    (∫ z, H (t • z) ∂lebesgue_value d) =
      (t ^ d)⁻¹ • ∫ y, H y ∂lebesgue_value d := by
  have h := integral_map_equiv (μ := lebesgue_value d)
    (completedEquiv d (dilationEquiv t ht.ne')) H
  change (∫ y, H y ∂Measure.map (dilationEquiv t ht.ne') (lebesgue_value d)) = _ at h
  rw [map_dilation, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos ht d))] at h
  exact h.symm

lemma convolution_dilation (φ f : Point d → 𝕜) {t : ℝ} (ht : 0 < t) (x : Point d) :
    convolution d (scaledKernel d φ t) f x =
      ∫ z, φ z * f (x - t • z) ∂lebesgue_value d := by
  have h := integral_dilation (fun y => scaledKernel d φ t y * f (x-y)) ht
  have hi : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
  have hs : ∀ z : Point d,
      scaledKernel d φ t (t • z) * f (x - t • z) =
        (t ^ d)⁻¹ • (φ z * f (x - t • z)) := by
    intro z
    simp [scaledKernel, Specs.D11.Ch11.ApproximateIdentityUniform.scaledKernel_value,
      smul_smul, hi]
  simp_rw [hs] at h
  rw [integral_smul] at h
  have hc : (t ^ d)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ ht.ne')
  exact (smul_right_injective _ hc h).symm

lemma integrable_dilation {φ : Point d → 𝕜} (hφ : Integrable φ (lebesgue_value d))
    {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun z => φ (t • z)) (lebesgue_value d) := by
  have h := integrable_map_equiv (μ := lebesgue_value d)
    (completedEquiv d (dilationEquiv t ht)) φ
  change Integrable φ (Measure.map (dilationEquiv t ht) (lebesgue_value d)) ↔ _ at h
  rw [map_dilation] at h
  exact h.mp ((integrable_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero d ht)))))
    ENNReal.ofReal_ne_top).mpr hφ)

theorem absolute_existence : Specs.D11.Ch11.ApproximateIdentityUniform.absolute_existence := by
  intro d _ 𝕜 _ _ _
  let := lebesgueSpace_value d
  intro φ f _hφm hφ hf ⟨B, _hB, hBf⟩ t ht x
  have hi : Integrable (scaledKernel d φ t) (lebesgue_value d) :=
    (integrable_dilation hφ (inv_ne_zero ht.ne')).smul (t ^ d)⁻¹
  constructor
  · exact ((ConvolutionBound.measurePreserving_const_sub x).integrable_comp_of_integrable hi).bdd_mul
      hf.aestronglyMeasurable (Eventually.of_forall hBf)
  · exact hi.mul_bdd (hf.comp (ConvolutionBound.measurePreserving_const_sub x).measurable).aestronglyMeasurable
      (Eventually.of_forall fun y => hBf (x-y))

/-- Absolute convergence of the normalized integral for every parameter. -/
lemma integrable_normalized {φ f : Point d → 𝕜}
    (hφ : Integrable φ (lebesgue_value d)) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (t : ℝ) (x : Point d) :
    Integrable (fun z => φ z * f (x - t • z)) (lebesgue_value d) :=
  hφ.mul_bdd (hf.comp (measurable_shift_dilation x t)).aestronglyMeasurable
    (Eventually.of_forall fun _ => hB _)

/-- Dominated convergence with the product of the parameter filter and the
principal filter of S retains uniformity in x. This avoids any measurability
assumption on a pointwise supremum over S. -/
lemma uniform_integral_normalized {φ f : Point d → 𝕜}
    (hφm : Measurable φ) (hφ : Integrable φ (lebesgue_value d)) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (S : Set (Point d))
    (hsmall : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ h : Point d, ‖h‖ < δ →
      ‖f (x-h) - f x‖ < ε) :
    TendstoUniformlyOn (fun t x => ∫ z, φ z * f (x - t • z) ∂lebesgue_value d)
      (fun x => (∫ z, φ z ∂lebesgue_value d) * f x) (𝓝 (0 : ℝ)) S := by
  let F : (ℝ × Point d) → Point d → 𝕜 :=
    fun q z => φ z * (f (q.2 - q.1 • z) - f q.2)
  have hlim (z : Point d) :
      Tendsto (fun q : ℝ × Point d => f (q.2-q.1 • z) - f q.2)
        ((𝓝 (0 : ℝ)) ×ˢ 𝓟 S) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := hsmall ε hε
    have ht : ∀ᶠ t : ℝ in 𝓝 0, ‖t • z‖ < δ := by
      have h : Tendsto (fun t : ℝ => ‖t • z‖) (𝓝 0) (𝓝 0) := by
        simpa using (((continuous_id : Continuous (fun t : ℝ => t)).smul
          (continuous_const : Continuous (fun _ : ℝ => z))).norm.tendsto (0 : ℝ))
      exact h.eventually (gt_mem_nhds hδ)
    filter_upwards [ht.prod_mk (eventually_mem_principal S)] with q hq
    simpa only [dist_zero_right] using hδf q.2 hq.2 (q.1 • z) hq.1
  have hmeas (q : ℝ × Point d) : AEStronglyMeasurable (F q) (lebesgue_value d) :=
    (hφm.mul ((hf.comp (measurable_shift_dilation q.2 q.1)).sub measurable_const)).aestronglyMeasurable
  have hbound (q : ℝ × Point d) (z : Point d) :
      ‖F q z‖ ≤ ‖φ z‖ * (B+B) := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hB _) (hB _)))
      (norm_nonneg _)
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := lebesgue_value d) (l := (𝓝 (0 : ℝ)) ×ˢ 𝓟 S)
    (F := F) (f := fun _ => (0 : 𝕜)) (fun z => ‖φ z‖ * (B+B))
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun q => Eventually.of_forall (hbound q))
    (hφ.norm.mul_const (B+B))
    (Eventually.of_forall fun z => by simpa only [mul_zero] using
      (tendsto_const_nhds.mul (hlim z)))
  have heq (q : ℝ × Point d) :
      (∫ z, F q z ∂lebesgue_value d) =
        (∫ z, φ z * f (q.2-q.1 • z) ∂lebesgue_value d) -
          (∫ z, φ z ∂lebesgue_value d) * f q.2 := by
    simp only [F, mul_sub]
    rw [integral_sub (integrable_normalized hφ hf hB q.1 q.2) (hφ.mul_const _),
      integral_mul_const]
  simp only [integral_zero] at hD
  simp_rw [heq] at hD
  apply tendstoUniformlyOn_iff_tendsto.mpr
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm'] using (tendsto_zero_iff_norm_tendsto_zero.mp hD)

/-- Continuity at every point of a compact set controls nearby points in the
ambient space as well, so no continuity outside the given open set is needed. -/
lemma compact_translation_control {f : Point d → 𝕜} {K U : Set (Point d)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hf : ContinuousOn f U) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ h : Point d, ‖h‖ < δ →
      ‖f (x-h) - f x‖ < ε := by
  intro ε hε
  have hu := hK.uniformContinuousAt_of_continuousAt f
    (fun x hx => (hf x (hKU hx)).continuousAt (hU.mem_nhds (hKU hx)))
    (Metric.uniformity_basis_dist.mem_of_mem hε)
  obtain ⟨δ, hδ, hδf⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ, hδ, fun x hx h hh => ?_⟩
  have hd : dist x (x-h) < δ := by simpa only [dist_eq_norm, sub_sub_cancel] using hh
  simpa only [mem_ofPred_eq, dist_eq_norm'] using hδf hd hx

/-- Return from the normalized expression to the source dilated kernel. -/
lemma uniform_convolution_of_translation_control {φ f : Point d → 𝕜}
    (hφm : Measurable φ) (hφ : Integrable φ (lebesgue_value d)) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (S : Set (Point d))
    (hsmall : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ h : Point d, ‖h‖ < δ →
      ‖f (x-h) - f x‖ < ε) :
    TendstoUniformlyOn (fun t => convolution d f (scaledKernel d φ t))
      (fun x => (∫ z, φ z ∂lebesgue_value d) * f x) (𝓝[>] (0 : ℝ)) S := by
  have h := uniform_integral_normalized hφm hφ hf hB S hsmall
  have hr : TendstoUniformlyOn
      (fun t x => ∫ z, φ z * f (x - t • z) ∂lebesgue_value d)
      (fun x => (∫ z, φ z ∂lebesgue_value d) * f x) (𝓝[>] (0 : ℝ)) S :=
    fun r hr => (h r hr).filter_mono nhdsWithin_le_nhds
  apply hr.congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x _hx
  exact (convolution_dilation φ f ht x).symm.trans
    (congrFun (ConvolutionYoung.commutative (scaledKernel d φ t) f) x)

theorem uniform_convergence : Specs.D11.Ch11.ApproximateIdentityUniform.uniform_convergence := by
  intro d _ 𝕜 _ _ _
  let := lebesgueSpace_value d
  intro φ f hφm hφ ⟨B, _hB, hBf⟩ hf
  apply tendstoUniformlyOn_univ.mp
  apply uniform_convolution_of_translation_control hφm hφ
    (completed_measurable_of_continuous hf.continuous) hBf
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  refine ⟨δ, hδ, fun x _hx h hh => ?_⟩
  have hd : dist x (x-h) < δ := by simpa only [dist_eq_norm, sub_sub_cancel] using hh
  simpa only [dist_eq_norm'] using hδf hd

theorem compact_local_convergence :
    Specs.D11.Ch11.ApproximateIdentityUniform.compact_local_convergence := by
  intro d _ 𝕜 _ _ _
  let := lebesgueSpace_value d
  intro φ f hφm hφ hf ⟨B, _hB, hBf⟩ U hU hfU K hK hKU
  exact uniform_convolution_of_translation_control hφm hφ hf hBf K
    (compact_translation_control hK hKU hU hfU)

end Completed
end D11.Ch11.ApproximateIdentityUniform
