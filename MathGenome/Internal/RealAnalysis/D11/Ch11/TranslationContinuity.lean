import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.TranslationContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch11.CcDensityEuclidean
import MathGenome.Internal.RealAnalysis.D11.Ch03.TranslationDilation
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace D11.Ch11.TranslationContinuity
open D11.Ch03 D11.Ch03.LebesgueMeasures

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]

omit [NeZero d] in
lemma sub_preimage (h : Point d) (s : Set (Point d)) :
    (fun x => x - h) ⁻¹' s = (fun x => h + (1 : ℝ) • x) '' s := by
  ext x
  simp only [mem_preimage, one_smul, mem_image]
  constructor
  · intro hx
    exact ⟨x - h, hx, by abel⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [add_sub_cancel_left] using hy

lemma measurable_sub_const (h : Point d) :
    @Measurable (Point d) (Point d) (lebesgueSpace d) (lebesgueSpace d)
      (fun x => x - h) := by
  intro s hs
  rw [sub_preimage]
  exact (TranslationDilation.lebesgue_affine d h 1 s hs).1

lemma measurePreserving_sub_const (h : Point d) :
    @MeasurePreserving (Point d) (Point d) (lebesgueSpace d) (lebesgueSpace d)
      (fun x => x - h) (lebesgue d) (lebesgue d) := by
  let : MeasurableSpace (Point d) := lebesgueSpace d
  refine ⟨measurable_sub_const h, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_sub_const h) hs, sub_preimage]
  have H := (TranslationDilation.lebesgue_affine d h 1 s hs).2
  change (lebesgue d) ((fun x => h + (1 : ℝ) • x) '' s) =
    ENNReal.ofReal (|1| ^ d) * (lebesgue d) s at H
  simpa using H

omit [NeZero d] in
/-- The library continuity theorem is used only on the Borel space. -/
private lemma borel_cc_translation_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (g : CompactlySupportedContinuousMap (Point d) 𝕜) (k : Point d) :
    Tendsto (fun h : Point d =>
      eLpNorm ((fun x => g (x - h)) - (fun x => g (x - k))) p volume)
      (𝓝 k) (𝓝 0) := by
  let F : C(Point d, C(Point d, Point d)) :=
    (⟨fun a : Point d × Point d => a.2 - a.1, continuous_snd.sub continuous_fst⟩ :
      C(Point d × Point d, Point d)).curry
  have hm (h : Point d) : MeasurePreserving (F h) volume volume :=
    measurePreserving_sub_right volume h
  have hg : MemLp (g : Point d → 𝕜) p volume :=
    g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have ht (h : Point d) : MemLp (fun x => g (x - h)) p volume :=
    hg.comp_measurePreserving (hm h)
  have hc : Continuous (fun h => (ht h).toLp (fun x => g (x - h))) :=
    (continuous_const : Continuous (fun _ : Point d => hg.toLp g)).compMeasurePreservingLp
      F.continuous hm hp
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ ht _ (ht k)).mp (hc.tendsto k)

/-- Trimming preserves the norm of the continuous difference. No BorelSpace
instance is asserted for the completed sigma-algebra. -/
private lemma completed_cc_translation_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (g : CompactlySupportedContinuousMap (Point d) 𝕜) (k : Point d) :
    Tendsto (fun h : Point d =>
      @eLpNorm _ _ _ _ (lebesgueSpace d)
        ((fun x => g (x - h)) - (fun x => g (x - k))) p (lebesgue d))
      (𝓝 k) (𝓝 0) := by
  have hB (h k : Point d) : StronglyMeasurable
      ((fun x => g (x - h)) - (fun x => g (x - k))) :=
    ((g.continuous.comp (continuous_id.sub continuous_const)).sub
      (g.continuous.comp (continuous_id.sub continuous_const))).stronglyMeasurable
  have heq (h : Point d) := eLpNorm_trim (p := p) (μ := lebesgue d)
    (native_borel_le d) (hB h k)
  have heq' (h : Point d) :
      @eLpNorm _ _ _ _ (lebesgueSpace d)
        ((fun x => g (x - h)) - (fun x => g (x - k))) p (lebesgue d) =
      eLpNorm ((fun x => g (x - h)) - (fun x => g (x - k))) p volume := by
    have H := heq h
    have htrim : (lebesgue d).trim (native_borel_le d) =
        (volume : Measure (Point d)) := borel_restriction d (native_borel_le d)
    rw [htrim] at H
    exact H.symm
  simpa only [heq'] using borel_cc_translation_tendsto hp g k

section Completed
local instance : MeasurableSpace (Point d) := lebesgueSpace d
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def translate (h : Point d) :
    Lp 𝕜 p (lebesgue d) →ₗᵢ[𝕜] Lp 𝕜 p (lebesgue d) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (fun x => x - h) (measurePreserving_sub_const h)

private lemma translate_add (h k : Point d) (f : Lp 𝕜 p (lebesgue d)) :
    translate h (translate k f) = translate (h + k) f := by
  change Lp.compMeasurePreserving (fun x => x - h) _
      (Lp.compMeasurePreserving (fun x => x - k) _ f) =
    Lp.compMeasurePreserving (fun x => x - (h + k)) _ f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have H : (fun x : Point d => x - k) ∘ (fun x => x - h) =
      (fun x => x - (h + k)) := by
    funext x
    dsimp only [Function.comp_apply]
    abel
  simp only [H]

private lemma translate_zero (f : Lp 𝕜 p (lebesgue d)) : translate 0 f = f := by
  have H : (fun x : Point d => x - 0) = id := by funext x; exact sub_zero x
  change Lp.compMeasurePreserving (fun x => x - 0) _ f = f
  simp only [H, Lp.compMeasurePreserving_id_apply]

private def translateEquiv (h : Point d) :
    Lp 𝕜 p (lebesgue d) ≃ₗᵢ[𝕜] Lp 𝕜 p (lebesgue d) :=
  { translate h with
    invFun := translate (-h)
    left_inv := fun f => by
      change translate (-h) (translate h f) = f
      rw [translate_add, neg_add_cancel, translate_zero]
    right_inv := fun f => by
      change translate h (translate (-h) f) = f
      rw [translate_add, add_neg_cancel, translate_zero] }

private lemma continuous_translate_cc (hp : p ≠ ∞)
    (g : CompactlySupportedContinuousMap (Point d) 𝕜)
    (hg : MemLp (g : Point d → 𝕜) p (lebesgue d)) :
    Continuous (fun h : Point d => translate h (hg.toLp g)) := by
  apply continuous_iff_continuousAt.mpr
  intro k
  have ht (h : Point d) : MemLp (fun x => g (x - h)) p (lebesgue d) :=
    hg.comp_measurePreserving (measurePreserving_sub_const h)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ ht _ (ht k)).mpr
    (completed_cc_translation_tendsto hp g k)

private lemma continuous_translate [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (hp : p ≠ ∞) (f : Lp 𝕜 p (lebesgue d)) :
    Continuous (fun h : Point d => translate h f) := by
  let S : Set (Lp 𝕜 p (lebesgue d)) :=
    {f | ∃ g : CompactlySupportedContinuousMap (Point d) 𝕜,
      ∃ hg : MemLp (g : Point d → 𝕜) p (lebesgue d), hg.toLp g = f}
  have hd : Dense S := by
    intro f
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨g, hg, herr⟩ := CcDensityEuclidean.cc_density d 𝕜 p hp f ε hε
    change MemLp (g : Point d → 𝕜) p (lebesgue d) at hg
    change ‖f - hg.toLp g‖ < ε at herr
    exact ⟨hg.toLp g, ⟨g, hg, rfl⟩, by simpa only [dist_eq_norm] using herr⟩
  have hc : Continuous (fun a : Lp 𝕜 p (lebesgue d) × Point d => translate a.2 a.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hd
    · rintro _ ⟨g, hg, rfl⟩
      exact continuous_translate_cc hp g hg
    · intro h
      exact (translate h).isometry.lipschitzWith
  exact hc.comp (continuous_const.prodMk continuous_id)

/-- Completed-Lebesgue translations are isometries and are strongly continuous
for every finite exponent, including p = 1, over real or complex scalars. -/
theorem translation_continuity :
    Specs.D11.Ch11.TranslationContinuity.translation_continuity := by
  intro d _ 𝕜 _ _ _ p _ hp
  let : MeasurableSpace (Point d) := lebesgueSpace d
  refine ⟨translateEquiv, ?_, ?_⟩
  · intro h f hf
    exact ⟨hf.comp_measurePreserving (measurePreserving_sub_const h), rfl⟩
  · intro f k
    exact tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_translate hp f).tendsto k)

end Completed
end D11.Ch11.TranslationContinuity
