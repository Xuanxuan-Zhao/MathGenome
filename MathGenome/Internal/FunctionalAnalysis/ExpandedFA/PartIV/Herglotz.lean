import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Herglotz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PositiveHarmonic
import Mathlib.Analysis.Complex.OpenMapping

noncomputable section

namespace ExpandedFA.PartIV.Herglotz

open Set MeasureTheory Complex Metric InnerProductSpace
open PositiveHarmonic

lemma herglotzTransform_eq_integral (μ : Measure Circle) (c : ℝ) (z : ℂ) :
    herglotzTransform μ c z = I * (c : ℂ) + ∫ ζ, circleHerglotzKernel z ζ ∂μ := by
  simp only [herglotzTransform, circleHerglotzKernel, herglotzRieszKernel, sub_zero]

lemma herglotzTransform_re (μ : Measure Circle) [IsFiniteMeasure μ]
    (c : ℝ) {z : ℂ} (hz : z ∈ unitDisk) :
    (herglotzTransform μ c z).re = poissonExtension μ z := by
  rw [herglotzTransform_eq_integral]
  simpa using (poissonExtension_eq_re_integral μ hz).symm

lemma herglotzTransform_zero (μ : Measure Circle) (c : ℝ) :
    herglotzTransform μ c 0 = I * (c : ℂ) + (μ.real univ : ℂ) := by
  simp [herglotzTransform, Circle.coe_ne_zero, measureReal_def]

lemma differentiableOn_herglotzTransform (μ : Measure Circle) [IsFiniteMeasure μ]
    (c : ℝ) : DifferentiableOn ℂ (herglotzTransform μ c) unitDisk := by
  convert (differentiableOn_const (c := I * (c : ℂ))).add
    (differentiableOn_herglotzIntegral μ) using 1
  funext z
  exact herglotzTransform_eq_integral μ c z

theorem center_normalization : Spec.CenterNormalization := by
  intro F μ c h
  have h0 := h.2.2 0 (by simp [unitDisk])
  rw [herglotzTransform_zero] at h0
  exact ⟨by simpa using (congrArg Complex.im h0).symm,
    by simpa using (congrArg Complex.re h0).symm⟩

theorem converse : Spec.Converse := by
  intro μ c hμ
  have := hμ
  refine ⟨⟨differentiableOn_herglotzTransform μ c, ?_⟩, ?_, ?_⟩
  · intro z hz
    rw [herglotzTransform_re μ c hz]
    exact poissonExtension_nonneg μ hz
  · simp [herglotzTransform_zero]
  · simp [herglotzTransform_zero]

lemma unitDisk_connected : IsConnected unitDisk := by
  have heq : unitDisk = ball (0 : ℂ) 1 := by
    ext z
    simp [unitDisk]
  rw [heq]
  exact (convex_ball (0 : ℂ) 1).isConnected ⟨0, by simp⟩

/-- Equal real parts determine a holomorphic function up to its value at zero. -/
lemma eq_transform_of_re_eq {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F unitDisk) (μ : Measure Circle) [IsFiniteMeasure μ]
    (hμ : ∀ z ∈ unitDisk, (F z).re = poissonExtension μ z) :
    ∀ z ∈ unitDisk, F z = herglotzTransform μ (F 0).im z := by
  let G : ℂ → ℂ := fun z => F z - herglotzTransform μ 0 z
  have hG : AnalyticOnNhd ℂ G unitDisk :=
    (hF.sub (differentiableOn_herglotzTransform μ 0)).analyticOnNhd isOpen_unitDisk
  have hre : ∀ z ∈ unitDisk, (G z).re = 0 := by
    intro z hz
    dsimp [G]
    rw [herglotzTransform_re μ 0 hz, hμ z hz, sub_self]
  obtain ⟨a, ha⟩ := hG.eq_const_of_re_eq_const hre isOpen_unitDisk unitDisk_connected
  have h0 := ha 0 (by simp [unitDisk])
  have hmass : μ.real univ = (F 0).re := by
    simpa using (hμ 0 (by simp [unitDisk])).symm
  have hval : a = I * ((F 0).im : ℂ) := by
    rw [← h0]
    dsimp [G]
    rw [herglotzTransform_zero]
    apply Complex.ext <;> simp [hmass]
  intro z hz
  have h := ha z hz
  rw [hval] at h
  dsimp [G] at h
  rw [herglotzTransform_eq_integral] at h
  simp only [ofReal_zero, mul_zero, zero_add] at h
  rw [herglotzTransform_eq_integral]
  exact sub_eq_iff_eq_add.mp h

lemma represents_unique {F : ℂ → ℂ} {μ ν : Measure Circle} {c d : ℝ}
    (hμ : Represents F μ c) (hν : Represents F ν d) : μ = ν ∧ c = d := by
  have := hμ.1
  have := hν.1
  constructor
  · apply poissonExtension_injective μ ν
    intro z hz
    rw [← herglotzTransform_re μ c hz, ← herglotzTransform_re ν d hz,
      ← hμ.2.2 z hz, ← hν.2.2 z hz]
  · exact (center_normalization F μ c hμ).1.trans (center_normalization F ν d hν).1.symm

theorem representation : Spec.Representation := by
  intro F hF
  have hu : NonnegativeHarmonic (fun z => (F z).re) := by
    refine ⟨?_, hF.2⟩
    intro z hz
    exact ((hF.1.analyticOnNhd isOpen_unitDisk) z hz).harmonicAt_re
  obtain ⟨μ, hμ, _⟩ := PositiveHarmonic.representation _ hu
  have := hμ.1
  have hrep : Represents F μ (F 0).im :=
    ⟨hμ.1, hμ.2.1, eq_transform_of_re_eq hF.1 μ hμ.2.2.1⟩
  refine ⟨(μ, (F 0).im), hrep, ?_⟩
  rintro ⟨ν, d⟩ hν
  exact Prod.ext (represents_unique hν hrep).1 (represents_unique hν hrep).2

end ExpandedFA.PartIV.Herglotz
