import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilitySmallSets

/-! Conditions (1) and (2) of Theorem 1.10 of the source. The subtype `H`
indexes the entire family, including the empty family. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

universe u v

namespace ProbabilityFoundations.Ch01

variable {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]

private theorem cutoff_norm_eq (μ : Measure S) (f : S → E)
    (hf : AEStronglyMeasurable f μ) (C : ℝ≥0) :
    eLpNorm ({x | C ≤ ‖f x‖₊}.indicator f) 1 μ =
      ∫⁻ x in {x | (C : ℝ) ≤ ‖f x‖}, ‖f x‖ₑ ∂μ := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (nullMeasurableSet_le aemeasurable_const hf.nnnorm.aemeasurable),
    eLpNorm_one_eq_lintegral_enorm hf.restrict]
  rfl

/-- The source's strict-tail formulation equals Mathlib's formulation for
an arbitrary family, without a countability or nonemptiness assumption. -/
theorem sourceUniformIntegrable_iff_uniformIntegrable
    (μ : Measure S) [IsFiniteMeasure μ] (H : Set (S → E)) :
    SourceUniformIntegrable μ H ↔
      UniformIntegrable (fun f : H => (f : S → E)) 1 μ := by
  constructor
  · rintro ⟨hH, htail⟩
    apply uniformIntegrable_of le_rfl ENNReal.one_ne_top
      (fun f : H => (hH f f.property).aestronglyMeasurable)
    intro ε hε
    obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp htail ε hε
    let C : ℝ≥0 := ⟨max R 0 + 1, by positivity⟩
    refine ⟨C, fun f => ?_⟩
    rw [cutoff_norm_eq μ (f : S → E) (hH f f.property).aestronglyMeasurable C]
    calc
      (∫⁻ x in {x | (C : ℝ) ≤ ‖(f : S → E) x‖}, ‖(f : S → E) x‖ₑ ∂μ) ≤ tailIntegral μ (f : S → E) R := by
        apply lintegral_mono_set
        intro x hx
        have hRC : R < (C : ℝ) :=
          (le_max_left R 0).trans_lt (lt_add_one (max R 0))
        exact hRC.trans_le hx
      _ ≤ uniformTailIntegral μ H R := le_iSup₂ (f := fun (g : S → E) (_ : g ∈ H) => tailIntegral μ g R) (f : S → E) f.property
      _ ≤ ε := hR R le_rfl
  · intro h
    refine ⟨fun f hf => memLp_one_iff_integrable.mp (h.memLp ⟨f, hf⟩), ?_⟩
    apply ENNReal.tendsto_atTop_zero.mpr
    intro ε hε
    obtain ⟨C, hC⟩ := h.spec one_ne_zero ENNReal.one_ne_top hε
    refine ⟨(C : ℝ), fun R hR => ?_⟩
    apply iSup₂_le
    intro f hf
    calc
      tailIntegral μ f R ≤ ∫⁻ x in {x | (C : ℝ) ≤ ‖f x‖}, ‖f x‖ₑ ∂μ := by
        exact lintegral_mono_set (fun x hx => hR.trans hx.le)
      _ = eLpNorm ({x | C ≤ ‖f x‖₊}.indicator f) 1 μ :=
        (cutoff_norm_eq μ f (h.aestronglyMeasurable ⟨f, hf⟩) C).symm
      _ ≤ ε := hC ⟨f, hf⟩

/-- Uniform absolute continuity and boundedness, expressed with actual
integrals and real thresholds. -/
private theorem uniformIntegrable_iff_bounded_small_sets
    (μ : Measure S) (H : Set (S → E)) (hH : ∀ f ∈ H, Integrable f μ) :
    UniformIntegrable (fun f : H => (f : S → E)) 1 μ ↔
      (∃ C : ℝ, ∀ f ∈ H, l1Norm μ f ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ A : Set S, MeasurableSet A → μ A < ENNReal.ofReal δ →
          (⨆ f ∈ H, ∫⁻ x in A, ‖f x‖ₑ ∂μ) < ENNReal.ofReal ε) := by
  constructor
  · intro h
    constructor
    · obtain ⟨C, hC⟩ := h.2
      refine ⟨C, fun f hf => ?_⟩
      apply ENNReal.ofReal_le_coe.mp
      change ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) ≤ (C : ℝ≥0∞)
      rw [ofReal_integral_norm_eq_lintegral_enorm (hH f hf),
        ← eLpNorm_one_eq_lintegral_enorm (hH f hf).aestronglyMeasurable]
      exact hC ⟨f, hf⟩
    · intro ε hε
      obtain ⟨δ, hδ, hsmall⟩ := unifIntegrable_iff'.mp h.1
        (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
      obtain ⟨d, hd, hdδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
      refine ⟨d, by exact_mod_cast hd, fun A hA hμA => ?_⟩
      have hbound : (⨆ f ∈ H, ∫⁻ x in A, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal (ε / 2) := by
        apply iSup₂_le
        intro f hf
        rw [← eLpNorm_one_eq_lintegral_enorm (hH f hf).aestronglyMeasurable.restrict]
        apply hsmall ⟨f, hf⟩ A hA
        exact (hμA.trans (by simpa using hdδ)).le
      exact hbound.trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (half_lt_self hε))
  · rintro ⟨⟨C, hC⟩, hsmall⟩
    constructor
    · apply unifIntegrable_iff'.mpr
      intro ε hε
      obtain ⟨e, he, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
      have hepos : 0 < (e : ℝ) := by exact_mod_cast he
      obtain ⟨δ, hδ, hδsmall⟩ := hsmall e hepos
      refine ⟨ENNReal.ofReal (δ / 2), ENNReal.ofReal_pos.mpr (half_pos hδ), ?_⟩
      intro f A hA hμA
      rw [eLpNorm_one_eq_lintegral_enorm (hH f f.property).aestronglyMeasurable.restrict]
      have hμA' : μ A < ENNReal.ofReal δ :=
        hμA.trans_lt (ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr (half_lt_self hδ))
      exact (le_iSup₂ (f := fun (g : S → E) (_ : g ∈ H) => ∫⁻ x in A, ‖g x‖ₑ ∂μ) (f : S → E) f.property).trans
        ((hδsmall A hA hμA').trans (by simpa using heε)).le
    · refine ⟨Real.toNNReal C, fun f => ?_⟩
      rw [eLpNorm_one_eq_lintegral_enorm (hH f f.property).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hH f f.property)]
      exact ENNReal.ofReal_le_ofReal (hC f f.property)

/-- Conditions (1) and (2) in the source, for every family in L¹ on a finite
measure space. Both constants are uniform in the entire family. -/
theorem sourceUniformIntegrable_iff_bounded_small_sets
    (μ : Measure S) [IsFiniteMeasure μ] (H : Set (S → E))
    (hH : ∀ f ∈ H, Integrable f μ) :
    SourceUniformIntegrable μ H ↔
      (∃ C : ℝ, ∀ f ∈ H, l1Norm μ f ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ A : Set S, MeasurableSet A → μ A < ENNReal.ofReal δ →
          (⨆ f ∈ H, ∫⁻ x in A, ‖f x‖ₑ ∂μ) < ENNReal.ofReal ε) := by
  exact (sourceUniformIntegrable_iff_uniformIntegrable μ H).trans
    (uniformIntegrable_iff_bounded_small_sets μ H hH)

end ProbabilityFoundations.Ch01
