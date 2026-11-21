import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UniformIntegrability

/-! Source uniform integrability for arbitrary indexed Banach-valued families.
No codomain measurable space, nonempty index, or separability is assumed. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

universe u v w

namespace P207.Martingale

/-- Extended expectation of the strict norm tail. -/
noncomputable def tailIntegral {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | R < ‖f x‖}, ‖f x‖ₑ ∂μ

/-- Complete-lattice supremum: the empty supremum is zero. -/
noncomputable def uniformTailIntegral {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ) : ℝ≥0∞ :=
  ⨆ i, tailIntegral μ (X i) R

/-- The analogous supremum with non-strict norm cutoffs. -/
noncomputable def nonstrictUniformTailIntegral
    {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ) : ℝ≥0∞ :=
  ⨆ i, ∫⁻ x in {x | R ≤ ‖X i x‖}, ‖X i x‖ₑ ∂μ

/-- The canonical source UI predicate, including the Bochner-integrability
hypothesis on each variable. It includes real and complex Banach spaces. -/
noncomputable def SourceUniformIntegrable
    {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : I → Ω → E) : Prop :=
  (∀ i, Integrable (X i) μ) ∧
    Tendsto (uniformTailIntegral μ X) atTop (𝓝 0)

variable {Ω : Type u} {E : Type v} {I : Type w}
  [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- The extended tail is the actual (integrable) indicator expectation.
Null measurability suffices, including on an uncompleted probability space. -/
theorem tailIntegral_eq_ofReal_integral (μ : Measure Ω) (f : Ω → E)
    (hf : Integrable f μ) (R : ℝ) :
    tailIntegral μ f R =
      ENNReal.ofReal (∫ x, {x | R < ‖f x‖}.indicator (fun x => ‖f x‖) x ∂μ) := by
  rw [integral_indicator₀ (nullMeasurableSet_lt aemeasurable_const
    hf.aestronglyMeasurable.norm.aemeasurable)]
  exact (ofReal_integral_norm_eq_lintegral_enorm hf.restrict).symm

theorem tailIntegral_lt_top (μ : Measure Ω) (f : Ω → E)
    (hf : Integrable f μ) (R : ℝ) : tailIntegral μ f R < ∞ := by
  exact hasFiniteIntegral_iff_enorm.mp hf.restrict.2

theorem uniformTailIntegral_empty [IsEmpty I]
    (μ : Measure Ω) (X : I → Ω → E) (R : ℝ) :
    uniformTailIntegral μ X R = 0 ∧ nonstrictUniformTailIntegral μ X R = 0 := by
  simp [uniformTailIntegral, nonstrictUniformTailIntegral]

theorem sourceUniformIntegrable_empty [IsEmpty I]
    (μ : Measure Ω) (X : I → Ω → E) : SourceUniformIntegrable μ X := by
  refine ⟨fun i => isEmptyElim i, ?_⟩
  simpa only [funext (fun R => (uniformTailIntegral_empty μ X R).1)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- Enlarging each sufficiently large non-strict cutoff slightly makes it
contained in a fixed strict cutoff; the reverse inclusion is immediate. -/
theorem sourceUniformIntegrable_iff_nonstrict
    (μ : Measure Ω) (X : I → Ω → E) :
    SourceUniformIntegrable μ X ↔
      (∀ i, Integrable (X i) μ) ∧
        Tendsto (nonstrictUniformTailIntegral μ X) atTop (𝓝 0) := by
  constructor
  · rintro ⟨hX, ht⟩
    refine ⟨hX, ENNReal.tendsto_atTop_zero.mpr ?_⟩
    intro ε hε
    obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp ht ε hε
    refine ⟨R + 1, fun t ht => ?_⟩
    apply iSup_le
    intro i
    calc
      (∫⁻ x in {x | t ≤ ‖X i x‖}, ‖X i x‖ₑ ∂μ) ≤ tailIntegral μ (X i) R :=
        lintegral_mono_set (fun x hx => (lt_add_one R).trans_le (ht.trans hx))
      _ ≤ uniformTailIntegral μ X R := le_iSup (fun i => tailIntegral μ (X i) R) i
      _ ≤ ε := hR R le_rfl
  · rintro ⟨hX, ht⟩
    refine ⟨hX, ENNReal.tendsto_atTop_zero.mpr ?_⟩
    intro ε hε
    obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp ht ε hε
    refine ⟨R, fun t ht => ?_⟩
    apply iSup_le
    intro i
    calc
      tailIntegral μ (X i) t ≤
          ∫⁻ x in {x | t ≤ ‖X i x‖}, ‖X i x‖ₑ ∂μ :=
        lintegral_mono_set (fun x hx => (show t < ‖X i x‖ from hx).le)
      _ ≤ nonstrictUniformTailIntegral μ X t :=
        le_iSup (fun j => ∫⁻ x in {x | t ≤ ‖X j x‖}, ‖X j x‖ₑ ∂μ) i
      _ ≤ ε := hR t ht

/-- At exponent one Mathlib's cutoff norm is exactly a non-strict norm tail. -/
private theorem cutoff_norm_eq (μ : Measure Ω) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (C : ℝ≥0) :
    eLpNorm ({x | C ≤ ‖f x‖₊}.indicator f) 1 μ =
      ∫⁻ x in {x | (C : ℝ) ≤ ‖f x‖}, ‖f x‖ₑ ∂μ := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (nullMeasurableSet_le aemeasurable_const hf.nnnorm.aemeasurable),
    eLpNorm_one_eq_lintegral_enorm hf.restrict]
  rfl

/-- Bridge for every finite measure, in particular every probability measure. -/
theorem sourceUniformIntegrable_iff_uniformIntegrable
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E) :
    SourceUniformIntegrable μ X ↔ MeasureTheory.UniformIntegrable X 1 μ := by
  constructor
  · rintro ⟨hX, ht⟩
    apply uniformIntegrable_of le_rfl ENNReal.one_ne_top
      (fun i => (hX i).aestronglyMeasurable)
    intro ε hε
    obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp ht ε hε
    let C : ℝ≥0 := ⟨max R 0 + 1, by positivity⟩
    refine ⟨C, fun i => ?_⟩
    rw [cutoff_norm_eq μ (X i) (hX i).aestronglyMeasurable C]
    calc
      (∫⁻ x in {x | (C : ℝ) ≤ ‖X i x‖}, ‖X i x‖ₑ ∂μ) ≤
          tailIntegral μ (X i) R := by
        apply lintegral_mono_set
        intro x hx
        exact ((le_max_left R 0).trans_lt (lt_add_one (max R 0))).trans_le hx
      _ ≤ uniformTailIntegral μ X R := le_iSup (fun j => tailIntegral μ (X j) R) i
      _ ≤ ε := hR R le_rfl
  · intro h
    refine ⟨fun i => memLp_one_iff_integrable.mp (h.memLp i), ?_⟩
    apply ENNReal.tendsto_atTop_zero.mpr
    intro ε hε
    obtain ⟨C, hC⟩ := h.spec one_ne_zero ENNReal.one_ne_top hε
    refine ⟨(C : ℝ), fun R hR => ?_⟩
    apply iSup_le
    intro i
    calc
      tailIntegral μ (X i) R ≤
          ∫⁻ x in {x | (C : ℝ) ≤ ‖X i x‖}, ‖X i x‖ₑ ∂μ :=
        lintegral_mono_set (fun _ hx => hR.trans hx.le)
      _ = eLpNorm ({x | C ≤ ‖X i x‖₊}.indicator (X i)) 1 μ :=
        (cutoff_norm_eq μ (X i) (h.aestronglyMeasurable i) C).symm
      _ ≤ ε := hC i

/-- A genuine finite bound on the extended supremum of all first moments. -/
theorem sourceUniformIntegrable_firstMomentSup_lt_top
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E)
    (h : SourceUniformIntegrable μ X) : (⨆ i, ∫⁻ x, ‖X i x‖ₑ ∂μ) < ∞ := by
  obtain ⟨C, hC⟩ := ((sourceUniformIntegrable_iff_uniformIntegrable μ X).mp h).2
  have hb : (⨆ i, ∫⁻ x, ‖X i x‖ₑ ∂μ) ≤ (C : ℝ≥0∞) := by
    refine iSup_le (fun i => ?_)
    rw [← eLpNorm_one_eq_lintegral_enorm (h.1 i).aestronglyMeasurable]
    exact hC i
  exact hb.trans_lt ENNReal.coe_lt_top

/-- The same conclusion as an ordinary common real first-moment bound.
All integrals are integrable norm expectations, by the predicate's first clause. -/
theorem sourceUniformIntegrable_bounded
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E)
    (h : SourceUniformIntegrable μ X) :
    ∃ C : ℝ≥0, ∀ i, (∫ x, ‖X i x‖ ∂μ) ≤ C := by
  obtain ⟨C, hC⟩ := ((sourceUniformIntegrable_iff_uniformIntegrable μ X).mp h).2
  refine ⟨C, fun i => ?_⟩
  apply ENNReal.ofReal_le_coe.mp
  rw [ofReal_integral_norm_eq_lintegral_enorm (h.1 i),
    ← eLpNorm_one_eq_lintegral_enorm (h.1 i).aestronglyMeasurable]
  exact hC i

end P207.Martingale
