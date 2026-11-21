import MathGenome.Internal.RealAnalysis.D11.Ch04.AeCommonException
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.EssentialBounds

/-!
# Ordinary a.e. essential bounds

The source infimum is over finite nonnegative constants, in the complete
lattice `ℝ≥0∞`. The bridge to the library essential supremum is proved below;
in particular neither an empty admissible class nor a zero measure is
interpreted using the conditionally complete infimum of real numbers.
No function measurability is needed for these order statements. Specializing
to measurable real or complex functions gives exactly the source assertions.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

universe u v

namespace D11.Ch04.EssentialBounds

open D11.Ch04.AeCommonException

variable {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]

/-- The source's admissible finite nonnegative bounds. -/
def admissibleBounds (μ : Measure α) (f : α → E) : Set ℝ≥0 :=
  {M | almostEverywhere μ (fun x => ‖f x‖ ≤ (M : ℝ))}

/-- Essential supremum of the absolute value; an empty class has infimum infinity. -/
noncomputable def essentialSupNorm (μ : Measure α) (f : α → E) : ℝ≥0∞ :=
  sInf ((fun M : ℝ≥0 => (M : ℝ≥0∞)) '' admissibleBounds μ f)

def essentiallyBounded (μ : Measure α) (f : α → E) : Prop :=
  essentialSupNorm μ f < ∞

/-- Null modifications preserve the entire admissible class. -/
theorem admissibleBounds_congr (μ : Measure α) (f g : α → E) (h : aeEq μ f g) :
    admissibleBounds μ f = admissibleBounds μ g := by
  have hfg := (aeEq_iff_native μ f g).mp h
  ext M
  change almostEverywhere μ _ ↔ almostEverywhere μ _
  rw [almostEverywhere_iff_native, almostEverywhere_iff_native]
  exact Filter.eventually_congr (hfg.mono fun _ hx => by rw [hx])

theorem essentialSupNorm_congr (μ : Measure α) (f g : α → E) (h : aeEq μ f g) :
    essentialSupNorm μ f = essentialSupNorm μ g := by
  simp only [essentialSupNorm, admissibleBounds_congr μ f g h]

theorem essentialSupNorm_empty (μ : Measure α) (f : α → E)
    (h : admissibleBounds μ f = ∅) : essentialSupNorm μ f = ∞ := by
  simp [essentialSupNorm, h]

/-- The finite-bound infimum equals the native extended-real essential supremum.
If the native value is finite, its a.e. upper-bound property supplies a finite
admissible constant; if it is infinite, the reverse inequality is automatic. -/
theorem essentialSupNorm_eq_native (μ : Measure α) (f : α → E) :
    essentialSupNorm μ f = essSup (fun x => ‖f x‖ₑ) μ := by
  apply le_antisymm
  · by_cases h : essSup (fun x => ‖f x‖ₑ) μ = ∞
    · rw [h]
      exact le_top
    · have ha := ENNReal.ae_le_essSup (μ := μ) (fun x => ‖f x‖ₑ)
      have hb : (essSup (fun x => ‖f x‖ₑ) μ).toNNReal ∈ admissibleBounds μ f := by
        apply (almostEverywhere_iff_native μ _).mpr
        filter_upwards [ha] with x hx
        rw [← ENNReal.coe_toNNReal h] at hx
        exact_mod_cast hx
      have hle := sInf_le (Set.mem_image_of_mem (fun M : ℝ≥0 => (M : ℝ≥0∞)) hb)
      simpa only [essentialSupNorm, ENNReal.coe_toNNReal h] using hle
  · apply le_sInf
    rintro b ⟨M, hM, rfl⟩
    refine essSup_le_of_ae_le _ ?_
    have hM := (almostEverywhere_iff_native μ _).mp hM
    filter_upwards [hM] with x hx
    exact_mod_cast hx

theorem essential_bound_attained (μ : Measure α) (f : α → E)
    (h : essentialSupNorm μ f < ∞) :
    almostEverywhere μ (fun x => ‖f x‖ ≤ (essentialSupNorm μ f).toReal) := by
  apply (almostEverywhere_iff_native μ _).mpr
  have ha := ENNReal.ae_le_essSup (μ := μ) (fun x => ‖f x‖ₑ)
  rw [← essentialSupNorm_eq_native μ f] at ha
  filter_upwards [ha] with x hx
  exact (ENNReal.toReal_mono h.ne hx)

theorem essentialSupNorm_eq_zero_iff (μ : Measure α) (f : α → E) :
    essentialSupNorm μ f = 0 ↔ aeEq μ f (fun _ => 0) := by
  rw [essentialSupNorm_eq_native, ENNReal.essSup_eq_zero_iff, aeEq_iff_native]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact enorm_eq_zero.mp hx
  · intro h
    filter_upwards [h] with x hx
    exact enorm_eq_zero.mpr hx

theorem essentialSupNorm_mono (μ : Measure α) (f g : α → E)
    (h : almostEverywhere μ (fun x => ‖f x‖ ≤ ‖g x‖)) :
    essentialSupNorm μ f ≤ essentialSupNorm μ g := by
  rw [essentialSupNorm_eq_native, essentialSupNorm_eq_native]
  refine essSup_mono_ae ?_
  have h := (almostEverywhere_iff_native μ _).mp h
  filter_upwards [h] with x hx
  exact enorm_le_iff_norm_le.mpr hx

theorem essentialSupNorm_le_iff (μ : Measure α) (f : α → E) (M : ℝ≥0) :
    essentialSupNorm μ f ≤ (M : ℝ≥0∞) ↔ M ∈ admissibleBounds μ f := by
  constructor
  · intro h
    apply (almostEverywhere_iff_native μ _).mpr
    have ha := ENNReal.ae_le_essSup (μ := μ) (fun x => ‖f x‖ₑ)
    rw [← essentialSupNorm_eq_native μ f] at ha
    filter_upwards [ha] with x hx
    exact_mod_cast hx.trans h
  · intro h
    exact sInf_le (Set.mem_image_of_mem (fun M : ℝ≥0 => (M : ℝ≥0∞)) h)

theorem essentiallyBounded_iff (μ : Measure α) (f : α → E) :
    essentiallyBounded μ f ↔ (admissibleBounds μ f).Nonempty := by
  constructor
  · intro h
    refine ⟨(essentialSupNorm μ f).toNNReal, ?_⟩
    apply (essentialSupNorm_le_iff μ f _).mp
    rw [ENNReal.coe_toNNReal h.ne]
  · rintro ⟨M, hM⟩
    exact lt_of_le_of_lt ((essentialSupNorm_le_iff μ f M).mpr hM) ENNReal.coe_lt_top

theorem essentialSupNorm_zero_measure (f : α → E) :
    essentialSupNorm (0 : Measure α) f = 0 := by
  rw [essentialSupNorm_eq_native, essSup_measure_zero]
  rfl

end D11.Ch04.EssentialBounds
