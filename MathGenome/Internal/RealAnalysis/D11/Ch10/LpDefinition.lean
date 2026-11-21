import MathGenome.Internal.RealAnalysis.D11.Ch04.EssentialBounds
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition

/-! Raw finite-power spaces and the ordinary essential-bounded space,
with ordinary measurable representatives, on arbitrary positive measures.
In particular no complete or sigma-finite measure instance is used. -/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u v
noncomputable section
namespace D11.Ch10.LpDefinition
open D11.Ch04.EssentialBounds D11.Ch04.AeCommonException
open D11.Ch05.NonnegativeIntegral

def powerNorm {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (p : ℝ) (f : X → E) : ℝ≥0∞ :=
  (nonnegativeIntegral μ (fun x => ENNReal.ofReal (‖f x‖ ^ p))) ^ (1 / p)

def rawLp {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure X) (p : ℝ) : Set (X → E) :=
  {f | Measurable f ∧ powerNorm μ p f < ∞}

def rawLInfinity {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure X) : Set (X → E) :=
  {f | Measurable f ∧ essentialSupNorm μ f < ∞}

theorem powerNorm_formula : Specs.D11.Ch10.LpDefinition.powerNorm_formula := by
  intro X E _ _ μ p f _
  change powerNorm μ p f = _
  rw [powerNorm, integral_eq_lintegral]

theorem rawLp_iff_finite_integral : Specs.D11.Ch10.LpDefinition.rawLp_iff_finite_integral := by
  intro X E _ _ _ μ p f hp
  change (Measurable f ∧ _ ^ (1 / p) < ∞) ↔ _
  rw [ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hp))]

theorem measurable_strict_level : Specs.D11.Ch10.LpDefinition.measurable_strict_level := by
  intro X E _ _ _ _ f hf M
  exact measurableSet_lt measurable_const hf.norm

private theorem bound_iff_level_null {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X) (f : X → E) (M : ℝ≥0) :
    M ∈ admissibleBounds μ f ↔ μ {x | (M : ℝ) < ‖f x‖} = 0 := by
  change almostEverywhere μ _ ↔ _
  rw [almostEverywhere_iff_native, MeasureTheory.ae_iff]
  simp only [not_le]

theorem essentialSupNorm_level_formula :
    Specs.D11.Ch10.LpDefinition.essentialSupNorm_level_formula := by
  intro X E _ _ _ _ μ f _
  change essentialSupNorm μ f = _
  unfold essentialSupNorm
  congr 2
  ext M
  exact bound_iff_level_null μ f M

theorem infinity_norm_attained : Specs.D11.Ch10.LpDefinition.infinity_norm_attained := by
  intro X E _ _ _ μ f hf
  exact essential_bound_attained μ f hf.2

theorem bounded_measurable_representative :
    Specs.D11.Ch10.LpDefinition.bounded_measurable_representative := by
  intro X E _ _ _ _ μ f hf
  change Measurable f ∧ essentialSupNorm μ f < ∞ at hf
  let a := (essentialSupNorm μ f).toReal
  let N : Set X := {x | a < ‖f x‖}
  have hN : MeasurableSet N := measurableSet_lt measurable_const hf.1.norm
  have ha : ∀ᵐ x ∂μ, ‖f x‖ ≤ a :=
    (almostEverywhere_iff_native μ _).mp (essential_bound_attained μ f hf.2)
  let g : X → E := N.piecewise (fun _ => 0) f
  have hg : Measurable g := measurable_const.piecewise hN hf.1
  have hfg : aeEq μ f g := by
    apply (aeEq_iff_native μ f g).mpr
    filter_upwards [ha] with x hx
    simp [g, N, not_lt.mpr hx]
  have hb : ∀ x, ‖g x‖ ≤ a := by
    intro x
    by_cases hx : x ∈ N
    · simpa only [g, Set.piecewise, ite_eq_left hx, norm_zero] using
        (ENNReal.toReal_nonneg : 0 ≤ (essentialSupNorm μ f).toReal)
    · simpa [g, hx] using (not_lt.mp hx : ‖f x‖ ≤ a)
  have heq : essentialSupNorm μ g = essentialSupNorm μ f :=
    (essentialSupNorm_congr μ f g hfg).symm
  refine ⟨g, hg, hfg, hb, ⟨hg, ?_⟩, heq⟩
  change essentialSupNorm μ g < ∞
  rw [heq]
  exact hf.2

theorem powerNorm_zero_measure : Specs.D11.Ch10.LpDefinition.powerNorm_zero_measure := by
  intro X E _ _ p f hp
  change powerNorm (0 : Measure X) p f = 0
  rw [powerNorm, integral_eq_lintegral, lintegral_zero_measure]
  exact ENNReal.zero_rpow_of_pos (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hp))

theorem rawLp_zero_measure : Specs.D11.Ch10.LpDefinition.rawLp_zero_measure := by
  intro X E _ _ _ p f hp
  change (Measurable f ∧ powerNorm 0 p f < ∞) ↔ Measurable f
  have hz : powerNorm (0 : Measure X) p f = 0 := powerNorm_zero_measure p f hp
  rw [hz]
  simp

theorem rawLInfinity_zero_measure : Specs.D11.Ch10.LpDefinition.rawLInfinity_zero_measure := by
  intro X E _ _ _ f
  change (Measurable f ∧ essentialSupNorm 0 f < ∞) ↔ Measurable f
  rw [essentialSupNorm_zero_measure]
  simp

theorem powerNorm_eq_eLpNorm : Specs.D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm := by
  intro X E _ _ _ _ _ μ p f hp hf
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
    ENNReal.ofReal_ne_top hf.stronglyMeasurable.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  rw [powerNorm_formula μ p f hp]
  congr 2
  funext x
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  simp

theorem essentialSupNorm_eq_eLpNorm :
    Specs.D11.Ch10.LpDefinition.essentialSupNorm_eq_eLpNorm := by
  intro X E _ _ _ _ _ μ f hf
  rw [eLpNorm_exponent_top hf.stronglyMeasurable.aestronglyMeasurable]
  exact essentialSupNorm_eq_native μ f

theorem rawLp_iff_memLp : Specs.D11.Ch10.LpDefinition.rawLp_iff_memLp := by
  intro X E _ _ _ _ _ μ p f hp
  change (Measurable f ∧ powerNorm μ p f < ∞) ↔ Measurable f ∧ MemLp f _ μ
  constructor
  · rintro ⟨hf, hn⟩
    refine ⟨hf, ?_⟩
    change eLpNorm f (ENNReal.ofReal p) μ < ∞
    have h : powerNorm μ p f = eLpNorm f (ENNReal.ofReal p) μ :=
      powerNorm_eq_eLpNorm μ p f hp hf
    rw [← h]
    exact hn
  · rintro ⟨hf, hn⟩
    refine ⟨hf, ?_⟩
    have h : powerNorm μ p f = eLpNorm f (ENNReal.ofReal p) μ :=
      powerNorm_eq_eLpNorm μ p f hp hf
    rw [h]
    exact hn

theorem rawLInfinity_iff_memLp : Specs.D11.Ch10.LpDefinition.rawLInfinity_iff_memLp := by
  intro X E _ _ _ _ _ μ f
  change (Measurable f ∧ essentialSupNorm μ f < ∞) ↔ Measurable f ∧ MemLp f ∞ μ
  constructor
  · rintro ⟨hf, hn⟩
    refine ⟨hf, ?_⟩
    change eLpNorm f ∞ μ < ∞
    have h : essentialSupNorm μ f = eLpNorm f ∞ μ := essentialSupNorm_eq_eLpNorm μ f hf
    rw [← h]
    exact hn
  · rintro ⟨hf, hn⟩
    refine ⟨hf, ?_⟩
    have h : essentialSupNorm μ f = eLpNorm f ∞ μ := essentialSupNorm_eq_eLpNorm μ f hf
    rw [h]
    exact hn

end D11.Ch10.LpDefinition
