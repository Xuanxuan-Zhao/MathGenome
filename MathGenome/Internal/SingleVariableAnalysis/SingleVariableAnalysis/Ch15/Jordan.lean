import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Jordan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Monotone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Jordan decomposition of real functions, using strict endpoint partitions.
No continuity or measure theoretic decomposition is assumed. -/
namespace SingleVariableAnalysis.BV

noncomputable abbrev variationFunction :=
  Specs.SingleVariableAnalysis.Ch15.Jordan.variationFunctionValue
noncomputable abbrev positiveComponent :=
  Specs.SingleVariableAnalysis.Ch15.Jordan.positiveComponentValue
noncomputable abbrev negativeComponent :=
  Specs.SingleVariableAnalysis.Ch15.Jordan.negativeComponentValue

/-- Restricting an interval preserves finite variation. -/
theorem hasBoundedVariation_subinterval {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) {a b x y : ℝ} (hf : HasBoundedVariation f a b)
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) : HasBoundedVariation f x y := by
  have hab : a ≤ b := hax.trans (hxy.trans hyb)
  have hle : totalVariation f x y ≤ totalVariation f a b := by
    change Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue f x y ≤
      Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue f a b
    rw [totalVariation_eq_eVariationOn f hxy, totalVariation_eq_eVariationOn f hab]
    exact eVariationOn.mono f (Set.Icc_subset_Icc hax hyb)
  exact hle.trans_lt hf

/-- Convert additivity to real values only after proving finiteness of both terms. -/
theorem variationFunction_increment :
    Specs.SingleVariableAnalysis.Ch15.Jordan.variationIncrement := by
  intro f a b _hab hf x y hx hy hxy
  have hax := hasBoundedVariation_subinterval f hf le_rfl hx.1 hx.2
  have hxyfin := hasBoundedVariation_subinterval f hf hx.1 hxy hy.2
  change (totalVariation f a y).toReal - (totalVariation f a x).toReal =
    (totalVariation f x y).toReal
  simp only [totalVariation]
  rw [totalVariation_additive f hx.1 hxy,
    ENNReal.toReal_add (ne_of_lt hax) (ne_of_lt hxyfin)]
  ring

theorem abs_sub_le_variationFunction_increment :
    Specs.SingleVariableAnalysis.Ch15.Jordan.absoluteIncrementBound := by
  intro f a b hab hf x y hx hy hxy
  rw [variationFunction_increment f hab hf hx hy hxy]
  have hxyfin := hasBoundedVariation_subinterval f hf hx.1 hxy hy.2
  simpa only [Real.norm_eq_abs] using
    norm_sub_le_totalVariation f hxy hxyfin ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩

/-- Both signed increments are bounded by the variation increment, so both
half-sum components are nondecreasing. -/
theorem jordan_canonical : Specs.SingleVariableAnalysis.Ch15.Jordan.canonicalDecomposition := by
  intro f a b hab hf
  have hp : MonotoneOn (positiveComponent f a) (Set.Icc a b) := by
    intro x hx y hy hxy
    have h := abs_sub_le_variationFunction_increment f hab hf hx hy hxy
    have hl := (abs_le.mp h).1
    change (variationFunction f a x + f x - f a) / 2 ≤
      (variationFunction f a y + f y - f a) / 2
    linarith
  have hq : MonotoneOn (negativeComponent f a) (Set.Icc a b) := by
    intro x hx y hy hxy
    have h := abs_sub_le_variationFunction_increment f hab hf hx hy hxy
    have hu := (abs_le.mp h).2
    change (variationFunction f a x - f x + f a) / 2 ≤
      (variationFunction f a y - f y + f a) / 2
    linarith
  refine ⟨hp, hq, ?_, ?_, ?_⟩
  · intro x _hx
    change f x = f a + (variationFunction f a x + f x - f a) / 2 -
      (variationFunction f a x - f x + f a) / 2
    ring
  · change ((totalVariation f a a).toReal + f a - f a) / 2 = 0
    simp only [totalVariation]
    rw [totalVariation_degenerate f a]
    simp
  · change ((totalVariation f a a).toReal - f a + f a) / 2 = 0
    simp only [totalVariation]
    rw [totalVariation_degenerate f a]
    simp

/-- Differences of nondecreasing functions have finite variation on the closed
interval. Equality is required only on that interval. -/
theorem hasBoundedVariation_of_monotone_difference (f g h : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hg : MonotoneOn g (Set.Icc a b))
    (hh : MonotoneOn h (Set.Icc a b))
    (heq : ∀ x ∈ Set.Icc a b, f x = g x - h x) : HasBoundedVariation f a b := by
  have hgbv := (hasBoundedVariation_of_monotone g hab (Or.inl hg)).1
  have hhbv := (hasBoundedVariation_of_monotone h hab (Or.inl hh)).1
  have hneg := (totalVariation_smul_finite (-1 : ℝ) h hab hhbv).1
  have hsub : HasBoundedVariation (fun x => g x - h x) a b := by
    simpa only [neg_one_smul, sub_eq_add_neg] using hasBoundedVariation_add hab hgbv hneg
  change totalVariation f a b < ⊤
  simp only [totalVariation]
  rw [interval_congruence heq]
  exact hsub

theorem jordan_iff : Specs.SingleVariableAnalysis.Ch15.Jordan.jordanIff := by
  intro f a b hab
  constructor
  · intro hf
    obtain ⟨hp, hq, heq, _⟩ := jordan_canonical f hab hf
    refine ⟨fun x => f a + positiveComponent f a x, negativeComponent f a,
      ?_, hq, ?_⟩
    · intro x hx y hy hxy
      exact add_le_add le_rfl (hp hx hy hxy)
    · exact heq
  · rintro ⟨g, h, hg, hh, heq⟩
    exact hasBoundedVariation_of_monotone_difference f g h hab hg hh heq

end SingleVariableAnalysis.BV
