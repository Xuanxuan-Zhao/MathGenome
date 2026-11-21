import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuityPartitions
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.TailAndTruncatedMoments
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Portmanteau
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
Portmanteau for arbitrary metric spaces (paper.tex 1473–1514).
The set criteria use Mathlib’s Portmanteau results. For extended-valued
semicontinuous functions, open superlevel sets, the upstream tail formula, and
Fatou give the lower bound; finite translation and negation give the full result.
There is no separability, completeness, tightness, or integrability assumption.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
open Specs.ProbabilityFoundations.Ch06.Portmanteau

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section
variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Closed-set form of Portmanteau on an arbitrary metric space. -/
theorem weaklyConverges_iff_closed (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) :
    WeaklyConverges atTop μs μ ↔ ClosedUpperBound μs μ := by
  constructor
  · intro h F hF
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hF
  · exact tendsto_of_forall_isClosed_limsup_le'

/-- Open-set form of Portmanteau. -/
theorem weaklyConverges_iff_open (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) :
    WeaklyConverges atTop μs μ ↔ OpenLowerBound μs μ := by
  constructor
  · intro h G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hG
  · exact tendsto_of_forall_isOpen_le_liminf_nat'

/-- Convergence on all Borel continuity sets is equivalent to weak convergence. -/
theorem weaklyConverges_iff_continuitySets
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) :
    WeaklyConverges atTop μs μ ↔ ContinuitySetConvergence μs μ := by
  constructor
  · intro h A hA
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hA.2
  · intro h
    apply (weaklyConverges_iff_closed μs μ).mpr
    exact limsup_measure_closed_le_of_forall_tendsto_measure (fun hA hnull => h _ ⟨hA, hnull⟩)

omit [MetricSpace S] [BorelSpace S] in
/-- Layer cake for a nonnegative extended-valued function, including infinity. -/
lemma lintegral_eq_extended_tail (μ : Measure S) [SFinite μ]
    (f : S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ t : ℝ in Ioi 0, μ {x | ENNReal.ofReal t < f x} := by
  simpa using Ch01.lintegral_rpow_eq_tail μ f hf 1 zero_lt_one

/-- Fatou applied to the open superlevel sets of a lower semicontinuous test. -/
lemma lintegral_le_liminf_of_open
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (h : OpenLowerBound μs μ) (f : S → ℝ≥0∞) (hf : LowerSemicontinuous f) :
    (∫⁻ x, f x ∂(μ : Measure S)) ≤
      liminf (fun n => ∫⁻ x, f x ∂(μs n : Measure S)) atTop := by
  simp_rw [lintegral_eq_extended_tail _ f hf.measurable]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioi 0,
        liminf (fun n => (μs n : Measure S) {x | ENNReal.ofReal t < f x}) atTop :=
      lintegral_mono (fun t => h _ (hf.isOpen_preimage _))
    _ ≤ _ := lintegral_liminf_le (fun n => Antitone.measurable
      (fun a b hab => measure_mono (fun x hx =>
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hx)))

/-- Translation by a finite constant is continuous even at infinite values. -/
lemma continuous_ereal_add_real (c : ℝ) :
    Continuous (fun x : EReal => x + (c : EReal)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot c))
    (Or.inr (EReal.coe_ne_top c))).comp
      (continuousAt_id.prodMk continuousAt_const)

omit [MeasurableSpace S] [BorelSpace S] in
lemma lowerSemicontinuous_translate (f : S → EReal) (hf : LowerSemicontinuous f)
    (c : ℝ) : LowerSemicontinuous (fun x => (f x - (c : EReal)).toENNReal) := by
  have ht : LowerSemicontinuous (fun x => f x - (c : EReal)) := by
    simpa only [EReal.coe_neg, sub_eq_add_neg, Function.comp_def] using
      (continuous_ereal_add_real (-c)).comp_lowerSemicontinuous hf
        (fun _ _ h => add_le_add h le_rfl)
  exact EReal.continuous_toENNReal.comp_lowerSemicontinuous ht
    (fun _ _ h => EReal.toENNReal_le_toENNReal h)

omit [MetricSpace S] [BorelSpace S] in
/-- Increasing the real lower bound leaves the extended integral unchanged. -/
lemma lowerIntegral_eq_of_le (μ : ProbabilityMeasure S) (f : S → EReal)
    (c d : ℝ) (hcd : c ≤ d) (hd : ∀ x, (d : EReal) ≤ f x) :
    lowerIntegral μ f c = lowerIntegral μ f d := by
  have hshift : (fun x => (f x - (c : EReal)).toENNReal) =
      fun x => (f x - (d : EReal)).toENNReal + ENNReal.ofReal (d - c) := by
    funext x
    have hdx := hd x
    generalize f x = y at hdx ⊢
    induction y with
    | bot => exact False.elim (not_le_of_gt (EReal.bot_lt_coe d) hdx)
    | top => simp
    | coe r =>
      have hdr : d ≤ r := EReal.coe_le_coe_iff.mp hdx
      simp only [← EReal.coe_sub, EReal.real_coe_toENNReal]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hdr) (sub_nonneg.mpr hcd)]
      congr 1
      exact (sub_add_sub_cancel r d c).symm
  have hconst : (ENNReal.ofReal (d - c) : EReal) = ((d - c : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (sub_nonneg.mpr hcd)]
  unfold lowerIntegral
  rw [hshift, lintegral_add_right _ measurable_const, lintegral_const,
    measure_univ, mul_one, EReal.coe_ennreal_add, hconst]
  calc
    _ = ((c : EReal) + ((d - c : ℝ) : EReal)) +
        ((∫⁻ x, (f x - (d : EReal)).toENNReal ∂(μ : Measure S)) : EReal) := by ac_rfl
    _ = _ := by rw [← EReal.coe_add, add_comm c, sub_add_cancel]

omit [MetricSpace S] [BorelSpace S] in
/-- The extended integral does not depend on which valid real bound is used. -/
theorem lowerIntegral_bound_independent (μ : ProbabilityMeasure S) (f : S → EReal)
    (c d : ℝ) (hc : ∀ x, (c : EReal) ≤ f x) (hd : ∀ x, (d : EReal) ≤ f x) :
    lowerIntegral μ f c = lowerIntegral μ f d := by
  rcases le_total c d with h | h
  · exact lowerIntegral_eq_of_le μ f c d h hd
  · exact (lowerIntegral_eq_of_le μ f d c h hc).symm

omit [MetricSpace S] [BorelSpace S] in
/-- Nonnegative tests use precisely the usual extended nonnegative integral. -/
theorem lowerIntegral_nonnegative (μ : ProbabilityMeasure S) (f : S → ℝ≥0∞) :
    lowerIntegral μ (fun x => (f x : EReal)) 0 =
      ((∫⁻ x, f x ∂(μ : Measure S)) : EReal) := by
  simp only [lowerIntegral, EReal.coe_zero, sub_zero, EReal.toENNReal_coe, zero_add]

omit [MetricSpace S] [BorelSpace S] in
/-- On integrable real tests the extended integral agrees with the real integral. -/
theorem lowerIntegral_integrable (μ : ProbabilityMeasure S) (f : S → ℝ)
    (hf : Integrable f (μ : Measure S)) (c : ℝ) (hc : ∀ x, c ≤ f x) :
    lowerIntegral μ (fun x => (f x : EReal)) c =
      ((∫ x, f x ∂(μ : Measure S) : ℝ) : EReal) := by
  have hsub : Integrable (fun x => f x - c) (μ : Measure S) :=
    hf.sub (integrable_const c)
  have hn : 0 ≤ᵐ[(μ : Measure S)] (fun x => f x - c) :=
    ae_of_all _ (fun x => sub_nonneg.mpr (hc x))
  unfold lowerIntegral
  simp only [← EReal.coe_sub, EReal.real_coe_toENNReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hsub hn,
    EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae hn),
    integral_sub hf (integrable_const c), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [← EReal.coe_add, add_comm c, sub_add_cancel]

/-- The lower semicontinuous integral inequality retains infinite values. -/
theorem weaklyConverges_iff_lowerIntegrals
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) :
    WeaklyConverges atTop μs μ ↔ LowerIntegralBound μs μ := by
  constructor
  · intro h f hf c _hc
    have hlin := lintegral_le_liminf_of_open μs μ
      ((weaklyConverges_iff_open μs μ).mp h) _ (lowerSemicontinuous_translate f hf c)
    let v : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, (f x - (c : EReal)).toENNReal ∂(μs n : Measure S)
    have hmap : ((liminf v atTop : ℝ≥0∞) : EReal) =
        liminf (fun n => (v n : EReal)) atTop :=
      (show Monotone ((↑) : ℝ≥0∞ → EReal) from
        fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h).map_liminf_of_continuousAt
          v continuous_coe_ennreal_ereal.continuousAt
    have hcoe := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hlin
    change _ ≤ ((liminf v atTop : ℝ≥0∞) : EReal) at hcoe
    rw [hmap] at hcoe
    exact (add_le_add (le_refl (c : EReal)) hcoe).trans (by
      simpa [lowerIntegral, Pi.add_def, v] using
        (EReal.le_liminf_add (u := fun _ : ℕ => (c : EReal))
          (v := fun n => (v n : EReal)) (f := atTop)))
  · intro h
    apply (weaklyConverges_iff_open μs μ).mpr
    intro G hG
    have hi := h (G.indicator (fun _ => (1 : EReal)))
      (hG.lowerSemicontinuous_indicator zero_le_one) 0
      (fun x => indicator_nonneg (fun _ _ => zero_le_one) x)
    have he (ν : ProbabilityMeasure S) :
        lowerIntegral ν (G.indicator (fun _ => (1 : EReal))) 0 =
          ((ν : Measure S) G : EReal) := by
      simp only [lowerIntegral, EReal.coe_zero, sub_zero, zero_add]
      have hfun : (fun x => (G.indicator (fun _ => (1 : EReal)) x).toENNReal) =
          G.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext x
        by_cases hx : x ∈ G <;> simp [hx, ← EReal.coe_one]
      rw [hfun, lintegral_indicator_const hG.measurableSet, one_mul]
    simp_rw [he] at hi
    have hmap : ((liminf (fun n => (μs n : Measure S) G) atTop : ℝ≥0∞) : EReal) =
        liminf (fun n => ((μs n : Measure S) G : EReal)) atTop :=
      (show Monotone ((↑) : ℝ≥0∞ → EReal) from
        fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h).map_liminf_of_continuousAt
          _ continuous_coe_ennreal_ereal.continuousAt
    rw [← hmap] at hi
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hi

omit [BorelSpace S] in
/-- Negation exchanges the two extended integral conditions. -/
theorem lowerIntegralBound_iff_upperIntegralBound
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) :
    LowerIntegralBound μs μ ↔ UpperIntegralBound μs μ := by
  constructor
  · intro h f hf c hc
    have hi := h (fun x => -f x)
      (continuous_neg.comp_upperSemicontinuous_antitone hf (fun _ _ h => EReal.neg_le_neg_iff.mpr h))
      (-c) (fun x => by simpa only [EReal.coe_neg] using EReal.neg_le_neg_iff.mpr (hc x))
    change limsup (-(fun n => lowerIntegral (μs n) (fun x => -f x) (-c))) atTop ≤ _
    rw [EReal.limsup_neg]
    exact EReal.neg_le_neg_iff.mpr hi
  · intro h f hf c hc
    have hi := h (fun x => -f x)
      (continuous_neg.comp_lowerSemicontinuous_antitone hf (fun _ _ h => EReal.neg_le_neg_iff.mpr h))
      (-c) (fun x => by simpa only [EReal.coe_neg] using EReal.neg_le_neg_iff.mpr (hc x))
    simp only [upperIntegral, neg_neg] at hi
    change limsup (-(fun n => lowerIntegral (μs n) f c)) atTop ≤ -lowerIntegral μ f c at hi
    rw [EReal.limsup_neg] at hi
    exact EReal.neg_le_neg_iff.mp hi

/-- Upper semicontinuous tests may have value negative infinity. -/
theorem weaklyConverges_iff_upperIntegrals
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) :
    WeaklyConverges atTop μs μ ↔ UpperIntegralBound μs μ :=
  (weaklyConverges_iff_lowerIntegrals μs μ).trans
    (lowerIntegralBound_iff_upperIntegralBound μs μ)

end
end ProbabilityFoundations.Ch06
