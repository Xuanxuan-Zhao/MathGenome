import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.DominationCounterexamples
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! The two examples of paper.tex:2060–2070, on completed Lebesgue measure.
Positive paper indices are represented by `n+1`. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace D11.Ch06.DominationCounterexamples
open ScalarIntegral
namespace S
export Specs.D11.Ch06.DominationCounterexamples
  (lebesgue intervalMeasure openUnitInterval Interval intervalDomainMeasure)
end S
open S

def spreading : ℕ → ℝ → ℝ :=
  Specs.D11.Ch06.DominationCounterexamples.spreading_value

def concentrating : ℕ → ℝ → ℝ :=
  Specs.D11.Ch06.DominationCounterexamples.concentrating_value

private lemma interval_measurable (a b : ℝ) :
    @MeasurableSet (NullMeasurableSpace ℝ volume) _ (Ioo a b : Set ℝ) :=
  (measurableSet_Ioo (a := a) (b := b)).nullMeasurableSet

private lemma interval_volume (a b : ℝ) :
    lebesgue (Ioo a b : Set ℝ) = ENNReal.ofReal (b - a) := Real.volume_Ioo

private lemma pos_index (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity

private lemma reciprocal_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem domain_masses : Specs.D11.Ch06.DominationCounterexamples.domain_masses := by
  constructor
  · exact Real.volume_univ
  · change (lebesgue.restrict openUnitInterval) univ = 1
    erw [Measure.restrict_apply_univ, interval_volume]
    norm_num [openUnitInterval]

private instance : IsFiniteMeasure intervalMeasure :=
  ⟨by rw [domain_masses.2]; exact ENNReal.one_lt_top⟩

private lemma spreading_measurable (n : ℕ) :
    @Measurable (NullMeasurableSpace ℝ volume) ℝ _ _ (spreading n) := by
  exact measurable_const.indicator (interval_measurable 0 ((n : ℝ) + 1))

private lemma concentrating_measurable (n : ℕ) :
    @Measurable (NullMeasurableSpace ℝ volume) ℝ _ _ (concentrating n) := by
  exact measurable_const.indicator (interval_measurable 0 ((n : ℝ) + 1)⁻¹)

theorem spreading_integrable :
    Specs.D11.Ch06.DominationCounterexamples.spreading_integrable := by
  intro n
  apply (scalarIntegrable_iff lebesgue (spreading n)).mpr
  refine ⟨spreading_measurable n, ?_⟩
  exact (integrable_indicator_iff (interval_measurable 0 ((n : ℝ) + 1))).mpr
    (integrableOn_const (by simp [interval_volume]))

private lemma spreading_bound (n : ℕ) (x : ℝ) :
    |spreading n x| ≤ ((n : ℝ) + 1)⁻¹ := by
  by_cases hx : x ∈ Ioo 0 ((n : ℝ) + 1)
  · simp [spreading, Specs.D11.Ch06.DominationCounterexamples.spreading_value,
      hx, abs_of_pos (inv_pos.mpr (pos_index n))]
  · simp [spreading, Specs.D11.Ch06.DominationCounterexamples.spreading_value, hx,
      le_of_lt (inv_pos.mpr (pos_index n))]

theorem spreading_sup : Specs.D11.Ch06.DominationCounterexamples.spreading_sup := by
  intro n
  apply le_antisymm (ciSup_le (spreading_bound n))
  have hx : ((n : ℝ) + 1) / 2 ∈ Ioo 0 ((n : ℝ) + 1) := by
    constructor <;> linarith [pos_index n]
  calc
    ((n : ℝ) + 1)⁻¹ = |spreading n (((n : ℝ) + 1) / 2)| := by
      simp [spreading, Specs.D11.Ch06.DominationCounterexamples.spreading_value,
        hx, abs_of_pos (inv_pos.mpr (pos_index n))]
    _ ≤ ⨆ x : ℝ, |spreading n x| :=
      le_ciSup ⟨_, fun y hy => by obtain ⟨x, rfl⟩ := hy; exact spreading_bound n x⟩ _

theorem spreading_uniform :
    Specs.D11.Ch06.DominationCounterexamples.spreading_uniform := by
  change TendstoUniformly spreading (fun _ => 0) atTop
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [reciprocal_tendsto.eventually (gt_mem_nhds hε)] with n hn x
  simpa only [Real.dist_eq, zero_sub, abs_neg] using (spreading_bound n x).trans_lt hn

theorem spreading_integral :
    Specs.D11.Ch06.DominationCounterexamples.spreading_integral := by
  intro n _
  change (∫ x, spreading n x ∂lebesgue) = 1
  erw [spreading, Specs.D11.Ch06.DominationCounterexamples.spreading_value,
    integral_indicator_const _ (interval_measurable _ _)]
  simp [Measure.real, interval_volume, ENNReal.toReal_ofReal (le_of_lt (pos_index n)),
    mul_inv_cancel₀ (ne_of_gt (pos_index n))]

private lemma integral_one_not_tendsto_zero {μ : Measure (NullMeasurableSpace ℝ volume)}
    (F : ℕ → ℝ → ℝ) (h : ∀ n, ∫ x, F n x ∂μ = 1) :
    ¬Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
  simp_rw [h]
  intro hc
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  exact one_ne_zero this

theorem spreading_integrals_not_tendsto_zero :
    Specs.D11.Ch06.DominationCounterexamples.spreading_integrals_not_tendsto_zero := by
  intro h
  exact integral_one_not_tendsto_zero spreading (fun n => spreading_integral n (h n))

theorem concentrating_integrable :
    Specs.D11.Ch06.DominationCounterexamples.concentrating_integrable := by
  intro n
  apply (scalarIntegrable_iff intervalMeasure (concentrating n)).mpr
  refine ⟨concentrating_measurable n, ?_⟩
  exact (integrable_indicator_iff (interval_measurable 0 ((n : ℝ) + 1)⁻¹)).mpr
    (integrableOn_const (measure_ne_top _ _))

private lemma concentrating_pointwise_all (x : ℝ) :
    Tendsto (fun n => concentrating n x) atTop (𝓝 0) := by
  by_cases hx : 0 < x
  · apply tendsto_const_nhds.congr'
    filter_upwards [reciprocal_tendsto.eventually (gt_mem_nhds hx)] with n hn
    simp [concentrating, Specs.D11.Ch06.DominationCounterexamples.concentrating_value,
      show x ∉ Ioo 0 ((n : ℝ) + 1)⁻¹ from fun h => (not_lt_of_ge hn.le) h.2]
  · have heq : (fun n => concentrating n x) = fun _ => 0 := by
      funext n
      simp [concentrating, Specs.D11.Ch06.DominationCounterexamples.concentrating_value,
        show x ∉ Ioo 0 ((n : ℝ) + 1)⁻¹ from fun h => hx h.1]
    rw [heq]
    exact tendsto_const_nhds

theorem concentrating_pointwise :
    Specs.D11.Ch06.DominationCounterexamples.concentrating_pointwise := by
  intro x _
  exact concentrating_pointwise_all x

private lemma reciprocal_le_one (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
  apply (inv_le_one₀ (pos_index n)).mpr
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem concentrating_integral :
    Specs.D11.Ch06.DominationCounterexamples.concentrating_integral := by
  intro n _
  change (∫ x, concentrating n x ∂intervalMeasure) = 1
  erw [concentrating, Specs.D11.Ch06.DominationCounterexamples.concentrating_value,
    integral_indicator_const _ (interval_measurable _ _)]
  have hs : (Ioo 0 ((n : ℝ) + 1)⁻¹ : Set ℝ) ⊆ openUnitInterval :=
    fun _ hx => ⟨hx.1, hx.2.trans_le (reciprocal_le_one n)⟩
  erw [Measure.real, Measure.restrict_apply (interval_measurable _ _),
    inter_eq_left.mpr hs, interval_volume]
  simp [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (pos_index n))),
    inv_mul_cancel₀ (ne_of_gt (pos_index n))]

theorem concentrating_integrals_not_tendsto_zero :
    Specs.D11.Ch06.DominationCounterexamples.concentrating_integrals_not_tendsto_zero := by
  intro h
  exact integral_one_not_tendsto_zero concentrating (fun n => concentrating_integral n (h n))


private lemma no_dominator_of_integral_one
    (μ : Measure (NullMeasurableSpace ℝ volume)) (F : ℕ → ℝ → ℝ)
    (hFm : ∀ n, @Measurable (NullMeasurableSpace ℝ volume) ℝ _ _ (F n))
    (hlim : ∀ x : ℝ, Tendsto (fun n => F n x) atTop (𝓝 0))
    (hint : ∀ n, ∫ x, F n x ∂μ = 1) :
    ¬∃ g : ℝ → ℝ, scalarIntegrable μ g ∧
      (∀ n, ∀ᵐ x ∂μ, |F n x| ≤ g x) := by
  rintro ⟨g, hg, hb⟩
  have hc := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := F) (f := fun _ => (0 : ℝ)) g
    (fun n => (hFm n).aestronglyMeasurable)
    ((scalarIntegrable_iff μ g).mp hg).2
    (by
      intro n
      filter_upwards [hb n] with x hx
      change |F n x| ≤ g x at hx
      rw [Real.norm_eq_abs]
      exact hx)
    (Eventually.of_forall hlim)
  apply integral_one_not_tendsto_zero F hint
  simpa only [integral_zero] using hc

theorem spreading_no_integrable_dominator :
    Specs.D11.Ch06.DominationCounterexamples.spreading_no_integrable_dominator := by
  rintro ⟨g, hg, _, hb⟩
  exact no_dominator_of_integral_one lebesgue spreading spreading_measurable
    (fun x => (show TendstoUniformly spreading (fun _ => 0) atTop from
      spreading_uniform).tendsto_at x)
    (fun n => spreading_integral n (spreading_integrable n)) ⟨g, hg, hb⟩

theorem concentrating_no_integrable_dominator :
    Specs.D11.Ch06.DominationCounterexamples.concentrating_no_integrable_dominator := by
  rintro ⟨g, hg, _, hb⟩
  exact no_dominator_of_integral_one intervalMeasure concentrating concentrating_measurable
    concentrating_pointwise_all
    (fun n => concentrating_integral n (concentrating_integrable n)) ⟨g, hg, hb⟩


/-- The restriction calculation above also holds on the literal interval type,
with no requirement that a potential dominator be defined elsewhere. -/
theorem concentrating_on_interval :
    Specs.D11.Ch06.DominationCounterexamples.concentrating_on_interval := by
  let F : ℕ → Interval → ℝ := fun n x => concentrating n x.val
  have hI : @MeasurableSet (NullMeasurableSpace ℝ volume) _ openUnitInterval :=
    interval_measurable 0 1
  have hm : ∀ n, Measurable (F n) :=
    fun n => (concentrating_measurable n).comp measurable_subtype_coe
  have hFi : ∀ n, scalarIntegrable intervalDomainMeasure (F n) := by
    intro n
    apply (scalarIntegrable_iff intervalDomainMeasure _).mpr
    refine ⟨hm n, ?_⟩
    exact (integrableOn_iff_comap_subtypeVal hI).mp
      ((scalarIntegrable_iff intervalMeasure _).mp (concentrating_integrable n)).2
  have hint : ∀ n, ∫ x, F n x ∂intervalDomainMeasure = 1 := by
    intro n
    change (∫ x : Interval, concentrating n x.val ∂intervalDomainMeasure) = 1
    erw [integral_subtype_comap hI (concentrating n)]
    exact concentrating_integral n (concentrating_integrable n)
  have hlim : ∀ x : Interval, Tendsto (fun n => F n x) atTop (𝓝 0) :=
    fun x => concentrating_pointwise_all x.val
  have hmass : intervalDomainMeasure univ = 1 := by
    erw [comap_subtype_coe_apply hI lebesgue]
    have heq : (Subtype.val '' (univ : Set Interval)) = openUnitInterval := by
      ext x
      constructor
      · rintro ⟨y, _, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
    rw [heq]
    simpa only [intervalMeasure, Measure.restrict_apply_univ] using domain_masses.2
  refine ⟨hmass, hlim, hFi, hint, ?_, ?_⟩
  · change ¬Tendsto (fun n => ∫ x, F n x ∂intervalDomainMeasure) atTop (𝓝 0)
    simp_rw [hint]
    intro hc
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)
  · rintro ⟨g, hg, _, hb⟩
    have hc := tendsto_integral_of_dominated_convergence
      (μ := intervalDomainMeasure) (F := F) (f := fun _ => (0 : ℝ)) g
      (fun n => (hm n).aestronglyMeasurable)
      ((scalarIntegrable_iff intervalDomainMeasure g).mp hg).2
      (by
        intro n
        filter_upwards [hb n] with x hx
        rw [Real.norm_eq_abs]
        exact hx)
      (Eventually.of_forall hlim)
    simp only [integral_zero] at hc
    simp_rw [hint] at hc
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)

end D11.Ch06.DominationCounterexamples
