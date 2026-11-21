import MathGenome.Internal.RealAnalysis.D11.Ch21.ModularProperties
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.D11.Ch05.DensityMeasureDomains
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularWeightRadon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set MeasureTheory
open scoped ENNReal

/-! A positive continuous real density preserves precisely the source Radon
class on an arbitrary LCH space. Countable weight bands are used, never a
countable exhaustion of the underlying space by finite-measure sets. -/
namespace D11.Ch21.ModularWeightRadon.WeightedRegularity
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] {μ : Measure X} {f : X → ℝ}

lemma density_le (s : Set X) (hs : MeasurableSet s) (C : ℝ≥0∞)
    (hb : ∀ x ∈ s, ENNReal.ofReal (f x) ≤ C) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) s ≤ C * μ s := by
  rw [withDensity_apply _ hs, ← setLIntegral_const]
  exact setLIntegral_mono measurable_const hb

lemma le_density (s : Set X) (hs : MeasurableSet s) (c : ℝ≥0∞)
    (hb : ∀ x ∈ s, c ≤ ENNReal.ofReal (f x)) :
    c * μ s ≤ μ.withDensity (fun x => ENNReal.ofReal (f x)) s := by
  rw [withDensity_apply _ hs, ← setLIntegral_const]
  exact setLIntegral_mono' hs hb

/-- The countable bands exhaust the space because the weight is positive and finite. -/
def band (f : X → ℝ) (n : ℕ) : Set X :=
  {x | (n + 1 : ℝ)⁻¹ < f x ∧ f x < n + 1}

lemma band_open (hf : Continuous f) (n : ℕ) : IsOpen (band f n) :=
  (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)

lemma band_mono : Monotone (band f) := by
  intro n m h x hx
  have hnm : (n + 1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.add_le_add_right h 1
  exact ⟨(inv_anti₀ (by positivity) hnm).trans_lt hx.1, hx.2.trans_le hnm⟩

lemma band_iUnion (hp : ∀ x, 0 < f x) : (⋃ n, band f n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (max (f x) (f x)⁻¹)
  have hnf : f x < n + 1 := (lt_of_le_of_lt (le_max_left _ _) hn).trans (by linarith)
  have hni : (f x)⁻¹ < n + 1 := (lt_of_le_of_lt (le_max_right _ _) hn).trans (by linarith)
  have hi : (n + 1 : ℝ)⁻¹ < f x := (inv_lt_comm₀ (by positivity) (hp x)).mpr hni
  exact mem_iUnion.mpr ⟨n, hi, hnf⟩

lemma band_lower (n : ℕ) {x : X} (hx : x ∈ band f n) :
    (ENNReal.ofReal (n + 1))⁻¹ ≤ ENNReal.ofReal (f x) := by
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < n + 1)]
  exact ENNReal.ofReal_le_ofReal hx.1.le

lemma band_upper (n : ℕ) {x : X} (hx : x ∈ band f n) :
    ENNReal.ofReal (f x) ≤ ENNReal.ofReal (n + 1) :=
  ENNReal.ofReal_le_ofReal hx.2.le

/-- Compact approximation when the weight has a positive lower bound and a finite upper bound
on an open set. Infinite original measure and finite original measure are treated separately. -/
lemma inner_band [Measure.Regular μ] (hf : Continuous f) (n : ℕ)
    {U : Set X} (hU : IsOpen U) (hUb : U ⊆ band f n) {r : ℝ≥0∞}
    (hr : r < μ.withDensity (fun x => ENNReal.ofReal (f x)) U) :
    ∃ K ⊆ U, IsCompact K ∧ r < μ.withDensity (fun x => ENNReal.ofReal (f x)) K := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let C : ℝ≥0∞ := ENNReal.ofReal (n + 1)
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hCt : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hl (s : Set X) (hs : MeasurableSet s) (hsU : s ⊆ U) :
      C⁻¹ * μ s ≤ ν s :=
    le_density s hs _ (fun x hx => band_lower n (hUb (hsU hx)))
  have hu (s : Set X) (hs : MeasurableSet s) (hsU : s ⊆ U) :
      ν s ≤ C * μ s :=
    density_le s hs _ (fun x hx => band_upper n (hUb (hsU hx)))
  by_cases hμU : μ U = ∞
  · have hrt : r ≠ ∞ := (hr.trans_le le_top).ne
    have ht : C * r < μ U := by
      rw [hμU]
      exact ENNReal.mul_lt_top hCt.lt_top hrt.lt_top
    obtain ⟨K, hKU, hKc, hK⟩ := hU.exists_lt_isCompact ht
    refine ⟨K, hKU, hKc, lt_of_lt_of_le ?_ (hl K hKc.measurableSet hKU)⟩
    calc
      r = C⁻¹ * (C * r) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
      _ < C⁻¹ * μ K := ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hCt)
        (ENNReal.inv_ne_top.mpr hC0) hK
  · obtain ⟨ε, hε, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hr
    have he : (ε : ℝ≥0∞) / C ≠ 0 :=
      (ENNReal.div_pos (by exact_mod_cast hε.ne') hCt).ne'
    obtain ⟨K, hKU, hKc, hK⟩ :=
      hU.measurableSet.exists_isCompact_sdiff_lt hμU he
    have hdiff : ν (U \ K) < ε := by
      apply lt_of_le_of_lt (hu _ (hU.measurableSet.diff hKc.measurableSet) sdiff_subset)
      calc
        C * μ (U \ K) < C * ((ε : ℝ≥0∞) / C) := ENNReal.mul_lt_mul_right hC0 hCt hK
        _ = ε := ENNReal.mul_div_cancel hC0 hCt
    refine ⟨K, hKU, hKc, ?_⟩
    by_contra hh
    have hk : ν K ≤ r := le_of_not_gt hh
    have hdecomp : ν U = ν K + ν (U \ K) :=
      by simpa only [inter_eq_right.mpr hKU, add_comm] using
        (measure_sdiff_add_inter (μ := ν) U hKc.measurableSet).symm
    have hsmall : ν U < r + ε := by
      rw [hdecomp]
      calc
        ν K + ν (U \ K) ≤ r + ν (U \ K) := add_le_add hk le_rfl
        _ < r + ε := (ENNReal.add_lt_add_iff_left (a := r) (hr.trans_le le_top).ne).mpr hdiff
    exact (lt_asymm hrε hsmall)

lemma inner_open [Measure.Regular μ] (hf : Continuous f) (hp : ∀ x, 0 < f x) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))).InnerRegularWRT IsCompact IsOpen := by
  intro U hU r hr
  have hmono : Monotone (fun n => U ∩ band f n) := fun n m h =>
    inter_subset_inter_right U (band_mono h)
  have hcov : (⋃ n, U ∩ band f n) = U := by rw [← inter_iUnion, band_iUnion hp, inter_univ]
  rw [← hcov, hmono.measure_iUnion] at hr
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hr
  obtain ⟨K, hK, hKc, hrK⟩ := inner_band hf n (hU.inter (band_open hf n))
    inter_subset_right hn
  exact ⟨K, hK.trans inter_subset_left, hKc, hrK⟩

/-- Outer approximation uses countably many weight bands and a summable error budget.
The comparison is needed only when the weighted mass of A is finite. -/
lemma outer [Measure.Regular μ] (hf : Continuous f) (hp : ∀ x, 0 < f x) :
    Measure.OuterRegular (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  refine ⟨fun A hA r hr => ?_⟩
  have hAt : ν A ≠ ∞ := (hr.trans_le le_top).ne
  have hbm : ∀ n, MeasurableSet (band f n) := fun n => (band_open hf n).measurableSet
  obtain ⟨E, hEm, hEb, hEd, hAE⟩ :
      ∃ E : ℕ → Set X, (∀ n, MeasurableSet (E n)) ∧ (∀ n, E n ⊆ band f n) ∧
        Pairwise (fun n m => Disjoint (E n) (E m)) ∧ A = ⋃ n, E n := by
    refine ⟨fun n => A ∩ disjointed (band f) n,
      fun n => hA.inter (MeasurableSet.disjointed hbm n),
      fun n => inter_subset_right.trans (disjointed_subset _ _),
      (disjoint_disjointed (band f)).mono (fun k l hkl => hkl.mono inf_le_right inf_le_right), ?_⟩
    rw [← inter_iUnion, iUnion_disjointed, band_iUnion hp, inter_univ]
  have hEt (n : ℕ) : ν (E n) ≠ ∞ :=
    ne_top_of_le_ne_top hAt (measure_mono (hAE ▸ subset_iUnion E n))
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' (tsub_pos_iff_lt.mpr hr).ne' ℕ
  rw [lt_tsub_iff_right, add_comm] at hδsum
  have hO : ∀ n, ∃ O ⊇ E n, IsOpen O ∧ ν O < ν (E n) + δ n := by
    intro n
    let C : ℝ≥0∞ := ENNReal.ofReal (n + 1)
    have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hCt : C ≠ ∞ := ENNReal.ofReal_ne_top
    have hEfin : μ (E n) ≠ ∞ := by
      have hl : C⁻¹ * μ (E n) ≤ ν (E n) :=
        le_density (E n) (hEm n) _ (fun x hx => band_lower n (hEb n hx))
      exact (ENNReal.lt_top_of_mul_ne_top_right
        (ne_top_of_le_ne_top (hEt n) hl) (ENNReal.inv_ne_zero.mpr hCt)).ne
    have hdC : δ n / C ≠ 0 := (ENNReal.div_pos (hδ n).ne' hCt).ne'
    obtain ⟨V, hEV, hVo, _, hV⟩ := (hEm n).exists_isOpen_sdiff_lt hEfin hdC
    let O := V ∩ {x | f x < n + 1}
    have hEO : E n ⊆ O := fun x hx => ⟨hEV hx, (hEb n hx).2⟩
    have hOo : IsOpen O := hVo.inter (isOpen_lt hf continuous_const)
    have hdiff : ν (O \ E n) < δ n := by
      calc
        ν (O \ E n) ≤ C * μ (O \ E n) := density_le _ (hOo.measurableSet.diff (hEm n)) _
          (fun x hx => ENNReal.ofReal_le_ofReal hx.1.2.le)
        _ ≤ C * μ (V \ E n) := by
          have hsub : O \ E n ⊆ V \ E n := fun x hx => ⟨hx.1.1, hx.2⟩
          exact mul_le_mul le_rfl (measure_mono (μ := μ) hsub) bot_le bot_le
        _ < C * (δ n / C) := ENNReal.mul_lt_mul_right hC0 hCt hV
        _ = δ n := ENNReal.mul_div_cancel hC0 hCt
    refine ⟨O, hEO, hOo, ?_⟩
    have heq : ν O = ν (E n) + ν (O \ E n) := by
      simpa only [inter_eq_right.mpr hEO, add_comm] using
        (measure_sdiff_add_inter (μ := ν) O (hEm n)).symm
    rw [heq]
    exact (ENNReal.add_lt_add_iff_left (hEt n)).mpr hdiff
  choose O hEO hOo hOlt using hO
  refine ⟨⋃ n, O n, ?_, isOpen_iUnion hOo, ?_⟩
  · rw [hAE]
    exact iUnion_mono hEO
  · calc
      ν (⋃ n, O n) ≤ ∑' n, ν (O n) := measure_iUnion_le _
      _ ≤ ∑' n, (ν (E n) + δ n) := ENNReal.tsum_le_tsum (fun n => (hOlt n).le)
      _ = (∑' n, ν (E n)) + ∑' n, δ n := ENNReal.tsum_add
      _ = ν A + ∑' n, δ n := by rw [← measure_iUnion hEd hEm, ← hAE]
      _ < r := hδsum

lemma regular [Measure.Regular μ] (hf : Continuous f) (hp : ∀ x, 0 < f x) :
    Measure.Regular (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  letI := IsLocallyFiniteMeasure.withDensity_ofReal (μ := μ) hf
  exact { toIsFiniteMeasureOnCompacts := inferInstance
          toOuterRegular := outer hf hp
          innerRegular := inner_open hf hp }
end D11.Ch21.ModularWeightRadon.WeightedRegularity


namespace D11.Ch21.ModularWeightRadon
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

def weight {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)) (x : G) : ℝ :=
  Specs.D11.Ch21.ModularWeightRadon.weight_value μ x

def weightedMeasure {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)) : @Measure G (borel G) :=
  D11.Ch05.DensityMeasureDomains.densityMeasure μ (fun x => ENNReal.ofReal (weight μ x))

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

theorem weightedMeasure_apply (μ : @Measure G (borel G)) (E : Set G)
    (hE : MeasurableSet E) :
    weightedMeasure μ E =
      D11.Ch05.NonnegativeIntegral.nonnegativeIntegral
        (D11.Ch01.ExhaustionRestriction.restrictOnSpace μ E)
        (fun x => ENNReal.ofReal (weight μ x)) := by
  rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  exact withDensity_apply _ hE

variable [T2Space G] [LocallyCompactSpace G]

theorem weight_properties (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    Continuous (weight μ) ∧ ∀ x, 0 < weight μ x := by
  exact ⟨(ModularProperties.continuous μ hμ).comp continuous_inv,
    fun x => ModularProperties.positive μ hμ x⁻¹⟩

open ModularFunction (modularFunction)

lemma weight_mul (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) (x a : G) :
    weight μ (x * a) = (modularFunction μ a)⁻¹ * weight μ x := by
  change modularFunction μ (x * a)⁻¹ = _
  rw [mul_inv_rev, ModularProperties.map_mul μ hμ, ModularProperties.map_inv μ hμ]
  rfl

lemma right_invariant (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ)
    (a : G) (E : Set G) (hE : MeasurableSet E) :
    weightedMeasure μ ((fun x => x * a) '' E) = weightedMeasure μ E := by
  let v : G → ℝ≥0∞ := fun x => ENNReal.ofReal (weight μ x)
  have hv : Measurable v :=
    ((ModularProperties.continuous μ hμ).comp continuous_inv).measurable.ennreal_ofReal
  have ht : Measurable (fun x : G => x * a) := (continuous_id.mul_const a).measurable
  let F : G → ℝ≥0∞ := E.indicator (fun x => v (x * a))
  have hF : Measurable F := (hv.comp ht).indicator hE
  have hid (x : G) : F (x * a⁻¹) =
      ((fun y => y * a) '' E).indicator v x := by
    have hx : x * a⁻¹ ∈ E ↔ x ∈ (fun y => y * a) '' E := by
      constructor
      · intro h; exact ⟨x * a⁻¹, h, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    by_cases h : x * a⁻¹ ∈ E
    · simp only [F, indicator_of_mem h, indicator_of_mem (hx.mp h), inv_mul_cancel_right]
    · simp only [F, indicator_of_notMem h, indicator_of_notMem (not_iff_not.mpr hx |>.mp h)]
  have hEa : MeasurableSet ((fun x => x * a) '' E) :=
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableSet_image.mpr hE
  have htrans := ModularProperties.nonnegative_translation μ hμ a F hF
  simp only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral] at htrans
  simp_rw [hid] at htrans
  rw [lintegral_indicator hEa] at htrans
  change (μ.withDensity v) ((fun x => x * a) '' E) = (μ.withDensity v) E
  rw [withDensity_apply _ hEa, htrans, withDensity_apply _ hE]
  have hw (x : G) : v (x * a) = (ENNReal.ofReal (modularFunction μ a))⁻¹ * v x := by
    dsimp [v]
    rw [weight_mul μ hμ, ENNReal.ofReal_mul (inv_pos.mpr (ModularProperties.positive μ hμ a)).le,
      ENNReal.ofReal_inv_of_pos (ModularProperties.positive μ hμ a)]
  have hFeq : F = fun x => (ENNReal.ofReal (modularFunction μ a))⁻¹ * E.indicator v x := by
    funext x
    by_cases hx : x ∈ E
    · simp [F, hx, hw]
    · simp [F, hx]
  rw [hFeq, lintegral_const_mul _ (hv.indicator hE), lintegral_indicator hE,
    ← mul_assoc, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_pos.mpr (ModularProperties.positive μ hμ a)).ne'
      ENNReal.ofReal_ne_top, one_mul]

/-- Regularity is established directly for the density measure, before any
comparison of this measure with an invariant Haar measure. -/
theorem weightedMeasure_radon (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    D11.Ch18.isRadon (weightedMeasure μ) := by
  let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
  exact (D11.Ch18.isRadon_iff_regular _).mpr
    (WeightedRegularity.regular (weight_properties μ hμ).1 (weight_properties μ hμ).2)

/-- Strict positivity of the density preserves nonzero mass without any
finiteness hypothesis on the original measure. -/
theorem weightedMeasure_nonzero (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    weightedMeasure μ ≠ 0 := by
  have hac : μ ≪ weightedMeasure μ :=
    withDensity_absolutelyContinuous' (weight_properties μ hμ).1.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x =>
        (ENNReal.ofReal_pos.mpr ((weight_properties μ hμ).2 x)).ne'))
  intro heq
  apply hμ.1
  ext E hE
  have hzero : weightedMeasure μ E = 0 := by rw [heq]; rfl
  simpa using hac hzero

/-- The weighted measure satisfies the full source right-Haar definition on
all Borel sets of an arbitrary Hausdorff locally compact group. -/
theorem weightedMeasure_rightHaar (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    isRightHaarMeasure (weightedMeasure μ) :=
  ⟨weightedMeasure_nonzero μ hμ, weightedMeasure_radon μ hμ, right_invariant μ hμ⟩

end
end D11.Ch21.ModularWeightRadon
