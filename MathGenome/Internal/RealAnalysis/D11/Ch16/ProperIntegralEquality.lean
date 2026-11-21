import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.ProperIntegralEquality
import MathGenome.Internal.RealAnalysis.D11.Ch16.RiemannCriterion
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.StepComparison
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace D11.Ch16.ProperIntegralEquality
open SingleVariableAnalysis.Riemann
open SingleVariableAnalysis.Riemann.Step

local notation "mL" => Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ)
local notation "μL" => Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ)

lemma completed_measurableSet {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet[mL] S := hS.nullMeasurableSet

lemma indicator_const_integrable {S : Set ℝ} (hS : MeasurableSet S)
    (hfin : volume S ≠ ∞) (c : ℝ) :
    MeasureTheory.Integrable (S.indicator (fun _ => c)) μL := by
  apply IntegrableOn.integrable_indicator (μ := μL) _ (completed_measurableSet hS)
  exact integrableOn_const (by exact hfin)

lemma step_value_eq {a b : ℝ} (s : StepData a b) : value s = fun x =>
    (∑ i : Fin s.partition.n,
      (Ioo (s.partition.point i.castSucc) (s.partition.point i.succ)).indicator
        (fun _ => s.constant i) x) +
    ∑ i : Fin (s.partition.n + 1),
      ({s.partition.point i} : Set ℝ).indicator (fun _ => s.node i) x := by
  classical
  funext x
  simp only [value, Set.indicator, mem_singleton_iff]

lemma step_lebesgue_integrable {a b : ℝ} (s : StepData a b) :
    MeasureTheory.Integrable (value s) μL := by
  classical
  rw [step_value_eq]
  change MeasureTheory.Integrable (fun x =>
    (∑ i : Fin s.partition.n,
      (Ioo (s.partition.point i.castSucc) (s.partition.point i.succ)).indicator
        (fun _ => s.constant i) x) +
    ∑ i : Fin (s.partition.n + 1),
      ({s.partition.point i} : Set ℝ).indicator (fun _ => s.node i) x) μL
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    exact indicator_const_integrable measurableSet_Ioo (by simp) _
  · apply integrable_finsetSum
    intro i _
    exact indicator_const_integrable (measurableSet_singleton _) (by simp) _

lemma step_lebesgue_integral {a b : ℝ} (s : StepData a b) :
    (∫ x, value s x ∂μL) = weightedIntegral s := by
  classical
  let u (i : Fin s.partition.n) :=
    (Ioo (s.partition.point i.castSucc) (s.partition.point i.succ)).indicator
      (fun _ => s.constant i)
  let v (i : Fin (s.partition.n + 1)) :=
    ({s.partition.point i} : Set ℝ).indicator (fun _ => s.node i)
  have hu (i) : MeasureTheory.Integrable (u i) μL := by
    dsimp [u]
    exact indicator_const_integrable measurableSet_Ioo (by simp) _
  have hv (i) : MeasureTheory.Integrable (v i) μL := by
    dsimp [v]
    exact indicator_const_integrable (measurableSet_singleton _) (by simp) _
  rw [step_value_eq]
  change (∫ x, (∑ i, u i x) + ∑ i, v i x ∂μL) = _
  rw [integral_add (integrable_finsetSum _ (fun i _ => hu i))
    (integrable_finsetSum _ (fun i _ => hv i)),
    integral_finsetSum _ (fun i _ => hu i), integral_finsetSum _ (fun i _ => hv i)]
  have huval (i : Fin s.partition.n) : (∫ x, u i x ∂μL) =
      s.constant i * cellLength s.partition i := by
    dsimp [u]
    rw [integral_indicator_const _ (completed_measurableSet measurableSet_Ioo)]
    change (volume (Ioo _ _)).toReal * _ = _
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (s.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le)]
    exact mul_comm _ _
  have hvval (i : Fin (s.partition.n + 1)) : (∫ x, v i x ∂μL) = 0 := by
    dsimp [v]
    rw [integral_indicator_const _ (completed_measurableSet (measurableSet_singleton _))]
    change (volume {_}).toReal * _ = 0
    simp
  simp_rw [huval, hvval]
  simp only [Finset.sum_const_zero, add_zero]
  rfl

lemma step_zero_off_interval {a b : ℝ} (s : StepData a b) {x : ℝ}
    (hx : x ∉ Icc a b) : value s x = 0 := by
  classical
  have ho (i : Fin s.partition.n) :
      x ∉ Ioo (s.partition.point i.castSucc) (s.partition.point i.succ) := by
    intro hi
    exact hx (cell_subset_interval s.partition i ⟨hi.1.le, hi.2.le⟩)
  have hn (i : Fin (s.partition.n + 1)) : x ≠ s.partition.point i := by
    intro hi
    apply hx
    rw [hi]
    exact ⟨by simpa only [s.partition.first] using
      s.partition.strictMono.monotone (Fin.zero_le i),
      by simpa only [s.partition.last] using
        s.partition.strictMono.monotone (Fin.le_last i)⟩
  simp [value, ho, hn]

lemma real_indicator_measurable (f : ℝ → ℝ) {a b : ℝ}
    (hR : RealIntegrable f a b) :
    @Measurable ℝ ℝ mL (borel ℝ) ((Icc a b).indicator f) := by
  rcases hR.ordered.eq_or_lt with h | h
  · subst b
    have heq : (Icc a a).indicator f =
        ({a} : Set ℝ).indicator (fun _ => f a) := by
      ext x
      by_cases hx : x = a <;> simp [hx]
    rw [heq]
    exact measurable_const.indicator (completed_measurableSet (measurableSet_singleton a))
  · exact D11.Ch16.RiemannCriterion.representative_measurable f a b h hR

/-- Boundedness and the finite interval give absolute integrability first. -/
lemma real_indicator_integrable (f : ℝ → ℝ) {a b : ℝ}
    (hR : RealIntegrable f a b) :
    MeasureTheory.Integrable ((Icc a b).indicator f) μL := by
  obtain ⟨l, hl⟩ := hR.bounded.1
  obtain ⟨u, hu⟩ := hR.bounded.2
  let M := |l| + |u|
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb (x) (hx : x ∈ Icc a b) : ‖f x‖ ≤ M := by
    have hlx := hl (mem_image_of_mem f hx)
    have hux := hu (mem_image_of_mem f hx)
    rw [Real.norm_eq_abs, abs_le]
    dsimp [M]
    constructor
    · linarith [neg_abs_le l, abs_nonneg u]
    · linarith [le_abs_self u, abs_nonneg l]
  have hg := indicator_const_integrable (S := Icc a b) measurableSet_Icc (by simp) M
  apply hg.mono' (real_indicator_measurable f hR).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Icc a b
  · simpa only [indicator_of_mem hx] using hb x hx
  · simp only [indicator_of_notMem hx, norm_zero, le_refl]

/-- Every closed-cell Darboux sum bounds the Lebesgue integral. Endpoint
values are retained in the step data and their integral contributions vanish. -/
lemma lebesgue_darboux_bounds (f : ℝ → ℝ) {a b : ℝ}
    (hR : RealIntegrable f a b) (P : Partition a b) :
    lowerSum f P hR.bounded ≤ (∫ x, (Icc a b).indicator f x ∂μL) ∧
    (∫ x, (Icc a b).indicator f x ∂μL) ≤ upperSum f P hR.bounded := by
  have hI := real_indicator_integrable f hR
  constructor
  · have hs := step_lebesgue_integrable (lowerStep f P hR.bounded)
    have hle : ∀ x, value (lowerStep f P hR.bounded) x ≤ (Icc a b).indicator f x := by
      intro x
      by_cases hx : x ∈ Icc a b
      · simpa only [indicator_of_mem hx] using lowerStep_le f P hR.bounded x hx
      · rw [indicator_of_notMem hx, step_zero_off_interval _ hx]
    have hi := integral_mono hs hI hle
    rwa [step_lebesgue_integral] at hi
  · have hs := step_lebesgue_integrable (upperStep f P hR.bounded)
    have hle : ∀ x, (Icc a b).indicator f x ≤ value (upperStep f P hR.bounded) x := by
      intro x
      by_cases hx : x ∈ Icc a b
      · simpa only [indicator_of_mem hx] using le_upperStep f P hR.bounded x hx
      · rw [indicator_of_notMem hx, step_zero_off_interval _ hx]
    have hi := integral_mono hI hs hle
    rwa [step_lebesgue_integral] at hi

lemma real_integral_eq (f : ℝ → ℝ) {a b : ℝ} (hR : RealIntegrable f a b) :
    realIntegral f hR = ∫ x, (Icc a b).indicator f x ∂μL := by
  have hl : lowerIntegral f hR.ordered hR.bounded ≤
      ∫ x, (Icc a b).indicator f x ∂μL := by
    apply (lowerIntegral_isLUB f hR.ordered hR.bounded).2
    rintro r ⟨P, rfl⟩
    exact (lebesgue_darboux_bounds f hR P).1
  have hu : (∫ x, (Icc a b).indicator f x ∂μL) ≤
      upperIntegral f hR.ordered hR.bounded := by
    apply (upperIntegral_isGLB f hR.ordered hR.bounded).2
    rintro r ⟨P, rfl⟩
    exact (lebesgue_darboux_bounds f hR P).2
  have hc := realIntegral_common_value f hR hR.ordered hR.bounded
  exact le_antisymm (hc.1.le.trans hl) (hu.trans hc.2.ge)

theorem real_proper_equality :
    Specs.D11.Ch16.ProperIntegralEquality.real_proper_equality := by
  intro f a b hR
  have hm := real_indicator_measurable f hR
  have hi := real_indicator_integrable f hR
  have hL := (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff ℝ ℝ mL _
    (borel ℝ) inferInstance μL ((Icc a b).indicator f)).mpr ⟨hm, hi⟩
  exact ⟨hL, real_integral_eq f hR⟩

theorem complex_proper_equality :
    Specs.D11.Ch16.ProperIntegralEquality.complex_proper_equality := by
  intro f a b hR
  obtain ⟨hr, er⟩ := real_proper_equality (fun x => (f x).re) a b hR.1
  obtain ⟨hi, ei⟩ := real_proper_equality (fun x => (f x).im) a b hR.2
  have hRe : (fun x => ((Icc a b).indicator f x).re) =
      (Icc a b).indicator (fun x => (f x).re) := by
    ext x
    by_cases hx : x ∈ Icc a b <;> simp [hx]
  have hIm : (fun x => ((Icc a b).indicator f x).im) =
      (Icc a b).indicator (fun x => (f x).im) := by
    ext x
    by_cases hx : x ∈ Icc a b <;> simp [hx]
  have hL := (@D11.Ch06.ScalarIntegral.complex_integrable_iff_coordinates ℝ mL
    μL ((Icc a b).indicator f)).mpr
      ⟨by simpa only [hRe] using hr, by simpa only [hIm] using hi⟩
  refine ⟨hL, ?_⟩
  have hint := (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff ℝ ℂ mL _
    (borel ℂ) inferInstance μL ((Icc a b).indicator f)).mp hL |>.2
  have heq : (∫ x, (Icc a b).indicator f x ∂μL) =
      ((∫ x, (Icc a b).indicator (fun x => (f x).re) x ∂μL : ℝ) : ℂ) +
      ((∫ x, (Icc a b).indicator (fun x => (f x).im) x ∂μL : ℝ) : ℂ) * Complex.I := by
    simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
      RCLike.I_to_complex, RCLike.ofReal_eq_complex_ofReal, hRe, hIm]
      using (@integral_re_add_im ℝ mL μL ℂ inferInstance ((Icc a b).indicator f) hint).symm
  apply Eq.trans _ heq.symm
  exact congrArg₂ (fun r i : ℝ => (r : ℂ) + (i : ℂ) * Complex.I) er ei

theorem real_degenerate : Specs.D11.Ch16.ProperIntegralEquality.real_degenerate := by
  intro f a
  let hR := realIntegrable_degenerate f a
  obtain ⟨hL, heq⟩ := real_proper_equality f a a hR
  have hz := realIntegral_degenerate f a hR
  exact ⟨hR, hL, hz, heq.symm.trans hz⟩

theorem complex_degenerate : Specs.D11.Ch16.ProperIntegralEquality.complex_degenerate := by
  intro f a
  let hR : ComplexIntegrable f a a :=
    ⟨realIntegrable_degenerate _ a, realIntegrable_degenerate _ a⟩
  obtain ⟨hL, heq⟩ := complex_proper_equality f a a hR
  have hz : complexIntegral f hR = 0 := by
    apply Complex.ext
    · exact (complexIntegral_components f hR).1.trans (realIntegral_degenerate _ a hR.1)
    · exact (complexIntegral_components f hR).2.trans (realIntegral_degenerate _ a hR.2)
  exact ⟨hR, hL, hz, heq.symm.trans hz⟩

end D11.Ch16.ProperIntegralEquality
