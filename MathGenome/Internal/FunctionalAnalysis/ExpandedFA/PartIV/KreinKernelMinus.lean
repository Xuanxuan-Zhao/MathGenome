import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinKernelMinus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinSpectralKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace ExpandedFA.PartIV.KreinKernelMinus
open KreinSpectralKernel

/-- The apparent singularity at zero is exactly removable, with the value
specified in the manuscript. -/
theorem compensated_eq (ξ s : ℝ) :
    Spec.compensated ξ s = -2 * KreinSolutions.Specs.SValue ξ (s / 2) ^ 2 := by
  by_cases hz : ξ = 0
  · subst ξ
    simp [Spec.compensated, KreinSolutions.Specs.SValue]
    ring
  · have h := KreinSolutions.additionDifference ξ (s / 2) (s / 2)
    have hzero := (KreinSolutions.initialData ξ).1
    have hadd : s / 2 + s / 2 = s := by ring
    rw [sub_self, hzero, hadd] at h
    simp only [Spec.compensated, hz, ite_false]
    apply (div_eq_iff hz).2
    nlinarith [h]

theorem compensated_nonpos (ξ s : ℝ) : Spec.compensated ξ s ≤ 0 := by
  rw [compensated_eq]
  nlinarith [sq_nonneg (KreinSolutions.Specs.SValue ξ (s / 2))]

theorem continuous_compensated : Continuous (Function.uncurry Spec.compensated) := by
  change Continuous (fun z : ℝ × ℝ => Spec.compensated z.1 z.2)
  simp_rw [compensated_eq]
  exact continuous_const.mul
    (((KreinFiberAmplitudes.continuous_solution false).comp
      (continuous_fst.prodMk (continuous_snd.div_const 2))).pow 2)

/-- Pointwise compact domination exists even for the zero measure. -/
theorem constant_representation (c : ℝ) :
    ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      (∀ s : ℝ, Integrable (fun ξ => Spec.compensated ξ s) ν) ∧
      (∀ s : ℝ, c = c + ∫ ξ, Spec.compensated ξ s ∂ν) ∧ Spec.CompactDomination ν := by
  classical
  have hmax (R ξ : ℝ) (hR : 0 ≤ R) :
      ∃ b : ℝ, 0 ≤ b ∧ ∀ s, |s| ≤ R → |Spec.compensated ξ s| ≤ b := by
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
      ((continuous_compensated.comp (continuous_const.prodMk continuous_id)).abs.continuousOn)
    exact ⟨_, abs_nonneg _, fun s hs => hmax (abs_le.mp hs)⟩
  refine ⟨0, inferInstance, fun _ => integrable_zero_measure, ?_, ?_⟩
  · simp
  · intro R hR
    choose b hb hbound using fun ξ => hmax R ξ hR
    exact ⟨b, integrable_zero_measure, hb, fun s ξ hs => hbound ξ s hs⟩

/-- The oscillatory energy has a uniform positive lower bound after the
frequency has left a compact set. -/
theorem sin_square_integral (a : ℝ) (ha : 0 < a) :
    (∫ t in (-1 : ℝ)..1, Real.sin (a * t) ^ 2) =
      1 - Real.sin a * Real.cos a / a := by
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.sin t ^ 2) ha.ne']
  rw [integral_sin_sq]
  simp only [mul_neg_one, mul_one, Real.sin_neg, Real.cos_neg, smul_eq_mul]
  field_simp
  ring

/-- On the large negative spectral half-line, one local energy controls the
maximum at every spatial point. -/
theorem negative_tail_bound (ξ t : ℝ) (hξ : ξ ≤ -4) :
    KreinSolutions.Specs.SValue ξ t ^ 2 ≤
      2 * KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ := by
  have hn : ξ < 0 := by linarith
  let a := Real.sqrt (-ξ)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have ha2 : 2 ≤ a := by
    dsimp [a]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have hE : KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ =
      (1 - Real.sin a * Real.cos a / a) / a ^ 2 := by
    unfold KreinFiberAmplitudes.Spec.solutionEnergyValue intervalMeasure solution
    simp only [Bool.false_eq_true, ite_false, KreinSolutions.Specs.SValue, hn, ite_true,
      div_pow]
    rw [integral_div, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by norm_num : (-1 : ℝ) ≤ 1), sin_square_integral a ha]
  have hsc : Real.sin a * Real.cos a ≤ 1 :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hsmall : Real.sin a * Real.cos a / a ≤ 1 / 2 := by
    apply (div_le_iff₀ ha).2
    linarith
  rw [hE, KreinSolutions.Specs.SValue, ite_eq_left hn, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos ha)).2
  have hcancel : 2 * ((1 - Real.sin a * Real.cos a / a) / a ^ 2) * a ^ 2 =
      2 * (1 - Real.sin a * Real.cos a / a) := by field_simp
  rw [hcancel]
  linarith [Real.sin_sq_le_one (a * t)]


private theorem continuous_S (ξ : ℝ) : Continuous (KreinSolutions.Specs.SValue ξ) :=
  continuous_iff_continuousAt.mpr fun t => (KreinSolutions.firstDerivatives ξ t).2.continuousAt

/-- Monotonicity in absolute spatial position on the nonnegative spectral axis. -/
theorem abs_S_le_of_nonnegative (ξ s t : ℝ) (hξ : 0 ≤ ξ) (hst : |s| ≤ t) :
    |KreinSolutions.Specs.SValue ξ s| ≤ KreinSolutions.Specs.SValue ξ t := by
  have hn : ¬ξ < 0 := not_lt.mpr hξ
  by_cases hz : ξ = 0
  · simpa [KreinSolutions.Specs.SValue, hz] using hst
  · have hroot : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr (lt_of_le_of_ne hξ (Ne.symm hz))
    simp only [KreinSolutions.Specs.SValue, hn, hz, ite_false,
      abs_div, Real.abs_sinh, abs_mul, abs_of_pos hroot]
    exact div_le_div_of_nonneg_right (Real.sinh_le_sinh.mpr
      (mul_le_mul_of_nonneg_left hst hroot.le)) hroot.le

theorem nonnegative_parameter_bound (ξ s R : ℝ) (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (hs : |s| ≤ R) :
    KreinSolutions.Specs.SValue ξ s ^ 2 ≤
      KreinFiberAmplitudes.Spec.solutionEnergyValue false (R + 1) ξ := by
  have hcont := (continuous_S ξ).pow 2
  have hsub : Icc R (R + 1) ⊆ Icc (-(R + 1)) (R + 1) := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  calc
    KreinSolutions.Specs.SValue ξ s ^ 2 =
      ∫ t in Icc R (R + 1), KreinSolutions.Specs.SValue ξ s ^ 2 := by simp
    _ ≤ ∫ t in Icc R (R + 1), KreinSolutions.Specs.SValue ξ t ^ 2 := by
      apply setIntegral_mono_on
        (continuous_const.integrableOn_Icc) (hcont.integrableOn_Icc) measurableSet_Icc
      intro t ht
      have h := abs_S_le_of_nonnegative ξ s t hξ (hs.trans ht.1)
      change KreinSolutions.Specs.SValue ξ s ^ 2 ≤ KreinSolutions.Specs.SValue ξ t ^ 2
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).2 h
    _ ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false (R + 1) ξ := by
      apply setIntegral_mono_set hcont.integrableOn_Icc
        (Filter.Eventually.of_forall fun t => sq_nonneg _)
        (Filter.Eventually.of_forall fun t ht => hsub ht)


/-- The elementary sine estimate also controls the removable zero parameter. -/
theorem S_square_le_of_nonpositive (ξ t : ℝ) (hξ : ξ ≤ 0) :
    KreinSolutions.Specs.SValue ξ t ^ 2 ≤ t ^ 2 := by
  by_cases hz : ξ = 0
  · simp [hz, KreinSolutions.Specs.SValue]
  · have hn : ξ < 0 := lt_of_le_of_ne hξ hz
    have ha : 0 < Real.sqrt (-ξ) := Real.sqrt_pos.mpr (neg_pos.mpr hn)
    simp only [KreinSolutions.Specs.SValue, hn, ite_true, div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).2
    nlinarith [Real.sin_sq_le_sq (x := Real.sqrt (-ξ) * t)]

theorem negative_axis_bound (R m : ℝ) (hR : 0 ≤ R) (hm : 0 < m)
    (hmin : ∀ ξ ∈ Icc (-4 : ℝ) 0,
      m ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ) :
    ∀ ξ t : ℝ, ξ ≤ 0 → |t| ≤ R →
      KreinSolutions.Specs.SValue ξ t ^ 2 ≤
        (2 + R ^ 2 / m) * KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ := by
  intro ξ t hξ ht
  have hE : 0 ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ :=
    integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ 2 + R ^ 2 / m := by positivity
  by_cases htail : ξ ≤ -4
  · exact (negative_tail_bound ξ t htail).trans
      (mul_le_mul_of_nonneg_right (by linarith [div_nonneg (sq_nonneg R) hm.le] : 2 ≤ 2 + R ^ 2 / m) hE)
  · have hcompact : ξ ∈ Icc (-4 : ℝ) 0 := ⟨(not_le.mp htail).le, hξ⟩
    have hsq : t ^ 2 ≤ R ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 ht
    have hprod : R ^ 2 ≤ (2 + R ^ 2 / m) * m := by
      rw [add_mul, div_mul_cancel₀ _ hm.ne']
      linarith
    exact (S_square_le_of_nonpositive ξ t hξ).trans
      (hsq.trans (hprod.trans (mul_le_mul_of_nonneg_left (hmin ξ hcompact) hB)))


/-- An energy majorant uniform on each compact spatial interval. -/
theorem compact_energy_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ t : ℝ, |t| ≤ R →
      KreinSolutions.Specs.SValue ξ t ^ 2 ≤
        B * KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ +
          KreinFiberAmplitudes.Spec.solutionEnergyValue false (R + 1) ξ := by
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_forall_le'
    (KreinFiberAmplitudes.continuous_solutionEnergy false 1).continuousOn
    (fun ξ _ => KreinFiberAmplitudes.positive_solutionEnergy false 1 ξ zero_lt_one)
  refine ⟨2 + R ^ 2 / m, by positivity, ?_⟩
  intro ξ t ht
  have hE1 : 0 ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ :=
    integral_nonneg fun _ => sq_nonneg _
  have hER : 0 ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false (R + 1) ξ :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases hξ : ξ ≤ 0
  · have h := negative_axis_bound R m hR hm hmin ξ t hξ ht
    linarith
  · have h := nonnegative_parameter_bound ξ t R (not_le.mp hξ).le hR ht
    have : 0 ≤ (2 + R ^ 2 / m) *
        KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ := by positivity
    linarith

/-- Local square energy is an integrable real-valued function of the spectral
parameter; this conversion imposes no finite-total-mass condition. -/
theorem integrable_energy (ν : Measure ℝ)
    (hν : ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure R ∂ν) < ∞) (R : ℝ) (hR : 0 < R) :
    Integrable (KreinFiberAmplitudes.Spec.solutionEnergyValue false R) ν := by
  have hn : ∀ ξ, 0 ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false R ξ :=
    fun ξ => integral_nonneg fun t => sq_nonneg _
  apply (lintegral_ofReal_ne_top_iff_integrable
    (KreinFiberAmplitudes.continuous_solutionEnergy false R).aestronglyMeasurable
    (ae_of_all _ hn)).1
  have hident (ξ : ℝ) :
      ENNReal.ofReal (KreinFiberAmplitudes.Spec.solutionEnergyValue false R ξ) =
        ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2) ∂intervalMeasure R := by
    simp only [sq_abs]
    exact ofReal_integral_eq_lintegral_ofReal (continuous_S ξ |>.pow 2 |>.integrableOn_Icc)
      (ae_of_all _ fun t => sq_nonneg _)
  simpa only [hident] using (hν R hR).ne

/-- Compact domination for the squared odd solution follows solely from local
energy and therefore works for infinite positive measures. -/
theorem square_compact_domination (ν : Measure ℝ)
    (hν : ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure R ∂ν) < ∞) (R : ℝ) (hR : 0 ≤ R) :
    ∃ g : ℝ → ℝ, Integrable g ν ∧ (∀ ξ, 0 ≤ g ξ) ∧
      ∀ t ξ : ℝ, |t| ≤ R → KreinSolutions.Specs.SValue ξ t ^ 2 ≤ g ξ := by
  obtain ⟨B, hB, hb⟩ := compact_energy_bound R hR
  refine ⟨fun ξ => B * KreinFiberAmplitudes.Spec.solutionEnergyValue false 1 ξ +
      KreinFiberAmplitudes.Spec.solutionEnergyValue false (R + 1) ξ,
    ((integrable_energy ν hν 1 zero_lt_one).const_mul B).add
      (integrable_energy ν hν (R + 1) (by linarith)), ?_, fun t ξ ht => hb ξ t ht⟩
  intro ξ
  have hE (T : ℝ) : 0 ≤ KreinFiberAmplitudes.Spec.solutionEnergyValue false T ξ :=
    integral_nonneg fun t => sq_nonneg _
  exact add_nonneg (mul_nonneg hB (hE 1)) (hE (R + 1))


/-- Scalar squared solution integral in the actual positive measure. -/
def squareIntegral (ν : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ ξ, KreinSolutions.Specs.SValue ξ s ^ 2 ∂ν

private theorem continuous_S_parameter (t : ℝ) : Continuous (fun ξ => KreinSolutions.Specs.SValue ξ t) :=
  (KreinFiberAmplitudes.continuous_solution false).comp
    (continuous_id.prodMk continuous_const)

theorem integrable_square (ν : Measure ℝ)
    (hν : ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure R ∂ν) < ∞) (t : ℝ) :
    Integrable (fun ξ => KreinSolutions.Specs.SValue ξ t ^ 2) ν := by
  obtain ⟨g, hg, hpos, hbound⟩ := square_compact_domination ν hν |t| (abs_nonneg t)
  apply hg.mono' (continuous_S_parameter t |>.pow 2 |>.aestronglyMeasurable)
  exact ae_of_all _ fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound t ξ le_rfl

theorem continuous_squareIntegral (ν : Measure ℝ)
    (hν : ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure R ∂ν) < ∞) : Continuous (squareIntegral ν) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨g, hg, hpos, hbound⟩ := square_compact_domination ν hν (|s| + 1) (by positivity)
  apply continuousAt_of_dominated (bound := g)
    (Eventually.of_forall fun t => (continuous_S_parameter t |>.pow 2 |>.aestronglyMeasurable))
    ?_ hg (ae_of_all _ fun ξ => (continuous_S ξ |>.pow 2 |>.continuousAt))
  have hopen : IsOpen {t : ℝ | |t| < |s| + 1} := isOpen_lt continuous_abs continuous_const
  have hnear : ∀ᶠ t in 𝓝 s, |t| < |s| + 1 :=
    hopen.mem_nhds (by change |s| < |s| + 1; linarith)
  filter_upwards [hnear] with t ht
  exact ae_of_all _ fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound t ξ ht.le

theorem compensated_compact_domination (ν : Measure ℝ)
    (hν : ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure R ∂ν) < ∞) : Spec.CompactDomination ν := by
  intro R hR
  obtain ⟨g, hg, hpos, hbound⟩ := square_compact_domination ν hν R hR
  refine ⟨fun ξ => 2 * g ξ, hg.const_mul 2, fun ξ => mul_nonneg (by norm_num) (hpos ξ), ?_⟩
  intro s ξ hs
  have ht : |s / 2| ≤ R := by rw [abs_div]; norm_num; linarith
  have h := hbound (s / 2) ξ ht
  have habs : |(-2 : ℝ)| = 2 := by norm_num
  rw [compensated_eq, abs_mul, habs, abs_pow, sq_abs]
  linarith

theorem integrable_compensated (ν : Measure ℝ)
    (hν : ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure R ∂ν) < ∞) (s : ℝ) :
    Integrable (fun ξ => Spec.compensated ξ s) ν := by
  simp_rw [compensated_eq]
  exact (integrable_square ν hν (s / 2)).const_mul (-2)

theorem even_symmetric_integral (f : ℝ → ℝ) (hf : Continuous f) (he : Function.Even f)
    (R : ℝ) : (∫ t in -R..R, f t) = 2 * ∫ t in 0..R, f t := by
  have hneg : (∫ t in -R..0, f t) = ∫ t in 0..R, f t := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := R)
    have hpoint (x : ℝ) : f (-x) = f x := he x
    simpa only [hpoint, neg_zero] using h.symm
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-R) 0) (hf.intervalIntegrable (μ := volume) 0 R)
  rw [hneg] at h
  linarith

/-- For continuous even functions, symmetric-interval integrals determine every
point value. This avoids any claim about point evaluations in a direct integral. -/
theorem eq_of_even_symmetric_integrals (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hef : Function.Even f) (heg : Function.Even g)
    (h : ∀ R : ℝ, 0 < R → (∫ t in -R..R, f t) = ∫ t in -R..R, g t) : f = g := by
  have hall (R : ℝ) : (∫ t in -R..R, f t) = ∫ t in -R..R, g t := by
    rcases lt_trichotomy 0 R with hR | hR | hR
    · exact h R hR
    · subst R; simp
    · have h' := h (-R) (by linarith)
      simp only [neg_neg] at h'
      rw [intervalIntegral.integral_symm (-R) R, intervalIntegral.integral_symm (-R) R] at h'
      exact neg_injective h'
  have hprim : (fun R : ℝ => ∫ t in 0..R, f t) = fun R : ℝ => ∫ t in 0..R, g t := by
    funext R
    have h' := hall R
    rw [even_symmetric_integral f hf hef, even_symmetric_integral g hg heg] at h'
    linarith
  funext s
  have hdf := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 s)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hdg := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 s)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  rw [hprim] at hdf
  exact hdf.unique hdg


/-- The exact amplitude-weighted energy identity, rather than only its
finiteness. It holds also when the Gram space or the amplitude vanishes. -/
theorem amplitude_interval_energy
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData false F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S}
    (K : KernelData G M) (A : AmplitudeData K) (R : ℝ) (hR : 0 < R) :
    (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (KreinSolutions.Specs.SValue ξ t ^ 2)
      ∂intervalMeasure R ∂amplitudeMeasure M.μ A.c) =
      ENNReal.ofReal (∫ t, ‖G.vectors t‖ ^ 2 ∂intervalMeasure R) := by
  have ht := KreinSpectralKernel.amplitude_energy_transfer M.μ (intervalMeasure R)
    A.c A.measurable K.h (fun ξ t => (solution false ξ t : ℂ))
    (A.factorization.mono fun _ hξ => ae_restrict_of_ae hξ)
  have hnorm (ξ t : ℝ) : ‖(solution false ξ t : ℂ)‖ₑ ^ 2 =
      ENNReal.ofReal (KreinSolutions.Specs.SValue ξ t ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _)]
    simp only [solution, Bool.false_eq_true, ite_false, sq_abs]
  simp_rw [hnorm] at ht
  exact ht.symm.trans (K.energy R hR)

/-- Tonelli turns the local kernel energy into a symmetric-interval identity
for the continuous scalar square integral. -/
theorem square_integral_interval
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData false F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S}
    (K : KernelData G M) (A : AmplitudeData K) (R : ℝ) (hR : 0 < R) :
    (∫ t in -R..R, squareIntegral (amplitudeMeasure M.μ A.c) t) =
      ∫ t in -R..R, ‖G.vectors t‖ ^ 2 := by
  let ν := amplitudeMeasure M.μ A.c
  let : IsLocallyFiniteMeasure ν := A.locally_finite
  have hν : ∀ T : ℝ, 0 < T →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure T ∂ν) < ∞ := by
    simpa only [solution, Bool.false_eq_true, ite_false] using A.local_energy
  have hqcont := continuous_squareIntegral ν hν
  have hqpos (t : ℝ) : 0 ≤ squareIntegral ν t := integral_nonneg fun ξ => sq_nonneg _
  have hscalar (t : ℝ) : ENNReal.ofReal (squareIntegral ν t) =
      ∫⁻ ξ, ENNReal.ofReal (KreinSolutions.Specs.SValue ξ t ^ 2) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal (integrable_square ν hν t)
      (ae_of_all _ fun ξ => sq_nonneg _)
  have he : ENNReal.ofReal (∫ t, squareIntegral ν t ∂intervalMeasure R) =
      ENNReal.ofReal (∫ t, ‖G.vectors t‖ ^ 2 ∂intervalMeasure R) := by
    calc
      _ = ∫⁻ t, ENNReal.ofReal (squareIntegral ν t) ∂intervalMeasure R :=
        ofReal_integral_eq_lintegral_ofReal hqcont.integrableOn_Icc (ae_of_all _ hqpos)
      _ = ∫⁻ t, ∫⁻ ξ, ENNReal.ofReal (KreinSolutions.Specs.SValue ξ t ^ 2)
          ∂ν ∂intervalMeasure R := by simp_rw [hscalar]
      _ = ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (KreinSolutions.Specs.SValue ξ t ^ 2)
          ∂intervalMeasure R ∂ν := by
        apply lintegral_lintegral_swap
        exact (((KreinFiberAmplitudes.continuous_solution false).comp
          continuous_swap).pow 2).measurable.ennreal_ofReal.aemeasurable
      _ = _ := amplitude_interval_energy K A R hR
  have hreal : (∫ t, squareIntegral ν t ∂intervalMeasure R) =
      ∫ t, ‖G.vectors t‖ ^ 2 ∂intervalMeasure R := by
    apply_fun ENNReal.toReal at he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg hqpos),
      ENNReal.toReal_ofReal (integral_nonneg fun t => sq_nonneg _)] using he
  simpa only [intervalMeasure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)] using hreal

/-- Recover pointwise diagonal values from exact interval energies and
continuity. No pointwise evaluation of an arbitrary direct-integral class is
used or postulated. -/
theorem squareIntegral_eq_gram_diagonal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData false F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S}
    (K : KernelData G M) (A : AmplitudeData K) (s : ℝ) :
    squareIntegral (amplitudeMeasure M.μ A.c) s = ‖G.vectors s‖ ^ 2 := by
  have hν : ∀ T : ℝ, 0 < T →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure T ∂amplitudeMeasure M.μ A.c) < ∞ := by
    simpa only [solution, Bool.false_eq_true, ite_false] using A.local_energy
  apply congrFun (eq_of_even_symmetric_integrals _ _
    (continuous_squareIntegral _ hν) (G.continuous_vectors.norm.pow 2) ?_ ?_
    (square_integral_interval K A)) s
  · intro t
    unfold squareIntegral
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      change KreinSolutions.Specs.SValue ξ (-t) ^ 2 = KreinSolutions.Specs.SValue ξ t ^ 2
      rw [(KreinSolutions.parity ξ).2 t]
      ring
  · intro t
    change ‖G.vectors (-t)‖ ^ 2 = ‖G.vectors t‖ ^ 2
    rw [G.parity t]
    simp [KreinSymmetricOperator.Spec.paritySign]


/-- The minus-kernel lemma, with the original positivity hypothesis and all
absolute-convergence and compact-domination conclusions. -/
theorem representation : Spec.Main := by
  intro F hF he hpos
  have hpos' : KreinSolutions.Specs.PositiveDefiniteValue
      (KreinSymmetricOperator.Spec.kernel false F) := hpos
  obtain ⟨H, hn, hi, hc, hsep, G, S₀, S, hdom, haction, hsym, hcomm,
    hclosable, hext, hself, M, K, ⟨A⟩⟩ :=
    KreinSpectralKernel.spectral_kernel false F hF he hpos'
  let := hn
  let := hi
  let := hc
  let ν := amplitudeMeasure M.μ A.c
  have hν : ∀ T : ℝ, 0 < T →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|KreinSolutions.Specs.SValue ξ t| ^ 2)
        ∂intervalMeasure T ∂ν) < ∞ := by
    simpa only [solution, Bool.false_eq_true, ite_false] using A.local_energy
  refine ⟨ν, A.locally_finite, integrable_compensated ν hν, ?_,
    compensated_compact_domination ν hν⟩
  intro s
  have hdiag : ‖G.vectors (s / 2)‖ ^ 2 = (F 0 - F s) / 2 := by
    have hadd : s / 2 + s / 2 = s := by ring
    calc
      ‖G.vectors (s / 2)‖ ^ 2 =
          (⟪G.vectors (s / 2), G.vectors (s / 2)⟫_ℂ).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (F 0 - F s) / 2 := by
        rw [G.gram]
        simp only [KreinSymmetricOperator.Spec.kernel, Bool.false_eq_true, ite_false,
          KreinSolutions.Specs.KernelMinusValue, sub_self, hadd, Complex.ofReal_re]
  have hint : (∫ ξ, Spec.compensated ξ s ∂ν) = -2 * ‖G.vectors (s / 2)‖ ^ 2 := by
    simp_rw [compensated_eq]
    rw [integral_const_mul]
    exact congrArg (fun z : ℝ => -2 * z) (squareIntegral_eq_gram_diagonal K A (s / 2))
  rw [hint, hdiag]
  ring

end ExpandedFA.PartIV.KreinKernelMinus
