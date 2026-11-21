import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinOdd
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinKernelMinus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

set_option maxHeartbeats 1500000

namespace ExpandedFA.PartIV.KreinOdd

/-- Necessity once the continuous odd-test/kernel bridge has been established. -/
theorem representation_of_kernel_positive (q : ℝ → ℝ) (hq : Continuous q)
    (he : Function.Even q)
    (hp : KreinSolutions.Specs.PositiveDefiniteValue (KreinSolutions.Specs.KernelMinusValue q)) :
    Spec.Representation q := KreinKernelMinus.representation q hq he hp

/-- Each compensated elementary kernel is a positive rank-one kernel. -/
theorem compensated_kernel (ξ s t : ℝ) :
    (KreinKernelMinus.Spec.compensated ξ (s-t) -
      KreinKernelMinus.Spec.compensated ξ (s+t)) / 2 =
      KreinSolutions.Specs.SValue ξ s * KreinSolutions.Specs.SValue ξ t := by
  by_cases hz : ξ = 0
  · subst ξ
    simp [KreinKernelMinus.Spec.compensated, KreinSolutions.Specs.SValue]
    ring
  · have h := KreinSolutions.additionDifference ξ s t
    simp only [KreinKernelMinus.Spec.compensated, hz, ite_false]
    field_simp
    nlinarith [h]

/-- Integrability of every spectral kernel entry follows from absolute
integrability of the two compensated values; no finite mass is assumed. -/
theorem integrable_spectral_product (ν : Measure ℝ)
    (hi : ∀ s, Integrable (fun ξ => KreinKernelMinus.Spec.compensated ξ s) ν)
    (s t : ℝ) : Integrable (fun ξ =>
      KreinSolutions.Specs.SValue ξ s * KreinSolutions.Specs.SValue ξ t) ν := by
  simp_rw [← compensated_kernel]
  exact ((hi (s-t)).sub (hi (s+t))).div_const 2

/-- The constant cancels, leaving the integral of real rank-one kernels. -/
theorem kernel_eq_integral {q : ℝ → ℝ} (ν : Measure ℝ)
    (hi : ∀ s, Integrable (fun ξ => KreinKernelMinus.Spec.compensated ξ s) ν)
    (hr : ∀ s, q s = q 0 + ∫ ξ, KreinKernelMinus.Spec.compensated ξ s ∂ν)
    (s t : ℝ) : KreinSolutions.Specs.KernelMinusValue q s t =
      ∫ ξ, KreinSolutions.Specs.SValue ξ s * KreinSolutions.Specs.SValue ξ t ∂ν := by
  simp_rw [← compensated_kernel]
  rw [integral_div, integral_sub (hi (s-t)) (hi (s+t))]
  unfold KreinSolutions.Specs.KernelMinusValue
  rw [hr (s-t), hr (s+t)]
  ring

theorem rank_one_sum (n : ℕ) (a v : Fin n → ℝ) :
    (∑ i, ∑ j, a i * a j * (v i * v j)) = (∑ i, a i * v i) ^ 2 := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The converse at the kernel level works for the possibly infinite measure
of the original theorem. -/
theorem kernel_positive_of_representation {q : ℝ → ℝ} (hr : Spec.Representation q) :
    KreinSolutions.Specs.PositiveDefiniteValue (KreinSolutions.Specs.KernelMinusValue q) := by
  obtain ⟨ν, hν, hi, hr, hd⟩ := hr
  constructor
  · intro s t
    rw [kernel_eq_integral ν hi hr s t, kernel_eq_integral ν hi hr t s]
    congr 1
    funext ξ
    ring
  · intro n x a
    simp_rw [kernel_eq_integral ν hi hr]
    have hij (i j : Fin n) : Integrable (fun ξ =>
        a i * a j * (KreinSolutions.Specs.SValue ξ (x i) *
          KreinSolutions.Specs.SValue ξ (x j))) ν :=
      (integrable_spectral_product ν hi (x i) (x j)).const_mul _
    have hswap : (∑ i, ∑ j, a i * a j *
        ∫ ξ, KreinSolutions.Specs.SValue ξ (x i) * KreinSolutions.Specs.SValue ξ (x j) ∂ν) =
        ∫ ξ, ∑ i, ∑ j, a i * a j *
          (KreinSolutions.Specs.SValue ξ (x i) * KreinSolutions.Specs.SValue ξ (x j)) ∂ν := by
      simp_rw [← integral_const_mul]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        exact fun j _ => hij i j
      · intro i _
        exact integrable_finsetSum _ (fun j _ => hij i j)
    rw [hswap]
    exact integral_nonneg fun ξ => by
      rw [rank_one_sum]
      exact sq_nonneg _

/-- The exact rank-one kernel of the quadratic example. -/
theorem quadratic_kernel (s t : ℝ) :
    KreinSolutions.Specs.KernelMinusValue (fun u => -(u ^ 2)) s t = 2 * s * t := by
  unfold KreinSolutions.Specs.KernelMinusValue
  ring

theorem quadratic_kernel_positive : KreinSolutions.Specs.PositiveDefiniteValue
    (KreinSolutions.Specs.KernelMinusValue (fun s => -(s ^ 2))) := by
  constructor
  · intro s t; rw [quadratic_kernel, quadratic_kernel]; ring
  · intro n x a
    simp_rw [quadratic_kernel]
    have heq : (∑ i, ∑ j, a i * a j * (2 * x i * x j)) =
        2 * (∑ i, a i * x i) ^ 2 := by
      rw [← rank_one_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    positivity

/-- The mass-two atom at zero satisfies all the measure and domination
conditions of the compensated representation, not just its formal identity. -/
theorem quadratic_atom : Spec.QuadraticAtom := by
  let ν : Measure ℝ := (2 : ℝ≥0∞) • Measure.dirac 0
  haveI : IsFiniteMeasure ν := ⟨by simp [ν]⟩
  have hi (g : ℝ → ℝ) : Integrable g ν :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  refine ⟨inferInstance, fun s => hi _, ?_, ?_⟩
  · intro s
    simp [KreinKernelMinus.Spec.compensated]
    ring
  · intro R hR
    have hb (ξ : ℝ) : ∃ b : ℝ, 0 ≤ b ∧
        ∀ s, |s| ≤ R → |KreinKernelMinus.Spec.compensated ξ s| ≤ b := by
      obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMaxOn
        (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
        ((KreinKernelMinus.continuous_compensated.comp
          (continuous_const.prodMk continuous_id)).abs.continuousOn)
      exact ⟨_, abs_nonneg _, fun s hs => hm (abs_le.mp hs)⟩
    choose g hg hbound using hb
    exact ⟨g, hi g, hg, fun s ξ hs => hbound ξ s hs⟩

/-- Kernel positivity implies the original positivity for every continuous
compactly supported odd real test, via the actual Gram integral. -/
theorem odd_test_positive_of_kernel {q : ℝ → ℝ} (hq : Continuous q)
    (he : Function.Even q)
    (hp : KreinSolutions.Specs.PositiveDefiniteValue (KreinSolutions.Specs.KernelMinusValue q)) :
    Spec.OddTestPositive q := by
  obtain ⟨H, hn, hi, hc, hs, ⟨G⟩⟩ :=
    KreinSymmetricOperator.gram_space_exists false q hq he hp
  let := hn
  let := hi
  let := hc
  intro f hf hfs hfo
  let g : ℝ → ℂ := fun t => (f t : ℂ)
  have hg : Continuous g := Complex.continuous_ofReal.comp hf
  have hgs : HasCompactSupport g := hfs.comp_left (g := Complex.ofReal) (by simp)
  have hgo : ∀ t, g (-t) = KreinSymmetricOperator.Spec.paritySign false * g t := by
    intro t
    simp [g, hfo t, KreinSymmetricOperator.Spec.paritySign]
  have h := KreinSymmetricOperator.inner_testIntegral_kernel_parity G hq
    g g hg hgs hg hgs hgo
  have heq (s t : ℝ) : starRingEnd ℂ (g s) * g t * (q (s-t) : ℂ) =
      (q (s-t) * f s * f t : ℝ) := by
    simp [g]
    ring
  simp_rw [heq, integral_complex_ofReal] at h
  have hre := congrArg Complex.re h
  have hnz := sq_nonneg ‖KreinSymmetricOperator.Spec.testIntegral G.vectors g‖
  change 0 ≤ ∫ s : ℝ, ∫ t : ℝ, q (s-t) * f s * f t
  calc
    0 ≤ ‖KreinSymmetricOperator.Spec.testIntegral G.vectors g‖ ^ 2 := hnz
    _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans (by simpa using hre)

/-- Sufficiency of the compensated formula for the original tests. -/
theorem odd_test_positive_of_representation {q : ℝ → ℝ} (hq : Continuous q)
    (he : Function.Even q) (hr : Spec.Representation q) : Spec.OddTestPositive q :=
  odd_test_positive_of_kernel hq he (kernel_positive_of_representation hr)

/-- The fourth term of the positive cosh series is already enough to exclude
quadratic growth at every nonzero frequency. -/
theorem fourth_power_le_cosh (x : ℝ) : x ^ 4 / 24 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.le_tsum 2
    (fun n _ => div_nonneg ((even_two_mul n).pow_nonneg x) (Nat.cast_nonneg _))
  norm_num at h
  simpa only [← Real.cosh_eq_tsum] using h

/-- A nonnegative fourth-degree term cannot have a global quadratic upper
bound. This elementary growth argument avoids any moment assumption. -/
theorem quartic_coefficient_zero (m A : ℝ) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, t ^ 4 * m ≤ 24 * (A + t ^ 2)) : m = 0 := by
  by_contra hne
  have hm' : 0 < m := lt_of_le_of_ne hm (Ne.symm hne)
  let t : ℝ := 24 * (A+1) / m + 1
  have ht : 1 < t := by
    dsimp [t]
    have : 0 < 24 * (A+1) / m := div_pos (by positivity) hm'
    linarith
  have htm : 24 * (A+1) < t * m := by
    dsimp [t]
    rw [add_mul, div_mul_cancel₀ _ hm'.ne']
    linarith
  have hsq : t ≤ t ^ 2 := by nlinarith
  have hlarge : 24 * (A+1) < t ^ 2 * m :=
    htm.trans_le (mul_le_mul_of_nonneg_right hsq hm)
  have hupper : 24 * (A + t ^ 2) ≤ (24 * (A+1)) * t ^ 2 := by
    nlinarith [mul_nonneg hA (show 0 ≤ t ^ 2 - 1 by nlinarith)]
  have hb := (h t).trans hupper
  have hc : (t ^ 2 * m) * t ^ 2 ≤ (24 * (A+1)) * t ^ 2 := by
    nlinarith [hb]
  have hcancel : t ^ 2 * m ≤ 24 * (A+1) :=
    (mul_le_mul_iff_left₀ (show 0 < t ^ 2 by nlinarith)).mp hc
  linarith

/-- The cosh component in a purported quadratic representation has zero
fourth moment, so it is concentrated at frequency zero. -/
theorem quadratic_counterexample : Spec.QuadraticCounterexample := by
  rintro ⟨μ, θ, hμ, hθ, hi, hr⟩
  let := hμ
  let := hθ
  let A : ℝ := μ.real univ
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hcos (t : ℝ) : (∫ a, Real.cos (a*t) ∂μ) ≤ A := by
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, one_mul, A] using
        (norm_integral_le_of_norm_le_const (μ := μ) (f := fun a : ℝ => Real.cos (a*t)) (C := 1)
          (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a*t))))
  have hupper (t : ℝ) : (∫ b, Real.cosh (b*t) ∂θ) ≤ A + t ^ 2 := by
    have h := hr t
    linarith [hcos t]
  have hfour : Integrable (fun b : ℝ => b ^ 4) θ := by
    have hmajor := (hi 1).const_mul 24
    apply hmajor.mono' (by fun_prop)
    exact ae_of_all _ fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ b ^ 4)]
      have h := fourth_power_le_cosh b
      simp only [mul_one]
      nlinarith
  let m : ℝ := ∫ b, b ^ 4 ∂θ
  have hm : 0 ≤ m := integral_nonneg fun b => by positivity
  have hbound (t : ℝ) : t ^ 4 * m ≤ 24 * (A + t ^ 2) := by
    have hpoint (b : ℝ) : t ^ 4 * b ^ 4 ≤ 24 * Real.cosh (b*t) := by
      have h := fourth_power_le_cosh (b*t)
      rw [mul_pow] at h
      nlinarith
    have h := integral_mono (hfour.const_mul (t ^ 4)) ((hi t).const_mul 24) hpoint
    simp only [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hupper t) (by norm_num))
  have hmzero : m = 0 := quartic_coefficient_zero m A hm hA hbound
  have hz : ∀ᵐ b ∂θ, b = (0 : ℝ) := by
    have h := (integral_eq_zero_iff_of_nonneg (fun b : ℝ => by positivity) hfour).mp hmzero
    filter_upwards [h] with b hb
    exact (pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hb
  have hconst (t : ℝ) : (∫ b, Real.cosh (b*t) ∂θ) = θ.real univ := by
    calc
      _ = ∫ b : ℝ, (1 : ℝ) ∂θ := integral_congr_ae (hz.mono fun b hb => by simp [hb])
      _ = _ := by simp
  have hzero := hr 0
  have hmass : θ.real univ = A := by
    simp only [mul_zero, Real.cos_zero, Real.cosh_zero, integral_const, smul_eq_mul,
      mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero] at hzero
    dsimp [A]
    linarith
  have hlow (t : ℝ) : -A ≤ (∫ a, Real.cos (a*t) ∂μ) := by
    have hnorm := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a : ℝ => Real.cos (a*t)) (C := 1)
      (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a*t))
    have habs : |∫ a, Real.cos (a*t) ∂μ| ≤ A := by simpa [Real.norm_eq_abs, A] using hnorm
    exact (abs_le.mp habs).1
  have ht := hr (2*A+1)
  rw [hconst, hmass] at ht
  have hl := hlow (2*A+1)
  nlinarith [sq_nonneg A]

/-- A family of even nonnegative smooth probability densities with shrinking
compact support. -/
def shrinkingBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

def density (n : ℕ) : ℝ → ℝ := (shrinkingBump n).normed volume

def smoothAverage (n : ℕ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u : ℝ, density n u * q (x-u)

theorem shrinkingBump_tendsto :
    Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa [shrinkingBump, div_eq_mul_inv] using h

/-- Averaging against the densities converges also with a moving evaluation
point. This joint limit permits applying the approximation twice. -/
theorem smoothAverage_joint {q : ℝ → ℝ} (hq : Continuous q) (x : ℝ) :
    Tendsto (fun p : ℕ × ℝ => smoothAverage p.1 q p.2) (atTop ×ˢ 𝓝 x) (𝓝 (q x)) := by
  exact ContDiffBump.convolution_tendsto_right
    (φ := fun p : ℕ × ℝ => shrinkingBump p.1)
    (g := fun _ : ℕ × ℝ => q) (k := fun p : ℕ × ℝ => p.2)
    (shrinkingBump_tendsto.comp tendsto_fst)
    (Eventually.of_forall fun _ => hq.aestronglyMeasurable)
    ((hq.tendsto x).comp tendsto_snd) tendsto_snd

/-- Double averaging recovers the original continuous value. -/
theorem double_smoothAverage_tendsto {q : ℝ → ℝ} (hq : Continuous q) (x : ℝ) :
    Tendsto (fun n => smoothAverage n (smoothAverage n q) x) atTop (𝓝 (q x)) := by
  apply ContDiffBump.convolution_tendsto_right (φ := shrinkingBump)
    (g := fun n => smoothAverage n q) (k := fun _ => x) shrinkingBump_tendsto
    (Eventually.of_forall fun n => ?_) (smoothAverage_joint hq x) tendsto_const_nhds
  exact (by
    unfold smoothAverage
    exact AEStronglyMeasurable.integral_prod_right'
      (((shrinkingBump n).continuous_normed.comp continuous_snd).mul
        (hq.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable)

/-- Compact support of both scalar tests makes the full real integrand
integrable on the product, even when q is unbounded. -/
theorem weighted_integrable (q f g : ℝ → ℝ) (hq : Continuous q)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun z : ℝ × ℝ => q (z.1-z.2) * f z.1 * g z.2)
      (volume.prod volume) := by
  apply (((hq.comp (continuous_fst.sub continuous_snd)).mul
    (hf.comp continuous_fst)).mul (hg.comp continuous_snd)).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hfs.isCompact.prod hgs.isCompact)
  rintro ⟨s,t⟩ hst
  change q (s-t) * f s * g t = 0
  by_cases hs : s ∈ tsupport f
  · have ht : t ∉ tsupport g := by simpa only [Set.mem_prod, hs, true_and] using hst
    rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, zero_mul]

theorem weighted_section_integrable (q f g : ℝ → ℝ) (hq : Continuous q)
    (hg : Continuous g) (hgs : HasCompactSupport g) (s : ℝ) :
    Integrable (fun t => q (s-t) * f s * g t) :=
  (((hq.comp (continuous_const.sub continuous_id)).mul continuous_const).mul hg).integrable_of_hasCompactSupport hgs.mul_left

theorem density_continuous (n : ℕ) : Continuous (density n) :=
  (shrinkingBump n).continuous_normed

theorem density_compact (n : ℕ) : HasCompactSupport (density n) :=
  (shrinkingBump n).hasCompactSupport_normed

theorem density_even (n : ℕ) : Function.Even (density n) :=
  (shrinkingBump n).normed_neg

theorem translated_density_compact (n : ℕ) (x : ℝ) :
    HasCompactSupport (fun s => density n (s-x)) := by
  exact (density_compact n).comp_homeomorph (Homeomorph.subRight x)

/-- The bilinear integral of two translated even densities is a double
convolution, with exactly the spatial difference as its argument. -/
theorem translated_density_integral (q : ℝ → ℝ) (n : ℕ) (x y : ℝ) :
    (∫ s : ℝ, ∫ t : ℝ, q (s-t) * density n (s-x) * density n (t-y)) =
      smoothAverage n (smoothAverage n q) (x-y) := by
  rw [← integral_sub_left_eq_self
    (fun s : ℝ => ∫ t : ℝ, q (s-t) * density n (s-x) * density n (t-y)) volume x]
  unfold smoothAverage
  apply integral_congr_ae
  apply ae_of_all
  intro u
  change (∫ t : ℝ, q (x-u-t) * density n (x-u-x) * density n (t-y)) =
    density n u * ∫ v : ℝ, density n v * q (x-y-u-v)
  rw [← integral_add_left_eq_self (μ := volume)
    (fun t : ℝ => q (x-u-t) * density n (x-u-x) * density n (t-y)) y,
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  have h₁ : x-u-x = -u := by ring
  have h₂ : y+v-y = v := by ring
  have h₃ : x-u-(y+v) = x-y-u-v := by ring
  rw [h₁, h₂, h₃, density_even]
  ring

/-- Expansion of a mollified finite quadratic sum. All uses of linearity of
integration are justified by compact support of the actual integrands. -/
theorem quadraticForm_density_sum {ι : Type} [Fintype ι] (q : ℝ → ℝ) (hq : Continuous q)
    (a x : ι → ℝ) (n : ℕ) :
    Spec.quadraticForm q (fun s => ∑ i, a i * density n (s-x i)) =
      ∑ i, ∑ j, a i * a j * smoothAverage n (smoothAverage n q) (x i-x j) := by
  classical
  have hi (s : ℝ) (i j : ι) : Integrable (fun t => a i * a j *
      (q (s-t) * density n (s-x i) * density n (t-x j))) :=
    (weighted_section_integrable q (fun s => density n (s-x i)) (fun t => density n (t-x j)) hq
      ((density_continuous n).comp (continuous_id.sub continuous_const))
      (translated_density_compact n (x j)) s).const_mul _
  have ho (i j : ι) : Integrable (fun s => ∫ t, a i * a j *
      (q (s-t) * density n (s-x i) * density n (t-x j))) :=
    ((weighted_integrable q (fun s => density n (s-x i)) (fun t => density n (t-x j)) hq
      ((density_continuous n).comp (continuous_id.sub continuous_const))
      (translated_density_compact n (x i))
      ((density_continuous n).comp (continuous_id.sub continuous_const))
      (translated_density_compact n (x j))).const_mul _).integral_prod_left
  have hexpand (s t : ℝ) :
      q (s-t) * (∑ i, a i * density n (s-x i)) * (∑ j, a j * density n (t-x j)) =
      ∑ i, ∑ j, a i * a j * (q (s-t) * density n (s-x i) * density n (t-x j)) := by
    conv_lhs => lhs; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold Spec.quadraticForm
  simp_rw [hexpand]
  have hin (s : ℝ) := integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi s i j))
  simp_rw [hin]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ _ j)]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => ho i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => ho i j)]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [integral_const_mul]
  rw [translated_density_integral]

theorem quadraticForm_density_sum_tendsto {ι : Type} [Fintype ι]
    (q : ℝ → ℝ) (hq : Continuous q) (a x : ι → ℝ) :
    Tendsto (fun n => Spec.quadraticForm q (fun s => ∑ i, a i * density n (s-x i)))
      atTop (𝓝 (∑ i, ∑ j, a i * a j * q (x i-x j))) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (double_smoothAverage_tendsto hq (x i-x j)).const_mul (a i * a j)))
  exact h.congr (fun n => (quadraticForm_density_sum q hq a x n).symm)

theorem density_sum_compact {ι : Type} [Fintype ι] (a x : ι → ℝ) (n : ℕ) :
    HasCompactSupport (fun s => ∑ i, a i * density n (s-x i)) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_iUnion fun i : ι => (translated_density_compact n (x i)).isCompact)
  intro s hs
  by_contra hn
  have hz (i : ι) : density n (s-x i) = 0 := by
    have hnot : s ∉ tsupport (fun t => density n (t-x i)) :=
      fun h => hn (mem_iUnion.mpr ⟨i, h⟩)
    exact image_eq_zero_of_notMem_tsupport (f := fun t : ℝ => density n (t-x i)) hnot
  change (∑ i, a i * density n (s-x i)) ≠ 0 at hs
  exact hs (by simp [hz])

/-- Odd symmetrization of an arbitrary finite sum of approximate point masses. -/
def oddPositions {n : ℕ} (x : Fin n → ℝ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim x (fun i => -x i)

def oddCoefficients {n : ℕ} (a : Fin n → ℝ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim a (fun i => -a i)

theorem density_odd_sum (n : ℕ) (x a : Fin n → ℝ) (k : ℕ) :
    Function.Odd (fun s => ∑ i, oddCoefficients a i * density k (s-oddPositions x i)) := by
  intro s
  simp only [Fintype.sum_sum_type, oddCoefficients, oddPositions, Sum.elim_inl, Sum.elim_inr]
  have hn₁ (i : Fin n) : density k (-s-x i) = density k (s-(-x i)) := by
    convert density_even k (s+x i) using 1 <;> congr 1 <;> ring
  have hn₂ (i : Fin n) : density k (-s-(-x i)) = density k (s-x i) := by
    convert density_even k (s-x i) using 1
    congr 1
    ring
  simp_rw [hn₁, hn₂, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Algebraic normalization of the finite odd symmetrization. -/
theorem oddized_quadratic_sum (q : ℝ → ℝ) (he : Function.Even q)
    (n : ℕ) (x a : Fin n → ℝ) :
    (∑ i, ∑ j, oddCoefficients a i * oddCoefficients a j *
      q (oddPositions x i-oddPositions x j)) =
      4 * ∑ i, ∑ j, a i * a j * KreinSolutions.Specs.KernelMinusValue q (x i) (x j) := by
  have hn₁ (s t : ℝ) : q (-s-t) = q (s+t) := by
    rw [show -s-t = -(s+t) by ring, he]
  have hn₂ (s t : ℝ) : q (-s-(-t)) = q (s-t) := by
    rw [show -s-(-t) = -(s-t) by ring, he]
  simp only [Fintype.sum_sum_type, oddCoefficients, oddPositions, Sum.elim_inl, Sum.elim_inr]
  simp_rw [hn₂, hn₁, sub_neg_eq_add]
  simp_rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold KreinSolutions.Specs.KernelMinusValue
  ring

/-- Odd approximate point masses recover every finite quadratic sum of the
minus kernel. The approximation uses continuous compact tests from the actual
hypothesis, rather than assuming positivity for measures. -/
theorem kernel_positive_of_odd_test {q : ℝ → ℝ} (hq : Continuous q)
    (he : Function.Even q) (hp : Spec.OddTestPositive q) :
    KreinSolutions.Specs.PositiveDefiniteValue (KreinSolutions.Specs.KernelMinusValue q) := by
  constructor
  · exact ((KreinSolutions.kernelRegularity q hq he).2).2
  · intro n x a
    have hlim := quadraticForm_density_sum_tendsto q hq (oddCoefficients a) (oddPositions x)
    have hn (k : ℕ) : 0 ≤ Spec.quadraticForm q
        (fun s => ∑ i, oddCoefficients a i * density k (s-oddPositions x i)) := by
      apply hp _
        (continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul
          ((density_continuous k).comp (continuous_id.sub continuous_const))))
        (density_sum_compact _ _ _) (density_odd_sum n x a k)
    have h := ge_of_tendsto hlim (Eventually.of_forall hn)
    rw [oddized_quadratic_sum q he n x a] at h
    linarith

theorem test_kernel_equivalence : Spec.TestKernelEquivalence := by
  intro q hq he
  exact ⟨kernel_positive_of_odd_test hq he, odd_test_positive_of_kernel hq he⟩

/-- Krein's corrected odd-test representation, including the constant and
quadratic cases and locally finite measures of possibly infinite total mass. -/
theorem representation : Spec.Main := by
  intro q hq he
  exact ⟨fun hp => representation_of_kernel_positive q hq he
    (kernel_positive_of_odd_test hq he hp), odd_test_positive_of_representation hq he⟩

theorem constant_freedom : Spec.ConstantFreedom := by
  intro q c hq he
  have hqc : Continuous (fun s => q s+c) := hq.add continuous_const
  have hec : Function.Even (fun s => q s+c) := fun s => by simp [he s]
  rw [test_kernel_equivalence _ hqc hec, test_kernel_equivalence _ hq he]
  have hkernel : KreinSolutions.Specs.KernelMinusValue (fun s => q s+c) =
      KreinSolutions.Specs.KernelMinusValue q := by
    funext s t
    unfold KreinSolutions.Specs.KernelMinusValue
    ring
  rw [hkernel]

theorem quadratic_example : Spec.QuadraticExample := by
  have hc : Continuous (fun s : ℝ => -(s ^ 2)) := continuous_id.pow 2 |>.neg
  have he : Function.Even (fun s : ℝ => -(s ^ 2)) := by intro s; dsimp; ring
  refine ⟨hc, he, odd_test_positive_of_kernel hc he quadratic_kernel_positive,
    quadratic_kernel, ?_⟩
  obtain ⟨hν, hi, hr, hd⟩ := quadratic_atom
  refine ⟨(2 : ℝ≥0∞) • Measure.dirac 0, hν, hi, ?_, hd⟩
  intro s
  simpa using hr s

end ExpandedFA.PartIV.KreinOdd
