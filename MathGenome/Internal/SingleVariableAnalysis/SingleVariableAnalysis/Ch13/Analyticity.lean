import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Recentering
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Analyticity

/-!
# Real analyticity of scalar power series

The local definition uses the original ordered partial sums and the original
coefficient-root radius. On an interior neighborhood the radius theorem
proves absolute summability; ordinary-sum uniqueness then gives the library
`HasSum`. Conversely, a library power-series representation converges at a
positive real increment. The exterior divergence theorem bounds the original
radius below by that increment. Shrinking the neighborhood gives the explicit
positive-radius witness in our definition.

One-dimensional continuous multilinear maps are products of real increments
times a scalar coefficient. Thus the bridge uses `AnalyticAt ℝ` even for ℂ
values. Recentering supplies a new local expansion at every interior point.
The library analytic calculus gives C∞ and the factorial derivative formula.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology ContDiff

def realCoefficientSeries (a : ℕ → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a n)

def complexRealCoefficientSeries (a : ℕ → ℂ) : FormalMultilinearSeries ℝ ℝ ℂ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a n)

def RealPowerSeriesRepresentsAt (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < realPowerSeriesRadius a ∧
    ∀ h : ℝ, |h| < r → RealPowerSeriesHasSum a c (c+h) (f (c+h))

def ComplexRealPowerSeriesRepresentsAt (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < complexPowerSeriesRadius a ∧
    ∀ h : ℝ, |h| < r → ComplexPowerSeriesHasSum a c ((c+h : ℝ) : ℂ) (f (c+h))

def RealAnalyticOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ c ∈ I, ∃ a : ℕ → ℝ, RealPowerSeriesRepresentsAt a f c

def ComplexRealAnalyticOn (f : ℝ → ℂ) (I : Set ℝ) : Prop :=
  ∀ c ∈ I, ∃ a : ℕ → ℂ, ComplexRealPowerSeriesRepresentsAt a f c

namespace RealAnalyticity

@[simp] theorem real_coefficient (a : ℕ → ℝ) (n : ℕ) :
    (realCoefficientSeries a).coeff n = a n := by
  simp [realCoefficientSeries, FormalMultilinearSeries.coeff]

@[simp] theorem complex_coefficient (a : ℕ → ℂ) (n : ℕ) :
    (complexRealCoefficientSeries a).coeff n = a n := by
  simp [complexRealCoefficientSeries, FormalMultilinearSeries.coeff]

/-- Absolute summability is derived from the radius, not assumed of an
ordinary-series value. -/
theorem real_hasSum (a : ℕ → ℝ) (c h S : ℝ)
    (hR : ENNReal.ofReal |h| < realPowerSeriesRadius a)
    (hs : RealPowerSeriesHasSum a c (c+h) S) :
    HasSum (fun n => h^n • a n) S := by
  have hn := Recentering.real_majorant a |h| (abs_nonneg _) hR
  have ht : Summable (fun n => a n * h^n) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_pow, Real.norm_eq_abs] using hn
  have hv : RealSeriesHasSum (fun n => a n * h^n) S := by
    change RealSeriesHasSum (fun n => a n * (c+h-c)^n) S at hs
    simpa only [add_sub_cancel_left] using hs
  have he := real_series_sum_unique _ _ _ (real_series_hasSum_of_hasSum ht.hasSum) hv
  simpa only [smul_eq_mul, mul_comm, he] using ht.hasSum

theorem complex_hasSum (a : ℕ → ℂ) (c h : ℝ) (S : ℂ)
    (hR : ENNReal.ofReal |h| < complexPowerSeriesRadius a)
    (hs : ComplexPowerSeriesHasSum a c ((c+h : ℝ) : ℂ) S) :
    HasSum (fun n => h^n • a n) S := by
  have hn := Recentering.complex_majorant a |h| (abs_nonneg _) hR
  have ht : Summable (fun n => a n * (h : ℂ)^n) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using hn
  have hv : ComplexSeriesHasSum (fun n => a n * (h : ℂ)^n) S := by
    change ComplexSeriesHasSum (fun n => a n * (((c+h : ℝ) : ℂ)-(c : ℂ))^n) S at hs
    simpa only [Complex.ofReal_add, add_sub_cancel_left] using hs
  have he := complex_series_sum_unique _ _ _ (complex_series_hasSum_of_hasSum ht.hasSum) hv
  simpa only [Complex.real_smul, Complex.ofReal_pow, mul_comm, he] using ht.hasSum

/-- Ordinary convergence on a neighborhood already forces a positive radius.
This justifies the radius clause in the local definition without strengthening
its mathematical hypotheses. -/
theorem real_represents_of_neighborhood (a : ℕ → ℝ) (f : ℝ → ℝ) (c r : ℝ)
    (hr : 0 < r)
    (hf : ∀ h : ℝ, |h| < r → RealPowerSeriesHasSum a c (c+h) (f (c+h))) :
    RealPowerSeriesRepresentsAt a f c := by
  have hhalf : |r/2| < r := by rw [abs_of_pos (by positivity : 0 < r/2)]; linarith
  have hle : ENNReal.ofReal (r/2) ≤ realPowerSeriesRadius a := by
    by_contra h
    apply real_powerSeries_radius_diverges a c (c+r/2) _ ⟨_, hf (r/2) hhalf⟩
    simpa only [add_sub_cancel_left, abs_of_pos (by positivity : 0 < r/2)] using lt_of_not_ge h
  refine ⟨r/4, by positivity, ?_, fun h hh => hf h (by linarith)⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r/2)).mpr
    (by linarith : r/4 < r/2)).trans_le hle

theorem complex_represents_of_neighborhood (a : ℕ → ℂ) (f : ℝ → ℂ) (c r : ℝ)
    (hr : 0 < r)
    (hf : ∀ h : ℝ, |h| < r → ComplexPowerSeriesHasSum a c ((c+h : ℝ) : ℂ) (f (c+h))) :
    ComplexRealPowerSeriesRepresentsAt a f c := by
  have hhalf : |r/2| < r := by rw [abs_of_pos (by positivity : 0 < r/2)]; linarith
  have hle : ENNReal.ofReal (r/2) ≤ complexPowerSeriesRadius a := by
    by_contra h
    apply complex_powerSeries_radius_diverges a c ((c+r/2 : ℝ) : ℂ) _ ⟨_, hf (r/2) hhalf⟩
    simpa only [Complex.ofReal_add, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r/2)] using lt_of_not_ge h
  refine ⟨r/4, by positivity, ?_, fun h hh => hf h (by linarith)⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r/2)).mpr
    (by linarith : r/4 < r/2)).trans_le hle

theorem real_represents_of_formal {a : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hp : HasFPowerSeriesAt f (realCoefficientSeries a) c) :
    RealPowerSeriesRepresentsAt a f c := by
  have hh := hasFPowerSeriesAt_iff.mp hp
  simp only [real_coefficient] at hh
  obtain ⟨δ, hδ, hsum⟩ := Metric.eventually_nhds_iff.mp hh
  apply real_represents_of_neighborhood a f c δ hδ
  intro h hh
  have hs := hsum (by simpa only [dist_zero_right, Real.norm_eq_abs] using hh)
  change RealSeriesHasSum (fun n => a n * (c+h-c)^n) (f (c+h))
  simpa only [add_sub_cancel_left, smul_eq_mul, mul_comm] using
    real_series_hasSum_of_hasSum hs

theorem complex_represents_of_formal {a : ℕ → ℂ} {f : ℝ → ℂ} {c : ℝ}
    (hp : HasFPowerSeriesAt f (complexRealCoefficientSeries a) c) :
    ComplexRealPowerSeriesRepresentsAt a f c := by
  have hh := hasFPowerSeriesAt_iff.mp hp
  simp only [complex_coefficient] at hh
  obtain ⟨δ, hδ, hsum⟩ := Metric.eventually_nhds_iff.mp hh
  apply complex_represents_of_neighborhood a f c δ hδ
  intro h hh
  have hs := hsum (by simpa only [dist_zero_right, Real.norm_eq_abs] using hh)
  change ComplexSeriesHasSum (fun n => a n * (((c+h : ℝ) : ℂ)-(c : ℂ))^n) (f (c+h))
  simpa only [Complex.ofReal_add, add_sub_cancel_left, Complex.real_smul,
    Complex.ofReal_pow, mul_comm] using complex_series_hasSum_of_hasSum hs

end RealAnalyticity

open RealAnalyticity

theorem real_powerSeries_representsAt_iff_neighborhood (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ) :
    RealPowerSeriesRepresentsAt a f c ↔ ∃ r : ℝ, 0 < r ∧
      ∀ h : ℝ, |h| < r → RealPowerSeriesHasSum a c (c+h) (f (c+h)) := by
  constructor
  · rintro ⟨r, hr, _, hf⟩
    exact ⟨r, hr, hf⟩
  · rintro ⟨r, hr, hf⟩
    exact real_represents_of_neighborhood a f c r hr hf

theorem complex_real_powerSeries_representsAt_iff_neighborhood (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ) :
    ComplexRealPowerSeriesRepresentsAt a f c ↔ ∃ r : ℝ, 0 < r ∧
      ∀ h : ℝ, |h| < r → ComplexPowerSeriesHasSum a c ((c+h : ℝ) : ℂ) (f (c+h)) := by
  constructor
  · rintro ⟨r, hr, _, hf⟩
    exact ⟨r, hr, hf⟩
  · rintro ⟨r, hr, hf⟩
    exact complex_represents_of_neighborhood a f c r hr hf

theorem real_powerSeries_representsAt_iff (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ) :
    RealPowerSeriesRepresentsAt a f c ↔ HasFPowerSeriesAt f (realCoefficientSeries a) c := by
  constructor
  · rintro ⟨r, hr, hR, hf⟩
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with h hh
    have hh' : |h| < r := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hh
    simpa only [real_coefficient] using real_hasSum a c h _
      ((ENNReal.ofReal_le_ofReal hh'.le).trans_lt hR) (hf h hh')
  · exact real_represents_of_formal

theorem complex_real_powerSeries_representsAt_iff (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ) :
    ComplexRealPowerSeriesRepresentsAt a f c ↔
      HasFPowerSeriesAt f (complexRealCoefficientSeries a) c := by
  constructor
  · rintro ⟨r, hr, hR, hf⟩
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with h hh
    have hh' : |h| < r := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hh
    simpa only [complex_coefficient] using complex_hasSum a c h _
      ((ENNReal.ofReal_le_ofReal hh'.le).trans_lt hR) (hf h hh')
  · exact complex_represents_of_formal

theorem real_analyticOn_iff (f : ℝ → ℝ) (I : Set ℝ) :
    RealAnalyticOn f I ↔ AnalyticOnNhd ℝ f I := by
  constructor
  · intro hf c hc
    obtain ⟨a, ha⟩ := hf c hc
    exact ⟨realCoefficientSeries a, (real_powerSeries_representsAt_iff a f c).mp ha⟩
  · intro hf c hc
    obtain ⟨p, hp⟩ := hf c hc
    have he : realCoefficientSeries p.coeff = p := by
      funext n
      exact FormalMultilinearSeries.mkPiRing_coeff_eq p n
    exact ⟨p.coeff, real_represents_of_formal (he.symm ▸ hp)⟩

theorem complex_real_analyticOn_iff (f : ℝ → ℂ) (I : Set ℝ) :
    ComplexRealAnalyticOn f I ↔ AnalyticOnNhd ℝ f I := by
  constructor
  · intro hf c hc
    obtain ⟨a, ha⟩ := hf c hc
    exact ⟨complexRealCoefficientSeries a, (complex_real_powerSeries_representsAt_iff a f c).mp ha⟩
  · intro hf c hc
    obtain ⟨p, hp⟩ := hf c hc
    have he : complexRealCoefficientSeries p.coeff = p := by
      funext n
      exact FormalMultilinearSeries.mkPiRing_coeff_eq p n
    exact ⟨p.coeff, complex_represents_of_formal (he.symm ▸ hp)⟩

theorem real_analytic_smooth (f : ℝ → ℝ) (I : Set ℝ) (hf : RealAnalyticOn f I) :
    ContDiffOn ℝ ∞ f I :=
  ((real_analyticOn_iff f I).mp hf).contDiffOn_of_completeSpace

theorem complex_real_analytic_smooth (f : ℝ → ℂ) (I : Set ℝ) (hf : ComplexRealAnalyticOn f I) :
    ContDiffOn ℝ ∞ f I :=
  ((complex_real_analyticOn_iff f I).mp hf).contDiffOn_of_completeSpace

/-- Recentering constructs an ordinary local expansion at each interior point. -/
theorem real_powerSeries_analytic (a : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ENNReal.ofReal |x-c| < realPowerSeriesRadius a →
      RealPowerSeriesHasSum a c x (f x)) :
    RealAnalyticOn f {x | ENNReal.ofReal |x-c| < realPowerSeriesRadius a} := by
  intro b hb
  obtain ⟨r, hr, hR, hn⟩ := real_powerSeries_recentering_neighborhood a c b hb
  refine ⟨realRecenteredCoefficient a c b,
    real_represents_of_neighborhood _ f b r hr ?_⟩
  intro h hh
  obtain ⟨S, ho, hs, _⟩ := hn h hh
  have hy : ENNReal.ofReal |b+h-c| < realPowerSeriesRadius a := by
    apply (ENNReal.ofReal_le_ofReal (show |b+h-c| ≤ |b-c|+r from ?_)).trans_lt hR
    calc
      |b+h-c| = |(b-c)+h| := by congr 1; ring
      _ ≤ |b-c|+|h| := abs_add_le _ _
      _ ≤ |b-c|+r := by linarith
  have he := real_powerSeries_sum_unique a c (b+h) S (f (b+h)) ho (hf _ hy)
  exact he ▸ hs

/-- Complex coefficients still give analyticity over the real scalar field. -/
theorem complex_real_powerSeries_analytic (a : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, ENNReal.ofReal |x-c| < complexPowerSeriesRadius a →
      ComplexPowerSeriesHasSum a c (x : ℂ) (f x)) :
    ComplexRealAnalyticOn f {x | ENNReal.ofReal |x-c| < complexPowerSeriesRadius a} := by
  intro b hb
  obtain ⟨r, hr, hR, hn⟩ := complex_powerSeries_recentering_neighborhood a c b hb
  refine ⟨complexRecenteredCoefficient a c b,
    complex_represents_of_neighborhood _ f b r hr ?_⟩
  intro h hh
  have hh' : ‖(h : ℂ)‖ < r := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hh
  obtain ⟨S, ho, hs, _⟩ := hn (h : ℂ) hh'
  have hy : ENNReal.ofReal |b+h-c| < complexPowerSeriesRadius a := by
    apply (ENNReal.ofReal_le_ofReal (show |b+h-c| ≤ |b-c|+r from ?_)).trans_lt hR
    calc
      |b+h-c| = |(b-c)+h| := by congr 1; ring
      _ ≤ |b-c|+|h| := abs_add_le _ _
      _ ≤ |b-c|+r := by linarith
  have ho' : ComplexPowerSeriesHasSum a c ((b+h : ℝ) : ℂ) S := by
    simpa only [Complex.ofReal_add] using ho
  have he := complex_powerSeries_sum_unique a c ((b+h : ℝ) : ℂ) S (f (b+h)) ho' (hf _ hy)
  simpa only [Complex.ofReal_add, he] using hs

/-- The coefficient convention is the usual Taylor normalization. -/
theorem real_coefficient_derivative (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ)
    (hf : RealPowerSeriesRepresentsAt a f c) (k : ℕ) :
    iteratedDeriv k f c = (k.factorial : ℝ) * a k := by
  obtain ⟨r, hp⟩ := (real_powerSeries_representsAt_iff a f c).mp hf
  have he := hp.factorial_smul 1 k
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, real_coefficient,
    one_pow, one_smul, nsmul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv] using he.symm

theorem complex_real_coefficient_derivative (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ)
    (hf : ComplexRealPowerSeriesRepresentsAt a f c) (k : ℕ) :
    iteratedDeriv k f c = (k.factorial : ℂ) * a k := by
  obtain ⟨r, hp⟩ := (complex_real_powerSeries_representsAt_iff a f c).mp hf
  have he := hp.factorial_smul 1 k
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, complex_coefficient,
    one_pow, one_smul, nsmul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv] using he.symm


end SingleVariableAnalysis
