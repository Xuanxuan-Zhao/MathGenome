import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FejerConcentration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.FejerKernel

noncomputable section
namespace SingleVariableAnalysis
open Riemann Fourier
open Specs.SingleVariableAnalysis.Ch19.FejerConcentration

abbrev fejerOutsideMass := massValue

namespace Fourier

/-- On the half period, the sine denominator is bounded below by its value
at δ/2. Squaring removes the sign on the negative half period. -/
theorem fejer_sine_denominator {δ t : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hlo : δ ≤ |t|) (hhi : |t| ≤ Real.pi) :
    0 < Real.sin (δ/2) ∧ Real.sin (δ/2)^2 ≤ Real.sin (t/2)^2 := by
  have hs : 0 < Real.sin (δ/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hm : Real.sin (δ/2) ≤ Real.sin (|t|/2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith)
  have heq : Real.sin (|t|/2)^2 = Real.sin (t/2)^2 := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, neg_div, Real.sin_neg, neg_sq]
  exact ⟨hs, heq ▸ (pow_le_pow_left₀ hs.le hm 2)⟩

end Fourier

theorem fejerKernel_outside_bound : pointwiseBound := by
  intro δ hδ hδπ N t hlo hhi
  obtain ⟨hs, hsquare⟩ := fejer_sine_denominator hδ hδπ hlo hhi
  have ht : Real.sin (t/2) ≠ 0 := by
    intro hz
    rw [hz] at hsquare
    nlinarith [sq_pos_of_pos hs]
  have hlat : ∀ k : ℤ, t ≠ (k : ℝ)*(2*Real.pi) := by
    intro k he
    apply ht
    rw [show t/2 = (k : ℝ)*Real.pi by linarith [he], Real.sin_int_mul_pi]
  refine ⟨fejerKernel_nonnegative N t, ?_⟩
  rw [fejerKernel_quotient N t hlat, Complex.ofReal_re]
  have hn : 0 < (N : ℝ)+1 := by positivity
  have hd : 0 < ((N : ℝ)+1) * Real.sin (t/2)^2 :=
    mul_pos hn (sq_pos_of_ne_zero ht)
  calc
    _ ≤ 1 / (((N : ℝ)+1) * Real.sin (t/2)^2) :=
      div_le_div_of_nonneg_right (Real.sin_sq_le_one _) hd.le
    _ ≤ 1 / (((N : ℝ)+1) * Real.sin (δ/2)^2) :=
      one_div_le_one_div_of_le (mul_pos hn (sq_pos_of_pos hs))
        (mul_le_mul_of_nonneg_left hsquare hn.le)

theorem fejerKernel_outside_integrable : outsideIntegrability := by
  intro δ hδ hδπ N
  have hc : Continuous (fun t => (fejerKernel N t).re) :=
    Complex.continuous_re.comp (fejerKernel_continuous N)
  exact ⟨realIntegrable_of_continuousOn (by linarith) hc.continuousOn,
    realIntegrable_of_continuousOn hδπ.le hc.continuousOn⟩

namespace Fourier

theorem realIntegral_nonnegative {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (h : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    0 ≤ realIntegral f hf := by
  obtain ⟨hz, hv⟩ := real_zero_value hf.ordered
  have hm := realIntegral_mono (fun _ => 0) f hz hf h
  change realIntegral (fun _ => 0) hz ≤ realIntegral f hf at hm
  rwa [hv] at hm

end Fourier

theorem fejerKernel_outside_integral_bound : outsideIntegralBound := by
  intro δ hδ hδπ N hl hr
  have hleft : ∀ t ∈ Set.Icc (-Real.pi) (-δ),
      (fejerKernel N t).re ≤ 1 / (((N : ℝ)+1) * Real.sin (δ/2)^2) := by
    intro t ht
    have ht0 : t ≤ 0 := by linarith [ht.2]
    exact (fejerKernel_outside_bound δ hδ hδπ N t
      (by rw [abs_of_nonpos ht0]; linarith [ht.2])
      (by rw [abs_of_nonpos ht0]; linarith [ht.1])).2
  have hright : ∀ t ∈ Set.Icc δ Real.pi,
      (fejerKernel N t).re ≤ 1 / (((N : ℝ)+1) * Real.sin (δ/2)^2) := by
    intro t ht
    have ht0 : 0 ≤ t := hδ.le.trans ht.1
    exact (fejerKernel_outside_bound δ hδ hδπ N t
      (by simpa only [abs_of_nonneg ht0] using ht.1)
      (by simpa only [abs_of_nonneg ht0] using ht.2)).2
  have hl0 := realIntegral_nonnegative hl (fun t _ => fejerKernel_nonnegative N t)
  have hr0 := realIntegral_nonnegative hr (fun t _ => fejerKernel_nonnegative N t)
  have hlb := realIntegral_le_mul_bound hl hleft
  have hrb := realIntegral_le_mul_bound hr hright
  have hπ : 0 < 2*Real.pi := by positivity
  have hB : 0 ≤ 1 / (((N : ℝ)+1) * Real.sin (δ/2)^2) := by positivity
  change 0 ≤ (1/(2*Real.pi)) * (realIntegral _ hl + realIntegral _ hr) ∧ _
  constructor
  · exact mul_nonneg (one_div_pos.mpr hπ).le (add_nonneg hl0 hr0)
  · change (1/(2*Real.pi)) * (realIntegral _ hl + realIntegral _ hr) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add hlb hrb)
      (one_div_pos.mpr hπ).le).trans
    have hlen : (-δ - -Real.pi) + (Real.pi - δ) ≤ 2*Real.pi := by linarith
    calc
      _ = (1/(2*Real.pi)) * (((-δ - -Real.pi) + (Real.pi - δ)) *
          (1 / (((N : ℝ)+1) * Real.sin (δ/2)^2))) := by ring
      _ ≤ (1/(2*Real.pi)) * ((2*Real.pi) *
          (1 / (((N : ℝ)+1) * Real.sin (δ/2)^2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlen hB)
          (one_div_pos.mpr hπ).le
      _ = _ := by field_simp

theorem fejerKernel_concentration : concentration := by
  intro δ hδ hδπ hl hr
  have hlim : Filter.Tendsto (fun N : ℕ =>
      1 / (((N : ℝ)+1) * Real.sin (δ/2)^2)) Filter.atTop (nhds 0) := by
    have hrec : Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ)+1))
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ)+1)) Filter.atTop (nhds (0 : ℝ)))
    simpa only [zero_div, div_mul_eq_div_div] using hrec.div_const (Real.sin (δ/2)^2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N => (fejerKernel_outside_integral_bound δ hδ hδπ N (hl N) (hr N)).1)
    (fun N => (fejerKernel_outside_integral_bound δ hδ hδπ N (hl N) (hr N)).2)

end SingleVariableAnalysis
