import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.Tan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Product

/-!
K03.07.tan. Tangent is defined only on its natural domain. The quotient
rule and the series Pythagorean identity give its real derivative.
For the limits we use Mathlib's `Real.tendsto_tan_pi_div_two` and
`Real.tendsto_tan_neg_pi_div_two` (Trigonometric.Basic). Those results
use the positive one-sided cosine limit and the nonzero sine limit.
Translation by integer periods supplies every pole, including negative
integer indices. The canonical identities used in this transfer are
proved upstream for the actual factorial series and the constructed π.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology

def realTangentDomain : Set ℝ := {x | realSeriesCos x ≠ 0}
def realTangent : realTangentDomain → ℝ :=
  fun x => realSeriesSin x / realSeriesCos x

namespace Tan
private theorem sine_eq : realSeriesSin = Real.sin :=
  funext fun x => (sinCosSeries_eq_real x).1
private theorem cosine_eq : realSeriesCos = Real.cos :=
  funext fun x => (sinCosSeries_eq_real x).2

private theorem tangent_eq : realTangent = fun x : realTangentDomain => Real.tan (x : ℝ) := by
  funext x
  change realSeriesSin (x : ℝ) / realSeriesCos (x : ℝ) = Real.tan x
  rw [sine_eq, cosine_eq, Real.tan_eq_sin_div_cos]

theorem domain_description (x : ℝ) :
    x ∈ realTangentDomain ↔ ¬ ∃ k : ℤ, x = analyticPi / 2 + k * analyticPi := by
  change realSeriesCos x ≠ 0 ↔ _
  have h : firstPositiveCosineZero = analyticPi / 2 := by
    unfold analyticPi
    ring
  rw [ne_eq, PiPeriod.piPeriod_cosine_zeros x, h]

theorem pole_excluded (k : ℤ) :
    analyticPi / 2 + k * analyticPi ∉ realTangentDomain := by
  rw [domain_description]
  exact not_not.mpr ⟨k, rfl⟩

theorem domain_period (x : ℝ) :
    x + analyticPi ∈ realTangentDomain ↔ x ∈ realTangentDomain := by
  change realSeriesCos (x + analyticPi) ≠ 0 ↔ realSeriesCos x ≠ 0
  rw [cosine_eq, PiPeriod.analyticPi_eq_pi, Real.cos_add_pi, neg_ne_zero]

theorem periodic (x : ℝ) (hx : x ∈ realTangentDomain)
    (hshift : x + analyticPi ∈ realTangentDomain) :
    realTangent ⟨x + analyticPi, hshift⟩ = realTangent ⟨x, hx⟩ := by
  simp only [realTangent, sine_eq, cosine_eq, PiPeriod.analyticPi_eq_pi,
    Real.sin_add_pi, Real.cos_add_pi, neg_div_neg_eq]

theorem hasDerivAt (x : ℝ) (hx : x ∈ realTangentDomain) :
    HasDerivAt (fun t => realSeriesSin t / realSeriesCos t)
      (1 / realSeriesCos x ^ 2) x := by
  have h := (real_sinCosSeries_hasDerivAt x).1.div
    (real_sinCosSeries_hasDerivAt x).2 hx
  change HasDerivAt (fun t => realSeriesSin t / realSeriesCos t)
    ((realSeriesCos x * realSeriesCos x - realSeriesSin x * -realSeriesSin x) /
      realSeriesCos x ^ 2) x at h
  have hn : realSeriesCos x * realSeriesCos x - realSeriesSin x * -realSeriesSin x = 1 := by
    nlinarith [realSeriesSin_sq_add_realSeriesCos_sq x]
  rwa [hn] at h

theorem extension_hasDerivAt (f : ℝ → ℝ)
    (hf : ∀ x : realTangentDomain, f x = realTangent x)
    (x : ℝ) (hx : x ∈ realTangentDomain) :
    HasDerivAt f (1 / realSeriesCos x ^ 2) x := by
  have hopen : IsOpen realTangentDomain := by
    change IsOpen {t | realSeriesCos t ≠ 0}
    rw [cosine_eq]
    exact isOpen_ne_fun Real.continuous_cos continuous_const
  have heq : f =ᶠ[𝓝 x] (fun t => realSeriesSin t / realSeriesCos t) := by
    filter_upwards [hopen.mem_nhds hx] with t ht
    exact hf ⟨t, ht⟩
  exact (hasDerivAt x hx).congr_of_eventuallyEq heq

private theorem sub_tendsto_left (a c : ℝ) :
    Tendsto (fun x : ℝ => x - c) (𝓝[<] (a + c)) (𝓝[<] a) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hc : Continuous (fun x : ℝ => x - c) := continuous_id.sub continuous_const
    simpa only [add_sub_cancel_right] using
      (hc.tendsto (a + c)).mono_left
        (show 𝓝[<] (a + c) ≤ 𝓝 (a + c) from inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change x - c < a
    change x < a + c at hx
    linarith

private theorem sub_tendsto_right (a c : ℝ) :
    Tendsto (fun x : ℝ => x - c) (𝓝[>] (a + c)) (𝓝[>] a) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hc : Continuous (fun x : ℝ => x - c) := continuous_id.sub continuous_const
    simpa only [add_sub_cancel_right] using
      (hc.tendsto (a + c)).mono_left
        (show 𝓝[>] (a + c) ≤ 𝓝 (a + c) from inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change a < x - c
    change a + c < x at hx
    linarith

theorem left_pole_limit (k : ℤ) :
    Tendsto realTangent
      (comap (fun x : realTangentDomain => (x : ℝ))
        (𝓝[<] (analyticPi / 2 + k * analyticPi))) atTop := by
  rw [PiPeriod.analyticPi_eq_pi]
  have h : Tendsto Real.tan (𝓝[<] (Real.pi / 2 + k * Real.pi)) atTop := by
    simpa only [Function.comp_def, Real.tan_sub_int_mul_pi] using
      Real.tendsto_tan_pi_div_two.comp (sub_tendsto_left (Real.pi / 2) (k * Real.pi))
  rw [tangent_eq]
  exact h.comp
      (tendsto_comap : Tendsto (fun x : realTangentDomain => (x : ℝ))
        (comap (fun x : realTangentDomain => (x : ℝ))
          (𝓝[<] (Real.pi / 2 + k * Real.pi))) _)

theorem right_pole_limit (k : ℤ) :
    Tendsto realTangent
      (comap (fun x : realTangentDomain => (x : ℝ))
        (𝓝[>] (analyticPi / 2 + k * analyticPi))) atBot := by
  rw [PiPeriod.analyticPi_eq_pi]
  have he : -(Real.pi / 2) + (↑(k + 1) : ℝ) * Real.pi =
      Real.pi / 2 + k * Real.pi := by push_cast; ring
  have h : Tendsto Real.tan (𝓝[>] (Real.pi / 2 + k * Real.pi)) atBot := by
    simpa only [Function.comp_def, Real.tan_sub_int_mul_pi, he] using
      Real.tendsto_tan_neg_pi_div_two.comp
        (sub_tendsto_right (-(Real.pi / 2)) ((↑(k + 1) : ℝ) * Real.pi))
  rw [tangent_eq]
  exact h.comp
      (tendsto_comap : Tendsto (fun x : realTangentDomain => (x : ℝ))
        (comap (fun x : realTangentDomain => (x : ℝ))
          (𝓝[>] (Real.pi / 2 + k * Real.pi))) _)

end Tan
end SingleVariableAnalysis
