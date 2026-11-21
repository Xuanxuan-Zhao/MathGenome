import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Uniqueness
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Fejer

/-! Fourier coefficient uniqueness via uniform Fejer convergence.
Equal coefficients give equal finite partial sums and equal Cesaro means;
their pointwise limits therefore agree. No quotient by almost-everywhere
equality is used, and continuity remains a hypothesis in every conclusion. -/
noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators

namespace Fourier

theorem partialSum_eq_of_coeff_eq (f g : ℝ → ℂ)
    (hf : ∀ n : ℤ, ComplexIntegrable (fun y => f y * fourierMode (-n) y)
      (-Real.pi) Real.pi)
    (hg : ∀ n : ℤ, ComplexIntegrable (fun y => g y * fourierMode (-n) y)
      (-Real.pi) Real.pi)
    (h : ∀ n : ℤ, fourierCoeff f n (hf n) = fourierCoeff g n (hg n))
    (N : ℕ) (x : ℝ) : fourierPartialSum f hf N x = fourierPartialSum g hg N x := by
  unfold fourierPartialSum Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun z : ℂ => z * fourierMode n x) (h n)

theorem fejerMean_eq_of_coeff_eq (f g : ℝ → ℂ)
    (hf : ∀ n : ℤ, ComplexIntegrable (fun y => f y * fourierMode (-n) y)
      (-Real.pi) Real.pi)
    (hg : ∀ n : ℤ, ComplexIntegrable (fun y => g y * fourierMode (-n) y)
      (-Real.pi) Real.pi)
    (h : ∀ n : ℤ, fourierCoeff f n (hf n) = fourierCoeff g n (hg n))
    (N : ℕ) (x : ℝ) : fejerMean f hf N x = fejerMean g hg N x := by
  unfold fejerMean Specs.SingleVariableAnalysis.Ch19.FejerKernel.meanValue
  congr 1
  exact Finset.sum_congr rfl (fun n _ => partialSum_eq_of_coeff_eq f g hf hg h n x)

end Fourier

theorem fourierCoeff_zero_implies_zero :
    Specs.SingleVariableAnalysis.Ch19.Uniqueness.complexZero := by
  intro f hf hp h hz x
  have hm (N : ℕ) : fejerMean f h N x = 0 := by
    simp [fejerMean, Specs.SingleVariableAnalysis.Ch19.FejerKernel.meanValue,
      Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue, hz]
  by_contra hx
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hx
  obtain ⟨N, hN⟩ := fejer_uniform_convergence f hf hp h ‖f x‖ hpos
  have hh := hN N le_rfl x
  change ‖fejerMean f h N x - f x‖ < ‖f x‖ at hh
  rw [hm N, zero_sub, norm_neg] at hh
  exact (lt_irrefl _ hh)

theorem fourierCoeff_unique :
    Specs.SingleVariableAnalysis.Ch19.Uniqueness.complexUnique := by
  intro f g hf hg hp hq hfi hgi he
  funext x
  by_contra hx
  have hpos : 0 < ‖f x - g x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  obtain ⟨N, hN⟩ := fejer_uniform_convergence f hf hp hfi _ (half_pos hpos)
  obtain ⟨M, hM⟩ := fejer_uniform_convergence g hg hq hgi _ (half_pos hpos)
  let k := max N M
  have h₁ := hN k (le_max_left _ _) x
  have h₂ := hM k (le_max_right _ _) x
  change ‖fejerMean f hfi k x - f x‖ < ‖f x - g x‖ / 2 at h₁
  change ‖fejerMean g hgi k x - g x‖ < ‖f x - g x‖ / 2 at h₂
  have hm := Fourier.fejerMean_eq_of_coeff_eq f g hfi hgi he k x
  have ht : ‖f x - g x‖ ≤ ‖f x - fejerMean f hfi k x‖ +
      ‖fejerMean f hfi k x - g x‖ := by
    calc
      _ = ‖(f x - fejerMean f hfi k x) + (fejerMean f hfi k x - g x)‖ := by
        rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev (f x) (fejerMean f hfi k x)] at ht
  rw [← hm] at h₂
  linarith

theorem fourierCoeff_zero_implies_zero_real :
    Specs.SingleVariableAnalysis.Ch19.Uniqueness.realZero := by
  intro f hf hp h hz x
  have he := fourierCoeff_zero_implies_zero (fun y => (f y : ℂ))
    (Complex.continuous_ofReal.comp hf) (hp.comp Complex.ofReal) h hz x
  exact_mod_cast he

theorem fourierCoeff_unique_real :
    Specs.SingleVariableAnalysis.Ch19.Uniqueness.realUnique := by
  intro f g hf hg hp hq hfi hgi he
  have heq := fourierCoeff_unique (fun y => (f y : ℂ)) (fun y => (g y : ℂ))
    (Complex.continuous_ofReal.comp hf) (Complex.continuous_ofReal.comp hg)
    (hp.comp Complex.ofReal) (hq.comp Complex.ofReal) hfi hgi he
  funext x
  exact Complex.ofReal_injective (congrFun heq x)

end SingleVariableAnalysis
