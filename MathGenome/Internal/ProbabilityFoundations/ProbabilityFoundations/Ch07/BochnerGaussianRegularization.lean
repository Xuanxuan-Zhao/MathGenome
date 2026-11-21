import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.BochnerGaussianRegularization
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.BochnerGaussian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The Gaussian regularization stage of the Euclidean Bochner theorem.
MathGenome proves positive inversion in the `exp(-2πi⟪t,x⟫)` convention.
We apply it to `t ↦ φ((2π) • t)` with damping parameter `2πε` and prove
that its density is exactly the manuscript's `(2π)⁻ᵈ` inverse integral. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate

namespace ProbabilityFoundations.Ch07

noncomputable def regularizedTransform {d : ℕ} (φ : Euclidean d → ℂ)
    (ε : ℝ) (t : Euclidean d) : ℂ :=
  φ t * (Real.exp (-ε * ‖t‖ ^ 2 / 2) : ℂ)

noncomputable def regularizedInverseComplex {d : ℕ} (φ : Euclidean d → ℂ)
    (ε : ℝ) (x : Euclidean d) : ℂ :=
  ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) *
    ∫ t : Euclidean d, Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) *
      regularizedTransform φ ε t

noncomputable def regularizedDensity {d : ℕ} (φ : Euclidean d → ℂ)
    (ε : ℝ) (x : Euclidean d) : ℝ := (regularizedInverseComplex φ ε x).re

noncomputable def regularizedMeasure {d : ℕ} (φ : Euclidean d → ℂ)
    (ε : ℝ) : Measure (Euclidean d) :=
  volume.withDensity (fun x => ENNReal.ofReal (regularizedDensity φ ε x))

private abbrev MGPositiveDefinite {d : ℕ} (φ : Euclidean d → ℂ) :=
  ExpandedFA.PartIV.PositiveDefiniteContinuity.Spec.PositiveDefinite φ

/-- The finite-form conventions agree after interchanging the two indices. -/
theorem isPositiveDefinite_iff_mathGenome {d : ℕ} (φ : Euclidean d → ℂ) :
    IsPositiveDefinite φ ↔ MGPositiveDefinite φ := by
  have heq (n : ℕ) (t : Fin n → Euclidean d) (c : Fin n → ℂ) :
      characteristicQuadraticForm φ t c =
        ∑ j, ∑ k, conj (c j) * c k * φ (t k - t j) := by
    rw [characteristicQuadraticForm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [IsPositiveDefinite, MGPositiveDefinite,
    ExpandedFA.PartIV.PositiveDefiniteContinuity.Spec.PositiveDefinite, heq]

private def scaledFunction {d : ℕ} (φ : Euclidean d → ℂ) (t : Euclidean d) : ℂ :=
  φ ((2 * Real.pi) • t)

private theorem scaledFunction_positiveDefinite {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : IsPositiveDefinite φ) : MGPositiveDefinite (scaledFunction φ) := by
  have hp := (isPositiveDefinite_iff_mathGenome φ).mp hφ
  intro n t c
  simpa only [scaledFunction, smul_sub] using
    hp n (fun j => (2 * Real.pi) • t j) c

private theorem scaledFunction_continuous {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : Continuous φ) : Continuous (scaledFunction φ) := by
  unfold scaledFunction
  fun_prop

private theorem scaled_damped {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ)
    (t : Euclidean d) :
    ExpandedFA.PartIV.BochnerGaussian.damped (scaledFunction φ) (2 * Real.pi * ε) t =
      regularizedTransform φ ε ((2 * Real.pi) • t) := by
  unfold ExpandedFA.PartIV.BochnerGaussian.damped
    ExpandedFA.PartIV.BochnerGaussian.gaussianFactor scaledFunction regularizedTransform
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  ring

private theorem unscaled_damped {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ) :
    ExpandedFA.PartIV.BochnerGaussian.damped φ (ε / (2 * Real.pi)) =
      regularizedTransform φ ε := by
  funext t
  unfold ExpandedFA.PartIV.BochnerGaussian.damped
    ExpandedFA.PartIV.BochnerGaussian.gaussianFactor regularizedTransform
  congr 2
  field_simp

/-- Exact change of variables, including the dimension-dependent Jacobian. -/
private theorem scaled_density {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ) :
    ExpandedFA.PartIV.BochnerGaussian.density (scaledFunction φ) (2 * Real.pi * ε) =
      regularizedInverseComplex φ ε := by
  funext x
  unfold ExpandedFA.PartIV.BochnerGaussian.density ExpandedFA.Fourier.integralFourier
  simp_rw [scaled_damped]
  have heq (t : Euclidean d) :
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ t x : ℂ)) *
        regularizedTransform φ ε ((2 * Real.pi) • t) =
      (fun u => Complex.exp (-Complex.I * (inner ℝ u x : ℂ)) *
        regularizedTransform φ ε u) ((2 * Real.pi) • t) := by
    simp only [inner_smul_left, starRingEnd_apply, star_trivial, Complex.ofReal_mul]
    congr 2
    push_cast
    ring
  simp_rw [heq]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun u : Euclidean d => Complex.exp (-Complex.I * (inner ℝ u x : ℂ)) *
      regularizedTransform φ ε u) (2 * Real.pi)
    (hR := by positivity)]
  have hc : ((2 * Real.pi) ^ Module.finrank ℝ (Euclidean d))⁻¹ =
      (2 * Real.pi) ^ (-(d : ℝ)) := by
    simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hc]
  rfl

/-- The exact Gaussian regularization of the source is a characteristic
function with the specified bounded continuous inverse density. -/
theorem gaussian_regularization :
    Specs.ProbabilityFoundations.Ch07.BochnerGaussianRegularization.GaussianRegularization := by
  intro d φ hc hp hzero ε hε
  change IsPositiveDefinite φ at hp
  have hpg := (isPositiveDefinite_iff_mathGenome φ).mp hp
  have hη : 0 < ε / (2 * Real.pi) := by positivity
  have hi : Integrable (regularizedTransform φ ε) := by
    rw [← unscaled_damped]
    exact ExpandedFA.PartIV.BochnerGaussian.damping_integrable d φ hpg hc.continuousAt _ hη
  have hpd : IsPositiveDefinite (regularizedTransform φ ε) := by
    apply (isPositiveDefinite_iff_mathGenome _).mpr
    rw [← unscaled_damped]
    exact ExpandedFA.PartIV.BochnerGaussian.positiveDefinite_damped hpg hη
  have hps := scaledFunction_positiveDefinite hp
  have hcs := scaledFunction_continuous hc
  have hεs : 0 < 2 * Real.pi * ε := by positivity
  have hs0 : scaledFunction φ 0 = 1 := by simp [scaledFunction, hzero]
  have hid := scaled_density φ ε
  have hn := ExpandedFA.PartIV.BochnerGaussian.fourier_nonnegative d
    (scaledFunction φ) hps hcs.continuousAt _ hεs
  have hm := ExpandedFA.PartIV.BochnerGaussian.fourier_mass d
    (scaledFunction φ) hps hcs.continuousAt _ hεs
  rw [hid] at hn hm
  have hcont : Continuous (regularizedInverseComplex φ ε) := by
    rw [← hid]
    exact ExpandedFA.PartIV.BochnerGaussian.density_continuous hps hcs.continuousAt hεs
  have hbounded : ∃ C : ℝ, ∀ x, ‖regularizedInverseComplex φ ε x‖ ≤ C := by
    refine ⟨∫ t, ‖ExpandedFA.PartIV.BochnerGaussian.damped
      (scaledFunction φ) (2 * Real.pi * ε) t‖, ?_⟩
    intro x
    rw [← hid, ExpandedFA.PartIV.BochnerGaussian.density,
      ExpandedFA.PartIV.BochnerGaussian.integralFourier_eq_native]
    exact Real.norm_fourier_le_integral_norm _ x
  have hmass : (∫ x, regularizedDensity φ ε x) = 1 := by
    calc
      _ = (∫ x, regularizedInverseComplex φ ε x).re := integral_re hm.1
      _ = 1 := by rw [hm.2, hs0]; rfl
  have hmeasure : regularizedMeasure φ ε =
      ExpandedFA.PartIV.BochnerGaussian.densityMeasure (scaledFunction φ)
        (2 * Real.pi * ε) := by
    unfold regularizedMeasure ExpandedFA.PartIV.BochnerGaussian.densityMeasure
    simp only [hid, regularizedDensity]
  have hrep := ExpandedFA.PartIV.BochnerGaussian.representation d
    (scaledFunction φ) hps hcs.continuousAt _ hεs
  have hprob : IsProbabilityMeasure (regularizedMeasure φ ε) := by
    constructor
    rw [hmeasure, hrep.2.2.1, hs0]
    simp
  refine ⟨hi, hpd, hn, hcont, hbounded,
    Complex.continuous_re.comp hcont, hm.1.re, hmass, hprob, ?_⟩
  intro t
  change characteristicFunction (regularizedMeasure φ ε) t = regularizedTransform φ ε t
  rw [characteristicFunction_eq_integral, hmeasure]
  have hrepr := hrep.2.2.2 ((2 * Real.pi)⁻¹ • t)
  rw [scaled_damped, smul_smul, mul_inv_cancel₀ (by positivity :
    (2 * Real.pi : ℝ) ≠ 0), one_smul] at hrepr
  rw [hrepr]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp only [inner_smul_left, starRingEnd_apply, star_trivial,
    Complex.ofReal_mul, Complex.ofReal_inv]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end ProbabilityFoundations.Ch07
