import MathGenome.Internal.FourierSobolev.Specs.P102.U3.TemperedFourier
import MathGenome.Internal.FourierSobolev.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.P102.U3.FourierInversion
import MathGenome.Internal.FourierSobolev.P102.U3.Plancherel

noncomputable section
open MeasureTheory LineDeriv
open scoped FourierTransform

namespace P102.U3.TemperedFourier

/-- Transposition on the strong dual uses bounded convergence. The continuity
proof in `precomp` maps each von Neumann bounded set through the test operator. -/
def fourierStrong : P102.Specs.U3.TemperedFourier.strongMap_type := P102.Specs.U3.TemperedFourier.fourierStrong_value
def checkStrong : P102.Specs.U3.TemperedFourier.strongMap_type := P102.Specs.U3.TemperedFourier.checkStrong_value
/-- Transposition on the pointwise dual is a separate continuous map. -/
def fourierWeak : P102.Specs.U3.TemperedFourier.weakMap_type := P102.Specs.U3.TemperedFourier.fourierWeak_value
def checkWeak : P102.Specs.U3.TemperedFourier.weakMap_type := P102.Specs.U3.TemperedFourier.checkWeak_value

def derivative : P102.Specs.U3.TemperedFourier.coordinateMap_type := P102.Specs.U3.TemperedFourier.derivative_value
def multiply : P102.Specs.U3.TemperedFourier.coordinateMap_type := P102.Specs.U3.TemperedFourier.multiply_value
def regularLp : P102.Specs.U3.TemperedFourier.regularLp_type := P102.Specs.U3.TemperedFourier.regularLp_value

theorem transposition : P102.Specs.U3.TemperedFourier.transposition_type := by
  intro d U φ
  exact ⟨rfl, rfl⟩

theorem strong_inverse : P102.Specs.U3.TemperedFourier.strongInverse_type := by
  intro d
  constructor <;> ext U φ
  · change U (𝓕 (𝓕⁻ φ : Test d)) = U φ
    rw [FourierTransform.fourier_fourierInv_eq]
  · change U (𝓕⁻ (𝓕 φ : Test d)) = U φ
    rw [FourierTransform.fourierInv_fourier_eq]

theorem weak_inverse : P102.Specs.U3.TemperedFourier.weakInverse_type := by
  intro d
  constructor <;> ext U φ
  · change U (𝓕 (𝓕⁻ φ : Test d)) = U φ
    rw [FourierTransform.fourier_fourierInv_eq]
  · change U (𝓕⁻ (𝓕 φ : Test d)) = U φ
    rw [FourierTransform.fourierInv_fourier_eq]

theorem strong_weak : P102.Specs.U3.TemperedFourier.strongWeak_type := by
  intro d U
  exact ⟨rfl, rfl⟩

theorem bounded_testing : P102.Specs.U3.TemperedFourier.boundedTesting_type := by
  intro d B hB
  refine ⟨hB.image (P102.Specs.U3.fourierValue d),
    hB.image (P102.Specs.U3.checkValue d), ?_⟩
  intro U V
  constructor <;> constructor
  · rintro h ψ ⟨φ, hφ, rfl⟩
    exact h φ hφ
  · intro h φ hφ
    exact h _ ⟨φ, hφ, rfl⟩
  · rintro h ψ ⟨φ, hφ, rfl⟩
    exact h φ hφ
  · intro h φ hφ
    exact h _ ⟨φ, hφ, rfl⟩

theorem continuity : P102.Specs.U3.TemperedFourier.continuity_type := by
  intro d
  exact ⟨(fourierStrong d).continuous, (checkStrong d).continuous,
    (fourierWeak d).continuous, (checkWeak d).continuous⟩

/-- Explicit strong-dual automorphism, with continuous positive-sign inverse. -/
def strongEquiv (d : ℕ) : Tempered d ≃L[ℂ] Tempered d where
  toLinearMap := (fourierStrong d).toLinearMap
  invFun := checkStrong d
  left_inv U := by
    exact congrArg (fun A : Tempered d →L[ℂ] Tempered d => A U) (strong_inverse d).1
  right_inv U := by
    exact congrArg (fun A : Tempered d →L[ℂ] Tempered d => A U) (strong_inverse d).2
  continuous_toFun := (fourierStrong d).continuous
  continuous_invFun := (checkStrong d).continuous

/-- Explicit weak-dual automorphism on exactly the same functionals. -/
def weakEquiv (d : ℕ) : WeakTempered d ≃L[ℂ] WeakTempered d where
  toLinearMap := (fourierWeak d).toLinearMap
  invFun := checkWeak d
  left_inv U := by
    exact congrArg (fun A : WeakTempered d →L[ℂ] WeakTempered d => A U) (weak_inverse d).1
  right_inv U := by
    exact congrArg (fun A : WeakTempered d →L[ℂ] WeakTempered d => A U) (weak_inverse d).2
  continuous_toFun := (fourierWeak d).continuous
  continuous_invFun := (checkWeak d).continuous

theorem strong_automorphism : P102.Specs.U3.TemperedFourier.strongAutomorphism_type := by
  intro d
  exact ⟨strongEquiv d, fun _ => rfl, fun _ => rfl⟩

theorem weak_automorphism : P102.Specs.U3.TemperedFourier.weakAutomorphism_type := by
  intro d
  exact ⟨weakEquiv d, fun _ => rfl, fun _ => rfl⟩

theorem coordinate_actions : P102.Specs.U3.TemperedFourier.coordinateActions_type := by
  intro d j U φ
  exact ⟨map_neg U _, rfl⟩

/-- The derivative and coordinate multiplication rules are proved by testing;
there is no conjugation in moving a complex scalar through the functional. -/
theorem fourier_derivative : P102.Specs.U3.TemperedFourier.fourierDerivative_type := by
  intro d j U
  ext φ
  change U (-∂_{coordinateVector j} (𝓕 φ : Test d)) =
    (2 * Real.pi * Complex.I) * U (𝓕 (coordinateMul j φ) : Test d)
  rw [map_neg, SchwartzMap.lineDerivOp_fourier_eq]
  simp only [coordinateMul_eq_real,
    FourierTransform.fourier_smul, map_smul, smul_eq_mul, neg_mul, neg_neg]

theorem fourier_multiply : P102.Specs.U3.TemperedFourier.fourierMultiply_type := by
  intro d j U
  ext φ
  change U (coordinateMul j (𝓕 φ : Test d)) =
    (-(2 * Real.pi * Complex.I)⁻¹) * U (𝓕 (-∂_{coordinateVector j} φ) : Test d)
  rw [FourierTransform.fourier_neg, map_neg, SchwartzMap.fourier_lineDerivOp_eq]
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  simp only [coordinateMul_eq_real,
    map_smul, smul_eq_mul, neg_mul, mul_neg, neg_neg]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Integral formula for the underlying Lp functional; the scalar test is the
first factor in Mathlib's pairing, and multiplication commutes in ℂ. -/
theorem regularLp_apply {d : ℕ} {p : ENNReal} [Fact (1 ≤ p)]
    (f : Lp (α := Euclidean d) ℂ p volume) (φ : Test d) :
    regularLp f φ = ∫ x, f x * φ x := by
  change Lp.toTemperedDistribution f φ = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul, mul_comm]

theorem regular_l1 : P102.Specs.U3.TemperedFourier.regularL1_type := by
  intro d f hf φ
  refine ⟨(memLp_one_iff_integrable.mpr hf).integrable_mul (φ.memLp_top), ?_⟩
  rw [← show regularLp (memLp_one_iff_integrable.mpr hf).toLp =
      P102.Specs.U3.TemperedFourier.regularLp_value (memLp_one_iff_integrable.mpr hf).toLp from rfl,
    regularLp_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr hf).coeFn_toLp] with x hx
  rw [hx]

/-- The L¹ input has Schwartz-test products in L¹, and Fubini transfers the
Fourier operation. The output is bounded, so its products with tests are L¹. -/
theorem l1_compatibility : P102.Specs.U3.TemperedFourier.l1Compatibility_type := by
  intro d f hf
  have hF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hC : Continuous (𝓕⁻ f) := FourierInversion.continuous_check hf
  constructor
  · intro φ
    refine ⟨φ.integrable.bdd_mul hF.aestronglyMeasurable
      (Filter.Eventually.of_forall (Real.norm_fourier_le_integral_norm f)), ?_⟩
    change P102.Specs.U3.TemperedFourier.regularLp_value
      (memLp_one_iff_integrable.mpr hf).toLp (𝓕 φ : Test d) = _
    rw [(regular_l1 d f hf (𝓕 φ)).2]
    exact (FourierInversion.integral_fourier_mul f (φ : Euclidean d → ℂ)
      hf φ.integrable).symm
  · intro φ
    refine ⟨φ.integrable.bdd_mul (c := ∫ x, ‖f x‖) hC.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_), ?_⟩
    · rw [Real.fourierInv_eq_fourier_neg]
      exact Real.norm_fourier_le_integral_norm f (-x)
    · change P102.Specs.U3.TemperedFourier.regularLp_value
        (memLp_one_iff_integrable.mpr hf).toLp (𝓕⁻ φ : Test d) = _
      rw [(regular_l1 d f hf (𝓕⁻ φ)).2]
      rw [SchwartzMap.fourierInv_coe]
      exact (FourierInversion.integral_check_mul f (φ : Euclidean d → ℂ)
        hf φ.integrable).symm

theorem regular_l2 : P102.Specs.U3.TemperedFourier.regularL2_type := by
  intro d f φ
  exact ⟨(Lp.memLp f).integrable_mul (φ.memLp 2), regularLp_apply f φ⟩

/-- The library's L² extension commutes with the weak distribution embedding.
Equality here is equality of the underlying functionals, so also holds on the
strong dual; it does not assert continuity of weak-to-strong retopologization. -/
theorem l2_compatibility : P102.Specs.U3.TemperedFourier.l2Compatibility_type := by
  intro d f
  constructor
  · exact Lp.fourier_toTemperedDistribution_eq f
  · exact Lp.fourierInv_toTemperedDistribution_eq f

end P102.U3.TemperedFourier
