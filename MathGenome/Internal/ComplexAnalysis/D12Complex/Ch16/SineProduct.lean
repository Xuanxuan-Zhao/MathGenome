import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.SineProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-! Euler's formula is obtained from Mathlib's finite integral recurrences
and their limit (EulerSineProd), independently of Hadamard factorization.
Uniform product convergence is used on arbitrary compact sets, including
those containing zeros. Thus the tprod in the identity is an actual limit,
not a default value assigned to a nonconvergent infinite product. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace D12Complex.SineProduct

lemma paired_hasProdLocallyUniformlyOn :
    HasProdLocallyUniformlyOn
      (fun (n : ℕ) (z : ℂ) => 1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)
      (fun z => ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  simpa only [sineTerm, neg_div, ← sub_eq_add_neg] using
    (multipliableUniformlyOn_euler_sin_prod_on_compact hK).hasProdUniformlyOn

theorem sine_paired_locally_uniform :
    Specs.D12Complex.Ch16.SineProduct.sine_paired_locally_uniform_type := by
  exact paired_hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange

theorem sine_product :
    Specs.D12Complex.Ch16.SineProduct.sine_product_type := by
  intro z
  have hp := (paired_hasProdLocallyUniformlyOn.hasProd (mem_univ z)).tendsto_prod_nat
  exact tendsto_nhds_unique (Complex.tendsto_euler_sin_prod z)
    (tendsto_const_nhds.mul hp)

lemma product_with_z_eq (z : ℂ) :
    z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2) =
      (Real.pi : ℂ)⁻¹ * Complex.sin ((Real.pi : ℂ) * z) := by
  rw [sine_product z]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma product_with_z_fun_eq :
    (fun z : ℂ => z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) =
      (fun z => (Real.pi : ℂ)⁻¹ * Complex.sin ((Real.pi : ℂ) * z)) := by
  funext z
  exact product_with_z_eq z

theorem sine_product_holomorphic :
    Specs.D12Complex.Ch16.SineProduct.sine_product_holomorphic_type := by
  rw [Specs.D12Complex.Ch16.SineProduct.sine_product_holomorphic_type,
    product_with_z_fun_eq]
  exact ⟨isOpen_univ, fun z _ => by fun_prop⟩

lemma sin_pi_zero_iff (z : ℂ) :
    Complex.sin ((Real.pi : ℂ) * z) = 0 ↔ ∃ m : ℤ, z = (m : ℂ) := by
  rw [Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    simpa only [mul_comm] using hm
  · rintro ⟨m, rfl⟩
    exact ⟨m, mul_comm _ _⟩

theorem sine_product_zero_iff :
    Specs.D12Complex.Ch16.SineProduct.sine_product_zero_iff_type := by
  intro z
  rw [product_with_z_eq, mul_eq_zero]
  simp only [inv_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, false_or]
  exact sin_pi_zero_iff z

lemma hasDerivAt_scaled_sin (z : ℂ) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ)⁻¹ * Complex.sin ((Real.pi : ℂ) * w))
      (Complex.cos ((Real.pi : ℂ) * z)) z := by
  have hd := ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z
    (hasDerivAt_id z |>.const_mul (Real.pi : ℂ))).const_mul (Real.pi : ℂ)⁻¹
  convert hd using 1
  · rfl
  · field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem sine_product_simple_integer_zeros :
    Specs.D12Complex.Ch16.SineProduct.sine_product_simple_integer_zeros_type := by
  intro m
  rw [product_with_z_fun_eq]
  have hz : Complex.sin ((Real.pi : ℂ) * (m : ℂ)) = 0 :=
    (sin_pi_zero_iff _).mpr ⟨m, rfl⟩
  apply AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · fun_prop
  · simp only [hz, mul_zero]
  · rw [(hasDerivAt_scaled_sin (m : ℂ)).deriv]
    intro hcos
    have h := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * (m : ℂ))
    simp [hz, hcos] at h

theorem sine_product_normalization :
    Specs.D12Complex.Ch16.SineProduct.sine_product_normalization_type := by
  have h0 : (∏' n : ℕ, (1 - (0 : ℂ) ^ 2 / ((n : ℂ) + 1) ^ 2)) = 1 := by simp
  refine ⟨h0, ?_⟩
  have hc : ContinuousAt
      (fun z : ℂ => ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) 0 := by
    have h := sine_paired_locally_uniform.continuousOn
      (Eventually.of_forall (fun N => show ContinuousOn
        (fun z : ℂ => ∏ n ∈ Finset.range N, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2))
          univ from by fun_prop)).frequently
    exact h.continuousAt (univ_mem)
  apply Tendsto.congr' _ ((h0 ▸ hc.tendsto).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (mul_div_cancel_left₀ _ hz).symm

end D12Complex.SineProduct
