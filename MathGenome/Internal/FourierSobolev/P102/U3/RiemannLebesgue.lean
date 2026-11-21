import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RiemannLebesgue

noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform Topology RealInnerProductSpace

namespace P102.U3.RiemannLebesgue

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_formula (f : V → ℂ) (ξ : V) :
    𝓕 f ξ = ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℂ))) * f x := by
  rw [Real.fourier_eq']
  congr 1
  ext x
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem riemann_lebesgue (f : V → ℂ) (hf : Integrable f) :
    Continuous (𝓕 f) ∧ (∀ ξ, ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖) ∧
      (0 < Module.finrank ℝ V → Tendsto (𝓕 f) (cocompact V) (𝓝 0)) := by
  refine ⟨?_, Real.norm_fourier_le_integral_norm f, fun _ => ?_⟩
  · exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  · exact tendsto_integral_exp_inner_smul_cocompact f

theorem riemann_lebesgue_L1 (f : Lp (α := V) ℂ 1) :
    Continuous (𝓕 (f : V → ℂ)) ∧ (∀ ξ, ‖𝓕 (f : V → ℂ) ξ‖ ≤ ‖f‖) ∧
      (0 < Module.finrank ℝ V → Tendsto (𝓕 (f : V → ℂ)) (cocompact V) (𝓝 0)) := by
  obtain ⟨hc, hb, hd⟩ := riemann_lebesgue V f (L1.integrable_coeFn f)
  exact ⟨hc, fun ξ => (hb ξ).trans_eq (L1.norm_eq_integral_norm f).symm, hd⟩

/-- The dimension-zero space carries mass one, and Fourier transformation is the identity. -/
theorem zero_dimension (hd : Module.finrank ℝ V = 0) :
    volume (Set.univ : Set V) = 1 ∧ ∀ (f : V → ℂ), 𝓕 f = f := by
  let : Subsingleton V := Module.finrank_zero_iff.mp hd
  let b := stdOrthonormalBasis ℝ V
  have hp : parallelepiped b = univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Subsingleton.elim x (0 : V)]
    refine ⟨0, ?_, ?_⟩ <;> simp
  have hv : volume (Set.univ : Set V) = 1 := by
    rw [← hp]
    exact b.volume_parallelepiped
  refine ⟨hv, ?_⟩
  intro f
  have hf : f = fun _ => f 0 := by
    ext x
    rw [Subsingleton.elim x (0 : V)]
  ext ξ
  rw [Real.fourier_eq, Subsingleton.elim ξ (0 : V)]
  simp only [inner_zero_right, neg_zero, Real.fourierChar.map_zero_eq_one, one_smul]
  rw [hf, integral_const, Measure.real, hv]
  simp

/-- A fundamental interval, extended by zero, relates the circle to the real line.
This identity also holds for the totalized integrals of arbitrary representatives. -/
theorem coefficient_eq_fourier_zeroExtension (T : ℝ) [hT : Fact (0 < T)]
    (f : Periodic.Circle T → ℂ) (n : ℤ) :
    Periodic.coefficient T f n = T⁻¹ •
      𝓕 ((Ioc 0 T).indicator (fun t : ℝ => f (t : Periodic.Circle T))) ((n : ℝ) / T) := by
  rw [Periodic.coefficient_interval T f n 0, zero_add, one_div,
    intervalIntegral.integral_of_le hT.out.le, Real.fourier_eq']
  congr 1
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · simp only [indicator_of_mem ht, smul_eq_mul]
      rw [mul_comm (f _)]
      congr 2
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    · simp [ht]

theorem periodic (T : ℝ) [hT : Fact (0 < T)]
    (f : Periodic.Circle T → ℂ) (_hf : Integrable f (Periodic.haar T)) :
    Tendsto (Periodic.coefficient T f) cofinite (𝓝 0) := by
  have hn : Tendsto (fun n : ℤ => (n : ℝ) / T) cofinite (cocompact ℝ) := by
    have h := Int.tendsto_zmultiplesHom_cofinite (a := T⁻¹) (inv_ne_zero hT.out.ne')
    change Tendsto (fun n : ℤ => n • (T⁻¹ : ℝ)) cofinite (cocompact ℝ) at h
    simpa only [div_eq_mul_inv, zsmul_eq_mul] using h
  have h := (Real.zero_at_infty_fourier
    ((Ioc 0 T).indicator (fun t : ℝ => f (t : Periodic.Circle T)))).comp hn
  simpa only [Function.comp_apply, ← coefficient_eq_fourier_zeroExtension, smul_zero] using h.const_smul T⁻¹

theorem periodic_L1 (T : ℝ) [Fact (0 < T)] (f : Periodic.L1 T) :
    Tendsto (Periodic.coefficientL1 T f) cofinite (𝓝 0) :=
  periodic T f (L1.integrable_coeFn f)

end P102.U3.RiemannLebesgue
