import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.DirichletKernel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Orthogonality
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators Topology

abbrev dirichletKernel := Specs.SingleVariableAnalysis.Ch19.DirichletKernel.kernelValue

namespace Fourier

@[simp] theorem dirichletKernel_zero (t : ℝ) : dirichletKernel 0 t = 1 := by
  simp [dirichletKernel, Specs.SingleVariableAnalysis.Ch19.DirichletKernel.kernelValue,
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue]

/-- Adding the two endpoint frequencies gives the symmetric finite-sum recursion. -/
theorem dirichletKernel_succ_modes (N : ℕ) (t : ℝ) :
    dirichletKernel (N+1) t = fourierMode ((N : ℤ)+1) t +
      fourierMode (-((N : ℤ)+1)) t + dirichletKernel N t := by
  exact Finset.sum_Icc_succ_eq_add_endpoints (fun n => fourierMode n t)

/-- The opposite frequencies combine into a real cosine term. -/
theorem mode_add_neg (n : ℤ) (t : ℝ) :
    fourierMode n t + fourierMode (-n) t = ((2 * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) := by
  rw [mode_euler, mode_euler]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem dirichletKernel_succ (N : ℕ) (t : ℝ) :
    dirichletKernel (N+1) t = ((2 * Real.cos (((N : ℝ)+1)*t) : ℝ) : ℂ) +
      dirichletKernel N t := by
  rw [dirichletKernel_succ_modes, mode_add_neg]
  norm_cast

end Fourier
open Specs.SingleVariableAnalysis.Ch19.DirichletKernel
open Fourier

theorem dirichletKernel_real : kernelReal := by
  intro N t
  induction N with
  | zero => simp
  | succ N ih =>
    change (dirichletKernel (N+1) t).im = 0
    rw [dirichletKernel_succ, Complex.add_im, Complex.ofReal_im, zero_add]
    exact ih

theorem dirichletKernel_even : kernelEven := by
  intro N t
  induction N with
  | zero => simp
  | succ N ih => simp only [dirichletKernel_succ, mul_neg, Real.cos_neg, ih]

theorem dirichletKernel_continuous : kernelContinuous := by
  intro N
  exact continuous_finsetSum _ (fun n _ => FourierOrthogonality.mode_continuous n)

theorem dirichletKernel_integrable : kernelIntegrability := by
  intro N
  exact Fourier.complexIntegrable_of_continuousOn (by linarith [Real.pi_pos])
    (dirichletKernel_continuous N).continuousOn

namespace Fourier

/-- The uncancelled sine identity is valid even at the excluded lattice. -/
theorem dirichletKernel_sine_mul (N : ℕ) (t : ℝ) :
    (Real.sin (t/2) : ℂ) * dirichletKernel N t =
      (Real.sin (((N : ℝ)+1/2)*t) : ℂ) := by
  induction N with
  | zero =>
    rw [dirichletKernel_zero, mul_one]
    congr 2
    push_cast
    ring
  | succ N ih =>
    rw [dirichletKernel_succ, mul_add, ih]
    have he : Real.sin (t/2) * (2 * Real.cos (((N : ℝ)+1)*t)) +
        Real.sin (((N : ℝ)+1/2)*t) = Real.sin ((((N+1 : ℕ) : ℝ)+1/2)*t) := by
      rw [show ((N : ℝ)+1/2)*t = ((N : ℝ)+1)*t - t/2 by ring,
        show (((N+1 : ℕ) : ℝ)+1/2)*t = ((N : ℝ)+1)*t + t/2 by push_cast; ring,
        Real.sin_sub, Real.sin_add]
      ring
    exact_mod_cast he

end Fourier

theorem dirichletKernel_quotient : kernelQuotient := by
  intro N t ht
  have hs : Real.sin (t/2) ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hz
    exact ht k (by linarith)
  rw [Complex.ofReal_div]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hs)).mpr
  simpa only [Complex.ofReal_div, mul_comm] using dirichletKernel_sine_mul N t

theorem dirichletKernel_at_lattice : kernelAtLattice := by
  intro N k
  induction N with
  | zero => simp
  | succ N ih =>
    change dirichletKernel (N+1) ((k : ℝ)*(2*Real.pi)) = _
    change dirichletKernel N ((k : ℝ)*(2*Real.pi)) = _ at ih
    rw [dirichletKernel_succ, ih]
    have he : ((N : ℝ)+1)*((k : ℝ)*(2*Real.pi)) =
        (((((N : ℤ)+1)*k : ℤ) : ℝ) * (2*Real.pi)) := by push_cast; ring
    rw [he, Real.cos_int_mul_two_pi]
    push_cast
    ring

theorem dirichletKernel_integral_mean : kernelIntegralMean := by
  intro N
  induction N with
  | zero =>
    intro h
    have he := FourierOrthogonality.mode_normalized_integral 0 (fourierMode_integrable 0)
    simp only [ite_true] at he
    have hi : complexIntegral _ h = complexIntegral _ (fourierMode_integrable 0) := by
      congr 1
      funext t
      simp only [dirichletKernel_zero,
        Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue,
        Int.cast_zero, zero_mul, mul_zero, Complex.exp_zero]
    change ((1 / (2*Real.pi) : ℝ) : ℂ) * complexIntegral _ h = 1
    rw [hi]
    exact he
  | succ N ih =>
    intro h
    have hp := fourierMode_integrable ((N : ℤ)+1)
    have hn := fourierMode_integrable (-((N : ℤ)+1))
    obtain ⟨hpn, hepn⟩ := complex_add_value hp hn
    obtain ⟨hs, hes⟩ := complex_add_value hpn (dirichletKernel_integrable N)
    have hi : complexIntegral _ h = complexIntegral _ hs := by
      congr 1
      exact funext (dirichletKernel_succ_modes N)
    change ((1 / (2*Real.pi) : ℝ) : ℂ) * complexIntegral _ h = 1
    rw [hi, hes, hepn, mul_add, mul_add,
      FourierOrthogonality.mode_normalized_integral,
      FourierOrthogonality.mode_normalized_integral, ih]
    simp only [ite_eq_right (show (N : ℤ)+1 ≠ 0 by omega),
      ite_eq_right (show -((N : ℤ)+1) ≠ 0 by omega), zero_add]

theorem dirichletKernel_removable : kernelRemovable := by
  intro N k
  have hc := ((dirichletKernel_continuous N).continuousAt
    (x := (k : ℝ)*(2*Real.pi))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {t : ℝ | ∀ j : ℤ, t ≠ (j : ℝ)*(2*Real.pi)}))
  rw [dirichletKernel_at_lattice] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact dirichletKernel_quotient N t ht

end SingleVariableAnalysis
