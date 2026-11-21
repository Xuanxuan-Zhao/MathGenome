import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Convolution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.DirichletKernel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.PeriodicIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity

noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators
namespace Fourier

/-- The exponential addition law with the source's integer frequencies. -/
theorem mode_sub (n : ℤ) (x y : ℝ) :
    fourierMode n (x-y) = fourierMode (-n) y * fourierMode n x := by
  unfold fourierMode Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mode_periodic (n : ℤ) : Function.Periodic (fourierMode n) (2 * Real.pi) := by
  intro t
  rw [mode_euler, mode_euler]
  have hc := (Real.cos_periodic.int_mul n) ((n : ℝ) * t)
  have hs := (Real.sin_periodic.int_mul n) ((n : ℝ) * t)
  rw [mul_add, hc, hs]

theorem dirichletKernel_periodic (N : ℕ) :
    Function.Periodic (dirichletKernel N) (2 * Real.pi) := by
  intro t
  exact Finset.sum_congr rfl fun n _ => mode_periodic n t

end Fourier
end SingleVariableAnalysis

namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators
namespace Fourier

/-- Finite linearity for a finset of frequencies, including the empty set. -/
theorem complexIntegral_finset_linear {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℂ) (g : ι → ℝ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (h : ∀ i, ComplexIntegrable (g i) a b) :
    ∃ hs : ComplexIntegrable (fun t => ∑ i ∈ s, α i * g i t) a b,
      complexIntegral _ hs = ∑ i ∈ s, α i * complexIntegral _ (h i) := by
  induction s using Finset.induction_on with
  | empty => simpa using complex_zero_value hab
  | @insert i s hi ih =>
    obtain ⟨ht, htv⟩ := ih
    obtain ⟨hh, hhv⟩ := complex_mul_value (h i) (α i)
    obtain ⟨hs, hsv⟩ := complex_add_value hh ht
    simpa only [Finset.sum_insert hi, hsv, hhv, htv] using
      (show ∃ hs : ComplexIntegrable
          (fun t => α i * g i t + ∑ j ∈ s, α j * g j t) a b,
        complexIntegral _ hs = α i * complexIntegral _ (h i) +
          ∑ j ∈ s, α j * complexIntegral _ (h j) from
        ⟨hs, by rw [hsv, hhv, htv]⟩)

/-- Inserting the coefficient integrals requires only a finite interchange.
This first formula even holds for a nonperiodic function on the reference interval. -/
theorem partialSum_eq_kernel_integral (f : ℝ → ℂ)
    (h : ∀ n : ℤ, ComplexIntegrable (fun y => f y * fourierMode (-n) y)
      (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    ∃ hy : ComplexIntegrable (fun y => f y * dirichletKernel N (x-y))
      (-Real.pi) Real.pi,
    fourierPartialSum f h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ hy := by
  obtain ⟨hs, hsv⟩ := complexIntegral_finset_linear
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n => fourierMode n x)
    (fun n y => f y * fourierMode (-n) y) (by linarith [Real.pi_pos]) h
  have heq : (fun y => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fourierMode n x * (f y * fourierMode (-n) y)) =
      (fun y => f y * dirichletKernel N (x-y)) := by
    funext y
    simp only [dirichletKernel, Specs.SingleVariableAnalysis.Ch19.DirichletKernel.kernelValue,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    change fourierMode n x * (f y * fourierMode (-n) y) =
      f y * fourierMode n (x-y)
    rw [mode_sub]
    ring
  have hy : ComplexIntegrable (fun y => f y * dirichletKernel N (x-y))
      (-Real.pi) Real.pi := heq ▸ hs
  refine ⟨hy, ?_⟩
  have hi : complexIntegral _ hs = complexIntegral _ hy := by
    congr 1
  calc
    fourierPartialSum f h N x = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierMode n x * complexIntegral _ (h n) := by
      unfold fourierPartialSum Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue
      simp only [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.coefficientValue,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ hs := by rw [hsv]
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ hy := by rw [hi]

/-- Periodic reflection in the canonical interval [-π,π]. -/
theorem complexIntegral_periodic_reflect_pi {g : ℝ → ℂ}
    (hp : Function.Periodic g (2 * Real.pi))
    (hg : ComplexIntegrable g (-Real.pi) Real.pi) (c : ℝ) :
    ∃ ht : ComplexIntegrable (fun t => g (c-t)) (-Real.pi) Real.pi,
      complexIntegral _ ht = complexIntegral _ hg := by
  have hb : -Real.pi + (2 * Real.pi) = Real.pi := by ring
  have hg' : ComplexIntegrable g (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [hb]; exact hg
  have hv := complex_periodic_reflect (T := 2 * Real.pi) (b := -Real.pi)
    (by positivity) hp hg' (-Real.pi) c
  simpa only [hb] using hv

/-- Fold an integrable full interval into a sum of its reflected halves. -/
theorem complexIntegral_fold_pi {g : ℝ → ℂ}
    (hg : ComplexIntegrable g (-Real.pi) Real.pi) :
    ∃ hh : ComplexIntegrable (fun t => g (-t) + g t) 0 Real.pi,
      complexIntegral _ hh = complexIntegral _ hg := by
  have hl := hg.subinterval le_rfl (show -Real.pi ≤ 0 by linarith [Real.pi_pos])
    (show 0 ≤ Real.pi by positivity)
  have hr := hg.subinterval (show -Real.pi ≤ 0 by linarith [Real.pi_pos])
    (show 0 ≤ Real.pi by positivity) le_rfl
  have hl' : ComplexIntegrable g (0-Real.pi) (0-0) := by simpa using hl
  obtain ⟨hn, hnv⟩ := complex_integral_reflect (a := 0) (b := Real.pi) 0 hl'
  have he : complexIntegral g hl' = complexIntegral g hl :=
    complexIntegral_congr_endpoints hl' hl (by simp) (by simp)
  have hnv' := hnv.trans he
  simp only [zero_sub] at hn hnv'
  obtain ⟨hh, hhv⟩ := complex_add_value hn hr
  refine ⟨hh, ?_⟩
  rw [hhv, hnv']
  exact ((complex_split g (by linarith [Real.pi_pos]) (by positivity) hg.norm_bound).2
    hg hl hr).symm

end Fourier
open Fourier

/-- Proper finite Fourier convolution, in both full-period representations. -/
theorem fourierPartialSum_convolution :
    Specs.SingleVariableAnalysis.Ch19.Convolution.convolutionIdentities := by
  intro f hf h N x
  obtain ⟨hy, hyv⟩ := partialSum_eq_kernel_integral f h N x
  have hp : Function.Periodic (fun y => f y * dirichletKernel N (x-y))
      (2 * Real.pi) := by
    intro y
    change f (y + 2 * Real.pi) * dirichletKernel N (x-(y+2*Real.pi)) =
      f y * dirichletKernel N (x-y)
    rw [hf.1 y, show x - (y + 2 * Real.pi) = (x-y) - 2 * Real.pi by ring,
      (dirichletKernel_periodic N).sub_eq]
  obtain ⟨ht, htv⟩ := complexIntegral_periodic_reflect_pi hp hy x
  have heq : (fun t => f (x-t) * dirichletKernel N (x-(x-t))) =
      (fun t => f (x-t) * dirichletKernel N t) := by
    funext t; rw [sub_sub_cancel]
  have ht' : ComplexIntegrable (fun t => f (x-t) * dirichletKernel N t)
      (-Real.pi) Real.pi := heq ▸ ht
  have he : complexIntegral _ ht' = complexIntegral _ ht := by
    congr 1; exact heq.symm
  exact ⟨hy, ht', hyv, hyv.trans
    (congrArg (fun z : ℂ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
      (he.trans htv).symm)⟩

/-- The even half-interval convolution identity used by Dini and Jordan. -/
theorem fourierPartialSum_even_convolution :
    Specs.SingleVariableAnalysis.Ch19.Convolution.evenConvolutionIdentity := by
  intro f hf h N x
  obtain ⟨_, ht, _, htv⟩ := fourierPartialSum_convolution f hf h N x
  obtain ⟨hh, hhv⟩ := complexIntegral_fold_pi ht
  have heq : (fun t => f (x-(-t)) * dirichletKernel N (-t) +
      f (x-t) * dirichletKernel N t) =
      (fun t => (f (x+t) + f (x-t)) * dirichletKernel N t) := by
    funext t
    have heven : dirichletKernel N (-t) = dirichletKernel N t := dirichletKernel_even N t
    rw [sub_neg_eq_add, heven, add_mul]
  have hh' : ComplexIntegrable (fun t => (f (x+t) + f (x-t)) * dirichletKernel N t)
      0 Real.pi := heq ▸ hh
  have he : complexIntegral _ hh' = complexIntegral _ hh := by
    congr 1; exact heq.symm
  exact ⟨hh', htv.trans
    (congrArg (fun z : ℂ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
      (he.trans hhv).symm)⟩

/-- Integrability of the translated products follows from the original
periodic proper integrability assumption alone. -/
theorem fourier_convolution_integrable :
    Specs.SingleVariableAnalysis.Ch19.Convolution.translatedProductsIntegrable := by
  intro f hf N x
  have h := fourierCoeff_integrable f hf.2
  obtain ⟨hy, ht, _, _⟩ := fourierPartialSum_convolution f hf h N x
  obtain ⟨hh, _⟩ := fourierPartialSum_even_convolution f hf h N x
  exact ⟨hy, ht, hh⟩

/-- The common complex Fourier representation includes both scalar choices. -/
theorem fourierPartialSum_real_convolution :
    Specs.SingleVariableAnalysis.Ch19.Convolution.realConvolutionIdentities := by
  intro f hf h N x
  have hc : PeriodicRiemannIntegrable (fun y => (f y : ℂ)) :=
    ⟨hf.1.comp Complex.ofReal, fourierRealEmbedding_integrable f hf.2⟩
  obtain ⟨hy, ht, hyv, htv⟩ := fourierPartialSum_convolution _ hc h N x
  obtain ⟨hh, hhv⟩ := fourierPartialSum_even_convolution _ hc h N x
  exact ⟨hy, ht, hh, hyv, htv, hhv⟩

end SingleVariableAnalysis
