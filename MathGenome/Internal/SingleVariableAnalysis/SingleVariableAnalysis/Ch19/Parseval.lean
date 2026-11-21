import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Parseval
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Fejer
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Bessel

/-! Parseval for continuous periodic functions, using finite best approximation
against Fejer means and proper Riemann integral bounds. -/
noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators

namespace FourierProjection

/-- A uniform bound controls the normalized proper integral of the square. -/
theorem normSquared_le_bound {g : ℝ → ℂ}
    (hg : RealIntegrable (fun x => ‖g x‖ ^ 2) (-Real.pi) Real.pi)
    {a : ℝ} (_ha : 0 ≤ a) (hb : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, ‖g x‖ ≤ a) :
    fourierNormSquared g hg ≤ a ^ 2 := by
  have hi := realIntegral_le_mul_bound hg (fun x hx =>
    pow_le_pow_left₀ (norm_nonneg _) (hb x hx) 2)
  have hm := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  change (1 / (2 * Real.pi)) * realIntegral _ hg ≤ _
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((Real.pi - -Real.pi) * a ^ 2) := hm
    _ = a ^ 2 := by field_simp; ring

/-- The Fourier projection on [-N,N] minimizes error against the actual
Fejer mean, whose frequencies all belong to that same finite set. -/
theorem residual_le_fejer (f : ℝ → ℂ) (hf : Integrable f)
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f) (N : ℕ)
    (hr : RealIntegrable (fun x => ‖f x - fourierPartialSum f h N x‖ ^ 2)
      (-Real.pi) Real.pi) :
    ∃ hm : RealIntegrable (fun x => ‖f x - fejerMean f h N x‖ ^ 2)
      (-Real.pi) Real.pi,
    fourierNormSquared (fun x => f x - fourierPartialSum f h N x) hr ≤
      fourierNormSquared (fun x => f x - fejerMean f h N x) hm := by
  obtain ⟨c, hc⟩ := fejerMean_polynomial f h N
  have he : fejerMean f h N = fourierPolynomial (Finset.Icc (-(N : ℤ)) (N : ℤ)) c :=
    funext hc
  change fejerMean f h N =
    Specs.SingleVariableAnalysis.Ch19.FiniteProjection.polynomialValue
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) c at he
  have hm := fourierResidual_integrable f hf (Finset.Icc (-(N : ℤ)) (N : ℤ)) c
  rw [← he] at hm
  refine ⟨hm, ?_⟩
  have hb := fourierProjection_bestApproximation f hf h
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) c
  rw [← he] at hb
  exact hb hm hr

/-- Uniform Fejer convergence forces vanishing squared projection error. -/
theorem residual_tendsto_zero (f : ℝ → ℂ) (hc : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) (hf : Integrable f)
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f)
    (hr : ∀ N : ℕ, RealIntegrable
      (fun x => ‖f x - fourierPartialSum f h N x‖ ^ 2) (-Real.pi) Real.pi) :
    Filter.Tendsto (fun N => fourierNormSquared
      (fun x => f x - fourierPartialSum f h N x) (hr N)) Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := fejer_uniform_convergence f hc hp h
    (Real.sqrt (ε / 2)) (Real.sqrt_pos.2 (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hm, hb⟩ := residual_le_fejer f hf h n (hr n)
  have he := normSquared_le_bound hm (Real.sqrt_nonneg _) (fun x _ => by
    rw [norm_sub_rev]
    exact (hN n hn x).le)
  rw [Real.sq_sqrt (half_pos hε).le] at he
  have hz := normSquared_nonneg _ (hr n)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hz] using
    (hb.trans he).trans_lt (show ε / 2 < ε by linarith)

/-- Finite Pythagoras with the zero comparison polynomial. -/
theorem energy_decomposition (f : ℝ → ℂ) (hf : Integrable f)
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f)
    (hs : RealIntegrable (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi) (N : ℕ)
    (hr : RealIntegrable (fun x => ‖f x - fourierPartialSum f h N x‖ ^ 2)
      (-Real.pi) Real.pi) :
    fourierNormSquared f hs =
      fourierNormSquared (fun x => f x - fourierPartialSum f h N x) hr +
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f n (h n)‖ ^ 2 := by
  have hz : fourierPolynomial (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 0) =
      (fun _ => 0) := by
    funext x
    simp [fourierPolynomial, Specs.SingleVariableAnalysis.Ch19.FiniteProjection.polynomialValue]
  have hd : RealIntegrable (fun x => ‖f x -
      fourierPolynomial (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 0) x‖ ^ 2)
      (-Real.pi) Real.pi := by simpa only [hz, sub_zero] using hs
  have he := fourierProjection_identity f hf h (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun _ => 0) hd hr
  change fourierNormSquared
      (fun x => f x - fourierPolynomial (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 0) x) hd =
    fourierNormSquared (fun x => f x - fourierPartialSum f h N x) hr +
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f n (h n) - 0‖ ^ 2 at he
  simpa only [hz, sub_zero] using he

end FourierProjection

open Specs.SingleVariableAnalysis.Ch19.Parseval
open FourierProjection

theorem fourierParseval_complex : complexParseval := by
  intro f hc hp
  have hf := (continuous_periodic_regularity f hc hp).2.2
  let h := fourierCoeff_integrable f hf
  let hs := fourierNormSquared_integrable f hf
  have hr : ∀ N : ℕ, RealIntegrable
      (fun x => ‖f x - fourierPartialSum f h N x‖ ^ 2) (-Real.pi) Real.pi :=
    fun N => fourierResidual_integrable f hf (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun n => fourierCoeff f n (h n))
  have hlim := residual_tendsto_zero f hc hp hf h hr
  have hsum := fourierBessel_summable f hf h
  have hdecomp := energy_decomposition f hf h hs
  have heq : (∑' n : ℤ, ‖fourierCoeff f n (h n)‖ ^ 2) = fourierNormSquared f hs := by
    apply le_antisymm (fourierBessel_tsum_le f hf h hs)
    have hu (N : ℕ) := hsum.sum_le_tsum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun n _ => sq_nonneg ‖fourierCoeff f n (h n)‖)
    have hb (N : ℕ) : fourierNormSquared f hs ≤
        fourierNormSquared (fun x => f x - fourierPartialSum f h N x) (hr N) +
          ∑' n : ℤ, ‖fourierCoeff f n (h n)‖ ^ 2 := by
      rw [hdecomp N (hr N)]
      exact add_le_add le_rfl (hu N)
    exact ge_of_tendsto' (by simpa only [zero_add] using
      (hlim.add_const (∑' n : ℤ, ‖fourierCoeff f n (h n)‖ ^ 2))) hb
  refine ⟨h, hs, hr, hsum, heq, hlim, ?_, ?_⟩
  · simpa only [Real.sqrt_zero] using hlim.sqrt
  · have he (N : ℕ) :
        (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f n (h n)‖ ^ 2) =
        fourierNormSquared f hs -
          fourierNormSquared (fun x => f x - fourierPartialSum f h N x) (hr N) := by
      linarith [hdecomp N (hr N)]
    simp_rw [show (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖fourierCoeff f n (h n)‖ ^ 2) = (fun N : ℕ => fourierNormSquared f hs -
        fourierNormSquared (fun x => f x - fourierPartialSum f h N x) (hr N)) from funext he]
    simpa only [sub_zero] using hlim.const_sub (fourierNormSquared f hs)

theorem fourierParseval_real : realParseval := by
  intro f hc hp
  obtain ⟨h, hs, hr, hsum, heq, hlim, hnorm, _⟩ := fourierParseval_complex
    (fun x => (f x : ℂ)) (Complex.continuous_ofReal.comp hc) (hp.comp Complex.ofReal)
  have hs' : RealIntegrable (fun x => |f x| ^ 2) (-Real.pi) Real.pi := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hs
  refine ⟨h, hs', hr, hsum, ?_, hlim, hnorm⟩
  simpa only [Specs.SingleVariableAnalysis.Ch19.FiniteProjection.normSquaredValue,
    Complex.norm_real, Real.norm_eq_abs] using heq

end SingleVariableAnalysis
