import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.C1Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.CoefficientDecay
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Bessel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
namespace SingleVariableAnalysis
open Riemann Set Filter
open scoped BigOperators Topology

namespace FourierAbsolute

lemma mode_norm (n : ℤ) (x : ℝ) : ‖fourierMode n x‖ = 1 := by
  simp [fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue,
    Complex.norm_exp]

/-- Young's elementary square bound is enough for the ℓ² × ℓ² estimate. -/
lemma summable_coefficients {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ 1 f (Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi) :
    ∃ H : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f,
      Summable (fun n : ℤ => ‖fourierCoeff f n (H n)‖) := by
  obtain ⟨H, Hd, hn, hformula, _, _⟩ := fourierCoeff_derivative_decay f 1 (by omega) hf
    (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa using hend)
  let df := iteratedDerivWithin 1 f (Icc (-Real.pi) Real.pi)
  have hu : UniqueDiffOn ℝ (Icc (-Real.pi) Real.pi) :=
    uniqueDiffOn_Icc (by linarith [Real.pi_pos])
  have hc : ContinuousOn df (Icc (-Real.pi) Real.pi) :=
    ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hu).mp hf).1 1 le_rfl
  have hdi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hc
  have hs := fourierBessel_summable df hdi Hd
  have hi : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by omega)
  refine ⟨H, (hs.add hi).of_norm_bounded_eventually ?_⟩
  filter_upwards [show ∀ᶠ n : ℤ in cofinite, n ≠ 0 from
    (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hnz
  have he := congrArg norm (hformula n)
  have he' : ‖fourierCoeff df n (Hd n)‖ =
      |(n : ℝ)| * ‖fourierCoeff f n (H n)‖ := by
    simpa [df, pow_one, norm_mul, Complex.norm_intCast, ← Int.cast_abs] using he
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hnz
  have hdiv : ‖fourierCoeff f n (H n)‖ =
      ‖fourierCoeff df n (Hd n)‖ * (1 / |(n : ℝ)|) := by
    rw [he']; field_simp
  rw [norm_norm, hdiv]
  have hsquare := sq_nonneg (‖fourierCoeff df n (Hd n)‖ - 1 / |(n : ℝ)|)
  have hi2 : (1 / |(n : ℝ)|) ^ 2 = 1 / (n : ℝ) ^ 2 := by rw [div_pow, one_pow, sq_abs]
  nlinarith [sq_nonneg ‖fourierCoeff df n (Hd n)‖, sq_nonneg (1 / |(n : ℝ)|)]

lemma mode_periodic (n : ℤ) : Function.Periodic (fourierMode n) (2 * Real.pi) := by
  intro x
  change Complex.exp _ = Complex.exp _
  have he : Complex.I * ((n : ℂ) * ((x + 2 * Real.pi : ℝ) : ℂ)) =
      Complex.I * ((n : ℂ) * (x : ℂ)) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Symmetric integer intervals exhaust every finite set of modes. -/
lemma symmetric_tendsto : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ))
    atTop atTop := by
  refine tendsto_atTop.2 (fun E => eventually_atTop.2 ⟨E.sup Int.natAbs, ?_⟩)
  intro N hN n hn
  have ha : n.natAbs ≤ N := (Finset.le_sup hn).trans hN
  have h₁ := Int.le_natAbs (a := n)
  have h₂ := Int.le_natAbs (a := -n)
  simp only [Int.natAbs_neg] at h₂
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- The normalized proper integral is Lipschitz in the uniform norm.
This estimate is the termwise integration step used below. -/
lemma coefficient_distance_le {f g : ℝ → ℂ}
    (hf : FourierProjection.Integrable f) (hg : FourierProjection.Integrable g)
    (Hf : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f)
    (Hg : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights g)
    (n : ℤ) {M : ℝ} (hb : ∀ x ∈ Icc (-Real.pi) Real.pi, ‖f x - g x‖ ≤ M) :
    ‖fourierCoeff f n (Hf n) - fourierCoeff g n (Hg n)‖ ≤ M := by
  let hd := FourierProjection.integrable_sub hf hg
  let Hd := fourierCoeff_integrable _ hd
  have he : fourierCoeff (fun x => f x - g x) n (Hd n) =
      fourierCoeff f n (Hf n) - fourierCoeff g n (Hg n) := by
    rw [← FourierProjection.pair_mode_coefficient hd Hd,
      FourierProjection.pair_sub_left hf hg (FourierProjection.mode_integrable n),
      FourierProjection.pair_mode_coefficient hf Hf,
      FourierProjection.pair_mode_coefficient hg Hg]
  rw [← he]
  have hc := Fourier.coefficient_norm_bound Hd hd.norm n
  have hi := realIntegral_le_mul_bound hd.norm hb
  have hα : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc
    _ ≤ (1 / (2 * Real.pi)) * realIntegral _ hd.norm := hc
    _ ≤ (1 / (2 * Real.pi)) * ((Real.pi - -Real.pi) * M) :=
      mul_le_mul_of_nonneg_left hi hα
    _ = M := by field_simp; ring

end FourierAbsolute

/-- Absolute summability, uniform synthesis and preservation of all coefficients.
The equality of the synthesized function with the original interval function is
left for the independently proved uniqueness theorem. -/
theorem fourier_c1_absolute_uniform :
    Specs.SingleVariableAnalysis.Ch19.C1Absolute.absoluteUniform := by
  intro f hf hend
  obtain ⟨H, hs⟩ := FourierAbsolute.summable_coefficients hf hend
  let c : ℤ → ℂ := fun n => fourierCoeff f n (H n)
  let g : ℝ → ℂ := fun x => ∑' n : ℤ, c n * fourierMode n x
  have hb (n : ℤ) (x : ℝ) : ‖c n * fourierMode n x‖ = ‖c n‖ := by
    rw [norm_mul, FourierAbsolute.mode_norm, mul_one]
  have hcont : Continuous g := continuous_tsum
    (fun n => continuous_const.mul (FourierOrthogonality.mode_continuous n))
    hs (fun n x => (hb n x).le)
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro x
    apply tsum_congr
    intro n
    rw [FourierAbsolute.mode_periodic n x]
  have hfin := tendstoUniformly_tsum hs (fun n x => (hb n x).le)
  have huni : TendstoUniformly (fourierPartialSum f H) g atTop := by
    exact fun U hU => FourierAbsolute.symmetric_tendsto.eventually (hfin U hU)
  have hu : ComplexUniformConverges (fourierPartialSum f H) g :=
    (complexUniformConverges_iff _ _).mpr huni
  have hnorm : ∀ x : ℝ, Summable (fun n : ℤ => ‖c n * fourierMode n x‖) := by
    intro x
    simpa only [hb] using hs
  have ha : RealUniformConverges
      (fun N x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖c n * fourierMode n x‖)
      (fun _ => ∑' n : ℤ, ‖c n‖) := by
    have ht := hs.hasSum.comp FourierAbsolute.symmetric_tendsto
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
    refine ⟨N, fun n hn x => ?_⟩
    simpa only [hb, Real.dist_eq, Function.comp_apply, c] using hN n hn
  have hgi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hcont.continuousOn
  let Hg := fourierCoeff_integrable g hgi
  refine ⟨H, hs, g, hcont, hper, hu, ha, fun x => (hnorm x).of_norm.hasSum, Hg, ?_⟩
  intro n
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (half_pos hε)
  let K := max N n.natAbs
  have hnK : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    have h₁ := Int.le_natAbs (a := n)
    have h₂ := Int.le_natAbs (a := -n)
    simp only [Int.natAbs_neg] at h₂
    have : n.natAbs ≤ K := le_max_right _ _
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  let E := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let hp := FourierProjection.polynomial_integrable E c
  let Hp := fourierCoeff_integrable _ hp
  have he : fourierCoeff (fourierPolynomial E c) n (Hp n) = c n := by
    rw [← FourierProjection.pair_mode_coefficient hp Hp,
      FourierProjection.pair_polynomial_mode, ite_eq_left hnK]
  have hdist := FourierAbsolute.coefficient_distance_le hgi hp Hg Hp n
    (M := ε / 2) (fun x _ => by
      change ‖g x - fourierPartialSum f H K x‖ ≤ ε / 2
      rw [norm_sub_rev]
      exact (hN K (le_max_left _ _) x).le)
  rw [he] at hdist
  rw [dist_eq_norm]
  exact hdist.trans (by linarith)

end SingleVariableAnalysis
