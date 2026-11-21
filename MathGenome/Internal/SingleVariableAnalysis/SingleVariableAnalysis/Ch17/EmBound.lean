import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EmBound
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.EulerMaclaurin
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order

/-! Finite Euler–Maclaurin error estimate for real and complex functions.
All integrals are the upstream proper Darboux integrals. The proof combines
the attained unit-interval polynomial maximum, the integral triangle
inequality, pointwise order, and constant-factor linearity. -/
noncomputable section
namespace SingleVariableAnalysis
open Specs.SingleVariableAnalysis.Ch17.Bernoulli
open Specs.SingleVariableAnalysis.Ch17.EmRecursion
open Specs.SingleVariableAnalysis.Ch17.EmBound
open Specs.SingleVariableAnalysis.Ch08.Integral
open Riemann

noncomputable def bernoulliMaximum : bernoulliMaximumType := bernoulliMaximumValue

theorem bernoulli_maximum_attained :
    Specs.SingleVariableAnalysis.Ch17.EmBound.bernoulliMaximumAttained := by
  intro n
  have hc : Continuous (fun t : ℝ => |(bernoulliPolynomialValue n).eval t|) :=
    (bernoulliPolynomialValue n).continuous.abs
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hc.continuousOn
  have hg : IsGreatest ((fun u : ℝ => |(bernoulliPolynomialValue n).eval u|) ''
      Set.Icc 0 1) |(bernoulliPolynomialValue n).eval t| := by
    refine ⟨Set.mem_image_of_mem _ ht, ?_⟩
    rintro y ⟨u, hu, rfl⟩
    exact hmax hu
  have he : bernoulliMaximumValue n = |(bernoulliPolynomialValue n).eval t| :=
    hg.csSup_eq
  refine ⟨he.symm ▸ abs_nonneg _, t, ht, he.symm, ?_⟩
  intro u hu
  rw [he]
  exact hmax hu

namespace EulerMaclaurin

/-- The periodic Bernoulli factor is bounded at all real points, including
negative arguments and integer nodes. -/
theorem bernoulli_fract_bound (n : ℕ) (x : ℝ) :
    |(bernoulliPolynomialValue n).eval (Int.fract x)| ≤ bernoulliMaximumValue n := by
  obtain ⟨_, t, ht, he, hb⟩ := bernoulli_maximum_attained n
  exact hb _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- Pointwise domination does not require an order on the scalar target. -/
theorem norm_rawIntegrand_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (D : ℕ → ℝ → E) (x : ℝ) :
    ‖rawIntegrand n D x‖ ≤ bernoulliMaximumValue n * ‖D n x‖ := by
  rw [rawIntegrand, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (bernoulli_fract_bound n x) (norm_nonneg _)

end EulerMaclaurin

theorem em_real_remainder_bound :
    Specs.SingleVariableAnalysis.Ch17.EmBound.realRemainderBound := by
  intro a b hab m hm f D hD
  obtain ⟨hf, hR, hformula⟩ := euler_maclaurin_real a b hab m hm f D hD
  have hN := EulerMaclaurin.realCalculus.cont
    (show (a : ℝ) ≤ (b : ℝ) from (Int.cast_lt.mpr hab).le)
    (hD.2.1 (2 * m) le_rfl).norm
  obtain ⟨hnR, hnorm, _⟩ := real_norm_estimate _ hR
  obtain ⟨hM, hMval⟩ := real_mul_value hN (bernoulliMaximumValue (2 * m))
  have hle := realIntegral_mono _ _ hnR hM (fun x _ =>
    EulerMaclaurin.norm_rawIntegrand_le (2 * m) D x)
  change realIntegralValue _ hM =
    bernoulliMaximumValue (2 * m) * realIntegralValue _ hN at hMval
  rw [hMval] at hle
  refine ⟨hR, hN, ?_⟩
  have hfac : 0 ≤ 1 / (((2 * m).factorial : ℕ) : ℝ) := by positivity
  calc
    ‖-term (@realIntegralValue) (2 * m) D hR‖ =
        (1 / ((2 * m).factorial : ℝ)) * ‖realIntegralValue _ hR‖ := by
      rw [norm_neg, term, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
    _ ≤ (1 / ((2 * m).factorial : ℝ)) *
        (bernoulliMaximumValue (2 * m) * realIntegralValue _ hN) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hle) hfac
    _ = _ := by ring

theorem em_complex_remainder_bound :
    Specs.SingleVariableAnalysis.Ch17.EmBound.complexRemainderBound := by
  intro a b hab m hm f D hD
  obtain ⟨hf, hR, hformula⟩ := euler_maclaurin_complex a b hab m hm f D hD
  have hN := EulerMaclaurin.realCalculus.cont
    (show (a : ℝ) ≤ (b : ℝ) from (Int.cast_lt.mpr hab).le)
    (hD.2.1 (2 * m) le_rfl).norm
  obtain ⟨hnR, hnorm, _⟩ := complex_norm_estimate _ hR
  obtain ⟨hM, hMval⟩ := real_mul_value hN (bernoulliMaximumValue (2 * m))
  have hle := realIntegral_mono _ _ hnR hM (fun x _ =>
    EulerMaclaurin.norm_rawIntegrand_le (2 * m) D x)
  change realIntegralValue _ hM =
    bernoulliMaximumValue (2 * m) * realIntegralValue _ hN at hMval
  rw [hMval] at hle
  refine ⟨hR, hN, ?_⟩
  have hfac : 0 ≤ 1 / (((2 * m).factorial : ℕ) : ℝ) := by positivity
  calc
    ‖-term (@complexIntegralValue) (2 * m) D hR‖ =
        (1 / ((2 * m).factorial : ℝ)) * ‖complexIntegralValue _ hR‖ := by
      rw [norm_neg, term, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
    _ ≤ (1 / ((2 * m).factorial : ℝ)) *
        (bernoulliMaximumValue (2 * m) * realIntegralValue _ hN) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hle) hfac
    _ = _ := by ring

end SingleVariableAnalysis
