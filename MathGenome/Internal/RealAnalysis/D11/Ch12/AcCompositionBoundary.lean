import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcCompositionBoundary
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcBasic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.PSeries

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal BigOperators

namespace D11.Ch12.AcCompositionBoundary

abbrev cubeRoot := Specs.D11.Ch12.AcCompositionBoundary.cubeRoot
abbrev oscillation := Specs.D11.Ch12.AcCompositionBoundary.oscillation
abbrev oscillationDerivative := Specs.D11.Ch12.AcCompositionBoundary.oscillationDerivative

theorem lipschitz_outer_comp : Specs.D11.Ch12.AcCompositionBoundary.lipschitz_outer_comp := by
  intro 𝕂 𝕃 _ _ a b g H L hab hH hg
  apply (AcBasic.library_iff hab.le).mpr
  apply hH.comp_absolutelyContinuousOnInterval
    (by simpa only [uIcc_of_le hab.le] using (mapsTo_image g (Icc a b)))
    ((AcBasic.library_iff hab.le).mp hg)

theorem lipschitz_outer_subtype_comp :
    Specs.D11.Ch12.AcCompositionBoundary.lipschitz_outer_subtype_comp := by
  classical
  intro 𝕂 𝕃 _ _ a b g s H L hab hmap hH hg
  let ext : 𝕂 → 𝕃 := fun x => if hx : x ∈ s then H ⟨x, hx⟩ else 0
  have hL : LipschitzOnWith L ext (g '' Icc a b) := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    dsimp only [ext]
    simp only [dite_eq_left (hmap hu), dite_eq_left (hmap hv)]
    exact hH ⟨g u, hmap hu⟩ ⟨g v, hmap hv⟩
  exact lipschitz_outer_comp ext hab hL hg

@[simp] lemma oscillation_zero : oscillation 0 = 0 := by
  simp [oscillation, Specs.D11.Ch12.AcCompositionBoundary.oscillation]

lemma oscillation_formula (x : ℝ) :
    oscillation x = x ^ 2 * Real.cos (Real.pi / (2 * x)) := by
  by_cases hx : x = 0
  · subst x; simp
  · simp [oscillation, Specs.D11.Ch12.AcCompositionBoundary.oscillation, hx]

lemma abs_oscillation_le (x : ℝ) : |oscillation x| ≤ x ^ 2 := by
  rw [oscillation_formula, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)

theorem oscillation_mapsTo : Specs.D11.Ch12.AcCompositionBoundary.oscillation_mapsTo := by
  intro x hx
  have h := abs_oscillation_le x
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  exact abs_le.mp (h.trans hx2)

lemma oscillation_hasDerivAt_zero : HasDerivAt oscillation 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero, smul_zero, oscillation_zero]
  apply squeeze_zero (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun x : ℝ => |x|)
  · intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |x|⁻¹ * |oscillation x| ≤ |x|⁻¹ * x ^ 2 :=
        mul_le_mul_of_nonneg_left (abs_oscillation_le x) (inv_nonneg.mpr (abs_nonneg _))
      _ ≤ |x| := by
        by_cases hx : x = 0
        · simp [hx]
        · rw [← sq_abs, pow_two, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hx), one_mul]
  · simpa using (continuous_abs.tendsto (0 : ℝ))

theorem oscillation_derivative : Specs.D11.Ch12.AcCompositionBoundary.oscillation_derivative := by
  intro x
  by_cases hx : x = 0
  · subst x
    simpa [oscillationDerivative, Specs.D11.Ch12.AcCompositionBoundary.oscillationDerivative]
      using oscillation_hasDerivAt_zero
  · have harg := (hasDerivAt_const x Real.pi).div
      ((hasDerivAt_id x).const_mul 2) (mul_ne_zero (by norm_num) hx)
    have hd := ((hasDerivAt_id x).pow 2).mul harg.cos
    have heq :
        (2 * x ^ (2 - 1) * 1 * Real.cos (Real.pi / (2 * x)) +
          x ^ 2 * (-(Real.sin (Real.pi / (2 * x))) *
            ((0 * (2 * x) - Real.pi * (2 * 1)) / (2 * x) ^ 2))) =
        oscillationDerivative x := by
      simp only [oscillationDerivative,
        Specs.D11.Ch12.AcCompositionBoundary.oscillationDerivative, ite_eq_right hx]
      field_simp
      ring
    convert hd using 1
    · exact funext oscillation_formula
    · exact heq.symm

theorem oscillation_derivative_bound :
    Specs.D11.Ch12.AcCompositionBoundary.oscillation_derivative_bound := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [Specs.D11.Ch12.AcCompositionBoundary.oscillationDerivative, hx0]
    positivity
  · simp only [Specs.D11.Ch12.AcCompositionBoundary.oscillationDerivative, ite_eq_right hx0]
    calc
      _ ≤ |2 * x * Real.cos (Real.pi / (2 * x))| +
          |(Real.pi / 2) * Real.sin (Real.pi / (2 * x))| := abs_add_le _ _
      _ ≤ 2 * |x| + Real.pi / 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (div_pos Real.pi_pos (by norm_num))]
        exact add_le_add
          (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _))
      _ ≤ 2 + Real.pi / 2 := by have := abs_le.mpr hx; linarith

theorem oscillation_lipschitz : Specs.D11.Ch12.AcCompositionBoundary.oscillation_lipschitz := by
  let L : ℝ≥0 := ⟨2 + Real.pi / 2, by positivity⟩
  refine ⟨L, Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (oscillation_derivative x).differentiableAt) ?_ (convex_Icc _ _)⟩
  intro x hx
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, (oscillation_derivative x).deriv]
  exact oscillation_derivative_bound x hx

theorem oscillation_ac : Specs.D11.Ch12.AcCompositionBoundary.oscillation_ac := by
  obtain ⟨L, hL⟩ := oscillation_lipschitz
  exact AcBasic.lipschitzOn hL

theorem cubeRoot_cube : Specs.D11.Ch12.AcCompositionBoundary.cubeRoot_cube := by
  intro t
  have hroot {u : ℝ} (hu : 0 ≤ u) : (u ^ (1 / 3 : ℝ)) ^ 3 = u := by
    simpa using Real.rpow_inv_natCast_pow (n := 3) hu (by norm_num)
  by_cases ht : 0 ≤ t
  · simpa only [cubeRoot, Specs.D11.Ch12.AcCompositionBoundary.cubeRoot, ite_eq_left ht]
      using hroot ht
  · simp only [Specs.D11.Ch12.AcCompositionBoundary.cubeRoot, ite_eq_right ht]
    rw [neg_pow, hroot (show 0 ≤ -t by linarith)]
    norm_num

lemma integral_abs_power_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in 0..x, |t| ^ (-(2 / 3 : ℝ))) = 3 * x ^ (1 / 3 : ℝ) := by
  have heq : (∫ t in 0..x, |t| ^ (-(2 / 3 : ℝ))) =
      ∫ t in 0..x, t ^ (-(2 / 3 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    simp only [abs_of_nonneg ht.1]
  rw [heq, integral_rpow (Or.inl (by norm_num))]
  norm_num only [show -(2 / 3 : ℝ) + 1 = 1 / 3 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), sub_zero]
  ring

/-- Explicit primitive formula on both sides of the integrable singularity. -/
lemma cubeRoot_primitive (x : ℝ) :
    (1 / 3 : ℝ) * (∫ t in 0..x, |t| ^ (-(2 / 3 : ℝ))) = cubeRoot x := by
  by_cases hx : 0 ≤ x
  · rw [integral_abs_power_nonneg hx]
    simp only [cubeRoot, Specs.D11.Ch12.AcCompositionBoundary.cubeRoot, ite_eq_left hx]
    ring
  · have hsym : (∫ t in 0..x, |t| ^ (-(2 / 3 : ℝ))) =
        -(∫ t in 0..-x, |t| ^ (-(2 / 3 : ℝ))) := by
      calc
        _ = ∫ t in -x..0, |t| ^ (-(2 / 3 : ℝ)) := by
          simpa only [abs_neg, neg_zero] using
            (intervalIntegral.integral_comp_neg (fun t : ℝ => |t| ^ (-(2 / 3 : ℝ)))
              (a := 0) (b := x))
        _ = _ := intervalIntegral.integral_symm _ _
    rw [hsym, integral_abs_power_nonneg (show 0 ≤ -x by linarith)]
    simp only [cubeRoot, Specs.D11.Ch12.AcCompositionBoundary.cubeRoot, ite_eq_right hx]
    ring

lemma intervalIntegrable_abs_power :
    IntervalIntegrable (fun t : ℝ => |t| ^ (-(2 / 3 : ℝ))) volume (-1) 1 := by
  have hp : IntervalIntegrable (fun t : ℝ => |t| ^ (-(2 / 3 : ℝ))) volume 0 1 := by
    apply (intervalIntegrable_congr (f := fun t : ℝ => t ^ (-(2 / 3 : ℝ))) ?_).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [abs_of_nonneg ht.1.le]
  have hn := (IntervalIntegrable.iff_comp_neg (a := 0) (b := 1)
    (f := fun t : ℝ => |t| ^ (-(2 / 3 : ℝ)))).mp hp
  simp only [abs_neg, neg_zero] at hn
  exact hn.symm.trans hp

theorem cubeRoot_ac : Specs.D11.Ch12.AcCompositionBoundary.cubeRoot_ac := by
  have ha := intervalIntegrable_abs_power.absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by norm_num)
  apply (AcBasic.library_iff (by norm_num : (-1 : ℝ) ≤ 1)).mpr
  apply (ha.const_smul (1 / 3 : ℝ)).congr
  intro x _
  exact cubeRoot_primitive x

lemma oscillation_sample (n : ℕ) (hn : 0 < n) :
    oscillation (1 / (2 * (n : ℝ))) =
      (1 / (2 * (n : ℝ))) ^ 2 * (-1 : ℝ) ^ n := by
  rw [oscillation_formula]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have harg : Real.pi / (2 * (1 / (2 * (n : ℝ)))) = (n : ℝ) * Real.pi := by
    field_simp
  rw [harg, Real.cos_nat_mul_pi]

theorem composition_values : Specs.D11.Ch12.AcCompositionBoundary.composition_values := by
  intro n hn
  apply (show Odd 3 by decide).pow_injective (R := ℝ)
  change cubeRoot (oscillation (1 / (2 * (n : ℝ)))) ^ 3 =
    ((-1 : ℝ) ^ n * (2 * (n : ℝ)) ^ (-(2 / 3 : ℝ))) ^ 3
  rw [cubeRoot_cube, oscillation_sample n hn, mul_pow]
  have hs : ((-1 : ℝ) ^ n) ^ 3 = (-1 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
    norm_num
  have hp : ((2 * (n : ℝ)) ^ (-(2 / 3 : ℝ))) ^ 3 = (1 / (2 * (n : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [one_div, inv_pow]
  rw [hs, hp, mul_comm]

/-- The positive sampling points decrease and remain inside the stated domain. -/
def samplePoint (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1))

lemma samplePoint_mem (n : ℕ) : samplePoint n ∈ Icc (-1 : ℝ) 1 := by
  have hnon : 0 < samplePoint n := by dsimp [samplePoint]; positivity
  refine ⟨by linarith, ?_⟩
  dsimp [samplePoint]
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma samplePoint_antitone : Antitone samplePoint := by
  intro m n hmn
  dsimp [samplePoint]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : 2 * (m + 1) ≤ 2 * (n + 1)))

def sampleMagnitude (n : ℕ) : ℝ := (2 * ((n : ℝ) + 1)) ^ (-(2 / 3 : ℝ))

lemma sample_value (n : ℕ) :
    (cubeRoot ∘ oscillation) (samplePoint n) = (-1 : ℝ) ^ (n + 1) * sampleMagnitude n := by
  simpa only [samplePoint, sampleMagnitude, Nat.cast_add, Nat.cast_one, Function.comp_apply] using
    composition_values (n + 1) (by omega)

lemma sample_increment (n : ℕ) :
    ‖(cubeRoot ∘ oscillation) (samplePoint (n + 1)) -
        (cubeRoot ∘ oscillation) (samplePoint n)‖ =
      sampleMagnitude (n + 1) + sampleMagnitude n := by
  rw [sample_value, sample_value]
  have heq : (-1 : ℝ) ^ (n + 1 + 1) * sampleMagnitude (n + 1) -
      (-1 : ℝ) ^ (n + 1) * sampleMagnitude n =
      (-1 : ℝ) ^ (n + 1) * -(sampleMagnitude (n + 1) + sampleMagnitude n) := by
    rw [pow_succ]
    ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_neg,
    abs_of_nonneg (by dsimp [sampleMagnitude]; positivity)]

lemma harmonic_le_sampleMagnitude (n : ℕ) :
    (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1)) ≤ sampleMagnitude n := by
  have hbase : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (show (-1 : ℝ) ≤ -(2 / 3 : ℝ) by norm_num)
  simpa only [Real.rpow_neg_one, sampleMagnitude, mul_inv_rev, one_div,
    mul_comm] using h

/-- The lower comparison is a constant multiple of the divergent harmonic series. -/
lemma sampleMagnitude_not_summable : ¬ Summable sampleMagnitude := by
  intro h
  have hh : Summable (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) harmonic_le_sampleMagnitude h
  have hi : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    have := hh.mul_left 2
    simpa only [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul] using this
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hi

theorem composition_variation : Specs.D11.Ch12.AcCompositionBoundary.composition_variation := by
  change D11.Ch12.variation (cubeRoot ∘ oscillation) (-1) 1 = ⊤
  rw [D11.Ch12.variation_eq_eVariationOn]
  by_contra hfinite
  have hcomp := eVariationOn.comp_le_of_antitoneOn (cubeRoot ∘ oscillation) samplePoint
    (samplePoint_antitone.antitoneOn Set.univ) (fun n _ => samplePoint_mem n)
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N,
        ‖(cubeRoot ∘ oscillation) (samplePoint (n + 1)) -
          (cubeRoot ∘ oscillation) (samplePoint n)‖) ≤
        (eVariationOn (cubeRoot ∘ oscillation) (Icc (-1 : ℝ) 1)).toReal := by
    have hb := (eVariationOn.sum_le (f := (cubeRoot ∘ oscillation) ∘ samplePoint)
      (s := Set.univ) monotone_id (fun _ => mem_univ _) (n := N)).trans hcomp
    have ht := ENNReal.toReal_mono hfinite hb
    simp only [Function.comp_apply, id_eq, edist_dist, dist_eq_norm] at ht
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)] at ht
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (norm_nonneg _)] using ht
  apply sampleMagnitude_not_summable
  apply summable_of_sum_range_le (fun n => by dsimp [sampleMagnitude]; positivity)
  intro N
  apply le_trans _ (hsum N)
  apply Finset.sum_le_sum
  intro n _
  rw [sample_increment]
  exact le_add_of_nonneg_left (by dsimp [sampleMagnitude]; positivity)

theorem composition_not_bv : Specs.D11.Ch12.AcCompositionBoundary.composition_not_bv := by
  change ¬ D11.Ch12.variation (cubeRoot ∘ oscillation) (-1) 1 < ⊤
  have h : D11.Ch12.variation (cubeRoot ∘ oscillation) (-1) 1 = ⊤ := composition_variation
  rw [h]
  exact lt_irrefl _

end D11.Ch12.AcCompositionBoundary
