import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.SpectralDivergence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.LatticeLocalBounds
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace P207.Walk.SpectralDivergence
noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem angle_norm (t : Real.Angle) : ‖t‖ = |t.toReal| := by
  nth_rw 1 [← Real.Angle.coe_toReal t]
  apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity : 2 * Real.pi ≠ 0)).mpr
  simpa [abs_of_pos Real.two_pi_pos] using Real.Angle.abs_toReal_le_pi t

theorem abs_phi_le_one {d : ℕ} [NeZero d] (t : Torus d) : |phi t| ≤ 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  calc
    |phi t| ≤ (d : ℝ)⁻¹ * ∑ j : Fin d, |Real.Angle.cos (t j)| := by
      simpa only [phi, abs_mul, abs_inv, abs_of_pos hd] using
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hd.le)
    _ ≤ (d : ℝ)⁻¹ * ∑ j : Fin d, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun j _ => abs_le.mpr
        ⟨LatticeLocalBounds.neg_one_le_angle_cos _, LatticeLocalBounds.angle_cos_le_one _⟩
    _ = 1 := by simp [hd.ne']

theorem scalar_defect (t : Real.Angle) {r : ℝ} (_hr : 0 ≤ r) (ht : ‖t‖ ≤ r) :
    1 - Real.Angle.cos t ≤ r ^ 2 / 2 := by
  rw [angle_norm] at ht
  have hsq : t.toReal ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [← Real.Angle.cos_toReal]
  linarith [Real.one_sub_sq_div_two_le_cos (x := t.toReal)]

/-- The cosine estimate on a product metric ball uses its actual angular representatives. -/
theorem denominator_le {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 ≤ r)
    {t : Torus d} (ht : t ∈ Metric.closedBall 0 r) : 1 - phi t ^ 2 ≤ r ^ 2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [closedBall_pi _ hr] at ht
  have hj (j : Fin d) : ‖t j‖ ≤ r := by
    have h := (Set.mem_pi.mp ht) j (Set.mem_univ j)
    simpa using h
  have hs : ∑ j : Fin d, (1 - Real.Angle.cos (t j)) ≤ (d : ℝ) * (r ^ 2 / 2) := by
    calc
      _ ≤ ∑ j : Fin d, (r ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact scalar_defect (t j) hr (hj j)
      _ = _ := by simp
  have hdef : 1 - phi t ≤ r ^ 2 / 2 := by
    have he : 1 - phi t = (d : ℝ)⁻¹ * ∑ j : Fin d, (1 - Real.Angle.cos (t j)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, phi, mul_sub, inv_mul_cancel₀ hd.ne']
    rw [he]
    calc
      _ ≤ (d : ℝ)⁻¹ * ((d : ℝ) * (r ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp
  nlinarith [sq_nonneg (phi t - 1)]

theorem circle_closedBall {r : ℝ} (_hr : 0 ≤ r) (hrpi : r ≤ Real.pi) :
    AddCircle.haarAddCircle (Metric.closedBall (0 : AddCircle (2 * Real.pi)) r) =
      ENNReal.ofReal (r / Real.pi) := by
  have hv := AddCircle.volume_closedBall (T := 2 * Real.pi)
    (x := (0 : AddCircle (2 * Real.pi))) r
  rw [min_eq_right (by linarith)] at hv
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul] at hv
  have he := (ENNReal.eq_div_iff (by positivity : ENNReal.ofReal (2 * Real.pi) ≠ 0)
    ENNReal.ofReal_ne_top).mpr hv
  rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * Real.pi)] at he
  convert he using 2
  field_simp

theorem torus_closedBall (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (hrpi : r ≤ Real.pi) :
    torusMeasure d (Metric.closedBall 0 r) = ENNReal.ofReal (r / Real.pi) ^ d := by
  rw [torusMeasure, Measure.pi_closedBall _ _ hr]
  simp only [Pi.zero_apply, circle_closedBall hr hrpi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem integral_ball_lower (d : ℕ) [NeZero d] {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (r ^ 2))⁻¹ * torusMeasure d (Metric.closedBall 0 r) ≤
      (torusMeasure d).withDensity (fun t => (ENNReal.ofReal (1 - phi t ^ 2))⁻¹)
        (Metric.closedBall 0 r) := by
  rw [withDensity_apply _ measurableSet_closedBall]
  calc
    _ = ∫⁻ _t : Torus d in Metric.closedBall 0 r, (ENNReal.ofReal (r ^ 2))⁻¹ ∂torusMeasure d := by
      simp
    _ ≤ _ := lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_closedBall
      (fun t ht => ENNReal.inv_le_inv.mpr
        (ENNReal.ofReal_le_ofReal (denominator_le hr.le ht))))

theorem uniform_ball_lower (d : ℕ) [NeZero d] (hd : d = 1 ∨ d = 2)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((1 / Real.pi) ^ d) ≤
      (torusMeasure d).withDensity (fun t => (ENNReal.ofReal (1 - phi t ^ 2))⁻¹)
        (Metric.closedBall 0 r) := by
  have hpow : r ^ 2 ≤ r ^ d := by
    rcases hd with rfl | rfl
    · norm_num
      nlinarith
    · rfl
  have hreal : (1 / Real.pi) ^ d ≤ (r / Real.pi) ^ d / r ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hr)]
    calc
      _ = r ^ 2 / Real.pi ^ d := by rw [div_pow, one_pow]; ring
      _ ≤ r ^ d / Real.pi ^ d := div_le_div_of_nonneg_right hpow (by positivity)
      _ = _ := (div_pow _ _ _).symm
  calc
    _ ≤ ENNReal.ofReal ((r / Real.pi) ^ d / r ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = (ENNReal.ofReal (r ^ 2))⁻¹ *
        torusMeasure d (Metric.closedBall 0 r) := by
      rw [torus_closedBall d hr.le (hr1.trans (by linarith [Real.two_le_pi])),
        ENNReal.ofReal_div_of_pos (sq_pos_of_pos hr),
        ENNReal.ofReal_pow (by positivity : 0 ≤ r / Real.pi)]
      exact mul_comm _ _
    _ ≤ _ := integral_ball_lower d hr

theorem singleton_zero (d : ℕ) [NeZero d] : torusMeasure d {0} = 0 := by
  have h := torus_closedBall d (r := 0) (by rfl) (by positivity)
  simpa [NeZero.ne d] using h

/-- Finiteness would force the weighted masses of shrinking metric cubes to
converge to the mass of their intersection. The uniform lower bound contradicts
that intersection being a Haar-null singleton. -/
theorem divergence : SpectralDivergenceSpec.divergence := by
  intro d _ hd
  by_contra hfinite
  let ν : Measure (Torus d) := (torusMeasure d).withDensity
    (fun t => (ENNReal.ofReal (1 - phi t ^ 2))⁻¹)
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfinite
  let r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let s : ℕ → Set (Torus d) := fun n => Metric.closedBall 0 (r n)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr1 (n : ℕ) : r n ≤ 1 := by
    dsimp [r]
    apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hanti : Antitone s := by
    intro n m hnm
    apply Metric.closedBall_subset_closedBall
    dsimp [r]
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hinter : (⋂ n, s n) = {0} := by
    ext t
    constructor
    · intro ht
      apply Set.mem_singleton_iff.mpr
      apply dist_eq_zero.mp
      by_contra hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (lt_of_le_of_ne (dist_nonneg : 0 ≤ dist t 0) (Ne.symm hne))
      have hb : dist t 0 ≤ r n := Metric.mem_closedBall.mp (mem_iInter.mp ht n)
      exact (not_lt_of_ge hb) hn
    · rintro rfl
      apply mem_iInter.mpr
      intro n
      exact Metric.mem_closedBall.mpr (by simpa using (hr n).le)
  have hcont := hanti.measure_iInter (μ := ν)
    (fun n => measurableSet_closedBall.nullMeasurableSet) ⟨0, measure_ne_top ν (s 0)⟩
  have hnull : ν {0} = 0 :=
    withDensity_absolutelyContinuous (torusMeasure d) _ (singleton_zero d)
  have hbound : ENNReal.ofReal ((1 / Real.pi) ^ d) ≤ ν (⋂ n, s n) := by
    rw [hcont]
    exact le_iInf (fun n => uniform_ball_lower d hd (hr n) (hr1 n))
  rw [hinter, hnull] at hbound
  have hpos : 0 < ENNReal.ofReal ((1 / Real.pi) ^ d) := by positivity
  exact (not_le_of_gt hpos) hbound

end
end P207.Walk.SpectralDivergence
