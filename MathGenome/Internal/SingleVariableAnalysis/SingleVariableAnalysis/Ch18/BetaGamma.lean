import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BetaGamma
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.ShiftedBetaLimit
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaEulerLimit

/-! The one-variable proof of the Beta–Gamma identity. All analytic input
comes from the supplied shifted Beta and Euler limits. The remaining steps
are finite recurrence, positive quotients, inversion, and limit uniqueness. -/
noncomputable section
namespace SingleVariableAnalysis.SpecialIntegrals
open Filter
open scoped Topology BigOperators
namespace BG
export Specs.SingleVariableAnalysis.Ch18.BetaGamma
  (risingProductType risingProductValue risingProductPositive betaShiftRecurrence
    ratioPositive eulerRatioLimit inverseRatioLimit betaGammaIdentity)
end BG

abbrev risingProduct := BG.risingProductValue

theorem risingProduct_positive : BG.risingProductPositive := by
  intro p hp n
  exact Finset.prod_pos (fun j _ => add_pos_of_pos_of_nonneg hp (Nat.cast_nonneg j))

theorem risingProduct_succ (p : ℝ) (n : ℕ) :
    risingProduct p (n+1) = risingProduct p n * (p+n) :=
  Finset.prod_range_succ _ _

/-- Iterate the first-parameter recurrence by finite induction. -/
theorem beta_shift_recurrence : BG.betaShiftRecurrence := by
  intro p q hp hq n
  change beta (p+n) q = risingProduct p n * beta p q / risingProduct (p+q) n
  induction n with
  | zero => simp [risingProduct, BG.risingProductValue]
  | succ n ih =>
    have hpn : 0 < p+(n : ℝ) := add_pos_of_pos_of_nonneg hp (Nat.cast_nonneg n)
    have hsn : 0 < p+q+(n : ℝ) := add_pos_of_pos_of_nonneg (add_pos hp hq) (Nat.cast_nonneg n)
    have hr := beta_add_one_left (p+n) q hpn hq
    change beta (p+(n : ℝ)+1) q = (p+n)*beta (p+n) q / (p+(n : ℝ)+q) at hr
    simp only [Nat.cast_succ, ← add_assoc]
    rw [hr, ih, risingProduct_succ, risingProduct_succ]
    field_simp [ne_of_gt (risingProduct_positive (p+q) (add_pos hp hq) n),
      ne_of_gt hsn, show p+(n : ℝ)+q ≠ 0 by linarith]
    ring


theorem beta_gamma_ratio_positive : BG.ratioPositive := by
  intro p q hp hq
  refine ⟨?_, div_pos (gamma_positive _ _) (gamma_positive _ _),
    div_pos (gamma_positive _ _) (gamma_positive _ _)⟩
  intro n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact div_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (risingProduct_positive p hp n)) (risingProduct_positive (p+q) (add_pos hp hq) n)
  · exact div_pos (risingProduct_positive (p+q) (add_pos hp hq) n)
      (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (risingProduct_positive p hp n))

/-- Cancel the factorials and powers in the two Euler approximants. -/
theorem euler_rising_ratio_limit : BG.eulerRatioLimit := by
  intro p q hp hq
  have h := ((gamma_euler_limit (p+q) (add_pos hp hq)).2).div
    ((gamma_euler_limit p hp).2) (ne_of_gt (gamma_positive p hp))
  have hratio : Tendsto (fun n : ℕ => (n : ℝ)^q * risingProduct p (n+1) /
      risingProduct (p+q) (n+1)) atTop
      (𝓝 (gammaIntegral (p+q) (add_pos hp hq) / gammaIntegral p hp)) := by
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
    change ((n.factorial : ℝ)*(n : ℝ)^(p+q)/risingProduct (p+q) (n+1)) /
      ((n.factorial : ℝ)*(n : ℝ)^p/risingProduct p (n+1)) = _
    rw [Real.rpow_add hnR]
    field_simp [hf, ne_of_gt (Real.rpow_pos_of_pos hnR p),
      ne_of_gt (risingProduct_positive p hp (n+1)),
      ne_of_gt (risingProduct_positive (p+q) (add_pos hp hq) (n+1))]
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, gammaIntegral,
    risingProduct] using hratio

/-- The positive nonzero limit permits inversion. A scalar factor tending
to one changes the (n-1)^q normalization into n^q. -/
theorem inverse_rising_ratio_limit : BG.inverseRatioLimit := by
  intro p q hp hq
  have hinv := (euler_rising_ratio_limit p q hp hq).inv₀
    (ne_of_gt (div_pos (gamma_positive _ _) (gamma_positive _ _)))
  have hr : Tendsto (fun n : ℕ => ((n : ℝ)-1)/(n : ℝ)) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) (-1) 0 1
        (d := 1) one_ne_zero)
  have hpow := hr.rpow_const (p := q) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hpow
  have h := hinv.mul hpow
  rw [show (Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaIntegralValue
      (p+q) (add_pos hp hq) /
      Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaIntegralValue p hp)⁻¹ * 1 =
      gammaIntegral p hp / gammaIntegral (p+q) (add_pos hp hq) by
        rw [inv_div, mul_one]
        rfl] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  change (((n : ℝ)-1)^q * risingProduct p n / risingProduct (p+q) n)⁻¹ *
    (((n : ℝ)-1)/(n : ℝ))^q = _
  rw [Real.div_rpow hn1.le hn0.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hn0 q),
    ne_of_gt (Real.rpow_pos_of_pos hn1 q),
    ne_of_gt (risingProduct_positive p hp n),
    ne_of_gt (risingProduct_positive (p+q) (add_pos hp hq) n)]

/-- Multiply the two proved limits; the exact finite recurrence makes
this sequence constantly equal to B(p,q) on its positive-index tail. -/
theorem beta_gamma_identity : BG.betaGammaIdentity := by
  intro p q hp hq
  have h := (ShiftedBetaLimit.shifted_beta_limit p q hp hq).mul
    (inverse_rising_ratio_limit p q hp hq)
  have hc : Tendsto (fun _ : ℕ => beta p q) atTop
      (𝓝 (gammaIntegral q hq * (gammaIntegral p hp / gammaIntegral (p+q) (add_pos hp hq)))) := by
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [beta_shift_recurrence p q hp hq n]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hnR q),
      ne_of_gt (risingProduct_positive p hp n),
      ne_of_gt (risingProduct_positive (p+q) (add_pos hp hq) n)]
  have he := tendsto_nhds_unique tendsto_const_nhds hc
  change beta p q = _
  rw [he]
  simp only [gammaIntegral]
  ring

end SingleVariableAnalysis.SpecialIntegrals
