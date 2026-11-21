import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BohrMollerupSqueeze
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaEulerLimit
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! Finite Bohr–Mollerup squeeze. The logarithmic secant estimates are
`Real.BohrMollerup.f_add_nat_ge` and `f_add_nat_le`; these require only
convexity and the logarithmic recurrence, with no regularity hypothesis.
The limits below use the upstream Euler limit for the original Gamma integral.
-/
noncomputable section
namespace SingleVariableAnalysis.SpecialIntegrals
open Filter
open scoped Topology BigOperators
namespace BMSpec
export Specs.SingleVariableAnalysis.Ch18.BohrMollerupSqueeze
  (admissible lower upper factorialValues squeezeBounds squeezeLimits)
end BMSpec

theorem bohr_mollerup_factorial_values : BMSpec.factorialValues := by
  intro F hF n hn
  have h : ∀ k : ℕ, F ((k : ℝ) + 1) = (k.factorial : ℝ) := by
    intro k
    induction k with
    | zero => simpa using hF.2.1
    | succ k ih =>
      rw [Nat.cast_succ, hF.2.2.1 _ (by positivity), ih, Nat.factorial_succ]
      push_cast
      ring
  convert h (n - 1) using 1
  rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]

private theorem product_pos (x : ℝ) (hx : 0 < x) (n : ℕ) :
    0 < ∏ j ∈ Finset.range n, (x + (j : ℝ)) :=
  Finset.prod_pos (fun j _ => add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j))

private theorem quotient_pos (x b : ℝ) (hx : 0 < x) (hb : 0 < b) (n : ℕ) :
    0 < ((n - 1).factorial : ℝ) * b ^ x /
      ∏ j ∈ Finset.range n, (x + (j : ℝ)) :=
  div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hb x)) (product_pos x hx n)

private theorem log_quotient (x b : ℝ) (hx : 0 < x) (hb : 0 < b) (n : ℕ) :
    Real.log (((n - 1).factorial : ℝ) * b ^ x /
      ∏ j ∈ Finset.range n, (x + (j : ℝ))) =
      Real.log ((n - 1).factorial : ℝ) + x * Real.log b -
        ∑ j ∈ Finset.range n, Real.log (x + (j : ℝ)) := by
  rw [Real.log_div (mul_ne_zero (by positivity) (Real.rpow_pos_of_pos hb x).ne')
      (product_pos x hx n).ne',
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hb x).ne',
    Real.log_rpow hb, Real.log_prod (fun j _ =>
      (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j)).ne')]

theorem bohr_mollerup_squeeze_bounds : BMSpec.squeezeBounds := by
  intro F hF x hx hx1 n hn
  let G : ℝ → ℝ := fun y => Real.log (F y)
  have hG : ConvexOn ℝ (Set.Ioi 0) G :=
    (convexFunctionOn_iff_convexOn _ Set.ordConnected_Ioi G).mp hF.2.2.2
  have hrec : ∀ {y : ℝ}, 0 < y → G (y + 1) = G y + Real.log y := by
    intro y hy
    dsimp [G]
    rw [hF.2.2.1 y hy, Real.log_mul hy.ne' (hF.1 y hy).ne', add_comm]
  have hnat : G (n : ℝ) = Real.log ((n - 1).factorial : ℝ) := by
    dsimp [G]
    rw [bohr_mollerup_factorial_values F hF n (by omega)]
  have hadd := Real.BohrMollerup.f_add_nat_eq hrec hx n
  have hlow := Real.BohrMollerup.f_add_nat_ge hG hrec hn hx
  have hupp := Real.BohrMollerup.f_add_nat_le hG hrec (by omega : n ≠ 0) hx hx1
  rw [hnat, add_comm (n : ℝ) x, hadd] at hlow hupp
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnpred : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  constructor
  · apply (Real.log_le_log_iff (quotient_pos x _ hx hnpred n) (hF.1 x hx)).mp
    change Real.log (((n - 1).factorial : ℝ) * ((n : ℝ) - 1) ^ x /
      ∏ j ∈ Finset.range n, (x + (j : ℝ))) ≤ G x
    rw [log_quotient x _ hx hnpred n]
    linarith
  · apply (Real.log_le_log_iff (hF.1 x hx) (quotient_pos x _ hx hnpos n)).mp
    change G x ≤ Real.log (((n - 1).factorial : ℝ) * (n : ℝ) ^ x /
      ∏ j ∈ Finset.range n, (x + (j : ℝ)))
    rw [log_quotient x _ hx hnpos n]
    linarith

theorem bohr_mollerup_squeeze_limits : BMSpec.squeezeLimits := by
  intro x hx _hx1
  have heuler := (gamma_euler_limit x hx).2
  have hlower : Tendsto (BMSpec.lower x) atTop
      (𝓝 (Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaIntegralValue x hx)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [BMSpec.lower, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right] using heuler
  refine ⟨hlower, ?_⟩
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using
      (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hpower : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ)) ^ x)
      atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hratio.rpow_const (Or.inl one_ne_zero)
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hmul := ((tendsto_add_atTop_iff_nat 1).mpr hlower).mul hpower
  simp only [mul_one] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpow := (Real.rpow_pos_of_pos hnpos x).ne'
  dsimp [BMSpec.lower, BMSpec.upper]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [Real.div_rpow (by linarith) hnpos.le]
  field_simp

end SingleVariableAnalysis.SpecialIntegrals
