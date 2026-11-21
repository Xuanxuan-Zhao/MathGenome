import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.FiniteBinomialIdentities
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.FixedPrefixLimits
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators Topology
open Filter

namespace D03SupportRepairs

/-- Each fixed coefficient tends to the corresponding inverse factorial along positive rows. -/
theorem coefficientLimit (j : ℕ) :
    Tendsto (fun n : ℕ => b (n + 1) j) atTop (𝓝 (invFactorial j)) := by
  have hfactor (ℓ : ℕ) :
      Tendsto (fun n : ℕ => 1 - (ℓ : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n : ℕ => (ℓ : ℝ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ℓ : ℝ)
    simpa only [sub_zero] using tendsto_const_nhds.sub hdiv
  have hprod : Tendsto
      (fun n : ℕ => ∏ ℓ ∈ Finset.range j, (1 - (ℓ : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    simpa only [Finset.prod_const_one] using
      tendsto_finsetProd (Finset.range j) (fun ℓ _ => hfactor ℓ)
  have hlimit := hprod.const_mul (invFactorial j)
  simp only [mul_one] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop j] with n hn
  exact (coefficientProduct (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) j
    (hn.trans (Nat.le_succ n))).symm

/-- A finite sum of the coefficient limits, with the cutoff fixed before the limit. -/
theorem fixedPrefixLimit (J : ℕ) :
    Tendsto (fun n : ℕ => «prefix» (n + 1) J) atTop
      (𝓝 (∑ j ∈ Finset.range (J + 1), invFactorial j)) := by
  exact tendsto_finsetSum (Finset.range (J + 1)) (fun j _ => coefficientLimit j)

end D03SupportRepairs
