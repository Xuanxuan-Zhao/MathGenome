import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.CanonicalProductExpansion
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace ExpandedFA.FredholmDeterminant.CanonicalProductExpansion

universe u
variable {I : Type u} {a : I → ℂ}

/-- A square-summable family is uniformly bounded, without a countability premise. -/
theorem exists_positive_bound (ha : Summable (fun i => ‖a i‖ ^ 2)) :
    ∃ B : ℝ, 0 < B ∧ ∀ i, ‖a i‖ ≤ B := by
  let S := ∑' i, ‖a i‖ ^ 2
  have hS : 0 ≤ S := tsum_nonneg (fun _ => sq_nonneg _)
  refine ⟨S + 1, by linarith, fun i => ?_⟩
  have hi : ‖a i‖ ^ 2 ≤ S := ha.le_tsum i (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg (‖a i‖ - 1)]

/-- All powers starting with the second are absolutely summable. -/
theorem summable_norm_powers (ha : Summable (fun i => ‖a i‖ ^ 2)) (n : ℕ) :
    Summable (fun i => ‖a i ^ (n + 2)‖) := by
  obtain ⟨B, hB, hbound⟩ := exists_positive_bound ha
  apply (ha.mul_left (B ^ n)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [norm_pow, pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbound i) n)
    (sq_nonneg _)

/-- The absolute double series is dominated by a geometric sequence times the
square-summable family. This justifies both orders of summation. -/
theorem summable_norm_double (ha : Summable (fun i => ‖a i‖ ^ 2))
    {B : ℝ} (hB : 0 < B) (hbound : ∀ i, ‖a i‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    Summable (fun p : ℕ × I => ‖-((z * a p.2) ^ (p.1 + 2) /
      ((p.1 + 2 : ℕ) : ℂ))‖) := by
  have hgeo := summable_geometric_of_lt_one (mul_nonneg (norm_nonneg z) hB.le) hz
  have hmajor := hgeo.mul_of_nonneg (ha.mul_left (‖z‖ ^ 2))
    (fun n => pow_nonneg (mul_nonneg (norm_nonneg z) hB.le) n)
    (fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  rintro ⟨n, i⟩
  simp only [norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_natCast]
  have hd : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  calc
    (‖z‖ * ‖a i‖) ^ (n + 2) / (n + 2 : ℕ) ≤ (‖z‖ * ‖a i‖) ^ (n + 2) :=
      div_le_self (by positivity) hd
    _ = (‖z‖ * ‖a i‖) ^ n * (‖z‖ ^ 2 * ‖a i‖ ^ 2) := by ring
    _ ≤ (‖z‖ * B) ^ n * (‖z‖ ^ 2 * ‖a i‖ ^ 2) := by
      gcongr
      exact hbound i

/-- The scalar logarithm with its linear term removed. -/
theorem hasSum_regularized_log {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => -(w ^ (n + 2) / ((n + 2 : ℕ) : ℂ)))
      (Complex.log (1 - w) + w) := by
  have h := Complex.hasSum_taylorSeries_neg_log' hw
  have ht : HasSum (fun n : ℕ => w ^ (n + 2) / ((n + 2 : ℕ) : ℂ))
      (-Complex.log (1 - w) - w) := by
    have he := (hasSum_nat_add_iff (f := fun n : ℕ =>
      w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) 1).mpr
      (show HasSum (fun n : ℕ => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        ((-Complex.log (1 - w) - w) + ∑ i ∈ Finset.range 1,
          w ^ (i + 1) / ((i + 1 : ℕ) : ℂ)) by simpa using h)
    simpa [Nat.add_assoc] using he
  simpa [add_comm] using ht.neg

/-- The moment expansion follows by absolute Fubini and exponentiation of the
regularized logarithm. No convergence certificate is an input. -/
theorem canonical_expansion : Spec.CanonicalExpansion.{u} := by
  intro I a ha
  refine ⟨summable_norm_powers ha, ?_⟩
  obtain ⟨B, hB, hbound⟩ := exists_positive_bound ha
  refine ⟨B⁻¹, inv_pos.mpr hB, fun z hz => ?_⟩
  have hzB : ‖z‖ * B < 1 := (lt_div_iff₀ hB).mp (by simpa only [one_div] using hz)
  let f : ℕ → I → ℂ := fun n i =>
    -((z * a i) ^ (n + 2) / ((n + 2 : ℕ) : ℂ))
  have habs : Summable (fun p : ℕ × I => ‖f p.1 p.2‖) :=
    summable_norm_double ha hB hbound hzB
  have hf : Summable (Function.uncurry f) := habs.of_norm
  have hrow (n : ℕ) : (∑' i, f n i) =
      -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2)) := by
    calc
      (∑' i, f n i) = ∑' i,
          -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * a i ^ (n + 2) := by
        apply tsum_congr
        intro i
        dsimp [f]
        rw [mul_pow]
        ring
      _ = _ := tsum_mul_left
  have houter : Summable (fun n : ℕ =>
      ‖-(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2))‖) := by
    have hh : Summable (fun n => ∑' i, f n i) := hf.prod
    exact (hh.congr hrow).norm
  have hsmall (i : I) : ‖z * a i‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound i) (norm_nonneg z)).trans_lt hzB
  have hcol (i : I) : (∑' n, f n i) = Complex.log (1 - z * a i) + z * a i :=
    (hasSum_regularized_log (hsmall i)).tsum_eq
  have hlogs : Summable (fun i => Complex.log (1 - z * a i) + z * a i) := by
    have hh : Summable (fun i => ∑' n, f n i) := hf.prod_symm.prod
    exact hh.congr hcol
  have heq : (∑' i, (Complex.log (1 - z * a i) + z * a i)) =
      ∑' n : ℕ, -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2)) := by
    calc
      _ = ∑' i, ∑' n, f n i := tsum_congr (fun i => (hcol i).symm)
      _ = ∑' n, ∑' i, f n i := hf.tsum_comm
      _ = _ := tsum_congr hrow
  have hexp (i : I) : Complex.exp (Complex.log (1 - z * a i) + z * a i) =
      (1 - z * a i) * Complex.exp (z * a i) := by
    rw [Complex.exp_add, Complex.exp_log]
    intro hzero
    have hw : z * a i = 1 := sub_eq_zero.mp hzero |>.symm
    simpa [hw] using hsmall i
  have hprod : HasProd (fun i => (1 - z * a i) * Complex.exp (z * a i))
      (Complex.exp (∑' n : ℕ,
        -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) * (∑' i, a i ^ (n + 2)))) := by
    rw [← heq]
    simpa only [Function.comp_def, hexp] using hlogs.hasSum.cexp
  exact ⟨houter, hprod, hprod.tprod_eq⟩

end ExpandedFA.FredholmDeterminant.CanonicalProductExpansion
