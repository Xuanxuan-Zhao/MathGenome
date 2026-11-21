import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.ContinuousNotBv
import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcBasic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology BigOperators

namespace D11.Ch12.ContinuousNotBv

/-- The paper's displayed function, extended to an ambient real function. -/
noncomputable def oscillation (x : ℝ) : ℝ :=
  x * Real.cos (Real.pi / (2 * x))

@[simp] theorem oscillation_zero : oscillation 0 = 0 := by simp [oscillation]

lemma abs_oscillation_le (x : ℝ) : |oscillation x| ≤ |x| := by
  simpa only [oscillation, abs_mul, mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (Real.pi / (2*x))) (abs_nonneg x)

theorem continuous : ContinuousOn oscillation (Icc 0 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases h : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    simpa only [oscillation_zero, Real.dist_eq, sub_zero] using
      (abs_oscillation_le y).trans_lt (by simpa [Real.dist_eq] using hy)
  · unfold oscillation
    fun_prop (disch := positivity)

/-- Points with alternating sampled values tending down to zero. The shift avoids division by
zero and enumerates exactly the source's `1/(2n)` for `n ≥ 1`. -/
noncomputable def sample (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1))

lemma sample_pos (n : ℕ) : 0 < sample n := by unfold sample; positivity

lemma sample_mem (n : ℕ) : sample n ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact (sample_pos n).le
  · dsimp [sample]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma sample_antitone : Antitone sample := by
  intro m n hmn
  dsimp [sample]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hmn 1) (by norm_num)

lemma oscillation_sample (n : ℕ) :
    oscillation (sample n) = (-1 : ℝ) ^ (n+1) * sample n := by
  have hd : (2 : ℝ) * ((n : ℝ)+1) ≠ 0 := by positivity
  have harg : Real.pi / (2 * sample n) = (n+1 : ℝ) * Real.pi := by
    dsimp [sample]
    field_simp
  rw [oscillation, harg]
  rw [show (n+1 : ℝ) = ((n+1 : ℕ) : ℝ) by simp, Real.cos_nat_mul_pi]
  ring

lemma sample_increment (n : ℕ) :
    ‖oscillation (sample (n+1)) - oscillation (sample n)‖ = sample (n+1) + sample n := by
  rw [oscillation_sample, oscillation_sample]
  have heq : (-1 : ℝ) ^ (n+1+1) * sample (n+1) - (-1 : ℝ) ^ (n+1) * sample n =
      (-1 : ℝ) ^ (n+1) * (-(sample (n+1) + sample n)) := by rw [pow_succ]; ring
  rw [heq, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  exact Real.norm_of_nonneg (add_nonneg (sample_pos _).le (sample_pos _).le)

/-- Finite variation bounds the sum of all consecutive sampled increments. -/
lemma sampled_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N,
      edist (oscillation (sample (i+1))) (oscillation (sample i))) ≤
      eVariationOn oscillation (Icc 0 1) := by
  have hcomp := eVariationOn.comp_le_of_antitoneOn oscillation sample
    (sample_antitone.antitoneOn univ) (fun i _ => sample_mem i : MapsTo sample univ (Icc 0 1))
  exact (eVariationOn.sum_le (f := oscillation ∘ sample)
    (s := univ) (n := N) monotone_id (fun _ => mem_univ _)).trans hcomp

/-- A finite variation would make a constant multiple of the harmonic series
summable. No regularity assumption on variation is used. -/
theorem not_bv : ¬ D11.Ch12.BV oscillation 0 1 := by
  intro h
  have hfin : eVariationOn oscillation (Icc 0 1) ≠ ⊤ := by
    exact ((D11.Ch12.bv_iff_boundedVariationOn _ _ _).mp h)
  have hsum : ∀ N, ∑ i ∈ Finset.range N, sample i ≤
      (eVariationOn oscillation (Icc 0 1)).toReal := by
    intro N
    calc
      ∑ i ∈ Finset.range N, sample i ≤
          ∑ i ∈ Finset.range N,
            ‖oscillation (sample (i+1)) - oscillation (sample i)‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [sample_increment]
        exact le_add_of_nonneg_left (sample_pos _).le
      _ = (∑ i ∈ Finset.range N,
          edist (oscillation (sample (i+1))) (oscillation (sample i))).toReal := by
        rw [ENNReal.toReal_sum (fun _ _ => edist_ne_top _ _)]
        simp only [← dist_edist, dist_eq_norm]
      _ ≤ (eVariationOn oscillation (Icc 0 1)).toReal :=
        ENNReal.toReal_mono hfin (sampled_sum_le N)
  have hs : Summable sample := summable_of_sum_range_le (fun n => (sample_pos n).le) hsum
  have hh : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := by
    convert hs.mul_left 2 using 1
    ext n
    dsimp [sample]
    field_simp
  have : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hh)
  exact Real.not_summable_one_div_natCast this

theorem infinite_variation : D11.Ch12.variation oscillation 0 1 = ⊤ := by
  simpa only [D11.Ch12.BV, not_lt_top_iff] using not_bv

theorem not_ac : ¬ D11.Ch12.AbsolutelyContinuousOnInterval oscillation 0 1 := by
  intro h
  exact not_bv (D11.Ch12.AcBasic.bv (by norm_num) h)

end D11.Ch12.ContinuousNotBv
