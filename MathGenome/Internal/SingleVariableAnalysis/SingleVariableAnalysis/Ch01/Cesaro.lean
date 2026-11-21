import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Archimedean
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Cesaro
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Ring.GeomSum

/-!
# Arithmetic averages and counterexamples

The arithmetic means use the same shifted indexing as the upstream
sequence interface: their `n`th value averages the first `n+1` terms.
The library Cesàro theorem is proved by splitting the averaged errors
into a finite prefix and a small tail; it applies to real normed spaces,
so includes both canonical scalar types without extra assumptions.
We translate its real scalar action on ℂ to multiplication by the
complex reciprocal, and shift its averaging length to `n+1`.

The alternating counterexample is proved separately: its partial sums
have modulus at most one, so the Archimedean reciprocal estimate sends
its averages to zero. Its even and odd positive-index subsequences
are constant with distinct limits. The natural sequence tends to
positive infinity, which the upstream interface distinguishes from
every finite scalar limit.
-/

namespace SingleVariableAnalysis

open scoped Topology BigOperators

theorem real_cesaro (a : ℕ → ℝ) (L : ℝ) (h : RealSequenceConverges a L) :
    RealSequenceConverges
      (fun n => ((n : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), a j) L := by
  apply (realSequenceConverges_iff _ _).mpr
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (((realSequenceConverges_iff a L).mp h).cesaro.comp
      (Filter.tendsto_add_atTop_nat 1))

theorem complex_cesaro (a : ℕ → ℂ) (L : ℂ) (h : ComplexSequenceConverges a L) :
    ComplexSequenceConverges
      (fun n => ((n : ℂ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), a j) L := by
  apply (complexSequenceConverges_iff _ _).mpr
  simpa only [Function.comp_def, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one] using
    (((complexSequenceConverges_iff a L).mp h).cesaro_smul.comp
      (Filter.tendsto_add_atTop_nat 1))

theorem alternating_even_subsequence :
    RealSequenceConverges (fun n : ℕ => (-1 : ℝ) ^ ((2 * n + 1) + 1)) 1 := by
  have he : ∀ n : ℕ, (-1 : ℝ) ^ ((2 * n + 1) + 1) = 1 := by
    intro n
    exact (show Even ((2 * n + 1) + 1) from ⟨n + 1, by omega⟩).neg_one_pow
  simp_rw [he]
  exact (realSequenceConverges_iff _ _).mpr tendsto_const_nhds

theorem alternating_odd_subsequence :
    RealSequenceConverges (fun n : ℕ => (-1 : ℝ) ^ (2 * n + 1)) (-1) := by
  have ho : ∀ n : ℕ, (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    intro n
    exact (show Odd (2 * n + 1) from ⟨n, rfl⟩).neg_one_pow
  simp_rw [ho]
  exact (realSequenceConverges_iff _ _).mpr tendsto_const_nhds

theorem alternating_bounded (n : ℕ) : |(-1 : ℝ) ^ (n + 1)| ≤ 1 := by
  simp

theorem alternating_partial_sums_bounded (n : ℕ) :
    |∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1)| ≤ 1 := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, neg_one_geom_sum]
  split_ifs <;> norm_num

theorem alternating_not_convergent :
    ¬ ∃ L : ℝ, RealSequenceConverges (fun n => (-1 : ℝ) ^ (n + 1)) L := by
  rintro ⟨L, hL⟩
  have he : StrictMono (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 < 2 * b + 1
    omega
  have ho : StrictMono (fun n : ℕ => 2 * n) := by
    intro a b hab
    change 2 * a < 2 * b
    omega
  have h := (realSequenceConverges_iff _ _).mp hL
  have hpos : L = 1 := tendsto_nhds_unique (h.comp he.tendsto_atTop)
    ((realSequenceConverges_iff _ _).mp alternating_even_subsequence)
  have hneg : L = -1 := tendsto_nhds_unique (h.comp ho.tendsto_atTop)
    ((realSequenceConverges_iff _ _).mp alternating_odd_subsequence)
  norm_num [hpos] at hneg

theorem alternating_cesaro :
    RealSequenceConverges
      (fun n => ((n : ℝ) + 1)⁻¹ *
        ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1)) 0 := by
  intro ε hε
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hrecip := hN (n + 1) (hn.trans (Nat.le_succ n))
  simp only [Nat.cast_add, Nat.cast_one, one_div] at hrecip
  simp only [sub_zero, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (alternating_partial_sums_bounded n)).trans_lt
    hrecip

theorem natural_divergesToPosInfinity :
    DivergesToPosInfinity (fun n : ℕ => (n : ℝ) + 1) := by
  intro B
  obtain ⟨N, _, hN⟩ := archimedean_bound B
  refine ⟨N, fun n hn => ?_⟩
  exact (hN.trans_le (Nat.cast_le.mpr hn)).trans (lt_add_one _)

theorem natural_not_convergent :
    ¬ ∃ L : ℝ, RealSequenceConverges (fun n : ℕ => (n : ℝ) + 1) L := by
  rintro ⟨L, hL⟩
  exact posInfinity_not_finite _ natural_divergesToPosInfinity L hL

end SingleVariableAnalysis
