import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.BernoulliMGF
import MathGenome.Internal.ExtremalOptimization.P205.Probability.ExponentialMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory

namespace P205.Probability

/-- The one-variable Bernoulli MGF, using the actual success-event probability. -/
theorem bernoulli_mgf_single {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → ℝ)
    (hX : Measurable X) (h01 : ∀ᵐ ω ∂ν, X ω = 0 ∨ X ω = 1) (lam : ℝ) :
    mgf X ν lam = 1 + ν.real {ω | X ω = 1} * (Real.exp lam - 1) := by
  classical
  have hs : MeasurableSet {ω | X ω = 1} := measurableSet_eq_fun hX measurable_const
  have heq : (fun ω => Real.exp (lam * X ω)) =ᵐ[ν]
      (fun ω => (1 : ℝ) + {ω | X ω = 1}.indicator (fun _ => Real.exp lam - 1) ω) := by
    filter_upwards [h01] with ω hω
    rcases hω with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [mgf, integral_congr_ae heq,
    integral_add (integrable_const 1) ((integrable_const _).indicator hs),
    integral_const, integral_indicator_const _ hs]
  simp

/-- The moment formula and exponential bound, valid also for negative lam. -/
theorem bernoulli_mgf : Specs.P205.Probability.BernoulliMGF := by
  intro Ω ι _ _ ν _ X p hX h01 hp hpLaw hInd lam
  classical
  have hB (i : ι) : ∃ B : ℝ, ∀ᵐ ω ∂ν, |X i ω| ≤ B := by
    refine ⟨1, ?_⟩
    filter_upwards [h01 i] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  obtain ⟨_, hInt, hFactor⟩ := independent_mgf_sum ν X hX hB hInd lam
  refine ⟨hInt, ?_, ?_⟩
  · rw [hFactor]
    apply Finset.prod_congr rfl
    intro i _
    rw [bernoulli_mgf_single ν (X i) (hX i) (h01 i) lam, hpLaw i]
  · calc
      (∏ i, (1 + p i * (Real.exp lam - 1))) ≤
          ∏ i, Real.exp (p i * (Real.exp lam - 1)) := by
        apply Finset.prod_le_prod₀
        · intro i _
          have hmul := mul_nonneg (hp i).1 (Real.exp_pos lam).le
          nlinarith [(hp i).2]
        · intro i _
          linarith [Real.add_one_le_exp (p i * (Real.exp lam - 1))]
      _ = Real.exp ((∑ i, p i) * (Real.exp lam - 1)) := by
        rw [← Real.exp_sum, Finset.sum_mul]

/-- Zero total success probability forces the entire sum to vanish a.e. -/
theorem bernoulli_sum_zero : Specs.P205.Probability.BernoulliSumZero := by
  intro Ω ι _ _ ν _ X p _hX h01 hp hpLaw hSum
  classical
  have hp0 (i : ι) : p i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hp j).1)).mp hSum i (Finset.mem_univ i)
  have hXi (i : ι) : ∀ᵐ ω ∂ν, X i ω = 0 := by
    have hNull : ν {ω | X i ω = 1} = 0 := by
      apply (measureReal_eq_zero_iff).mp
      rw [← hpLaw i, hp0 i]
    have hNot : ∀ᵐ ω ∂ν, X i ω ≠ 1 := by
      simpa only [ae_iff, not_not] using hNull
    filter_upwards [h01 i, hNot] with ω hω hn
    exact hω.resolve_right hn
  filter_upwards [ae_all_iff.mpr hXi] with ω hω
  simp [hω]

end P205.Probability
