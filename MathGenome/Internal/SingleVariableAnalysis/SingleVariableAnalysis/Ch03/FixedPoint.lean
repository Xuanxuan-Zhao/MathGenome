import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.FixedPoint
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The contraction principle

K03.03.fixed_point, paper.tex:617–632. We use Mathlib's Banach theorem
on the same arbitrary complete metric space. Its proof makes the iterates
Cauchy by geometric bounds, takes their complete limit, and uses Lipschitz
continuity to show it is fixed. Its real-distance API gives both estimates.
The conversion `⟨q, hq₀⟩ : ℝ≥0` has real value exactly `q`; it does not
replace the source constant or require strict positivity. Every natural
index, including zero, is retained. A recurrence bridge below identifies
arbitrary sequences satisfying the source recursion with canonical iterates.
-/
namespace SingleVariableAnalysis

open scoped Topology NNReal
universe u

theorem contraction_principle
    {X : Type u} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : X → X) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hT : ∀ x y, dist (T x) (T y) ≤ q * dist x y) :
    ∃ p : X, T p = p ∧ (∀ r : X, T r = r → r = p) ∧
      ∀ x₀ : X,
        Filter.Tendsto (fun n : ℕ => T^[n] x₀) Filter.atTop (𝓝 p) ∧
        ∀ n : ℕ,
          dist (T^[n] x₀) p ≤ q ^ n / (1 - q) * dist (T x₀) x₀ ∧
          dist (T^[n] x₀) p ≤ dist (T^[n + 1] x₀) (T^[n] x₀) / (1 - q) := by
  let K : ℝ≥0 := ⟨q, hq₀⟩
  have hc : ContractingWith K T :=
    ⟨hq₁, LipschitzWith.of_dist_le_mul hT⟩
  refine ⟨hc.fixedPoint T, hc.fixedPoint_isFixedPt, ?_, ?_⟩
  · intro r hr
    exact hc.fixedPoint_unique hr
  · intro x₀
    refine ⟨hc.tendsto_iterate_fixedPoint x₀, fun n => ⟨?_, ?_⟩⟩
    · calc
        dist (T^[n] x₀) (hc.fixedPoint T) ≤
            dist x₀ (T x₀) * q ^ n / (1 - q) :=
          hc.apriori_dist_iterate_fixedPoint_le x₀ n
        _ = q ^ n / (1 - q) * dist (T x₀) x₀ := by
          rw [dist_comm x₀ (T x₀), div_mul_eq_mul_div, mul_comm (q ^ n)]
    · have h : dist (T^[n] x₀) (hc.fixedPoint T) ≤
          dist (T^[n] x₀) (T^[n + 1] x₀) / (1 - q) :=
        hc.aposteriori_dist_iterate_fixedPoint_le x₀ n
      simpa only [dist_comm (T^[n] x₀) (T^[n + 1] x₀)] using h

theorem contraction_orbit
    {X : Type u} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : X → X) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hT : ∀ x y, dist (T x) (T y) ≤ q * dist x y) :
    ∃ p : X, T p = p ∧ (∀ r : X, T r = r → r = p) ∧
      ∀ x : ℕ → X, (∀ n, x (n + 1) = T (x n)) →
        Filter.Tendsto x Filter.atTop (𝓝 p) ∧
        ∀ n : ℕ,
          dist (x n) p ≤ q ^ n / (1 - q) * dist (x 1) (x 0) ∧
          dist (x n) p ≤ dist (x (n + 1)) (x n) / (1 - q) := by
  obtain ⟨p, hp, hu, horbit⟩ := contraction_principle T q hq₀ hq₁ hT
  refine ⟨p, hp, hu, ?_⟩
  intro x hx
  have hit (n : ℕ) : T^[n] (x 0) = x n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hx n]
  simpa only [hit, ← hx 0] using horbit (x 0)

end SingleVariableAnalysis
