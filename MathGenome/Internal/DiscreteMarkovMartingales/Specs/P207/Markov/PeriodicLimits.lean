import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.CyclicStructure
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TotalVariation

/-! Paper §3.5 (W17). The Cesàro law at index n averages times 0 through n;
thus every average has positive length n+1. The residue limit specifies the
entire probability mass function, so it is exactly d π(· ∩ D_(l+r)). -/

open Filter
open scoped Topology ENNReal Classical
universe u
namespace P207.Markov
noncomputable section

/-- Average of the first n+1 marginal laws, including time zero. -/
def cesaroLaw {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S)
    (n : ℕ) : ProbabilityLaw S :=
  (PMF.ofFintype (fun _ : Fin (n + 1) => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (by simp))).bind
      (fun k => evolve ν P k.val)

/-- The two-state chain with P(0,1)=P(1,0)=1, on Bool={false,true}. -/
def alternatingKernel : StochasticMatrix Bool := fun i => PMF.pure (!i)

def alternatingLaw : ProbabilityLaw Bool :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) (by
    simp only [Fintype.sum_bool, ← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

namespace PeriodicLimitsSpec

def cesaroLawType := {S : Type u} → ProbabilityLaw S → StochasticMatrix S → ℕ → ProbabilityLaw S
noncomputable def cesaroLawValue : cesaroLawType.{u} := @cesaroLaw

def alternatingKernelType := StochasticMatrix Bool
noncomputable def alternatingKernelValue : alternatingKernelType := fun i => PMF.pure (!i)
def alternatingLawType := ProbabilityLaw Bool
noncomputable def alternatingLawValue : alternatingLawType :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) (by
    simp only [Fintype.sum_bool, ← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

def cesaroLaw_apply : Prop :=
  ∀ {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (n : ℕ) (j : S),
    (cesaroLaw ν P n j).toReal = ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), (evolve ν P k j).toReal

def cyclic_residue_limit : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S) (d : ℕ) (c : CyclicPartition P d),
    Irreducible P → IsStationary P π → (∀ i, period P i = d) →
    ∃ μ : Fin d → ProbabilityLaw S,
      (∀ l j, μ l j = if c.label j = l then (d : ℝ≥0∞) * π j else 0) ∧
      ∀ (i : S) (r : Fin d),
        Tendsto (fun m => totalVariation (power P (m * d + r.val) i)
          (μ ⟨((c.label i).val + r.val) % d, Nat.mod_lt _ c.period_pos⟩)) atTop (𝓝 0)

def cesaro_tendsto : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → IsStationary P π → ∀ ν : ProbabilityLaw S,
      Tendsto (fun n => totalVariation (cesaroLaw ν P n) π) atTop (𝓝 0)

def periodic_obstruction : Prop :=
  ∀ {S : Type u} [Countable S] (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (d : ℕ) (c : CyclicPartition P d), IsStationary P π → 1 < d →
    ∀ (i : S) (n : ℕ), 1 - 1 / (d : ℝ) ≤ totalVariation (power P n i) π

def stationary_marginals : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S),
    IsStationary P π → ∀ n, evolve π P n = π

def periodic_limits : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (d : ℕ),
    Irreducible P → (∃ i, PositiveRecurrent P i) → (∀ i, period P i = d) →
    ∃ π : ProbabilityLaw S, IsStationary P π ∧
      ∃ (c : CyclicPartition P d) (μ : Fin d → ProbabilityLaw S),
        c.StationaryData π ∧
        (∀ l j, μ l j = if c.label j = l then (d : ℝ≥0∞) * π j else 0) ∧
        (∀ (i : S) (r : Fin d),
          Tendsto (fun m => totalVariation (power P (m * d + r.val) i)
            (μ ⟨((c.label i).val + r.val) % d, Nat.mod_lt _ c.period_pos⟩)) atTop (𝓝 0)) ∧
        (∀ ν : ProbabilityLaw S,
          Tendsto (fun n => totalVariation (cesaroLaw ν P n) π) atTop (𝓝 0)) ∧
        (1 < d → ∀ (i : S) (n : ℕ),
          1 - 1 / (d : ℝ) ≤ totalVariation (power P n i) π) ∧
        (∀ n, evolve π P n = π)

/-- Explicit TV subsequence limits for the alternating example. -/
def alternating_cyclic_limits : Prop :=
  ∀ i : Bool,
    Tendsto (fun m => totalVariation (power alternatingKernel (m*2) i) (PMF.pure i))
      atTop (𝓝 0) ∧
    Tendsto (fun m => totalVariation (power alternatingKernel (m*2+1) i) (PMF.pure (!i)))
      atTop (𝓝 0)

def alternating_example : Prop :=
  alternatingKernel false true = 1 ∧ alternatingKernel true false = 1 ∧
  (∀ i, alternatingLaw i = (2 : ℝ≥0∞)⁻¹) ∧
  IsStationary alternatingKernel alternatingLaw ∧
  (∀ (i : Bool) (n : ℕ), totalVariation (power alternatingKernel n i) alternatingLaw = 1/2) ∧
  (∀ (i : Bool) (m : ℕ), power alternatingKernel (m * 2) i = PMF.pure i ∧
    power alternatingKernel (m * 2 + 1) i = PMF.pure (!i)) ∧
  (∀ ν : ProbabilityLaw Bool,
    Tendsto (fun n => totalVariation (cesaroLaw ν alternatingKernel n) alternatingLaw)
      atTop (𝓝 0)) ∧
  (∀ n, evolve alternatingLaw alternatingKernel n = alternatingLaw)

end PeriodicLimitsSpec
end
end P207.Markov
