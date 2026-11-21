import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.EventualPositivity
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TotalVariation
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Stationarity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Lattice.Fold

open scoped ENNReal Classical
universe u
namespace P207.Markov
noncomputable section

/-- The common mass in column `j` of the `m`-step transition matrix. -/
def blockCommonMass {S : Type u} [Fintype S] [Nonempty S]
    (P : StochasticMatrix S) (m : ℕ) (j : S) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => realMatrix (power P m) i j)

/-- Total common mass of all rows of the `m`-step matrix. -/
def blockMinorization {S : Type u} [Fintype S] [Nonempty S]
    (P : StochasticMatrix S) (m : ℕ) : ℝ := ∑ j, blockCommonMass P m j

/-! Paper.tex §3.6 (W18). All laws and transition powers are the canonical
row-vector objects. Natural-number division is the stated floor; the powers
below are ordinary natural powers, so exponent zero gives one, including
when the base is zero. `Nat.ceil` expresses the nonnegative number of blocks. -/
namespace FiniteGeometricMixingSpec

def positive_power : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S),
    Irreducible P → (∀ i, Aperiodic P i) →
    ∃ m : ℕ, 1 ≤ m ∧ ∀ i j, 0 < power P m i j

def minorization_bounds : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S) (m : ℕ),
    (∀ i j, 0 < power P m i j) →
    0 < blockMinorization P m ∧ blockMinorization P m ≤ 1

def geometric_bound : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S)
    (m : ℕ), 1 ≤ m → ∀ (n : ℕ) (μ ν : ProbabilityLaw S),
    totalVariation (evolve μ P n) (evolve ν P n) ≤
      (1 - blockMinorization P m) ^ (n / m) * totalVariation μ ν

def mass_one_rows : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S) (m : ℕ),
    blockMinorization P m = 1 → ∀ i j,
    realMatrix (power P m) i j = blockCommonMass P m j

def mass_one_stationarity : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S) (m : ℕ),
    blockMinorization P m = 1 → ∀ (μ π : ProbabilityLaw S),
    IsStationary P π → ∀ n : ℕ, m ≤ n → evolve μ P n = π

def mixing_time_bound : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S)
    (m : ℕ), 1 ≤ m → 0 < blockMinorization P m → blockMinorization P m < 1 →
    ∀ (μ π : ProbabilityLaw S), IsStationary P π →
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ n : ℕ,
    m * ⌈Real.log (1 / δ) / (-Real.log (1 - blockMinorization P m))⌉₊ ≤ n →
    totalVariation (evolve μ P n) π ≤ δ

def stationary_exists : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S),
    Irreducible P → ∃ π : ProbabilityLaw S, IsStationary P π

/-- End-to-end finite-chain result: the block and its minorization are
constructed from irreducibility and aperiodicity. -/
def finite_geometric_mixing : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] (P : StochasticMatrix S),
    Irreducible P → (∀ i, Aperiodic P i) →
    ∃ m : ℕ, 1 ≤ m ∧ (∀ i j, 0 < power P m i j) ∧
      0 < blockMinorization P m ∧ blockMinorization P m ≤ 1 ∧
      (∀ (n : ℕ) (μ ν : ProbabilityLaw S),
        totalVariation (evolve μ P n) (evolve ν P n) ≤
          (1 - blockMinorization P m) ^ (n / m) * totalVariation μ ν) ∧
      ∃ π : ProbabilityLaw S, IsStationary P π ∧
        (blockMinorization P m = 1 →
          (∀ i j, realMatrix (power P m) i j = blockCommonMass P m j) ∧
          ∀ (μ : ProbabilityLaw S) (n : ℕ), m ≤ n → evolve μ P n = π) ∧
        (blockMinorization P m < 1 → ∀ (μ : ProbabilityLaw S)
          (δ : ℝ), 0 < δ → δ < 1 → ∀ n : ℕ,
          m * ⌈Real.log (1 / δ) / (-Real.log (1 - blockMinorization P m))⌉₊ ≤ n →
          totalVariation (evolve μ P n) π ≤ δ)

end FiniteGeometricMixingSpec
end
end P207.Markov
