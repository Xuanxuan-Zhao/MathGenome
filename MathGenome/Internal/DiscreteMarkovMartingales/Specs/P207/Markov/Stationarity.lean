import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.DeterministicTransitions

open MeasureTheory
open scoped ENNReal MeasureTheory
universe u v

namespace P207.Markov
noncomputable section

/-- Invariance of the probability row vector under one transition. -/
def IsStationary {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S) : Prop :=
  π.bind P = π

/-- Equality of the probability flows in both directions. -/
def DetailedBalance {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S) : Prop :=
  ∀ i j, π i * P i j = π j * P j i

/-- All finite-dimensional laws, allowing any finite list of times. -/
def ShiftInvariant {S : Type u} [MeasurableSpace S] {Ω : Type v}
    [MeasurableSpace Ω] (X : ℕ → Ω → S) (μ : Measure Ω) : Prop :=
  ∀ (k : ℕ) (t : Fin k → ℕ) (r : ℕ),
    μ.map (fun ω a => X (r + t a) ω) = μ.map (fun ω a => X (t a) ω)

/-- Invariance of consecutive blocks, including the one-coordinate block. -/
def BlockShiftInvariant {S : Type u} [MeasurableSpace S] {Ω : Type v}
    [MeasurableSpace Ω] (X : ℕ → Ω → S) (μ : Measure Ω) : Prop :=
  ∀ (n r : ℕ), μ.map (fun ω (a : Fin (n + 1)) => X (r + a.val) ω) =
    μ.map (fun ω (a : Fin (n + 1)) => X a.val ω)

/-- A stationary canonical chain is reversible when all its finite segments
have the same law read in the opposite order. -/
def IsReversible {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (π : ProbabilityLaw S) : Prop :=
  IsStationary P π ∧ ∀ n : ℕ,
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω a.val) =
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω (n - a.val))

namespace StationaritySpec

def IsStationaryType := {S : Type u} → StochasticMatrix S → ProbabilityLaw S → Prop
def IsStationaryValue : IsStationaryType.{u} := fun {_} P π => π.bind P = π

def DetailedBalanceType := {S : Type u} → StochasticMatrix S → ProbabilityLaw S → Prop
def DetailedBalanceValue : DetailedBalanceType.{u} :=
  fun {_} P π => ∀ i j, π i * P i j = π j * P j i

def ShiftInvariantType := {S : Type u} → [MeasurableSpace S] → {Ω : Type v} →
  [MeasurableSpace Ω] → (ℕ → Ω → S) → Measure Ω → Prop
def ShiftInvariantValue : ShiftInvariantType.{u,v} := fun {_} [_] {_} [_] X μ =>
  ∀ (k : ℕ) (t : Fin k → ℕ) (r : ℕ),
    μ.map (fun ω a => X (r + t a) ω) = μ.map (fun ω a => X (t a) ω)

def BlockShiftInvariantType := ShiftInvariantType.{u,v}
def BlockShiftInvariantValue : BlockShiftInvariantType.{u,v} := fun {_} [_] {_} [_] X μ =>
  ∀ (n r : ℕ), μ.map (fun ω (a : Fin (n + 1)) => X (r + a.val) ω) =
    μ.map (fun ω (a : Fin (n + 1)) => X a.val ω)

def IsReversibleType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → ProbabilityLaw S → Prop
def IsReversibleValue : IsReversibleType.{u} := fun {_} [_] [_] [_] P π =>
  IsStationary P π ∧ ∀ n : ℕ,
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω a.val) =
    (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω (n - a.val))

def stationary_iff_masses : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S),
    IsStationary P π ↔ ∀ j, ∑' i, π i * P i j = π j

def stationary_evolve : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S),
    IsStationary P π → ∀ n, evolve π P n = π

def detailedBalance_stationary : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S),
    DetailedBalance P π → IsStationary P π

def stationary_positive : Prop :=
  ∀ {S : Type u} [Countable S] (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → IsStationary P π → ∀ i, 0 < π i

def stationary_future_law : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (π : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P π X ℱ μ → IsStationary P π → ∀ r,
    μ.map (fun ω n => X (r + n) ω) = pathLaw P π

def stationary_iff_shiftInvariant : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (π : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P π X ℱ μ → (IsStationary P π ↔ ShiftInvariant X μ)

def stationary_iff_blockShiftInvariant : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (π : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P π X ℱ μ → (IsStationary P π ↔ BlockShiftInvariant X μ)
end StationaritySpec
end
end P207.Markov
