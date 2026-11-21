import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences

/-!
Independent specification for the general metric-space portion of
K03.03.compact_interval (paper.tex:529–540).

`IsCompact univ` is connected explicitly to finite subcovers below.
Sequential compactness quantifies over every sequence and requires a strictly
increasing map of indices and a limit in the same space. Index zero denotes
the first term. There is no nonemptiness or completeness assumption.
For a metric subspace, instantiate X with its subtype and induced metric;
all balls and open sets then have precisely their relative meanings.
The scalar closed-and-bounded assertions are allocated to CompactInterval.
-/
namespace Specs.SingleVariableAnalysis.Ch03.MetricCompactness

open scoped Topology
universe u v

/-- The finite-open-subcover characterization, including empty covers of
empty spaces. The index universe u suffices for all families of open subsets
of X, since these can always be indexed by a subtype of Set X. -/
def metricCompactIffFiniteSubcover : Prop :=
  ∀ {X : Type u} [MetricSpace X],
    IsCompact (Set.univ : Set X) ↔
      ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) →
        (∀ x, ∃ i, x ∈ U i) →
        ∃ t : Finset ι, ∀ x, ∃ i ∈ t, x ∈ U i

/-- The metric compactness equivalence with the full subsequence property. -/
def metricCompactIffSequentiallyCompact : Prop :=
  ∀ {X : Type u} [MetricSpace X],
    IsCompact (Set.univ : Set X) ↔
      ∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x)

/-- Sequential compactness gives an internal finite open ε-net for each ε>0. -/
def metricSequentiallyCompactFiniteNet : Prop :=
  ∀ {X : Type u} [MetricSpace X],
    (∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x)) →
    ∀ ε : ℝ, 0 < ε → ∃ t : Finset X,
      ∀ x : X, ∃ y ∈ t, dist x y < ε

/-- Every open cover of a sequentially compact metric space has a single
positive radius such that each ball of that radius lies in one member. -/
def metricSequentiallyCompactLebesgueNumber : Prop :=
  ∀ {X : Type u} [MetricSpace X],
    (∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x)) →
    ∀ {ι : Type v} (U : ι → Set X), (∀ i, IsOpen (U i)) →
      (∀ x, ∃ i, x ∈ U i) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∃ i, Metric.ball x δ ⊆ U i

/-- The finite-net and Lebesgue-number properties used in the converse
really give a finite subcover. No nonempty space or index type is needed. -/
def metricFiniteSubcoverOfNetLebesgue : Prop :=
  ∀ {X : Type u} [MetricSpace X],
    (∀ ε : ℝ, 0 < ε → ∃ t : Finset X,
      ∀ x : X, ∃ y ∈ t, dist x y < ε) →
    ∀ {ι : Type v} (U : ι → Set X),
      (∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∃ i, Metric.ball x δ ⊆ U i) →
      ∃ t : Finset ι, ∀ x : X, ∃ i ∈ t, x ∈ U i

/-- The empty metric space is compact and has the subsequence property
vacuously; in particular no nonemptiness is hidden in the equivalence. -/
def metricEmptyCompactness : Prop :=
  ∀ {X : Type u} [MetricSpace X] [IsEmpty X],
    IsCompact (Set.univ : Set X) ∧
      (∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x))

end Specs.SingleVariableAnalysis.Ch03.MetricCompactness
