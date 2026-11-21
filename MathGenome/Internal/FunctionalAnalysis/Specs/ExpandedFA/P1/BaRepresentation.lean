import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.InvariantAbelianMean
import Mathlib.MeasureTheory.Function.SimpleFunc

/-! The real ba representation, `paper.tex:5384–5412`.
All subsets are allowed. Simple functions use the full power-set sigma algebra,
solely as a convenient finite-range function structure; no countable additivity
is imposed on the set function. -/

noncomputable section
universe u
namespace ExpandedFA.P1.BaRepresentation
open MeasureTheory
open scoped BigOperators
local instance (S : Type u) : MeasurableSpace S := ⊤

abbrev BoundedReal (S : Type u) := AbelianMean.BoundedRealFunction S
abbrev SimpleReal (S : Type u) := @SimpleFunc S ⊤ ℝ

/-- A signed finitely additive set function on the full power set. -/
def IsFinitelyAdditive {S : Type u} (μ : Set S → ℝ) : Prop :=
  μ ∅ = 0 ∧ ∀ A B, Disjoint A B → μ (A ∪ B) = μ A + μ B

/-- All finite disjoint-family variation sums (the empty family is allowed). -/
def variationSums {S : Type u} (μ : Set S → ℝ) : Set ℝ :=
  {r | ∃ P : Finset (Set S), (↑P : Set (Set S)).Pairwise Disjoint ∧ r = ∑ A ∈ P, |μ A|}

/-- Bounded variation is a bound on finite disjoint-family sums. -/
def HasBoundedVariation {S : Type u} (μ : Set S → ℝ) : Prop :=
  BddAbove (variationSums μ)

/-- Total variation on the whole space. -/
def variation {S : Type u} (μ : Set S → ℝ) : ℝ := sSup (variationSums μ)

/-- The usual finite simple-function integral. -/
def simpleIntegral {S : Type u} (μ : Set S → ℝ) (f : SimpleReal S) : ℝ :=
  ∑ r ∈ f.range, r * μ (f ⁻¹' {r})

/-- A finite-range real function viewed as a bounded function, including on an empty set. -/
def simpleToBounded {S : Type u} (f : SimpleReal S) : BoundedReal S := by
  classical
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  exact BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f
    (∑ r ∈ f.range, ‖r‖) (fun x =>
      Finset.single_le_sum (fun r _ => norm_nonneg r) (f.mem_range_self x))

/-- Positivity of a continuous real linear functional. -/
def IsPositive {S : Type u} (L : BoundedReal S →L[ℝ] ℝ) : Prop :=
  ∀ f : BoundedReal S, (∀ x, 0 ≤ f x) → 0 ≤ L f

end ExpandedFA.P1.BaRepresentation

namespace Specs.ExpandedFA.P1.BaRepresentation
open _root_.ExpandedFA.P1.BaRepresentation
open _root_.ExpandedFA.P1
open Filter
open scoped Topology

/-- A continuous functional induces a bounded-variation charge, with exactly its norm. -/
def forwardType : Prop :=
  ∀ (S : Type u) (L : BoundedReal S →L[ℝ] ℝ),
    let μ := fun A : Set S => L (AbelianMean.indicator A)
    IsFinitelyAdditive μ ∧ HasBoundedVariation μ ∧ variation μ = ‖L‖

/-- Every bounded-variation charge has a unique representing functional. The
finite simple integral is extended to all bounded functions. -/
def representationType : Prop :=
  ∀ (S : Type u) (μ : Set S → ℝ), IsFinitelyAdditive μ → HasBoundedVariation μ →
    ∃! L : BoundedReal S →L[ℝ] ℝ,
      (∀ A : Set S, L (AbelianMean.indicator A) = μ A) ∧
      (∀ f : SimpleReal S, L (simpleToBounded f) = simpleIntegral μ f) ∧
      ‖L‖ = variation μ

/-- Positivity is equivalent on the functional and its charge. -/
def positivityType : Prop :=
  ∀ (S : Type u) (L : BoundedReal S →L[ℝ] ℝ),
    IsPositive L ↔ ∀ A : Set S, 0 ≤ L (AbelianMean.indicator A)

/-- Finite simple functions are uniformly dense in all bounded real functions. -/
def densityType : Prop :=
  ∀ (S : Type u) (f : BoundedReal S) (ε : ℝ), 0 < ε →
    ∃ s : SimpleReal S, ‖simpleToBounded s - f‖ < ε

/-- The extension is integration by uniform approximation, for every sequence
of simple approximants, not just a selected approximation. -/
def uniformIntegrationType : Prop :=
  ∀ (S : Type u) (μ : Set S → ℝ), IsFinitelyAdditive μ → HasBoundedVariation μ →
    ∃ L : BoundedReal S →L[ℝ] ℝ,
      (∀ A, L (AbelianMean.indicator A) = μ A) ∧
      ∀ (s : ℕ → SimpleReal S) (f : BoundedReal S),
        Tendsto (fun n => simpleToBounded (s n)) atTop (𝓝 f) →
        Tendsto (fun n => simpleIntegral μ (s n)) atTop (𝓝 (L f))

/-- The identification is linear, injective, and onto exactly the charges of
bounded variation. Its norm assertion is in `forwardType`. -/
def linearIdentificationType : Prop :=
  ∀ (S : Type u), ∃ T : (BoundedReal S →L[ℝ] ℝ) →ₗ[ℝ] (Set S → ℝ),
    Function.Injective T ∧
    (∀ L A, T L A = L (AbelianMean.indicator A)) ∧
    ∀ μ, (∃ L, T L = μ) ↔ IsFinitelyAdditive μ ∧ HasBoundedVariation μ

/-- The invariant probability clause, using the same bounded-function objects. -/
def invariantProbabilityType : Prop :=
  ∀ (G : Type u) [CommGroup G],
    ∃ μ : Set G → ℝ, AbelianMean.IsInvariantProbability μ

end Specs.ExpandedFA.P1.BaRepresentation
