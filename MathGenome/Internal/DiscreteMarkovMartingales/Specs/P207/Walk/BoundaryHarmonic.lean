import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.ReversibleDirichletForm
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.HittingProbability
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

open MeasureTheory
open scoped BigOperators MeasureTheory Classical

universe u
namespace P207.Markov
noncomputable section

/-- Extend the prescribed data only to evaluate a full stopped process.
On a finite entrance the state belongs to the boundary. -/
def boundaryExtension {S : Type u} (B : Set S) (g : B → ℝ) (x : S) : ℝ :=
  if hx : x ∈ B then g ⟨x, hx⟩ else 0

/-- The payoff at first entrance, with an explicit real value at infinity. -/
def boundaryPayoff {S : Type u} (B : Set S) (g : B → ℝ) (c : ℝ) :
    (ℕ → S) → ℝ :=
  P207.fullStoppedValue (fun n ω => boundaryExtension B g (ω n))
    (hittingTime B) (fun _ => c)

/-- The proposed solution is the expectation under the actual canonical chain. -/
def boundaryHarmonic {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (B : Set S)
    (g : B → ℝ) (x : S) : ℝ :=
  stateExpectation P x (boundaryPayoff B g 0)

/-- Boundary values and the ordinary real row action in the interior. -/
def IsBoundaryHarmonic {S : Type u} [Fintype S] (P : StochasticMatrix S)
    (B : Set S) (g : B → ℝ) (h : S → ℝ) : Prop :=
  (∀ x : B, h x = g x) ∧
    ∀ x, x ∉ B → (∑ y, realMatrix P x y * h y) = h x

namespace BoundaryHarmonicSpec

def boundaryExtensionType := {S : Type u} → (B : Set S) → (B → ℝ) → S → ℝ
def boundaryExtensionValue : boundaryExtensionType.{u} := @boundaryExtension

def boundaryPayoffType := {S : Type u} → (B : Set S) → (B → ℝ) → ℝ → (ℕ → S) → ℝ
def boundaryPayoffValue : boundaryPayoffType.{u} := @boundaryPayoff

def boundaryHarmonicType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → (B : Set S) → (B → ℝ) → S → ℝ
def boundaryHarmonicValue : boundaryHarmonicType.{u} := @boundaryHarmonic

def IsBoundaryHarmonicType := {S : Type u} → [Fintype S] → StochasticMatrix S →
  (B : Set S) → (B → ℝ) → (S → ℝ) → Prop
def IsBoundaryHarmonicValue : IsBoundaryHarmonicType.{u} := @IsBoundaryHarmonic

/-- Finite entrance is proved, rather than supplied as a certificate. -/
def hittingTime_finite_ae : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S), Irreducible P →
    ∀ (B : Set S), B.Nonempty → ∀ x,
      ∀ᵐ ω ∂statePathLaw P x, hittingTime B ω < ⊤

/-- This bridge identifies the stopped process with the prescribed boundary data. -/
def boundaryPayoff_at_hit : Prop :=
  ∀ {S : Type u} (B : Set S) (g : B → ℝ) (c : ℝ) (ω : ℕ → S) (n : ℕ),
    hittingTime B ω = n →
      ∃ hb : ω n ∈ B, boundaryPayoff B g c ω = g ⟨ω n, hb⟩

/-- The expectation in the representation is an integral of an integrable payoff. -/
def integrable_boundaryPayoff : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (B : Set S)
    (g : B → ℝ) (c : ℝ) (x : S),
      Integrable (boundaryPayoff B g c) (statePathLaw P x)

/-- All infinity assignments give the same canonical expectation. -/
def boundary_representation : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S), Irreducible P →
    ∀ (B : Set S), B.Nonempty → ∀ (g : B → ℝ) (c : ℝ) (x : S),
      boundaryHarmonic P B g x = stateExpectation P x (boundaryPayoff B g c)

/-- Existence and uniqueness, including the case with empty interior. -/
def boundary_harmonic_unique : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : ∀ x, 0 < π x), Irreducible P → IsReversible P π →
    ∀ (B : Set S), B.Nonempty → ∀ (g : B → ℝ),
      IsBoundaryHarmonic P B g (boundaryHarmonic P B g) ∧
      ∀ f, IsBoundaryHarmonic P B g f → f = boundaryHarmonic P B g

/-- Full boundary: entrance occurs at time zero on every path. -/
def hittingTime_univ_zero : Prop :=
  ∀ {S : Type u} (ω : ℕ → S), hittingTime Set.univ ω = 0

end BoundaryHarmonicSpec
end
end P207.Markov
