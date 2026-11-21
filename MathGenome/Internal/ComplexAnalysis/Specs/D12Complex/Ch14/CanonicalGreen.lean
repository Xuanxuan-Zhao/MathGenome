import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.RegularGreen
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarnackConvergence

/-! The existence and leastness portion of paper.tex:2681–2691.
No boundary values on an arbitrary domain are prescribed. Total representatives
are compared only on the punctured domain. -/
noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex

/-- Positivity, harmonicity off the pole, and the normalized logarithmic pole. -/
def IsPositiveGreen (Ω : Set ℂ) (a : ℂ) (g : ℂ → ℝ) : Prop :=
  HarmonicOn (Ω \ {a}) g ∧ HasNormalizedLogPole Ω a g ∧
    ∀ z ∈ Ω \ {a}, 0 < g z

/-- Leastness among all positive functions with the same normalized pole. -/
def IsLeastPositiveGreen (Ω : Set ℂ) (a : ℂ) (g : ℂ → ℝ) : Prop :=
  IsPositiveGreen Ω a g ∧ ∀ v : ℂ → ℝ, IsPositiveGreen Ω a v →
    ∀ z ∈ Ω \ {a}, g z ≤ v z

end D12Complex

namespace Specs.D12Complex.Ch14.CanonicalGreen
open _root_.D12Complex _root_.D12Complex.CircularExhaustion

def IsPositiveGreen_type := Set ℂ → ℂ → (ℂ → ℝ) → Prop
def IsPositiveGreen_value : IsPositiveGreen_type := fun Ω a g =>
  HarmonicOn (Ω \ {a}) g ∧ HasNormalizedLogPole Ω a g ∧
    ∀ z ∈ Ω \ {a}, 0 < g z

def IsLeastPositiveGreen_type := Set ℂ → ℂ → (ℂ → ℝ) → Prop
def IsLeastPositiveGreen_value : IsLeastPositiveGreen_type := fun Ω a g =>
  IsPositiveGreen Ω a g ∧ ∀ v : ℂ → ℝ, IsPositiveGreen Ω a v →
    ∀ z ∈ Ω \ {a}, g z ≤ v z

def canonicalGreen_type := Set ℂ → ℂ → ℂ → ℝ
/-- Choice of a least Green representative when one exists; zero otherwise.
Existence is a separate theorem, never an assumed certificate. -/
def canonicalGreen_value : canonicalGreen_type := by
  classical
  exact fun Ω a => if h : ∃ g : ℂ → ℝ, IsLeastPositiveGreen Ω a g then Classical.choose h else fun _ => 0

def canonical_green_exists_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω → a ∈ Ω →
    ∃ g : ℂ → ℝ, IsLeastPositiveGreen Ω a g

def canonical_green_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω → a ∈ Ω →
    IsLeastPositiveGreen Ω a (canonicalGreen_value Ω a)

def least_green_unique_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ) (g h : ℂ → ℝ),
    IsLeastPositiveGreen Ω a g → IsLeastPositiveGreen Ω a h → EqOn g h (Ω \ {a})

def circular_exhaustion_containing_pole_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → a ∈ Ω →
    ∃ (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
      IsCircularExhaustion Ω s r ∧ ∀ j, a ∈ diskUnion (s j) (r j)

/-- Every such exhaustion gives the same finite, locally uniform limit.
The monotonicity assertion applies to the entire sequence of total regular
representatives, hence in particular on every common punctured stage. -/
def exhaustion_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω → a ∈ Ω →
    ∀ (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ), IsCircularExhaustion Ω s r →
    (∀ j, a ∈ diskUnion (s j) (r j)) →
    (∀ z : ℂ, Monotone (fun j => RegularGreen.regularGreen_value
      (diskUnion (s j) (r j)) a z)) ∧
    HarnackConvergence.ConvergesOnCompacts (Ω \ {a})
      (fun j => RegularGreen.regularGreen_value (diskUnion (s j) (r j)) a)
      (canonicalGreen_value Ω a)

end Specs.D12Complex.Ch14.CanonicalGreen
