import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CompactMapFiniteness
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CoveringPaths
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.LocallyConstant.Basic

/-! Independent finite-degree statements for paper.tex:3459–3486.
The weighted sum uses the actual chart-independent positive multiplicities.
The covering assertion is Mathlib's evenly-covered-neighborhood condition,
applied after deleting branch values and their full inverse image. -/
noncomputable section
open Set

namespace D12Complex.Surfaces
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The chart-independent multiplicity when it exists, and zero otherwise.
For nonconstant holomorphic maps its existence and uniqueness are proved upstream. -/
def localMultiplicity (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) (a : X) : ℕ := by
  classical
  exact if h : ∃ m, HasMultiplicity S T f a m then Classical.choose h else 0

/-- Sum over the whole fibre, with no omission of ramified points.
For the compact maps considered below the indexing type is finite. -/
def fiberMultiplicitySum (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) (b : Y) : ℕ :=
  ∑ᶠ a : {x // f x = b}, localMultiplicity S T f a.val

end D12Complex.Surfaces

namespace Specs.D12Complex.Ch20.FiniteDegree
open _root_.D12Complex.Surfaces
universe u v

def localMultiplicity_type := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] →
  RiemannSurface X → RiemannSurface Y → (X → Y) → X → ℕ

def localMultiplicity_value : localMultiplicity_type := by
  classical
  exact fun S T f a => if h : ∃ m, HasMultiplicity S T f a m then Classical.choose h else 0

def fiberMultiplicitySum_type := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] →
  RiemannSurface X → RiemannSurface Y → (X → Y) → Y → ℕ

def fiberMultiplicitySum_value : fiberMultiplicitySum_type := fun S T f b =>
  ∑ᶠ a : {x // f x = b}, localMultiplicity S T f a.val

def fiberMultiplicitySum_isLocallyConstant_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
    IsLocallyConstant (fiberMultiplicitySum S T f)

/-- Compactness supplies complete inverse images of target neighborhoods,
not just separate local inverse charts at points of a fibre. -/
def compact_holomorphicMap_coveringOn_regularValues_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
    IsCoveringMapOn f (branchValueSet S T f)ᶜ

/-- All finite-degree assertions, including every branch fibre and the
number of sheets of the holomorphic covering on the deleted surfaces.
Holomorphic inverse sheets are expressed in genuine surface coordinates.
The final conjunct gives evenly covered neighborhoods indexed by Fin d. -/
def compact_holomorphicMap_finite_degree_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
    Function.Surjective f ∧ (∀ b, Set.Finite {a | f a = b}) ∧
    (ramificationLocus S T f).Finite ∧ (branchValueSet S T f).Finite ∧
    ∃ d : ℕ, 0 < d ∧ (∀ b, fiberMultiplicitySum S T f b = d) ∧
      IsCoveringMap ((branchValueSet S T f)ᶜ.restrictPreimage f) ∧
      (∀ b ∈ (branchValueSet S T f)ᶜ, Nat.card {a // f a = b} = d) ∧
      (∀ a, f a ∈ (branchValueSet S T f)ᶜ → LocallyBiholomorphicAt S T f a) ∧
      ∀ b : ((branchValueSet S T f)ᶜ : Set Y),
        IsEvenlyCovered ((branchValueSet S T f)ᶜ.restrictPreimage f) b (Fin d)

end Specs.D12Complex.Ch20.FiniteDegree
