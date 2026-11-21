import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Topology.Compactness.Compact

/-! The finiteness stage of paper.tex:3459–3471. Compactness is assumed
only for the source; the target has precisely the Riemann-surface structure. -/
noncomputable section
open Set

namespace D12Complex.Surfaces
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Points whose (unique positive) local multiplicity exceeds one. -/
def ramificationLocus (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) : Set X := {a | ∃ m : ℕ, HasMultiplicity S T f a m ∧ 1 < m}

/-- Branch values are images of ramification points. -/
def branchValueSet (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) : Set Y := f '' ramificationLocus S T f
end D12Complex.Surfaces

namespace Specs.D12Complex.Ch20.CompactMapFiniteness
open _root_.D12Complex.Surfaces
universe u v

def ramificationLocus_type := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] →
  RiemannSurface X → RiemannSurface Y → (X → Y) → Set X
def ramificationLocus_value : ramificationLocus_type := fun S T f =>
  {a | ∃ m : ℕ, HasMultiplicity S T f a m ∧ 1 < m}

def branchValueSet_type := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] →
  RiemannSurface X → RiemannSurface Y → (X → Y) → Set Y
def branchValueSet_value : branchValueSet_type := fun S T f =>
  f '' ramificationLocus S T f

def holomorphicMap_isOpenMap_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) → IsOpenMap f

def compact_holomorphicMap_surjective_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) → Function.Surjective f

def compact_holomorphicMap_finite_fibers_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
      ∀ b : Y, Set.Finite {a | f a = b}

def compact_holomorphicMap_finite_ramification_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
      (ramificationLocus S T f).Finite

def compact_holomorphicMap_finite_branchValues_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
      (branchValueSet S T f).Finite

end Specs.D12Complex.Ch20.CompactMapFiniteness
