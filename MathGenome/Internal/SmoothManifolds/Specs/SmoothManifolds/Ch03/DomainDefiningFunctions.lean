import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.RegularDomains
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.SmoothExhaustion

/-! Independent statements for the global defining-function assertion in
M03.06(b). The real target is fixed by its standard coordinate, and regularity
uses the existing full tangent differential, including in dimension zero. -/
namespace SmoothManifolds.DomainDefiningData
open ModelData AtlasData MapData MapClassData RegularDomainData Set
universe u

/-- A defining function with the prescribed sign, zero set, and regularity. -/
def IsDefiningFunction {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ)
    (d : Set M) (f : M → ℝ) : Prop :=
  IsSmoothMap T R f ∧ d = sublevel f ∧ frontier d = f ⁻¹' {0} ∧
    IsRegularValue T R f 0

end SmoothManifolds.DomainDefiningData

namespace Specs.SmoothManifolds.Ch03.DomainDefiningFunctions
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.RegularDomainData _root_.SmoothManifolds.DomainDefiningData
open Set
universe u

def IsDefiningFunctionType :=
  {m : ℕ} → {b : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    SmoothManifold m b M → SmoothManifold 1 .euclidean ℝ → Set M → (M → ℝ) → Prop
def IsDefiningFunctionValue : IsDefiningFunctionType := @DomainDefiningData.IsDefiningFunction

/-- Source's boundary-free degenerate cases need no normal-coordinate data. -/
def exists_defining_function_of_frontier_emptyType : Prop :=
  ∀ {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ),
    HasStandardRealChart R → ∀ d : Set M, frontier d = ∅ →
      ∃ f : M → ℝ, IsDefiningFunction T R d f

/-- Full source obligation: no connectedness, nonemptiness, positive dimension,
or compactness of the ambient manifold is required. -/
def exists_defining_functionType : Prop :=
  ∀ {m : ℕ} {a b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ)
    (d : Set M) (S : SmoothManifold m a d),
    intrinsicBoundary T = ∅ → HasStandardRealChart R → IsRegularDomain T d S →
    ∃ f : M → ℝ, IsDefiningFunction T R d f ∧
      Subtype.val '' manifoldInterior S = {x | f x < 0} ∧
      Subtype.val '' intrinsicBoundary S = f ⁻¹' {0} ∧
      interior d = {x | f x < 0} ∧
      (∀ x ∉ d, 0 < f x) ∧
      (IsCompact d → ∀ c : ℝ, IsCompact {x | f x ≤ c})

/-- The compact strengthening preserves the germ at every point of the domain.
Its premise is a previously constructed defining function, not an added
hypothesis in the full existence theorem above. -/
def compactify_defining_functionType : Prop :=
  ∀ {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ)
    (d : Set M) (f : M → ℝ),
    HasStandardRealChart R → IsCompact d → IsDefiningFunction T R d f →
    ∃ g : M → ℝ, IsDefiningFunction T R d g ∧
      (∀ p ∈ d, g =ᶠ[nhds p] f) ∧
      ∀ c : ℝ, IsCompact {x | g x ≤ c}

/-- Assembly isolates the sole remaining construction from the already proved
compactification and the upstream intrinsic/ambient topology comparison. -/
def assemble_defining_functionType : Prop :=
  ∀ {m : ℕ} {a b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ)
    (d : Set M) (S : SmoothManifold m a d),
    intrinsicBoundary T = ∅ → HasStandardRealChart R → IsRegularDomain T d S →
    (∃ f : M → ℝ, IsDefiningFunction T R d f) →
    ∃ f : M → ℝ, IsDefiningFunction T R d f ∧
      Subtype.val '' manifoldInterior S = {x | f x < 0} ∧
      Subtype.val '' intrinsicBoundary S = f ⁻¹' {0} ∧
      interior d = {x | f x < 0} ∧
      (∀ x ∉ d, 0 < f x) ∧
      (IsCompact d → ∀ c : ℝ, IsCompact {x | f x ≤ c})

end Specs.SmoothManifolds.Ch03.DomainDefiningFunctions
