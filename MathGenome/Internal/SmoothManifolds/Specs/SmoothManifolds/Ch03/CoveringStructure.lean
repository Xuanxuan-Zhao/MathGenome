import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.CoveringTopology
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homeomorph.Lemmas

/-! The topology of the total space is fixed throughout.  Local branches are
actual open partial homeomorphisms agreeing with the covering projection.
Smoothness on their open sources and targets is the local-extension convention,
so it also expresses smoothness of the maps between individual open sheets.
No smooth atlas on the total space is an input to the existence theorem. -/
namespace SmoothManifolds.CoveringData
open ModelData AtlasData MapData Set
universe u v w

/-- All charts obtained by pulling back a base chart through a local branch. -/
def liftedAtlas {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (A : Set (ModelChart n a M)) (p : E → M) : Set (ModelChart n a E) :=
  {e | ∃ q : OpenPartialHomeomorph E M, EqOn q p q.source ∧
    ∃ c ∈ A, e = q.trans c}

/-- In a smooth covering, the projection and every local inverse branch are
smooth. Equivalently its restrictions to open sheets are diffeomorphisms.
The inverse is tested only on the branch target, not outside its domain. -/
def IsSmoothCovering {n : ℕ} {a b : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n a E) (S : SmoothManifold n b M) (p : E → M) : Prop :=
  IsCoveringMap p ∧ IsSmoothMap T S p ∧
    ∀ q : OpenPartialHomeomorph E M, EqOn q p q.source →
      ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val q.symm q.target

/-- Smooth coordinate germs along a given parameter map. This allows interval,
orthant and corner parameters without presupposing a manifold structure on them.
For an embedded orthant domain use its inclusion in ambient Euclidean space. -/
def SmoothAlongAt {n k : ℕ} {a : ModelKind} {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n a M) (ι : X → Euclidean k) (f : X → M) (x : X) : Prop :=
  ContinuousAt f x ∧ ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
    LocalCoordinateExtension (⊤ : ℕ∞) ι (fun y => (d (f y)).val) x

/-- The manuscript's extension test stated with agreement on the entire
embedded parameter domain inside an ambient open neighborhood. -/
def ParameterSmoothAt {n k : ℕ} {a : ModelKind} {X : Type u} {M : Type v}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n a M) (ι : X → Euclidean k) (f : X → M) (x : X) : Prop :=
  ContinuousAt f x ∧ ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
    HasLocalContDiffExtensionAt (⊤ : ℕ∞) ι (fun y => (d (f y)).val) x

/-- The usual real coordinate of the closed unit interval. -/
def intervalParameter (t : unitInterval) : Euclidean 1 := fun _ => t.val

end SmoothManifolds.CoveringData

namespace Specs.SmoothManifolds.Ch03.CoveringStructure
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.CoveringData Set
universe u v w

-- Full independent types and values of the new shared definitions.
def liftedAtlasType := {n : ℕ} → {a : ModelKind} → {E : Type u} → {M : Type v} →
  [TopologicalSpace E] → [TopologicalSpace M] →
  Set (ModelChart n a M) → (E → M) → Set (ModelChart n a E)
def liftedAtlasValue : liftedAtlasType := @CoveringData.liftedAtlas

def IsSmoothCoveringType := {n : ℕ} → {a b : ModelKind} → {E : Type u} → {M : Type v} →
  [TopologicalSpace E] → [TopologicalSpace M] →
  SmoothManifold n a E → SmoothManifold n b M → (E → M) → Prop
def IsSmoothCoveringValue : IsSmoothCoveringType := @CoveringData.IsSmoothCovering

def SmoothAlongAtType := {n k : ℕ} → {a : ModelKind} → {X : Type u} → {M : Type v} →
  [TopologicalSpace X] → [TopologicalSpace M] →
  SmoothManifold n a M → (X → Euclidean k) → (X → M) → X → Prop
def SmoothAlongAtValue : SmoothAlongAtType := @CoveringData.SmoothAlongAt

def ParameterSmoothAtType := {n k : ℕ} → {a : ModelKind} → {X : Type u} → {M : Type v} →
  [TopologicalSpace X] → [TopologicalSpace M] →
  SmoothManifold n a M → (X → Euclidean k) → (X → M) → X → Prop
def ParameterSmoothAtValue : ParameterSmoothAtType := @CoveringData.ParameterSmoothAt

def intervalParameterType := unitInterval → Euclidean 1
def intervalParameterValue : intervalParameterType := CoveringData.intervalParameter

/-- Existence, a specified canonical maximal atlas, actual uniqueness of smooth
structures on the same space, and the intrinsic boundary identity. The disjunction
includes the connected case and its empty extension through PreconnectedSpace. -/
def exists_canonical_smooth_coveringType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : E → M) (_hp : IsCoveringMap p),
    ((∀ y : M, (p ⁻¹' {y}).Countable) ∨ PreconnectedSpace E) →
    ∃ T : SmoothManifold n a E,
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (liftedAtlas S.smoothStructure.val p) ∧
      IsSmoothCovering T S p ∧
      intrinsicBoundary T = p ⁻¹' intrinsicBoundary S ∧
      ∀ T' : SmoothManifold n a E, IsSmoothCovering T' S p →
        T'.smoothStructure = T.smoothStructure

/-- Every continuous manifold lift is smooth, with no assumption on the
source dimension, boundary, nonemptiness, or connectedness. -/
def smooth_liftType : Prop :=
  ∀ {n k : ℕ} {a b c : ModelKind} {E : Type u} {M : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n a E) (S : SmoothManifold n c M)
    (R : SmoothManifold k b X) (p : E → M), IsSmoothCovering T S p →
    ∀ (f : X → M) (g : X → E), IsSmoothMap R S f → Continuous g →
      p ∘ g = f → IsSmoothMap R T g

/-- The same argument with arbitrary local Euclidean parameters supplies the
boundary/corner parameter version used by path and homotopy lifting. -/
def smooth_lift_alongAtType : Prop :=
  ∀ {n k : ℕ} {a : ModelKind} {E : Type u} {M : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M), IsSmoothCovering T S p →
    ∀ (ι : X → Euclidean k) (f : X → M) (g : X → E) (x : X),
      SmoothAlongAt S ι f x → ContinuousAt g x → p ∘ g = f →
        SmoothAlongAt T ι g x

/-- Uniqueness is equality of maximal atlases, independent of choices of a
covering chart cover or of topological-manifold records. -/
def smooth_covering_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T T' : SmoothManifold n a E) (S : SmoothManifold n a M) (p : E → M),
    IsSmoothCovering T S p → IsSmoothCovering T' S p →
      T.smoothStructure = T'.smoothStructure

/-- In dimension zero both intrinsic boundaries are empty. -/
def zero_boundaryType : Prop :=
  ∀ {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold 0 a E) (S : SmoothManifold 0 a M),
    intrinsicBoundary T = ∅ ∧ intrinsicBoundary S = ∅

/-- Raw ambient local extensions, including on orthant/corner parameter domains.
An inducing coordinate map gives exactly their subspace topology. -/
def smooth_parameter_liftType : Prop :=
  ∀ {n k : ℕ} {a : ModelKind} {E : Type u} {M : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M), IsSmoothCovering T S p →
    ∀ (ι : X → Euclidean k), Topology.IsInducing ι →
    ∀ (f : X → M) (g : X → E) (x : X),
      ParameterSmoothAt S ι f x → ContinuousAt g x → p ∘ g = f →
        ParameterSmoothAt T ι g x

/-- Application to the actual continuous path supplied by the topological
path lifting theorem, including both endpoints of the closed interval. -/
def smooth_liftPathType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (γ : C(unitInterval, M)) (e : E) (h₀ : γ 0 = p e),
    (∀ t, ParameterSmoothAt S intervalParameter γ t) →
    ∀ t, ParameterSmoothAt T intervalParameter (hp.1.liftPath γ e h₀) t

/-- Application to the actual topological homotopy lift. The parameter type
is arbitrary: this applies in every boundary or corner parameter chart. -/
def smooth_liftHomotopyType : Prop :=
  ∀ {n k : ℕ} {a : ModelKind} {E : Type u} {M : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (H : C(unitInterval × X, M)) (g₀ : C(X, E))
    (h₀ : ∀ x, H (0, x) = p (g₀ x)) (ι : unitInterval × X → Euclidean k),
    (∀ z, SmoothAlongAt S ι H z) →
    ∀ z, SmoothAlongAt T ι (hp.1.liftHomotopy H g₀ h₀) z

/-- The raw ambient-extension version for embedded homotopy parameters, such
as a closed square, a time interval times an orthant, and their subsets. -/
def smooth_parameter_liftHomotopyType : Prop :=
  ∀ {n k : ℕ} {a : ModelKind} {E : Type u} {M : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M)
    (p : E → M) (hp : IsSmoothCovering T S p)
    (H : C(unitInterval × X, M)) (g₀ : C(X, E))
    (h₀ : ∀ x, H (0, x) = p (g₀ x)) (ι : unitInterval × X → Euclidean k),
    Topology.IsInducing ι → (∀ z, ParameterSmoothAt S ι H z) →
    ∀ z, ParameterSmoothAt T ι (hp.1.liftHomotopy H g₀ h₀) z

/-- Conditional on topological existence: no universal-cover existence theorem
is being postulated. Simple connectedness supplies the connected alternative. -/
def simplyConnected_covering_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M] [SimplyConnectedSpace E]
    (S : SmoothManifold n a M) (p : E → M), IsCoveringMap p →
    ∃ T : SmoothManifold n a E, IsSmoothCovering T S p ∧
      intrinsicBoundary T = p ⁻¹' intrinsicBoundary S ∧
      ∀ T' : SmoothManifold n a E, IsSmoothCovering T' S p →
        T'.smoothStructure = T.smoothStructure

/-- Each sheet restriction and its inverse are smooth on their open domains. -/
def smooth_branchType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M) (p : E → M),
    IsSmoothCovering T S p → ∀ q : OpenPartialHomeomorph E M, EqOn q p q.source →
      ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val q q.source ∧
      ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val q.symm q.target

/-- Empty coverings have the empty maximal atlas. -/
def empty_atlasType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} [TopologicalSpace E] [IsEmpty E]
    (T : SmoothManifold n a E), T.smoothStructure.val = ∅

/-- An actual diffeomorphism on each open sheet, with both underlying functions
fixed by the original covering branch and no change of the given topology. -/
def exists_sheet_diffeomorphType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n a E) (S : SmoothManifold n a M) (p : E → M),
    IsSmoothCovering T S p → ∀ q : OpenPartialHomeomorph E M, EqOn q p q.source →
    ∃ D : Diffeomorph (openSubsetAtlas T.smoothStructure.val q.source q.open_source)
      (openSubsetAtlas S.smoothStructure.val q.target q.open_target),
      D.toEquiv = q.toHomeomorphSourceTarget.toEquiv

/-- If different permitted model kinds are used, uniqueness means smooth
compatibility on the same space. For a fixed model kind the theorem above gives
literal equality of maximal atlases. -/
def smooth_covering_compatibleType : Prop :=
  ∀ {n : ℕ} {a b c : ModelKind} {E : Type u} {M : Type v}
    [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n a E) (T' : SmoothManifold n b E)
    (S : SmoothManifold n c M) (p : E → M),
    IsSmoothCovering T S p → IsSmoothCovering T' S p →
      IsSmoothMap T T' id ∧ IsSmoothMap T' T id

end Specs.SmoothManifolds.Ch03.CoveringStructure
