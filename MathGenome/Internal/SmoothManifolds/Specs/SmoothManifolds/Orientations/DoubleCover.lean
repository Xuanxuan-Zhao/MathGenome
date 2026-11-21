import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.ProductsAndSigns
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.CoveringStructure
import Mathlib.Topology.Connected.Clopen

/-! Independent objects and original (unconditional) obligations for the covering
clauses of M09.02, paper.tex 1726--1736. The total space consists of actual
intrinsic determinant rays. Its topology is the final topology for all local
continuous ray sections on open subsets. This is the usual sheet topology;
no covering, separation, countability, smoothness or orientability certificate is
part of the construction data. Dimension zero and both model kinds are retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical Topology

namespace SmoothManifolds.OrientationCoverData
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  OrientationData OrientationProductData CoveringData Set
universe u

abbrev Space {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := (p : M) × DeterminantRay S p

/-- Continuity of a local ray field, tested on every overlap in determinant
coordinates, exactly as for the shared global orientation definition. -/
structure LocalOrientation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) where
  domain : Set M
  isOpen_domain : IsOpen domain
  ray : (p : domain) → DeterminantRay S p.val
  continuous : ∀ (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val),
    IsLocallyConstant (fun p : ↥(domain ∩ c.source) =>
      Module.Ray.map (determinantCoordinates K c hc ⟨p.val, p.property.2⟩)
        (ray ⟨p.val, p.property.1⟩))

def LocalOrientation.lift {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (L : LocalOrientation S) : L.domain → Space S :=
  fun p => ⟨p.val, L.ray p⟩

/-- This fixes the topology before any manifold structure or covering proof. -/
@[instance_reducible] def topology {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : TopologicalSpace (Space S) :=
  ⨆ L : LocalOrientation S, TopologicalSpace.coinduced L.lift inferInstance

instance instTopology {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : TopologicalSpace (Space S) := topology S

def projection {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : Space S → M := fun z => z.1

def deck {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : Space S → Space S := fun z => ⟨z.1, -z.2⟩

def sectionOf {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o : Orientation S) : M → Space S :=
  fun p => ⟨p, o.val p⟩

/-- Pull back the ray belonging to the point of the cover by the actual dπ.
Quantifying over every differential identification makes canonicity explicit. -/
def IsTautologicalOrientation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (T : SmoothManifold n a (Space S)) (o : Orientation T) : Prop :=
  ∀ E : ∀ z : Space S, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1,
    (∀ z, IsDifferential T S (projection S) z (E z).toLinearMap) →
    ∀ z, Module.Ray.map (determinantMap n (E z)) (o.val z) = z.2

end SmoothManifolds.OrientationCoverData

namespace Specs.SmoothManifolds.Orientations.DoubleCover
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.OrientationProductData
  _root_.SmoothManifolds.OrientationCoverData _root_.SmoothManifolds.CoveringData
  _root_.SmoothManifolds.BoundaryData Set
universe u

/-- Exactly two orientations in every fiber of the actual projection, including
in dimension zero. The topology of the cover is not a hypothesis. -/
def two_sheetsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M), Nonempty ((projection S ⁻¹' {p}) ≃ Bool)

/-- The topology already defined above is the smooth two-sheeted covering
space. This also specifies its unique canonical smooth atlas and boundary. -/
def constructionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M),
    T2Space (Space S) ∧ SecondCountableTopology (Space S) ∧
    ∃ T : SmoothManifold n a (Space S),
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (liftedAtlas S.smoothStructure.val (projection S)) ∧
      IsSmoothCovering T S (projection S) ∧
      IsLocalDiffeomorphism T S (projection S) ∧
      intrinsicBoundary T = projection S ⁻¹' intrinsicBoundary S ∧
      ∀ T' : SmoothManifold n a (Space S), IsSmoothCovering T' S (projection S) →
        T'.smoothStructure = T.smoothStructure

/-- The canonical orientation is the unique one whose transport by dπ is the
ray at the point of the total space. No orientability hypothesis on M. -/
def canonical_orientationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n a (Space S)),
    IsSmoothCovering T S (projection S) →
    ∃! o : Orientation T, IsTautologicalOrientation T o

/-- The actual sheet exchange is a smooth fixed-point-free deck involution,
and reverses the canonical orientation under its actual differential. -/
def deckType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n a (Space S)),
    IsSmoothCovering T S (projection S) →
    Function.Involutive (deck S) ∧ (∀ z, deck S z ≠ z) ∧
    projection S ∘ deck S = projection S ∧ IsSmoothMap T T (deck S) ∧
    ∀ (o : Orientation T), IsTautologicalOrientation T o →
      ∀ E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z),
        (∀ z, IsDifferential T T (deck S) z (E z).toLinearMap) →
        ∀ z, Module.Ray.map (determinantMap n (E z)) (o.val z) = -o.val (deck S z)

/-- An orientation gives the actual smooth section, and it and its negative
are the two disjoint open copies. The displayed homeomorphism records both
copies, rather than only asserting abstract disconnectedness. -/
def oriented_decompositionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n a (Space S)),
    IsSmoothCovering T S (projection S) → ∀ o : Orientation S,
    IsSmoothMap S T (sectionOf o) ∧
    IsSmoothMap S T (deck S ∘ sectionOf o) ∧
    projection S ∘ sectionOf o = id ∧
    ∃ h : (M ⊕ M) ≃ₜ Space S,
      (∀ p, h (Sum.inl p) = sectionOf o p) ∧
      (∀ p, h (Sum.inr p) = deck S (sectionOf o p)) ∧
      IsOpen (range (sectionOf o)) ∧ IsOpen (range (deck S ∘ sectionOf o)) ∧
      Disjoint (range (sectionOf o)) (range (deck S ∘ sectionOf o))

/-- Both directions, with the essential connected and nonempty hypothesis.
`ConnectedSpace` includes nonemptiness. Components are actual topological
connected components, not a selected labeling of fibers. -/
def connected_classificationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M),
    (Nonempty (ConnectedComponents (Space S) ≃ Bool) ↔ Nonempty (Orientation S)) ∧
    (ConnectedSpace (Space S) ↔ ¬ Nonempty (Orientation S))

end Specs.SmoothManifolds.Orientations.DoubleCover
