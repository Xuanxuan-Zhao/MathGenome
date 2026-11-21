import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.FundamentalGroupoid
import Mathlib.Topology.Connected.PathConnected

/-! The two-open-set group pushout, paper.tex §1.3, Theorem 1.5.
All groups use the paper's first-path-first convention, via `Pi1`.
The universal property is stated in the category of groups in the same universe.
No injectivity of the intersection homomorphisms is assumed. -/
namespace P202Specs.Topology.VanKampen

universe u
noncomputable section
variable {X : Type u} [TopologicalSpace X]

/-- Inclusion of one subspace in another, preserving the specified basepoint. -/
def subspaceMap {S T : Set X} (h : S ⊆ T) (x : X) (hx : x ∈ S) :
    PointedMap S T ⟨x, hx⟩ ⟨x, h hx⟩ where
  map := ⟨fun y => ⟨y.val, h y.property⟩, continuous_subtype_val.subtype_mk _⟩
  point := rfl

/-- Inclusion of a based subspace into the ambient space. -/
def ambientMap (S : Set X) (x : X) (hx : x ∈ S) : PointedMap S X ⟨x, hx⟩ x where
  map := ⟨Subtype.val, continuous_subtype_val⟩
  point := rfl

def leftMap (U V : Set X) (x : X) (hx : x ∈ U ∩ V) :
    Pi1 ↥(U ∩ V) ⟨x, hx⟩ →* Pi1 U ⟨x, hx.1⟩ :=
  (subspaceMap Set.inter_subset_left x hx).induced

def rightMap (U V : Set X) (x : X) (hx : x ∈ U ∩ V) :
    Pi1 ↥(U ∩ V) ⟨x, hx⟩ →* Pi1 V ⟨x, hx.2⟩ :=
  (subspaceMap Set.inter_subset_right x hx).induced

/-- Every compatible pair of homomorphisms has a unique extension. -/
def UniversalProperty (U V : Set X) (x : X) (hx : x ∈ U ∩ V) : Prop :=
  ∀ (G : Type u) [Group G]
    (f : Pi1 U ⟨x, hx.1⟩ →* G) (g : Pi1 V ⟨x, hx.2⟩ →* G),
    f.comp (leftMap U V x hx) = g.comp (rightMap U V x hx) →
    ∃! h : Pi1 X x →* G,
      h.comp (ambientMap U x hx.1).induced = f ∧
      h.comp (ambientMap V x hx.2).induced = g

namespace Expected

/-- The inclusion square commutes, without any open-cover assumptions. -/
def commutativity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (U V : Set X) (x : X) (hx : x ∈ U ∩ V),
    (ambientMap U x hx.1).induced.comp (leftMap U V x hx) =
      (ambientMap V x hx.2).induced.comp (rightMap U V x hx)

/-- The complete two-open-set theorem, including the pushout universal property. -/
def vanKampen : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (U V : Set X),
    IsOpen U → IsOpen V → U ∪ V = Set.univ →
    IsPathConnected U → IsPathConnected V → IsPathConnected (U ∩ V) →
    ∀ (x : X) (hx : x ∈ U ∩ V),
      (ambientMap U x hx.1).induced.comp (leftMap U V x hx) =
        (ambientMap V x hx.2).induced.comp (rightMap U V x hx) ∧
      UniversalProperty U V x hx

end Expected
end
end P202Specs.Topology.VanKampen
