import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.ComponentsAndPaths
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.OrderedConnectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.Pasting
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import Mathlib.Tactic.NormNum

/-! Components and paths in arbitrary topological spaces. The source allows
empty connected and path connected spaces. `UnitPath` is the standard path
structure on the real closed unit interval, with both endpoints specified.
Concatenation continuity below is proved using the accepted finite closed
pasting theorem on the two closed half-intervals. -/

open Set
universe u v

namespace D10Topology.Ch06

variable {X : Type u} [TopologicalSpace X]

def Component (x : X) : Set X := ComponentsPathsData.Component x
abbrev UnitPath (x y : X) := ComponentsPathsData.UnitPath x y
def PathConnected (X : Type u) [TopologicalSpace X] : Prop :=
  ComponentsPathsData.PathConnected X
def PathConnectedSubset (A : Set X) : Prop := ComponentsPathsData.PathConnectedSubset A
def PathComponent (x : X) : Set X := ComponentsPathsData.PathComponent x
noncomputable def concatenationFunction {x y z : X}
    (p : UnitPath x y) (q : UnitPath y z) : unitInterval → X :=
  ComponentsPathsData.concatenationFunction p q

theorem component_eq_mathlib (x : X) : Component x = connectedComponent x := by
  unfold Component ComponentsPathsData.Component connectedComponent
  congr 1
  ext A
  exact and_congr_left (fun _ => connectedSubset_iff_isPreconnected A)

theorem component_self (x : X) : x ∈ Component x := by
  rw [component_eq_mathlib]
  exact mem_connectedComponent

theorem component_connected (x : X) : ConnectedSubset (Component x) := by
  rw [component_eq_mathlib, connectedSubset_iff_isPreconnected]
  exact isPreconnected_connectedComponent

theorem connectedSubset_subset_component (A : Set X) (x : X)
    (hx : x ∈ A) (hA : ConnectedSubset A) : A ⊆ Component x := by
  rw [component_eq_mathlib]
  exact ((connectedSubset_iff_isPreconnected A).mp hA).subset_connectedComponent hx

theorem component_iff_maximal (A : Set X) :
    (∃ x : X, Component x = A) ↔
      A.Nonempty ∧ ConnectedSubset A ∧
        ∀ B : Set X, ConnectedSubset B → A ⊆ B → B ⊆ A := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, component_self x⟩, component_connected x,
      fun B hB hAB => connectedSubset_subset_component B x (hAB (component_self x)) hB⟩
  · rintro ⟨⟨x, hx⟩, hA, hmax⟩
    exact ⟨x, (hmax _ (component_connected x)
      (connectedSubset_subset_component A x hx hA)).antisymm
      (connectedSubset_subset_component A x hx hA)⟩

theorem component_partition (X : Type u) [TopologicalSpace X] :
    (⋃ x : X, Component x) = univ ∧
      ∀ x y : X, Component x = Component y ∨ Disjoint (Component x) (Component y) := by
  classical
  refine ⟨eq_univ_of_forall (fun x => mem_iUnion.mpr ⟨x, component_self x⟩), ?_⟩
  intro x y
  by_cases h : Component x = Component y
  · exact Or.inl h
  · right
    simp only [component_eq_mathlib] at h ⊢
    exact connectedComponent_disjoint h

theorem component_closed (x : X) : IsClosed (Component x) := by
  rw [component_eq_mathlib]
  exact isClosed_connectedComponent

theorem unitPath_iff_continuous_endpoints (x y : X) :
    Nonempty (UnitPath x y) ↔
      ∃ p : unitInterval → X, Continuous p ∧ p 0 = x ∧ p 1 = y := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p, p.continuous, p.source, p.target⟩
  · rintro ⟨p, hp, h0, h1⟩
    exact ⟨{ toFun := p, continuous_toFun := hp, source' := h0, target' := h1 }⟩

theorem pathConnected_iff_joined (X : Type u) [TopologicalSpace X] :
    PathConnected X ↔ ∀ x y : X, Joined x y := Iff.rfl

theorem pathConnectedSubset_iff_subspace (A : Set X) :
    PathConnectedSubset A ↔ PathConnected A := by
  constructor
  · intro h a b
    exact (h a.val a.property b.val b.property).joined_subtype
  · intro h x hx y hy
    exact (joinedIn_iff_joined hx hy).mpr (h ⟨x, hx⟩ ⟨y, hy⟩)

theorem pathConnectedSubset_iff_empty_or_isPathConnected (A : Set X) :
    PathConnectedSubset A ↔ A = ∅ ∨ IsPathConnected A := by
  constructor
  · intro h
    rcases A.eq_empty_or_nonempty with he | ⟨x, hx⟩
    · exact Or.inl he
    · exact Or.inr ⟨x, hx, fun _ hy => h x hx _ hy⟩
  · rintro (rfl | h)
    · intro x hx
      exact False.elim hx
    · exact h.joinedIn

/-- Pasting on `{t | t ≤ 1/2}` and `{t | 1/2 ≤ t}`, both closed in [0,1].
At their intersection both formulas equal the common endpoint. -/
theorem concatenation_continuous {x y z : X}
    (p : UnitPath x y) (q : UnitPath y z) : Continuous (concatenationFunction p q) := by
  let A : Bool → Set unitInterval := fun b =>
    if b then {t | (1 / 2 : ℝ) ≤ t} else {t | (t : ℝ) ≤ 1 / 2}
  let f : ∀ b, A b → X := fun b t =>
    if b then q.extend (2 * (t.val : ℝ) - 1) else p.extend (2 * (t.val : ℝ))
  apply Ch02.pasting_continuous_of_finite_closed A f (concatenationFunction p q)
  · apply eq_univ_of_forall
    intro t
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  · intro b
    cases b <;> dsimp [f] <;> fun_prop
  · intro b t
    cases b
    · have ht : (t.val : ℝ) ≤ 1 / 2 := t.property
      simp only [concatenationFunction, ComponentsPathsData.concatenationFunction, ite_eq_left ht,
        f, Bool.false_eq_true, ↓reduceIte]
    · have ht : (1 / 2 : ℝ) ≤ t.val := t.property
      dsimp [concatenationFunction, ComponentsPathsData.concatenationFunction, f]
      split_ifs with h
      · have heq : (t.val : ℝ) = 1 / 2 := le_antisymm h ht
        simp [heq]
      · rfl
  · intro b
    cases b
    · exact isClosed_le continuous_subtype_val continuous_const
    · exact isClosed_le continuous_const continuous_subtype_val

theorem concatenation_endpoints {x y z : X}
    (p : UnitPath x y) (q : UnitPath y z) :
    concatenationFunction p q 0 = x ∧ concatenationFunction p q 1 = z := by
  constructor <;> norm_num [concatenationFunction, ComponentsPathsData.concatenationFunction]

/-- This path's continuity certificate is the finite closed pasting proof above. -/
private noncomputable def concatenate {x y z : X} (p : UnitPath x y) (q : UnitPath y z) :
    UnitPath x z where
  toFun := concatenationFunction p q
  continuous_toFun := concatenation_continuous p q
  source' := (concatenation_endpoints p q).1
  target' := (concatenation_endpoints p q).2

theorem joined_equivalence (X : Type u) [TopologicalSpace X] :
    Equivalence (Joined : X → X → Prop) := by
  refine ⟨Joined.refl, fun h => h.symm, ?_⟩
  rintro x y z ⟨p⟩ ⟨q⟩
  exact ⟨concatenate p q⟩

theorem pathComponent_eq_mathlib (x : X) : PathComponent x = pathComponent x := rfl

theorem pathComponent_self (x : X) : x ∈ PathComponent x := Joined.refl x

theorem pathComponent_pathConnected (x : X) : PathConnectedSubset (PathComponent x) :=
  isPathConnected_pathComponent.joinedIn

theorem pathConnectedSubset_subset_pathComponent (A : Set X) (x : X)
    (hx : x ∈ A) (hA : PathConnectedSubset A) : A ⊆ PathComponent x :=
  fun y hy => (hA x hx y hy).joined

theorem pathComponent_iff_maximal (A : Set X) :
    (∃ x : X, PathComponent x = A) ↔
      A.Nonempty ∧ PathConnectedSubset A ∧
        ∀ B : Set X, PathConnectedSubset B → A ⊆ B → B ⊆ A := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, pathComponent_self x⟩, pathComponent_pathConnected x,
      fun B hB hAB => pathConnectedSubset_subset_pathComponent B x
        (hAB (pathComponent_self x)) hB⟩
  · rintro ⟨⟨x, hx⟩, hA, hmax⟩
    exact ⟨x, (hmax _ (pathComponent_pathConnected x)
      (pathConnectedSubset_subset_pathComponent A x hx hA)).antisymm
      (pathConnectedSubset_subset_pathComponent A x hx hA)⟩

theorem pathComponent_partition (X : Type u) [TopologicalSpace X] :
    (⋃ x : X, PathComponent x) = univ ∧
      ∀ x y : X, PathComponent x = PathComponent y ∨
        Disjoint (PathComponent x) (PathComponent y) := by
  classical
  refine ⟨eq_univ_of_forall (fun x => mem_iUnion.mpr ⟨x, pathComponent_self x⟩), ?_⟩
  intro x y
  by_cases h : PathComponent x = PathComponent y
  · exact Or.inl h
  · refine Or.inr (Set.disjoint_left.mpr ?_)
    intro z hx hy
    exact h ((pathComponent_congr hx).symm.trans (pathComponent_congr hy))

theorem path_range_connected {x y : X} (p : UnitPath x y) :
    ConnectedSubset (range p) := by
  apply (connectedSubset_iff_isPreconnected _).mpr
  exact isPreconnected_range p.continuous

theorem pathConnectedSubset_connected (A : Set X) (hA : PathConnectedSubset A) :
    ConnectedSubset A := by
  rcases (pathConnectedSubset_iff_empty_or_isPathConnected A).mp hA with rfl | h
  · exact connectedSubset_empty X
  · exact (connectedSubset_iff_isPreconnected A).mpr h.isConnected.isPreconnected

theorem pathComponent_subset_component (x : X) : PathComponent x ⊆ Component x :=
  connectedSubset_subset_component _ x (pathComponent_self x)
    (pathConnectedSubset_connected _ (pathComponent_pathConnected x))

theorem pathConnectedSubset_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (hA : PathConnectedSubset A) (hf : ContinuousOn f A) :
    PathConnectedSubset (f '' A) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (hA x hx y hy).map hf

theorem pathConnected_range {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hX : PathConnected X) (hf : Continuous f) :
    PathConnectedSubset (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨p⟩ := hX x y
  exact ⟨p.map hf, fun t => mem_range.mpr ⟨p t, rfl⟩⟩

theorem pathConnected_surjective_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hX : PathConnected X) (hf : Continuous f) (hs : Function.Surjective f) :
    PathConnected Y := by
  intro y z
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨w, rfl⟩ := hs z
  exact Joined.map (hX x w) hf

theorem pathConnected_product {I : Type u} (X : I → Type v)
    (tX : ∀ i, TopologicalSpace (X i)) (hX : ∀ i, @PathConnected (X i) (tX i)) :
    @PathConnected (∀ i, X i) (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  intro x y
  exact Joined.pi (fun i => hX i (x i) (y i))

end D10Topology.Ch06
