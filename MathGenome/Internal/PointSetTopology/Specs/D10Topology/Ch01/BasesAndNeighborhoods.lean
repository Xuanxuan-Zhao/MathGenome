import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.TopologicalFoundations
import Mathlib.Topology.Bases

/-!
Independent specification of paper.tex, d10:01:basis, d10:01:subbasis,
d10:01:neighborhood and d10:01:local-tests. All topologies are on the
specified underlying type. Empty types, empty unions and empty finite
intersections are allowed. Neighborhoods need not themselves be open.
-/

open Set
open scoped Topology
universe u

namespace Specs.D10Topology.Ch01.BasesAndNeighborhoods

/-- The paper's basis formulation: open members, with every open set a union
of members. It is bridged to Mathlib's basis interface by the implementation. -/
def BasisFor {X : Type u} (t : TopologicalSpace X) (B : Set (Set X)) : Prop :=
  (∀ V ∈ B, IsOpen[t] V) ∧
    ∀ U : Set X, IsOpen[t] U → ∃ A : Set (Set X), A ⊆ B ∧ U = ⋃₀ A

/-- Covering and local refinement of pairwise intersections. -/
def BasisCriterion {X : Type u} (B : Set (Set X)) : Prop :=
  (⋃₀ B = univ) ∧
    ∀ V ∈ B, ∀ W ∈ B, ∀ x ∈ V ∩ W, ∃ Z ∈ B, x ∈ Z ∧ Z ⊆ V ∩ W

/-- Finite subfamilies include the empty subfamily, whose intersection is X. -/
def finiteIntersections {X : Type u} (S : Set (Set X)) : Set (Set X) :=
  (fun F : Set (Set X) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ S}

/-- An open witness inside a neighborhood; there is no openness requirement on N. -/
def Neighborhood {X : Type u} (t : TopologicalSpace X) (x : X) (N : Set X) : Prop :=
  ∃ U : Set X, IsOpen[t] U ∧ x ∈ U ∧ U ⊆ N

/-- A subfamily of neighborhoods refining every neighborhood. -/
def LocalBase {X : Type u} (t : TopologicalSpace X) (x : X)
    (L : Set (Set X)) : Prop :=
  (∀ V ∈ L, Neighborhood t x V) ∧
    ∀ N : Set X, Neighborhood t x N → ∃ V ∈ L, V ⊆ N

end Specs.D10Topology.Ch01.BasesAndNeighborhoods

namespace Specs.D10Topology.Ch01.BasesAndNeighborhoods
open _root_.D10Topology.Ch01

-- Explicit value specifications for the canonical definitions above.
def basisForType : Type (u + 1) :=
  {X : Type u} → TopologicalSpace X → Set (Set X) → Prop
def basisForValue : basisForType := fun t B =>
  (∀ V ∈ B, IsOpen[t] V) ∧
    ∀ U : Set _, IsOpen[t] U → ∃ A : Set (Set _), A ⊆ B ∧ U = ⋃₀ A

def basisCriterionType : Type (u + 1) := {X : Type u} → Set (Set X) → Prop
def basisCriterionValue : basisCriterionType := fun B =>
  (⋃₀ B = univ) ∧
    ∀ V ∈ B, ∀ W ∈ B, ∀ x ∈ V ∩ W, ∃ Z ∈ B, x ∈ Z ∧ Z ⊆ V ∩ W

def finiteIntersectionsType : Type (u + 1) :=
  {X : Type u} → Set (Set X) → Set (Set X)
def finiteIntersectionsValue : finiteIntersectionsType := fun S =>
  (fun F : Set (Set _) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ S}

def neighborhoodType : Type (u + 1) :=
  {X : Type u} → TopologicalSpace X → X → Set X → Prop
def neighborhoodValue : neighborhoodType := fun t x N =>
  ∃ U : Set _, IsOpen[t] U ∧ x ∈ U ∧ U ⊆ N

def localBaseType : Type (u + 1) :=
  {X : Type u} → TopologicalSpace X → X → Set (Set X) → Prop
def localBaseValue : localBaseType := fun t x L =>
  (∀ V ∈ L, Neighborhood t x V) ∧
    ∀ N : Set _, Neighborhood t x N → ∃ V ∈ L, V ⊆ N

def basis_iff_mathlib : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (B : Set (Set X)),
    BasisFor t B ↔ TopologicalSpace.IsTopologicalBasis (t := t) B

def basis_criterion : Prop :=
  ∀ {X : Type u} (B : Set (Set X)),
    (∃ t : TopologicalSpace X, BasisFor t B) ↔ BasisCriterion B

def basis_generated : Prop :=
  ∀ {X : Type u} (B : Set (Set X)), BasisCriterion B →
    BasisFor (TopologicalSpace.generateFrom B) B

def basis_open_iff_union : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (B : Set (Set X)), BasisFor t B →
    ∀ U : Set X, IsOpen[t] U ↔ ∃ A : Set (Set X), A ⊆ B ∧ U = ⋃₀ A

def generated_basis_opens : Prop :=
  ∀ {X : Type u} (B : Set (Set X)), BasisCriterion B →
    ∀ U : Set X, IsOpen[TopologicalSpace.generateFrom B] U ↔
      ∃ A : Set (Set X), A ⊆ B ∧ U = ⋃₀ A

def basis_comparison : Prop :=
  ∀ {X : Type u} (t s : TopologicalSpace X) (B C : Set (Set X)),
    BasisFor t B → BasisFor s C →
      (openSets t ⊆ openSets s ↔
        ∀ V ∈ B, ∀ x ∈ V, ∃ W ∈ C, x ∈ W ∧ W ⊆ V)

def finiteIntersections_basis : Prop :=
  ∀ {X : Type u} (S : Set (Set X)),
    BasisFor (TopologicalSpace.generateFrom S) (finiteIntersections S)

def finiteIntersections_empty : Prop :=
  ∀ {X : Type u} (S : Set (Set X)), univ ∈ finiteIntersections S

def subbasis_generated_eq : Prop :=
  ∀ {X : Type u} (S : Set (Set X)),
    TopologicalSpace.generateFrom (finiteIntersections S) = TopologicalSpace.generateFrom S

def subbasis_smallest : Prop :=
  ∀ {X : Type u} (S : Set (Set X)),
    S ⊆ openSets (TopologicalSpace.generateFrom S) ∧
      ∀ t : TopologicalSpace X, S ⊆ openSets t →
        openSets (TopologicalSpace.generateFrom S) ⊆ openSets t

def subbasis_opens : Prop :=
  ∀ {X : Type u} (S : Set (Set X)) (U : Set X),
    IsOpen[TopologicalSpace.generateFrom S] U ↔
      ∃ A : Set (Set X), A ⊆ finiteIntersections S ∧ U = ⋃₀ A

def neighborhood_iff_mem_nhds : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X) (N : Set X),
    Neighborhood t x N ↔ N ∈ @nhds X t x

def localBase_iff_hasBasis : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X) (L : Set (Set X)),
    LocalBase t x L ↔ (@nhds X t x).HasBasis (fun V : Set X => V ∈ L) id

def neighborhood_contains : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X) (N : Set X),
    Neighborhood t x N → x ∈ N

def neighborhood_mono : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X) (N M : Set X),
    Neighborhood t x N → N ⊆ M → Neighborhood t x M

def neighborhood_univ : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X), Neighborhood t x univ

def neighborhood_inter : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X) (N M : Set X),
    Neighborhood t x N → Neighborhood t x M → Neighborhood t x (N ∩ M)

def neighborhood_finite_inter : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (x : X) (A : Set (Set X)),
    A.Finite → (∀ N ∈ A, Neighborhood t x N) → Neighborhood t x (⋂₀ A)

def open_iff_neighborhood : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (G : Set X),
    IsOpen[t] G ↔ ∀ x ∈ G, Neighborhood t x G

def basis_localBase : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (B : Set (Set X)), BasisFor t B →
    ∀ x : X, LocalBase t x {V ∈ B | x ∈ V}

end Specs.D10Topology.Ch01.BasesAndNeighborhoods
