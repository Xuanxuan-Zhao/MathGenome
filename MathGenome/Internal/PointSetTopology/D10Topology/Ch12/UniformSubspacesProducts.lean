import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformSubspacesProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-! Subspace and product uniformities, paper.tex `d10:12:subspace-product`.
The bases identify the canonical structures, and the induced-topology
equalities use the Chapter 12 section topology and Chapter 3 product topology.
All constructions allow empty subsets, empty factors, and an empty index type.
-/

open Set Filter
open scoped Uniformity Topology
universe u v w

namespace D10Topology.Ch12

def restrictedEntourage {X : Type u} (A : Set X) (U : Set (X × X)) : Set (A × A) :=
  (Prod.map Subtype.val Subtype.val) ⁻¹' U

def productEntourage {I : Type u} {X : I → Type v}
    (F : Set I) (U : ∀ i, Set (X i × X i)) : Set ((∀ i, X i) × (∀ i, X i)) :=
  ⋂ i ∈ F, (fun p => (p.1 i, p.2 i)) ⁻¹' U i

theorem restrictedEntourage_image {X : Type u} (A : Set X) (U : Set (X × X)) :
    (Prod.map Subtype.val Subtype.val) '' restrictedEntourage A U = U ∩ (A ×ˢ A) := by
  ext p
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨hab, a.property, b.property⟩
  · rintro ⟨hp, ha, hb⟩
    exact ⟨(⟨p.1, ha⟩, ⟨p.2, hb⟩), hp, rfl⟩

theorem subspace_uniformity_basis {X : Type u} [UniformSpace X] (A : Set X) :
    (𝓤 A).HasBasis (fun U : Set (X × X) => U ∈ 𝓤 X) (restrictedEntourage A) :=
  (𝓤 X).basis_sets.comap (Prod.map Subtype.val Subtype.val)

theorem subspace_uniformity_mem {X : Type u} [UniformSpace X]
    (A : Set X) (W : Set (A × A)) :
    W ∈ 𝓤 A ↔ ∃ U ∈ 𝓤 X, restrictedEntourage A U ⊆ W :=
  (subspace_uniformity_basis A).mem_iff

theorem subspace_uniform_topology {X : Type u} [UniformSpace X] (A : Set X) :
    (uniformTopology (X := A)) =
      TopologicalSpace.induced (Subtype.val : A → X) uniformTopology := by
  rw [uniformTopology_eq_canonical, uniformTopology_eq_canonical]
  rfl

theorem restrictedEntourage_ball {X : Type u}
    (A : Set X) (U : Set (X × X)) (a : A) :
    entourageBall (restrictedEntourage A U) a =
      (Subtype.val : A → X) ⁻¹' entourageBall U a.val := rfl

theorem product_uniformity_basis {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] :
    (𝓤 (∀ i, X i)).HasBasis
      (fun b : Set I × (∀ i, Set (X i × X i)) =>
        b.1.Finite ∧ ∀ i ∈ b.1, b.2 i ∈ 𝓤 (X i))
      (fun b => productEntourage b.1 b.2) := by
  rw [Pi.uniformity]
  exact Filter.HasBasis.iInf' fun i =>
    (𝓤 (X i)).basis_sets.comap (fun p : (∀ i, X i) × (∀ i, X i) => (p.1 i, p.2 i))

theorem product_uniformity_mem {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] (W : Set ((∀ i, X i) × (∀ i, X i))) :
    W ∈ 𝓤 (∀ i, X i) ↔
      ∃ (F : Set I) (U : ∀ i, Set (X i × X i)),
        F.Finite ∧ (∀ i ∈ F, U i ∈ 𝓤 (X i)) ∧ productEntourage F U ⊆ W := by
  rw [product_uniformity_basis.mem_iff]
  constructor
  · rintro ⟨⟨F, U⟩, ⟨hF, hU⟩, hsub⟩
    exact ⟨F, U, hF, hU, hsub⟩
  · rintro ⟨F, U, hF, hU, hsub⟩
    exact ⟨⟨F, U⟩, ⟨hF, hU⟩, hsub⟩

theorem productEntourage_empty {I : Type u} {X : I → Type v}
    (U : ∀ i, Set (X i × X i)) : productEntourage ∅ U = univ := by
  simp [productEntourage]

theorem productEntourage_ball {I : Type u} {X : I → Type v} (F : Set I)
    (U : ∀ i, Set (X i × X i)) (x : ∀ i, X i) :
    entourageBall (productEntourage F U) x = F.pi (fun i => entourageBall (U i) (x i)) := by
  ext y
  simp [entourageBall, productEntourage, Set.mem_pi]

theorem product_uniform_topology {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] :
    uniformTopology (X := ∀ i, X i) =
      Ch03.productTopology (fun i => uniformTopology (X := X i)) := by
  simp_rw [uniformTopology_eq_canonical]
  rw [Ch03.productTopology_eq_pi]
  rfl

theorem entourageContinuous_product_iff {I : Type u} {X : I → Type v} {Z : Type w}
    [∀ i, UniformSpace (X i)] [UniformSpace Z] (f : Z → ∀ i, X i) :
    EntourageContinuous f ↔ ∀ i, EntourageContinuous (fun z => f z i) :=
  uniformContinuous_pi

theorem separated_subspace {X : Type u} [UniformSpace X] (A : Set X)
    (hX : Separated (X := X)) : Separated (X := A) := by
  letI : T0Space X := separated_iff_mathlib.mp hX
  exact separated_iff_mathlib.mpr inferInstance

theorem separated_product {I : Type u} {X : I → Type v} [∀ i, UniformSpace (X i)]
    (hX : ∀ i, Separated (X := X i)) : Separated (X := ∀ i, X i) := by
  letI : ∀ i, T0Space (X i) := fun i => separated_iff_mathlib.mp (hX i)
  exact separated_iff_mathlib.mpr inferInstance

theorem empty_subspace_uniformity {X : Type u} [UniformSpace X]
    (A : Set X) [IsEmpty A] :
    (𝓤 A).sets = {∅} ∧ ∀ uA vA : UniformSpace A, uA = vA :=
  ⟨uniformity_empty, fun uA vA => uniformity_empty_unique uA vA⟩

theorem empty_factor_product_uniformity {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] (i : I) [IsEmpty (X i)] :
    IsEmpty (∀ i, X i) ∧ (𝓤 (∀ i, X i)).sets = {∅} ∧
      ∀ uP vP : UniformSpace (∀ i, X i), uP = vP := by
  letI := Ch03.product_empty_of_factor (X := X) i
  exact ⟨inferInstance, uniformity_empty, fun uP vP => uniformity_empty_unique uP vP⟩

theorem zero_factor_product_uniformity {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] [IsEmpty I] :
    (∃! _x : (∀ i, X i), True) ∧
      ∀ uP vP : UniformSpace (∀ i, X i), uP = vP := by
  exact ⟨Ch03.empty_product_singleton, fun _ _ => Subsingleton.elim _ _⟩

end D10Topology.Ch12
