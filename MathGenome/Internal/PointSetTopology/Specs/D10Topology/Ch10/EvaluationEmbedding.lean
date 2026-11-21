import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.InitialTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval

/-!
Independent statements for paper.tex, Theorem 10.1 and Proposition 10.3.
The product is the canonical dependent product topology. The displayed
`generateFrom` family is precisely all coordinate inverse images of opens.
There are no nonemptiness restrictions on X, the index type, or the factors.
Compactness means the upstream open-cover property, without Hausdorffness.
-/

open Set Topology
universe u v w

namespace Specs.D10Topology.Ch10.EvaluationEmbedding

/-- Point separation is exactly injectivity of the evaluation map. -/
def evaluation_injective_iff : Prop :=
  ∀ {X : Type u} {ι : Type v} {Y : ι → Type w} (f : ∀ i, X → Y i),
    Function.Injective (fun x i => f i x) ↔
      ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y

/-- Pulling the product topology back along evaluation gives the stated
initial topology, with all finite intersections (including the empty one)
and arbitrary unions included by `generateFrom`. -/
def evaluation_induced_topology : Prop :=
  ∀ {X : Type u} {ι : Type v} {Y : ι → Type w}
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, X → Y i),
    TopologicalSpace.induced (fun x i => f i x) Pi.topologicalSpace =
      TopologicalSpace.generateFrom
        {U : Set X | ∃ i V, IsOpen V ∧ U = f i ⁻¹' V}

def evaluation_continuous : Prop :=
  ∀ {X : Type u} {ι : Type v} {Y : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i), (∀ i, Continuous (f i)) →
      Continuous (fun x i => f i x)

/-- The required equivalence retains injectivity as a separate conjunct. -/
def evaluation_embedding_iff : Prop :=
  ∀ {X : Type u} {ι : Type v} {Y : ι → Type w}
    [tX : TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i), (∀ i, Continuous (f i)) →
      (IsEmbedding (fun x i => f i x) ↔
        Function.Injective (fun x i => f i x) ∧
          tX = TopologicalSpace.generateFrom
            {U : Set X | ∃ i V, IsOpen V ∧ U = f i ⁻¹' V})

/-- One coordinate inverse image at each point of each open set suffices,
provided the family also separates points. -/
def evaluation_embedding_of_coordinates : Prop :=
  ∀ {X : Type u} {ι : Type v} {Y : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i), (∀ i, Continuous (f i)) →
    (∀ x y, x ≠ y → ∃ i, f i x ≠ f i y) →
    (∀ U : Set X, IsOpen U → ∀ x ∈ U,
      ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ x ∈ f i ⁻¹' V ∧ f i ⁻¹' V ⊆ U) →
    IsEmbedding (fun x i => f i x)

/-- For interval-valued maps use the open relative ray (0,1]. Point
separation is still required, with no implicit T₁ assumption on X. -/
def evaluation_embedding_unitInterval : Prop :=
  ∀ {X : Type u} {ι : Type v} [TopologicalSpace X]
    (f : ι → X → unitInterval), (∀ i, Continuous (f i)) →
    (∀ x y, x ≠ y → ∃ i, f i x ≠ f i y) →
    (∀ U : Set X, IsOpen U → ∀ x ∈ U,
      ∃ i, 0 < (f i x : ℝ) ∧ ∀ y, y ∉ U → f i y = 0) →
    IsEmbedding (fun x i => f i x)

def compact_injection_embedding : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (f : X → Y),
    Specs.D10Topology.Ch05.Compactness.CoverCompact X →
    Continuous f → Function.Injective f → IsEmbedding f

def compact_evaluation_embedding : Prop :=
  ∀ {X : Type u} {ι : Type v} {Y : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
    (f : ∀ i, X → Y i),
    Specs.D10Topology.Ch05.Compactness.CoverCompact X →
    (∀ i, Continuous (f i)) →
    (∀ x y, x ≠ y → ∃ i, f i x ≠ f i y) →
    IsEmbedding (fun x i => f i x)

/-- The single ordinary coordinate on the discrete real line is a
continuous injection into a Hausdorff space but is not an embedding;
the inverse identity is not continuous. Topologies are explicit. -/
def discrete_real_counterexample : Prop :=
  @Continuous ℝ ℝ ⊥ inferInstance id ∧
  Function.Injective (id : ℝ → ℝ) ∧
  ¬ @IsEmbedding ℝ ℝ ⊥ inferInstance id ∧
  ¬ @Continuous ℝ ℝ inferInstance ⊥ id

end Specs.D10Topology.Ch10.EvaluationEmbedding
