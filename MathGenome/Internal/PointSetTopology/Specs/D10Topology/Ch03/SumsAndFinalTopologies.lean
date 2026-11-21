import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps

/-!
Independent specification for paper.tex, d10:03:sum and d10:03:final.
The disjoint sum is `Sigma X`, whose points retain their summand tags.
The topology on each factor is specified independently; the target of a
final family initially has no topology. Empty factors and empty indexing
types are permitted, with no separation or surjectivity assumptions.

The canonical data live here so later constructions can refer to them
without importing the candidate proofs. The open-set and mapping
characterizations below are obligations, not assumed certificates.
-/

open Set Topology
universe u v w z

namespace D10Topology.Ch03.SumFinalData

/-- The canonical topology on the dependent sum of tagged points. -/
@[instance_reducible] def sumTopology {I : Type u} (X : I → Type v)
    [∀ i, TopologicalSpace (X i)] : TopologicalSpace (Sigma X) := inferInstance

/-- Supremum in Lean's reverse order on topologies: opens must pull back
    to opens under every member of the family. -/
@[instance_reducible] def finalTopology {I : Type u} {X : I → Type v}
    [t : ∀ i, TopologicalSpace (X i)] {Y : Type w}
    (q : ∀ i, X i → Y) : TopologicalSpace Y :=
  ⨆ i, TopologicalSpace.coinduced (q i) (t i)

end D10Topology.Ch03.SumFinalData

namespace Specs.D10Topology.Ch03.SumsAndFinalTopologies
open _root_.D10Topology.Ch03.SumFinalData
open _root_.D10Topology.Ch01

def sumTopologyType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → (X : I → Type v) →
    [t : ∀ i, TopologicalSpace (X i)] → TopologicalSpace (Sigma X)

def sumTopologyValue : sumTopologyType := @sumTopology

def finalTopologyType : Type (max (u + 1) (v + 1) (w + 1)) :=
  {I : Type u} → {X : I → Type v} →
    [t : ∀ i, TopologicalSpace (X i)] → {Y : Type w} →
    (∀ i, X i → Y) → TopologicalSpace Y

def finalTopologyValue : finalTopologyType := @finalTopology

/-- The source's defining open family, including arbitrary dependent factors. -/
def sum_isOpen_iff : Prop :=
  ∀ {I : Type u} (X : I → Type v) [t : ∀ i, TopologicalSpace (X i)]
    (U : Set (Sigma X)),
    IsOpen[sumTopology X] U ↔ ∀ i, IsOpen[t i] (Sigma.mk i ⁻¹' U)

/-- Includes empty and whole sets, arbitrary unions and finite intersections. -/
def sum_open_axioms : Prop :=
  ∀ {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)],
    OpenFamilyAxioms (openSets (sumTopology X))

def sum_inclusion_embedding : Prop :=
  ∀ {I : Type u} (X : I → Type v) [t : ∀ i, TopologicalSpace (X i)] (i : I),
    @IsEmbedding (X i) (Sigma X) (t i) (sumTopology X) (Sigma.mk i)

def sum_inclusion_clopen : Prop :=
  ∀ {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)] (i : I),
    @IsClopen (Sigma X) (sumTopology X) (range (Sigma.mk i))

def sum_continuous_iff : Prop :=
  ∀ {I : Type u} (X : I → Type v) [t : ∀ i, TopologicalSpace (X i)]
    {Y : Type w} [tY : TopologicalSpace Y] (f : Sigma X → Y),
    Continuous[sumTopology X, tY] f ↔ ∀ i, Continuous (f ∘ Sigma.mk i)

/-- Any empty index type gives an empty dependent sum. -/
def sum_empty : Prop :=
  ∀ {I : Type u} [IsEmpty I] (X : I → Type v), IsEmpty (Sigma X)

def final_isOpen_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} [t : ∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) (V : Set Y),
    IsOpen[finalTopology q] V ↔ ∀ i, IsOpen[t i] (q i ⁻¹' V)

def final_open_axioms : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y),
    OpenFamilyAxioms (openSets (finalTopology q))

def final_maps_continuous : Prop :=
  ∀ {I : Type u} {X : I → Type v} [t : ∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) (i : I),
    Continuous[t i, finalTopology q] (q i)

/-- Finest in terms of the actual open families, with no joint-surjectivity
    assumption on the family. -/
def final_finest : Prop :=
  ∀ {I : Type u} {X : I → Type v} [t : ∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) (s : TopologicalSpace Y),
    (∀ i, Continuous[t i, s] (q i)) ↔ openSets s ⊆ openSets (finalTopology q)

/-- The same universal comparison with Lean's order direction explicit. -/
def final_le_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} [t : ∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) (s : TopologicalSpace Y),
    finalTopology q ≤ s ↔ ∀ i, Continuous[t i, s] (q i)

def final_continuous_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} [t : ∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) {Z : Type z} [tZ : TopologicalSpace Z]
    (h : Y → Z),
    Continuous[finalTopology q, tZ] h ↔ ∀ i, Continuous (h ∘ q i)

/-- The two constructions agree for the summand inclusions. -/
def sum_eq_final : Prop :=
  ∀ {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)],
    sumTopology X = finalTopology (fun i => (Sigma.mk i : X i → Sigma X))

/-- The empty final family gives the discrete topology on every target set. -/
def final_empty_eq_discrete : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) [IsEmpty I], finalTopology q = ⊥

def final_empty_continuous : Prop :=
  ∀ {I : Type u} {X : I → Type v} [∀ i, TopologicalSpace (X i)]
    {Y : Type w} (q : ∀ i, X i → Y) [IsEmpty I] {Z : Type z} [tZ : TopologicalSpace Z]
    (h : Y → Z), Continuous[finalTopology q, tZ] h

end Specs.D10Topology.Ch03.SumsAndFinalTopologies
