import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures

/-!
Basic weak-cell topology (paper.tex, Proposition 2.2, lines 515–568).
The cell and subcomplex objects are the canonical ones from CellStructures.
Finiteness means finitely many cells in total, with no bound imposed on the
ambient complex. The weak topology statement tests all subsets of the carrier
against the selected characteristic disks, using the actual subspace topology.
The support statements give finite support for loops and homotopies (compact
source I or I × I), and finite singular chains (finite families of compact
geometric simplices), as well as arbitrary compact sources.
-/

noncomputable section
open Set Topology
universe u v

namespace P202.Cellular

def Subcomplex.IsFinite {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) : Prop :=
  {d : Σ n, Cell X n | d.2 ∈ A.cells d.1}.Finite

end P202.Cellular

namespace P202Specs.Topology.CellTopology
open P202.Cellular

def subcomplexClosed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Subcomplex X),
    IsClosed A.carrier

/-- This is the closed-set test for the weak topology on the subcomplex,
expressed in its actual subspace topology. Every subset of the carrier is
the preimage of such a `B`, so the test determines that topology completely. -/
def subcomplexWeakTopology : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Subcomplex X)
    (B : Set X), B ⊆ A.carrier →
    (IsClosed ((Subtype.val : A.carrier → X) ⁻¹' B) ↔
      ∀ n (c : Cell X n), c ∈ A.cells n → IsClosed (characteristic X n c ⁻¹' B))

def compactContainedInFiniteSubcomplex : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (K : Set X), IsCompact K →
    ∃ A : Subcomplex X, A.IsFinite ∧ K ⊆ A.carrier

def compactImageFiniteSupport : Prop :=
  ∀ {X : Type u} {D : Type v} [TopologicalSpace X] [CWStructure X]
    [TopologicalSpace D] [CompactSpace D] (f : C(D, X)),
    ∃ A : Subcomplex X, A.IsFinite ∧ range f ⊆ A.carrier

def finiteCompactImagesFiniteSupport : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X]
    {ι : Type v} [Finite ι] (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    [∀ i, CompactSpace (D i)] (f : ∀ i, C(D i, X)),
    ∃ A : Subcomplex X, A.IsFinite ∧ ∀ i, range (f i) ⊆ A.carrier

/-- This applies in particular to based loops, since endpoint constraints do
not change the compactness of the parameter interval. -/
def intervalMapFiniteSupport : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (f : C(Interval, X)),
    ∃ A : Subcomplex X, A.IsFinite ∧ range f ⊆ A.carrier

/-- Homotopies of loops have this compact square as their parameter space,
with the ordinary product topology fixed by the source conventions. -/
def intervalHomotopyFiniteSupport : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X]
    (H : C(Interval × Interval, X)),
    ∃ A : Subcomplex X, A.IsFinite ∧ range H ⊆ A.carrier

/-- A singular chain has a finite support of singular simplices. This
statement simultaneously contains the images of any finite set of continuous
singular simplices, with arbitrary dimensions and arbitrary coefficients in
the eventual chain. -/
def finiteSingularSimplexSupport : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X]
    (σ : Finset (Σ n, C(StandardSimplex n, X))),
    ∃ A : Subcomplex X, A.IsFinite ∧ ∀ s ∈ σ, range s.2 ⊆ A.carrier

end P202Specs.Topology.CellTopology
