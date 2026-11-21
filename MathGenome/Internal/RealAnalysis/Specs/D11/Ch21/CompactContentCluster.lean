import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactCoveringRatios
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
Independent specification for paper.tex:5842–5853. Compact subsets are
bundled as `Compacts G`, including the empty set. The fixed `K₀` is the
same positive compact used in the covering ratios. The topology on the
function space is the product topology, with one coordinate per compact.
No countability assumption is imposed.
-/
namespace Specs.D11.Ch21.CompactContentCluster

open Set TopologicalSpace
open scoped Topology
universe u

/-- The compact product of the source's closed, finite real intervals. -/
def contentProduct (G : Type u) [Group G] [TopologicalSpace G]
    (K₀ : PositiveCompacts G) : Set (Compacts G → ℝ) :=
  Set.pi Set.univ fun K =>
    Set.Icc 0 (CompactCoveringRatios.coveringNumberValue G K K₀ : ℝ)

/-- Closure of the ratios over all identity neighborhoods contained in `V`.
We take closure in the ambient product of real lines, then intersect with
`contentProduct`; this gives the same points as relative closure in that
closed product. Neighborhoods need not themselves be open. -/
def ratioCluster (G : Type u) [Group G] [TopologicalSpace G]
    (K₀ : PositiveCompacts G) (V : Set G) : Set (Compacts G → ℝ) :=
  closure ((fun U => CompactCoveringRatios.coveringRatioValue G K₀ U) ''
    {U : Set G | U ⊆ V ∧ U ∈ 𝓝 (1 : G)})

/-- All content laws, including the quantitative covering bound. Real values
express finiteness. Binary subadditivity and disjoint additivity give their
finite-family versions by induction, starting with the empty-set law. -/
def ContentProperties (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K₀ : PositiveCompacts G) (h : Compacts G → ℝ) : Prop :=
  h ⊥ = 0 ∧ h K₀.toCompacts = 1 ∧
  (∀ K : Compacts G, 0 ≤ h K ∧
    h K ≤ (CompactCoveringRatios.coveringNumberValue G K K₀ : ℝ)) ∧
  (∀ (a : G) (K : Compacts G),
    h (K.map (fun x => a * x) (continuous_const_mul a)) = h K) ∧
  (∀ K L : Compacts G, (K : Set G) ⊆ L → h K ≤ h L) ∧
  (∀ K L : Compacts G, h (K ⊔ L) ≤ h K + h L) ∧
  (∀ K L : Compacts G, Disjoint (K : Set G) (L : Set G) →
    h (K ⊔ L) = h K + h L)

/-- Type of the compact content constructed in the source. -/
def contentType : Type (u + 1) :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G], PositiveCompacts G → Compacts G → ℝ

/-- Fix the library's choice from the compact-product intersection. Its
`chaar` definition chooses from `nonempty_iInter_clPrehaar`, whose proof
is Tychonoff compactness plus FIP. This is a compact content, before any
outer measure or subsequent normalization of a measure. -/
noncomputable def contentValue : contentType.{u} :=
  fun _ _ _ _ _ _ K₀ => MeasureTheory.Measure.haar.chaar K₀

/-- The laws and cluster characterization for the specified construction. -/
def contentStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (K₀ : PositiveCompacts G),
    contentValue G K₀ ∈ contentProduct G K₀ ∧
    (∀ V : Set G, V ∈ 𝓝 (1 : G) → contentValue G K₀ ∈ ratioCluster G K₀ V) ∧
    ContentProperties G K₀ (contentValue G K₀)

def productCompactStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (K₀ : PositiveCompacts G),
    IsCompact (contentProduct G K₀)

/-- Finite intersections of the closed tails meet the compact product. -/
def finiteIntersectionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (K₀ : PositiveCompacts G)
    (t : Finset (Set G)), (∀ V ∈ t, V ∈ 𝓝 (1 : G)) →
    (contentProduct G K₀ ∩ ⋂ V ∈ t, ratioCluster G K₀ V).Nonempty

/-- The chosen content lies in every neighborhood tail closure, and has
all the source's laws with the original fixed normalization. -/
def clusterStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (K₀ : PositiveCompacts G),
    ∃ h : Compacts G → ℝ,
      h ∈ contentProduct G K₀ ∧
      (∀ V : Set G, V ∈ 𝓝 (1 : G) → h ∈ ratioCluster G K₀ V) ∧
      ContentProperties G K₀ h

end Specs.D11.Ch21.CompactContentCluster
