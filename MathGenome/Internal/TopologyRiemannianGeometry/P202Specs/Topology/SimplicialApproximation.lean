import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Data.Finset.Max
import MathGenome.PointSetTopology.Topics.D10Topology.Ch09

/-!
Objects for paper.tex, §2.4 (lines 742–793). Realizations and their weak
topologies are those of CellStructures. In particular unused elements of an
ambient vertex type are allowed, and the empty complex is allowed.
-/

noncomputable section
open Set Topology Classical
universe u v

namespace P202.Cellular.AbstractSimplicialComplex

variable {V : Type u} {W : Type v}

/-- Only vertices that actually occur in the complex. -/
abbrev Vertex (K : AbstractSimplicialComplex V) :=
  {v : V // ({v} : Finset V) ∈ K.simplices}

def IsFinite (K : AbstractSimplicialComplex V) : Prop := K.simplices.Finite

theorem vertex_mem_of_mem {K : AbstractSimplicialComplex V}
    {s : Finset V} (hs : s ∈ K.simplices) {v : V} (hv : v ∈ s) :
    ({v} : Finset V) ∈ K.simplices :=
  K.face hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

def simplexVertices (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    Finset K.Vertex :=
  s.1.attach.map ⟨fun (v : s.1) => ⟨v.1, vertex_mem_of_mem s.2 v.2⟩,
    fun _a _b h => Subtype.ext (congrArg (fun x : K.Vertex => x.1) h)⟩

def activeCoordinates (K : AbstractSimplicialComplex V) (p : K.Realization) :
    Convexity.StdSimplex ℝ K.Vertex where
  weights := p.1.weights.subtypeDomain (fun v => ({v} : Finset V) ∈ K.simplices)
  nonneg v := p.1.weights_nonneg v.1
  total := by
    calc
      _ = p.1.weights.sum (fun (_ : V) r => r) :=
        Finsupp.sum_subtypeDomain_index (h := fun (_ : V) (r : ℝ) => r)
          (fun v hv => vertex_mem_of_mem p.2 hv)
      _ = 1 := p.1.total

/-- Vertex collapses are allowed. The domain is the actual vertex set, so
even an empty complex on a nonempty ambient type has its expected maps. -/
structure SimplicialMap (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) where
  vertex : K.Vertex → W
  map_simplex : ∀ s : K.Simplex, (K.simplexVertices s).image vertex ∈ L.simplices

def SimplicialMap.realization {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W} (g : SimplicialMap K L) :
    K.Realization → L.Realization := by
  classical
  intro p
  refine ⟨(K.activeCoordinates p).map g.vertex, ?_⟩
  convert g.map_simplex ⟨p.1.weights.support, p.2⟩ using 1
  rw [Convexity.StdSimplex.weights_map,
    Finsupp.support_mapDomain_of_nonneg (K.activeCoordinates p).nonneg]
  congr 1
  ext v
  simp [activeCoordinates, simplexVertices, Finsupp.mem_support_iff]
  constructor
  · intro h
    exact ⟨v.1, h, Subtype.ext rfl⟩
  · rintro ⟨a, ha, heq⟩
    have heq' := congrArg Subtype.val heq
    change a = v.1 at heq'
    rw [← heq']
    exact ha

def openStar (K : AbstractSimplicialComplex V) (v : K.Vertex) : Set K.Realization :=
  {p | 0 < p.1.weights v.1}

/-- The order complex of the nonempty faces. Distinct elements of a simplex
are strictly nested by inclusion, so these are precisely barycentric chains. -/
def barycentricSubdivision (K : AbstractSimplicialComplex V) :
    AbstractSimplicialComplex K.Simplex where
  simplices := {c | c.Nonempty ∧ ∀ s ∈ c, ∀ t ∈ c, s.1 ⊆ t.1 ∨ t.1 ⊆ s.1}
  nonempty _ h := h.1
  face hs hts ht := ⟨ht, fun s hs' t ht' => hs.2 s (hts hs') t (hts ht')⟩

def simplexBarycenter (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    Convexity.StdSimplex ℝ V :=
  .subBarycenter s.1 (K.nonempty s.1 s.2)

/-- The canonical affine evaluation of barycentric subdivision, first in
the ambient space of finite probability distributions. -/
def subdivisionCoordinates (K : AbstractSimplicialComplex V)
    (p : K.barycentricSubdivision.Realization) : Convexity.StdSimplex ℝ V :=
  p.1.iConvexComb K.simplexBarycenter

theorem chain_has_largest {K : AbstractSimplicialComplex V}
    {c : Finset K.Simplex} (hc : c ∈ K.barycentricSubdivision.simplices) :
    ∃ s ∈ c, ∀ t ∈ c, t.1 ⊆ s.1 := by
  obtain ⟨s, hs, hmax⟩ := c.exists_max_image (fun s => s.1.card) hc.1
  refine ⟨s, hs, fun t ht => ?_⟩
  rcases hc.2 t ht s hs with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h (hmax t ht)).symm.subset

def subdivisionMap (K : AbstractSimplicialComplex V) :
    K.barycentricSubdivision.Realization → K.Realization := by
  classical
  intro p
  refine ⟨K.subdivisionCoordinates p, ?_⟩
  obtain ⟨s, hs, htop⟩ := chain_has_largest p.2
  apply K.face s.2 _ (Convexity.StdSimplex.support_weights_nonempty _)
  intro v hv
  by_contra hv'
  have hz : (K.subdivisionCoordinates p).weights v = 0 := by
    change (((p.1.map K.simplexBarycenter).weights.sum
      (fun d r => r • d.weights)) v) = 0
    rw [Convexity.StdSimplex.weights_map,
      Finsupp.sum_mapDomain_index
        (h := fun (d : Convexity.StdSimplex ℝ V) (r : ℝ) => r • d.weights)
        (fun d => zero_smul ℝ d.weights) (fun d a b => add_smul a b d.weights)]
    simp only [Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro t ht
    dsimp only [simplexBarycenter]
    rw [Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero _ _ v
      (fun h => hv' (htop t ht h)), mul_zero]
  exact Finsupp.mem_support_iff.mp hv hz

/-- Each stage has its own vertex type. -/
def iteratedComplex (K : AbstractSimplicialComplex V) :
    ℕ → Σ W : Type u, AbstractSimplicialComplex W
  | 0 => ⟨V, K⟩
  | n + 1 => ⟨(iteratedComplex K n).2.Simplex,
      (iteratedComplex K n).2.barycentricSubdivision⟩

abbrev Subdivision (K : AbstractSimplicialComplex V) (n : ℕ) :=
  (K.iteratedComplex n).2

def iteratedSubdivisionMap (K : AbstractSimplicialComplex V) :
    ∀ n, (K.Subdivision n).Realization → K.Realization
  | 0 => id
  | n + 1 => K.iteratedSubdivisionMap n ∘ (K.Subdivision n).subdivisionMap

def inclusionRealization {K L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) : K.Realization → L.Realization :=
  fun p => ⟨p.1, h p.2⟩

def subdivisionInclusion {K L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) :
    K.barycentricSubdivision.Realization → L.barycentricSubdivision.Realization := by
  intro p
  let i : K.Simplex → L.Simplex := fun s => ⟨s.1, h s.2⟩
  refine ⟨p.1.map i, ?_⟩
  classical
  rw [Convexity.StdSimplex.weights_map,
    Finsupp.support_mapDomain_of_nonneg p.1.nonneg]
  refine ⟨p.1.support_weights_nonempty.image i, ?_⟩
  intro s hs t ht
  obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
  exact p.2.2 s' hs' t' ht'

end P202.Cellular.AbstractSimplicialComplex

namespace P202Specs.Topology.SimplicialApproximation
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

def simplicialMapContinuous : Prop :=
  ∀ {V : Type u} {W : Type v} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W} (g : SimplicialMap K L), Continuous g.realization

def openStars : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V),
    (∀ v : K.Vertex, IsOpen (K.openStar v)) ∧
    (⋃ v : K.Vertex, K.openStar v) = Set.univ

/-- An assignment satisfying the open-star test gives a simplicial map.
The support inclusion is the carrier condition for straight interpolation. -/
def starCriterion : Prop :=
  ∀ {V : Type u} {W : Type v} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f : K.Realization → L.Realization)
    (a : K.Vertex → W),
    (∀ v x, x ∈ K.openStar v → 0 < (f x).1.weights (a v)) →
    ∃ g : SimplicialMap K L, g.vertex = a ∧
      ∀ x, (g.realization x).1.weights.support ⊆ (f x).1.weights.support

def subdivisionFaceCompatibility : Prop :=
  ∀ {V : Type u} {K L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices)
    (x : K.barycentricSubdivision.Realization),
    L.subdivisionMap (subdivisionInclusion h x) = inclusionRealization h (K.subdivisionMap x)

/-- The homeomorphism is required to be the canonical barycentric evaluation,
not an arbitrary homeomorphism between the two spaces. -/
def subdivisionHomeomorphism : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V), K.IsFinite →
    ∀ n, ∃ h : (K.Subdivision n).Realization ≃ₜ K.Realization,
      (h : (K.Subdivision n).Realization → K.Realization) = K.iteratedSubdivisionMap n

/-- This includes the topology and compactness adapters for the specified
metric required by the public D10 Lebesgue-number theorem. -/
def finiteMetricRealization : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V), K.IsFinite →
    ∃ d : MetricSpace K.Realization,
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace = (inferInstance : TopologicalSpace K.Realization) ∧
      @D10Topology.Ch05.CoverCompact K.Realization
        (D10Topology.Ch09.metricTopology d.toPseudoMetricSpace)

/-- Mesh convergence and the star diameter estimate are stated in every
compatible metric. This permits later small-chain arguments to choose a metric
without changing the weak realization topology. -/
def shrinkingMeshAndStars : Prop :=
  ∀ {V : Type u} (K : AbstractSimplicialComplex V), K.IsFinite →
    ∀ (d : MetricSpace K.Realization),
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace = (inferInstance : TopologicalSpace K.Realization) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
        (∀ s : (K.Subdivision n).Simplex,
          D10Topology.Ch09.diameter d.toPseudoMetricSpace
            (K.iteratedSubdivisionMap n '' Set.range ((K.Subdivision n).simplexChart s)) <
            ENNReal.ofReal ε) ∧
        (∀ v : (K.Subdivision n).Vertex,
          D10Topology.Ch09.diameter d.toPseudoMetricSpace
            (K.iteratedSubdivisionMap n '' (K.Subdivision n).openStar v) <
            ENNReal.ofReal ε)

def starRefinement : Prop :=
  ∀ {V : Type u} {W : Type v} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W), K.IsFinite →
    ∀ f : C(K.Realization, L.Realization),
      ∃ N : ℕ, ∀ n, N ≤ n → ∀ v : (K.Subdivision n).Vertex,
        ∃ w : L.Vertex, Set.MapsTo (f ∘ K.iteratedSubdivisionMap n)
          ((K.Subdivision n).openStar v) (L.openStar w)

/-- Straight interpolation is a homotopy in the weak topology, with the
ordinary product topology on the parameter square/source product. -/
def starHomotopy : Prop :=
  ∀ {V : Type u} {W : Type v} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W), K.IsFinite →
    ∀ (f : C(K.Realization, L.Realization)) (g : SimplicialMap K L),
      (∀ v x, x ∈ K.openStar v → 0 < (f x).1.weights (g.vertex v)) →
      ∃ H : C(K.Realization × Interval, L.Realization),
        (∀ x, H (x, 0) = f x) ∧ (∀ x, H (x, 1) = g.realization x) ∧
        ∀ x t w, (H (x, t)).1.weights w =
          (1 - (t : ℝ)) * (f x).1.weights w + (t : ℝ) * (g.realization x).1.weights w

/-- paper.tex, Theorem 2.7. The source is finite, the target is arbitrary,
and the change of source coordinates is the canonical subdivision map. -/
def finiteSourceSimplicialApproximation : Prop :=
  ∀ {V : Type u} {W : Type v} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W), K.IsFinite →
    ∀ f : C(K.Realization, L.Realization),
      ∃ N : ℕ, ∀ n, N ≤ n →
        ∃ (g : SimplicialMap (K.Subdivision n) L)
          (h : (K.Subdivision n).Realization ≃ₜ K.Realization)
          (H : C((K.Subdivision n).Realization × Interval, L.Realization)),
          (h : (K.Subdivision n).Realization → K.Realization) = K.iteratedSubdivisionMap n ∧
          (∀ x, H (x, 0) = f (h x)) ∧ (∀ x, H (x, 1) = g.realization x)

end P202Specs.Topology.SimplicialApproximation
