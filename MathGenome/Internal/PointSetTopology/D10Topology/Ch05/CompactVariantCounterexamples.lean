import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CompactVariantCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Tychonoff
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CountableCompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.ProductLimitsAndHausdorff
import Lean.Elab.Tactic.Omega

/-! The two strict distinctions of paper.tex `d10:05:variant-counterexamples`.
The cube argument chooses its coordinate after an arbitrary strictly increasing
subsequence has been proposed. The second space keeps the indiscrete second
factor, and uses punctured-neighborhood accumulation without a T1 assumption. -/

open Set
open scoped Topology
namespace D10Topology.Ch05.CompactVariantCounterexamples


abbrev BinaryCube := Specs.D10Topology.Ch05.CompactVariantCounterexamples.BinaryCube
@[instance_reducible] def binaryCubeTopology : TopologicalSpace BinaryCube := Specs.D10Topology.Ch05.CompactVariantCounterexamples.binaryCubeTopology
noncomputable def binarySequence : ℕ → BinaryCube := Specs.D10Topology.Ch05.CompactVariantCounterexamples.binarySequence
def evenPositionSet : (ℕ → ℕ) → Set ℕ := Specs.D10Topology.Ch05.CompactVariantCounterexamples.evenPositionSet
abbrev FiberSpace := Specs.D10Topology.Ch05.CompactVariantCounterexamples.FiberSpace
@[instance_reducible] def fiberTopology : TopologicalSpace FiberSpace := Specs.D10Topology.Ch05.CompactVariantCounterexamples.fiberTopology
def fiberPair : ℕ → Set FiberSpace := Specs.D10Topology.Ch05.CompactVariantCounterexamples.fiberPair
def otherInFiber : FiberSpace → FiberSpace := Specs.D10Topology.Ch05.CompactVariantCounterexamples.otherInFiber

theorem binaryCube_topology_eq_pi :
    binaryCubeTopology = @Pi.topologicalSpace (Set ℕ) (fun _ => Bool) (fun _ => ⊥) :=
  Ch03.productTopology_eq_pi _

theorem binaryCube_compact : @CoverCompact BinaryCube binaryCubeTopology := by
  apply tychonoff_product (fun _ : Set ℕ => (⊥ : TopologicalSpace Bool))
  intro _
  exact (coverCompact_iff_compactSpace Bool).mpr inferInstance

theorem binaryCube_hausdorff : @T2Space BinaryCube binaryCubeTopology := by
  rw [binaryCube_topology_eq_pi]
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := discreteTopology_bot Bool
  infer_instance

theorem binarySequence_coordinate (n : ℕ) (A : Set ℕ) :
    binarySequence n A = true ↔ n ∈ A := by
  classical
  simp [binarySequence, Specs.D10Topology.Ch05.CompactVariantCounterexamples.binarySequence]

theorem selected_coordinate_alternates (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) :
    binarySequence (φ (2 * k)) (evenPositionSet φ) = false ∧
    binarySequence (φ (2 * k + 1)) (evenPositionSet φ) = true := by
  classical
  have hn : φ (2 * k) ∉ evenPositionSet φ := by
    rintro ⟨j, hj⟩
    have := hφ.injective hj
    omega
  have hy : φ (2 * k + 1) ∈ evenPositionSet φ := ⟨k, rfl⟩
  simp [binarySequence, Specs.D10Topology.Ch05.CompactVariantCounterexamples.binarySequence, hn, hy]

theorem selected_coordinate_not_convergent (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (b : Bool) :
    ¬ Ch04.Converges ⊥ (fun k => binarySequence (φ k) (evenPositionSet φ)) b := by
  intro h
  obtain ⟨N, hN⟩ := h {b} ⟨{b}, trivial, rfl, Subset.rfl⟩
  have he := hN (2 * N) (by omega)
  have ho := hN (2 * N + 1) (by omega)
  change binarySequence (φ (2 * N)) (evenPositionSet φ) = b at he
  change binarySequence (φ (2 * N + 1)) (evenPositionSet φ) = b at ho
  rw [(selected_coordinate_alternates φ hφ N).1] at he
  rw [(selected_coordinate_alternates φ hφ N).2] at ho
  exact Bool.false_ne_true (he.trans ho.symm)

theorem binarySequence_no_convergent_subsequence (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : BinaryCube) :
    ¬ Ch04.Converges binaryCubeTopology (binarySequence ∘ φ) x := by
  intro h
  have hcoords := (Ch04.net_product_converges_iff
    (fun _ : Set ℕ => (⊥ : TopologicalSpace Bool)) (binarySequence ∘ φ) x).mp h
  exact selected_coordinate_not_convergent φ hφ (x (evenPositionSet φ))
    (hcoords (evenPositionSet φ))

theorem binaryCube_not_sequentiallyCompact :
    ¬ @SequentiallyCompact BinaryCube binaryCubeTopology := by
  intro h
  obtain ⟨x, φ, hφ, hx⟩ := h binarySequence
  exact binarySequence_no_convergent_subsequence φ hφ x hx

theorem fiber_open_iff (U : Set FiberSpace) :
    IsOpen[fiberTopology] U ↔ ∃ S : Set ℕ, U = Prod.fst ⁻¹' S := by
  have ht : fiberTopology = (⊥ : TopologicalSpace ℕ).induced Prod.fst := by
    change (⊥ : TopologicalSpace ℕ).induced Prod.fst ⊓
      (⊤ : TopologicalSpace Bool).induced Prod.snd = _
    rw [induced_top, inf_top_eq]
  rw [ht]
  change (∃ S : Set ℕ, IsOpen[⊥] S ∧ Prod.fst ⁻¹' S = U) ↔ _
  constructor
  · rintro ⟨S, _, hS⟩
    exact ⟨S, hS.symm⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S, trivial, rfl⟩

theorem fiber_neighborhood_contains_pair (p : FiberSpace) (N : Set FiberSpace)
    (hN : Ch01.Neighborhood fiberTopology p N) : fiberPair p.1 ⊆ N := by
  obtain ⟨U, hU, hp, hUN⟩ := hN
  obtain ⟨S, rfl⟩ := (fiber_open_iff U).mp hU
  intro q hq
  apply hUN
  change q.1 ∈ S
  change q.1 = p.1 at hq
  rw [hq]
  exact hp

theorem otherInFiber_accumulation (A : Set FiberSpace) (p : FiberSpace) (hp : p ∈ A) :
    otherInFiber p ∈ @derivedSet FiberSpace fiberTopology A := by
  let : TopologicalSpace FiberSpace := fiberTopology
  rw [Ch01.derivedSet_eq_neighborhood_test]
  intro N hN
  refine ⟨p, fiber_neighborhood_contains_pair (otherInFiber p) N hN rfl, hp, ?_⟩
  simp only [mem_singleton_iff]
  intro heq
  have heq₂ := congrArg Prod.snd heq
  cases p.2 <;> simp [otherInFiber, Specs.D10Topology.Ch05.CompactVariantCounterexamples.otherInFiber] at heq₂

theorem nonempty_subset_has_accumulation (A : Set FiberSpace) (hA : A.Nonempty) :
    (@derivedSet FiberSpace fiberTopology A).Nonempty := by
  obtain ⟨p, hp⟩ := hA
  exact ⟨otherInFiber p, otherInFiber_accumulation A p hp⟩

theorem fiber_limitPointCompact : @LimitPointCompact FiberSpace fiberTopology := by
  intro A hA
  exact nonempty_subset_has_accumulation A hA.nonempty

theorem fiber_not_t1 : ¬ @T1Space FiberSpace fiberTopology := by
  intro hT
  let : TopologicalSpace FiberSpace := fiberTopology
  let : T1Space FiberSpace := hT
  have hU := (isClosed_singleton (x := ((0, false) : FiberSpace))).isOpen_compl
  obtain ⟨S, hS⟩ := (fiber_open_iff _).mp hU
  have htrue : ((0, true) : FiberSpace) ∈ ({((0, false) : FiberSpace)} : Set FiberSpace)ᶜ := by simp
  have hfalse : ((0, false) : FiberSpace) ∈ ({((0, false) : FiberSpace)} : Set FiberSpace)ᶜ := by
    rw [hS] at htrue ⊢
    exact htrue
  simp at hfalse

theorem fiber_pairs_countable_open_cover :
    (range fiberPair).Countable ∧
      (∀ n, IsOpen[fiberTopology] (fiberPair n)) ∧ ⋃ n, fiberPair n = univ := by
  refine ⟨countable_range _, fun n => (fiber_open_iff _).mpr ⟨{n}, rfl⟩, ?_⟩
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨p.1, rfl⟩

theorem fiber_pairs_no_finite_subcover (s : Finset ℕ) :
    ¬ (univ : Set FiberSpace) ⊆ ⋃ n ∈ s, fiberPair n := by
  intro h
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset s
  obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp (h (mem_univ ((n, false) : FiberSpace)))
  change n = i at hp
  exact hn (hp.symm ▸ hi)

theorem fiber_not_countablyCompact : ¬ @CountableCoverCompact FiberSpace fiberTopology := by
  intro h
  let : TopologicalSpace FiberSpace := fiberTopology
  obtain ⟨s, hs⟩ := countable_open_cover_finite_subcover h fiberPair
    fiber_pairs_countable_open_cover.2.1
    (by rw [fiber_pairs_countable_open_cover.2.2])
  exact fiber_pairs_no_finite_subcover s hs

end D10Topology.Ch05.CompactVariantCounterexamples
