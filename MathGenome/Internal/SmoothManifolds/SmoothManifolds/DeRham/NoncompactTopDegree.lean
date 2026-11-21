import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.NoncompactTopDegree
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Basic.Denumerable
import Mathlib.Tactic.Abel
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.ByContra
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.LocallyFinite
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.CompactSupport
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.MayerVietoris


import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.OrientedTopDegree
/-! Conditional derivation of the ordinary oriented noncompact clause of M11.07.
The connected escape cover, compact smooth partition pieces, locally finite
transfer construction, intrinsic open-submanifold transport, and signed integral
comparison are proved below. The final public helper has precisely the five full
upstream premises in the frozen order. The independent Spec remains the original
unconditional target; its closed implementation is reserved for the owner.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData
  Set Filter
open scoped Topology
universe u v

/-- A zero-dimensional chart has a singleton source. This applies to either
model, without a boundary or orientation assumption. -/
theorem zero_dimensional_discrete {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : ModelData.TopologicalManifold 0 a M) :
    DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro p
  obtain ⟨c, _, hp⟩ := A.covers p
  have he : c.source = {p} := by
    ext q
    constructor
    · intro hq
      exact Set.mem_singleton_iff.mpr
        (c.injOn hq hp (Subsingleton.elim _ _))
    · rintro rfl
      exact hp
  exact he ▸ c.open_source

/-- Connected zero-manifolds are compact, so the requested noncompact
zero-dimensional case is vacuous. -/
theorem zero_dimensional_compact {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M]
    (A : ModelData.TopologicalManifold 0 a M) : IsCompact (univ : Set M) := by
  letI := zero_dimensional_discrete A
  letI : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
  exact Set.finite_univ.isCompact

theorem dimension_pos_of_noncompact {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M]
    (A : ModelData.TopologicalManifold n a M)
    (hnc : ¬ IsCompact (univ : Set M)) : 0 < n := by
  cases n with
  | zero => exact False.elim (hnc (zero_dimensional_compact A))
  | succ n => exact Nat.succ_pos n

section InitialCover
variable {X : Type u} [TopologicalSpace X]

/-- Local connectedness and local compactness give connected precompact
open neighborhoods. This does not assert that arbitrary compact shells
are connected. -/
theorem connected_precompact_basis [T2Space X] [LocallyCompactSpace X]
    [LocallyConnectedSpace X] (x : X) :
    (𝓝 x).HasBasis (fun U : Set X =>
      IsOpen U ∧ x ∈ U ∧ IsConnected U ∧ IsCompact (closure U)) id := by
  apply Filter.hasBasis_iff.mpr
  intro U
  constructor
  · intro hU
    obtain ⟨L, hxL, hLU, hcL⟩ := local_compact_nhds hU
    obtain ⟨V, ⟨hoV, hxV, hconnV⟩, hVL⟩ :=
      (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp hxL
    exact ⟨V, ⟨hoV, hxV, hconnV,
      hcL.of_isClosed_subset isClosed_closure (closure_minimal hVL hcL.isClosed)⟩,
      hVL.trans hLU⟩
  · rintro ⟨V, ⟨hoV, hxV, _, _⟩, hVU⟩
    exact mem_of_superset (hoV.mem_nhds hxV) hVU

end InitialCover

/-- The initial cover used in the corrected proof exists in the original
manifold generality. It consists of connected precompact open sets; the
later-neighbor property still requires a further grouping construction. -/
theorem exists_initial_cover {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : ModelData.TopologicalManifold n a M)
    (hnc : ¬ IsCompact (univ : Set M)) :
    ∃ W : ℕ → Set M,
      (∀ j, IsOpen (W j) ∧ IsConnected (W j) ∧ IsCompact (closure (W j))) ∧
      (⋃ j, W j) = univ ∧ LocallyFinite W := by
  classical
  letI := A.hausdorff
  letI := A.secondCountable
  letI := _root_.SmoothManifolds.TopologicalManifold.locallyCompactSpace A
  letI := _root_.SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace A
  obtain ⟨ι, c, r, hr, hcover, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
      (fun x : M => connected_precompact_basis x)
  let W : ι → Set M := fun i => r i
  have hW (i : ι) : IsOpen (W i) ∧ IsConnected (W i) ∧ IsCompact (closure (W i)) :=
    ⟨(hr i).1, (hr i).2.2.1, (hr i).2.2.2⟩
  letI : Countable ι := Set.countable_univ_iff.mp
    (hlf.countable_univ (fun i => (hW i).2.1.nonempty))
  letI : Infinite ι := not_finite_iff_infinite.mp (by
    intro hf
    letI := hf
    apply hnc
    apply (isCompact_iUnion (fun i => (hW i).2.2)).of_isClosed_subset isClosed_univ
    intro x _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨i, subset_closure hi⟩)
  obtain ⟨e⟩ : Nonempty (ℕ ≃ ι) := nonempty_equiv_of_countable
  refine ⟨fun j => W (e j), fun j => hW (e j), ?_, hlf.comp_injective e.injective⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨j, rfl⟩ := e.surjective i
  exact mem_iUnion.mpr ⟨j, hi⟩

section CoverGraph
variable {X : Type*} [TopologicalSpace X] {ι : Type*}
/-- Finite chains of intersecting cover members, allowing the empty chain. -/
def CoverLinked (W : ι → Set X) (i j : ι) : Prop :=
  Relation.ReflTransGen (fun i j => (W i ∩ W j).Nonempty) i j

/-- Reachable cover members have a nonempty clopen union, hence cover the
connected base. In particular every two members are linked. -/
theorem cover_linked_of_connected [PreconnectedSpace X] (W : ι → Set X)
    (ho : ∀ i, IsOpen (W i)) (hne : ∀ i, (W i).Nonempty)
    (hcover : (⋃ i, W i) = univ) (i j : ι) : CoverLinked W i j := by
  let U : Set X := ⋃ k : {k // CoverLinked W i k}, W k.val
  have hoU : IsOpen U := isOpen_iUnion (fun k => ho k.val)
  have he : Uᶜ = ⋃ k : {k // ¬ CoverLinked W i k}, W k.val := by
    ext p
    constructor
    · intro hp
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
      have hnot : ¬ CoverLinked W i k := by
        intro hik
        exact hp (mem_iUnion.mpr ⟨⟨k,hik⟩,hk⟩)
      exact mem_iUnion.mpr ⟨⟨k,hnot⟩,hk⟩
    · rintro hp hpU
      obtain ⟨⟨k,hik⟩,hpk⟩ := mem_iUnion.mp hpU
      obtain ⟨⟨l,hil⟩,hpl⟩ := mem_iUnion.mp hp
      exact hil (Relation.ReflTransGen.tail hik ⟨p,hpk,hpl⟩)
  have hcU : IsClosed U := isOpen_compl_iff.mp (he ▸ isOpen_iUnion (fun k => ho k.val))
  have hnU : U.Nonempty := by
    obtain ⟨p,hp⟩ := hne i
    exact ⟨p, mem_iUnion.mpr ⟨⟨i,Relation.ReflTransGen.refl⟩,hp⟩⟩
  have hU : U = univ := IsClopen.eq_univ ⟨hcU,hoU⟩ hnU
  obtain ⟨p,hpj⟩ := hne j
  have hpU : p ∈ U := hU.symm ▸ mem_univ p
  obtain ⟨⟨k,hik⟩,hpk⟩ := mem_iUnion.mp hpU
  exact Relation.ReflTransGen.tail hik ⟨p,hpk,hpj⟩

/-- Compact closure and local finiteness give finite intersection degree. -/
theorem finite_cover_neighbors (W : ι → Set X) (hlf : LocallyFinite W)
    (hc : ∀ i, IsCompact (closure (W i))) (i : ι) :
    {j | (W i ∩ W j).Nonempty}.Finite := by
  apply (hlf.finite_nonempty_inter_compact (hc i)).subset
  rintro j ⟨p,hpi,hpj⟩
  exact ⟨p,hpj,subset_closure hpi⟩

end CoverGraph

section Quotient
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

/-- There is no closedness restriction on a top form. -/
theorem top_form_closed (ω : K.forms n) : ω ∈ K.closed n := by
  apply Subtype.ext
  funext p
  exact ExteriorAlgebraResults.fields_above_dimension C (n+1)
    (Nat.lt_succ_self n) (K.d n ω).val p

/-- Algebraic reduction from primitives of all top forms to the actual
ordinary quotient. No compact-support quotient is substituted. -/
theorem cohomology_subsingleton_of_all_exact (k : ℕ)
    (h : ∀ ω : K.forms k, ω ∈ K.exact k) : Subsingleton (K.Cohomology k) := by
  have hz (x : K.Cohomology k) : x = 0 := by
    obtain ⟨ω, rfl⟩ := (K.boundaries k).mkQ_surjective x
    exact (DeRhamResults.class_zero_iff_exact K k ω).mpr (h ω.val)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem all_top_exact_iff_cohomology_subsingleton :
    (∀ ω : K.forms n, ω ∈ K.exact n) ↔ Subsingleton (K.Cohomology n) := by
  constructor
  · exact cohomology_subsingleton_of_all_exact K n
  · intro h ω
    letI := h
    exact (DeRhamResults.class_zero_iff_exact K n ⟨ω, top_form_closed K ω⟩).mp
      (Subsingleton.elim _ _)

/-- Exactness in the compact subcomplex supplies an ordinary primitive,
by the actual chain-map commutation law. -/
theorem inclusion_exact {U : TopologicalSpace.Opens M}
    (D : CompactCalculus K U) (k : ℕ) (ω : D.complex.Obj k)
    (hω : ω ∈ D.complex.exact k) : D.inclusion.map k ω ∈ K.exact k := by
  cases k with
  | zero =>
    have hzero : ω = 0 := by simpa [Cochain.exact] using hω
    simp [hzero, Calculus.exact]
  | succ k =>
    obtain ⟨β, rfl⟩ := hω
    exact ⟨D.inclusion.map k β, D.inclusion.comm k β⟩

end Quotient

section LocallyFiniteSum
variable {X : Type u} [TopologicalSpace X] {E : X → Type v}
  [∀ x, AddCommGroup (E x)] {ι : Type*} (f : ι → ∀ x, E x)

/-- The dependent pointwise sum agrees with a finite sum on a neighborhood.
The finite set can be chosen to be exactly the closed supports containing x. -/
theorem locallyFinite_sum_germ
    (hlf : LocallyFinite (fun i => ModelData.sectionSupport (f i))) (x : X) :
    ∃ s : Finset ι, (∀ i, i ∈ s ↔ x ∈ ModelData.sectionSupport (f i)) ∧
      ∀ᶠ y in 𝓝 x, (∑ᶠ i, f i y) = ∑ i ∈ s, f i y := by
  classical
  let s := (hlf.point_finite x).toFinset
  refine ⟨s, fun i => Set.Finite.mem_toFinset _, ?_⟩
  filter_upwards [hlf.eventually_subset (fun _ => isClosed_closure) x] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact (hlf.point_finite x).mem_toFinset.mpr (hy (subset_closure hi))

end LocallyFiniteSum

section SmoothSum
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B) {ι : Type v} (k : ℕ) (ω : ι → K.forms k)

/-- Summing smooth sections needs local finiteness of their base supports,
not convergence in any invented norm on the space of global sections. -/
theorem finsum_form
    (hlf : LocallyFinite (fun i => ModelData.sectionSupport (ω i).val)) :
    IsForm (B k) (fun p => ∑ᶠ i, (ω i).val p) := by
  letI := (cotangentSpace C).topology
  letI := (B k).space.topology
  intro p
  obtain ⟨s, _, hs⟩ := locallyFinite_sum_germ (fun i => (ω i).val) hlf p
  have hsm := ExteriorDerivativeResults.sum_form C k (B k) s
    (fun i => (ω i).val) (fun i _ => (K.mem_forms _ _).mp (ω i).property)
  apply manifoldContDiffAt_congr (hsm p)
  filter_upwards [hs] with q hq
  congr 1
  simpa only [Finset.sum_apply] using hq.symm

def finsumForm
    (hlf : LocallyFinite (fun i => ModelData.sectionSupport (ω i).val)) : K.forms k :=
  ⟨fun p => ∑ᶠ i, (ω i).val p, (K.mem_forms _ _).mpr (finsum_form K k ω hlf)⟩

/-- Exterior differentiation commutes with this locally finite sum. -/
theorem d_finsumForm
    (hlf : LocallyFinite (fun i => ModelData.sectionSupport (ω i).val)) (p : M) :
    (K.d k (finsumForm K k ω hlf)).val p = ∑ᶠ i, (K.d k (ω i)).val p := by
  classical
  obtain ⟨s, hmem, hs⟩ := locallyFinite_sum_germ (fun i => (ω i).val) hlf p
  have hloc : ∀ᶠ q in 𝓝 p, (finsumForm K k ω hlf).val q = (∑ i ∈ s, (ω i).val) q := by
    simpa only [finsumForm, Finset.sum_apply] using hs
  have he := ExteriorDerivativeResults.axioms_locality C B K.D K.axioms k
    (finsumForm K k ω hlf).val (∑ i ∈ s, (ω i).val)
    ((K.mem_forms _ _).mp (finsumForm K k ω hlf).property)
    (ExteriorDerivativeResults.sum_form C k (B k) s (fun i => (ω i).val)
      (fun i _ => (K.mem_forms _ _).mp (ω i).property)) p hloc
  change K.D k _ p = _
  rw [he, ExteriorDerivativeResults.axioms_sum C B K.D K.axioms k s
    (fun i => (ω i).val) (fun i _ => (K.mem_forms _ _).mp (ω i).property)]
  simp only [Finset.sum_apply]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply (hmem i).mpr
  exact ExteriorDerivativeResults.derivative_support C k _ _
    (K.coordinates k (ω i).val ((K.mem_forms _ _).mp (ω i).property))
    (subset_closure hi)

end SmoothSum

section TransferAlgebra
variable {A : Type*} [AddCommGroup A]

/-- The incoming transfers at stage j. The later-neighbor inequality ensures
that these are ALL predecessors, not an arbitrary truncation of a fiber. -/
def incomingTransfer (next : ℕ → ℕ) (t : ℕ → A) (j : ℕ) : A :=
  ∑ i ∈ (Finset.range j).filter (fun i => next i = j), t i

theorem incomingTransfer_eq_fiber (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (t : ℕ → A) (j : ℕ) :
    incomingTransfer next t j = ∑ᶠ i : {i // next i = j}, t i.val := by
  classical
  rw [finsum_subtype_eq_finsum_cond (f := t) (fun i => next i = j)]
  symm
  apply finsum_cond_eq_sum_of_cond_iff
  intro i _
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨h ▸ hn i, h⟩
  · exact And.right

/-- Grouping transfers preserves finite support at each point. This is why
the cancellation below is legitimate for finite sums rather than a
conditionally convergent rearrangement. -/
theorem incomingTransfer_finite_support (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (t : ℕ → A) (ht : Function.HasFiniteSupport t) :
    Function.HasFiniteSupport (incomingTransfer next t) := by
  classical
  apply (ht.image next).subset
  intro j hj
  by_contra h
  have hz : ∀ i : {i // next i = j}, t i.val = 0 := by
    intro i
    by_contra hi
    exact h ⟨i.val, hi, i.property⟩
  exact hj (by rw [incomingTransfer_eq_fiber next hn]; simp [hz])

theorem finsum_incomingTransfer (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (t : ℕ → A) (ht : Function.HasFiniteSupport t) :
    ∑ᶠ j, incomingTransfer next t j = ∑ᶠ i, t i := by
  classical
  have heq (j : ℕ) : incomingTransfer next t j =
      ∑ i ∈ ht.toFinset with next i = j, t i := by
    rw [incomingTransfer_eq_fiber next hn,
      finsum_subtype_eq_finsum_cond (f := t) (fun i => next i = j)]
    apply finsum_cond_eq_sum_of_cond_iff
    intro i hi
    simp [ht.mem_toFinset.mpr hi]
  simp_rw [heq]
  rw [finsum_sum_filter next ht.toFinset t]
  exact (finsum_eq_sum _ ht).symm

/-- Each outgoing term appears once as an incoming term, even if several
earlier stages transfer to the same later stage. -/
theorem finsum_transfer_balance (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (a t : ℕ → A) (ha : Function.HasFiniteSupport a)
    (ht : Function.HasFiniteSupport t) :
    (∑ᶠ j, (a j + incomingTransfer next t j - t j)) = ∑ᶠ j, a j := by
  have hi := incomingTransfer_finite_support next hn t ht
  calc
    _ = (∑ᶠ j, (a j + incomingTransfer next t j)) - ∑ᶠ j, t j := by
      simpa only [Pi.add_apply] using finsum_sub_distrib (ha.add hi) ht
    _ = ((∑ᶠ j, a j) + ∑ᶠ j, incomingTransfer next t j) - ∑ᶠ j, t j := by
      rw [finsum_add_distrib ha hi]
    _ = _ := by rw [finsum_incomingTransfer next hn t ht]; abel

end TransferAlgebra

section TransferCoefficients

/-- The source's integral recurrence is well founded because only indices
strictly less than j occur in the jth incoming sum. -/
def transferCoefficients (next : ℕ → ℕ) (mass : ℕ → ℝ) (j : ℕ) : ℝ :=
  mass j + ∑ i : Fin j,
    if next i.val = j then transferCoefficients next mass i.val else 0
termination_by j

theorem transferCoefficients_eq (next : ℕ → ℕ) (mass : ℕ → ℝ) (j : ℕ) :
    transferCoefficients next mass j = mass j +
      incomingTransfer next (transferCoefficients next mass) j := by
  classical
  rw [transferCoefficients]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun i => if next i = j then transferCoefficients next mass i else 0) j).trans
      (by simp [incomingTransfer, Finset.sum_filter])

theorem corrected_mass_zero (next : ℕ → ℕ) (mass : ℕ → ℝ) (j : ℕ) :
    mass j + incomingTransfer next (transferCoefficients next mass) j -
      transferCoefficients next mass j = 0 := by
  rw [← transferCoefficients_eq]
  exact sub_self _

end TransferCoefficients

section TransferGluing
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B) (k : ℕ)

/-- The analytic and algebraic last step of the source proof, with all local
forms and all support hypotheses explicit. This lemma does not assert the
existence of the geometric cover or its local primitives. -/
theorem exact_of_locallyFinite_transfers (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (ω : K.forms (k+1)) (η τ : ℕ → K.forms (k+1)) (β : ℕ → K.forms k)
    (hη : LocallyFinite (fun j => ModelData.sectionSupport (η j).val))
    (hτ : LocallyFinite (fun j => ModelData.sectionSupport (τ j).val))
    (hβ : LocallyFinite (fun j => ModelData.sectionSupport (β j).val))
    (hω : ∀ p, (∑ᶠ j, (η j).val p) = ω.val p)
    (hd : ∀ j, K.d k (β j) = η j + incomingTransfer next τ j - τ j) :
    ω ∈ K.exact (k+1) := by
  refine ⟨finsumForm K k β hβ, ?_⟩
  apply Subtype.ext
  funext p
  rw [d_finsumForm K k β hβ]
  have hd' (j : ℕ) : (K.d k (β j)).val p =
      (η j).val p + incomingTransfer next (fun i => (τ i).val p) j - (τ j).val p := by
    rw [hd j]
    simp [incomingTransfer, Finset.sum_apply]
  simp_rw [hd']
  rw [finsum_transfer_balance next hn (fun j => (η j).val p)
    (fun j => (τ j).val p)
    ((hη.point_finite p).subset (fun j hj => subset_closure hj))
    ((hτ.point_finite p).subset (fun j hj => subset_closure hj))]
  exact hω p

end TransferGluing

open OrientationData BoundaryData LocalIntegrationData GlobalIntegrationData

/-- A specialization of the full frozen compact-support premise, keeping
its integral and its actual compact complex. This is an intermediate lemma;
it does not assert the ordinary noncompact conclusion. -/
theorem compact_exact_of_zero_integral
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M) (hb : intrinsicBoundary S = ∅)
    (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (ω : D.complex.Obj n) (μ : CompactTopForm S)
    (hμ : μ.field = (D.inclusion.map n ω).val) (hz : I μ = 0) :
    ω ∈ D.complex.exact n := by
  obtain ⟨ν, hν, he⟩ := hExact S hb o C B K D I hI ω
  have hνμ : ν = μ := by
    have hfield : ν.field = μ.field := hν.trans hμ.symm
    cases ν
    cases μ
    congr 1
  exact he.mpr (hνμ ▸ hz)


end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace SmoothManifolds.NoncompactTopDegreeResults.GraphPruning
attribute [local instance] Classical.propDecidable
variable {V : Type*} (r : V → V → Prop)

def edgeIn (S : Set V) (a b : V) : Prop := a ∈ S ∧ b ∈ S ∧ r a b

def linked (S : Set V) (a b : V) : Prop :=
  a ∈ S ∧ b ∈ S ∧ Relation.ReflTransGen (edgeIn r S) a b

def comp (S : Set V) (a : V) : Set V := {b | linked r S a b}

lemma linked_refl {S : Set V} {a : V} (ha : a ∈ S) : linked r S a a :=
  ⟨ha, ha, .refl⟩
lemma linked_trans {S : Set V} {a b c : V}
    (hab : linked r S a b) (hbc : linked r S b c) : linked r S a c :=
  ⟨hab.1, hbc.2.1, hab.2.2.trans hbc.2.2⟩
lemma linked_symm (hsym : ∀ a b, r a b → r b a) {S : Set V} {a b : V}
    (hab : linked r S a b) : linked r S b a := by
  refine ⟨hab.2.1, hab.1, ?_⟩
  have hp := hab.2.2
  induction hp with
  | refl => exact .refl
  | tail hp he ih => exact (ih ⟨hab.1, he.1, hp⟩).head ⟨he.2.1, he.1, hsym _ _ he.2.2⟩
lemma linked_mono {S T : Set V} (hST : S ⊆ T) {a b : V}
    (hab : linked r S a b) : linked r T a b :=
  ⟨hST hab.1, hST hab.2.1, Relation.ReflTransGen.mono (fun _ _ he =>
    ⟨hST he.1, hST he.2.1, he.2.2⟩) a b hab.2.2⟩
lemma comp_eq (hsym : ∀ a b, r a b → r b a) {S : Set V} {a b : V}
    (hab : linked r S a b) : comp r S a = comp r S b := by
  ext x
  constructor
  · exact fun hx => linked_trans r (linked_symm r hsym hab) hx
  · exact fun hx => linked_trans r hab hx

/-- A chain from a deleted vertex to another vertex has a last departure.
The tail after this departure avoids the deleted vertex. -/
lemma last_departure {S : Set V} {p x : V} (hpx : linked r S p x) (hxp : x ≠ p) :
    ∃ y, r p y ∧ linked r (S \ {p}) y x := by
  have hp := hpx.2.2
  induction hp with
  | refl => exact False.elim (hxp rfl)
  | @tail b c hpb he ih =>
      by_cases hbp : b = p
      · subst b
        exact ⟨c, he.2.2, linked_refl r ⟨he.2.1, hxp⟩⟩
      · obtain ⟨y, hpy, hyb⟩ := ih ⟨hpx.1, he.1, hpb⟩ hbp
        exact ⟨y, hpy, ⟨hyb.1, ⟨he.2.1, hxp⟩,
          hyb.2.2.tail ⟨hyb.2.1, ⟨he.2.1, hxp⟩, he.2.2⟩⟩⟩

/-- Paths not linked to the deleted root remain paths after its deletion. -/
lemma linked_delete_of_not_linked (hsym : ∀ a b, r a b → r b a)
    {S : Set V} {p x y : V} (hxy : linked r S x y)
    (hxp : ¬ linked r S x p) : linked r (S \ {p}) x y := by
  have hstart : x ∈ S \ {p} := ⟨hxy.1, fun h => hxp (h ▸ linked_refl r hxy.1)⟩
  have hp := hxy.2.2
  induction hp with
  | refl => exact linked_refl r hstart
  | @tail b c hxb he ih =>
      have hcp : c ≠ p := by
        intro hc
        apply hxp
        exact ⟨hxy.1, hc ▸ he.2.1, hc ▸ hxb.tail he⟩
      have ih := ih ⟨hxy.1, he.1, hxb⟩
      exact ⟨ih.1, ⟨he.2.1, hcp⟩,
        ih.2.2.tail ⟨ih.2.1, ⟨he.2.1, hcp⟩, he.2.2⟩⟩

/-- In a graph whose components are infinite, each finite component exposed
by deleting one root meets that root. -/
lemma finite_component_meets_root (hsym : ∀ a b, r a b → r b a)
    {S : Set V} (hinf : ∀ x ∈ S, (comp r S x).Infinite) {p x : V}
    (hx : x ∈ S \ {p}) (hfin : (comp r (S \ {p}) x).Finite) :
    ∃ y, r p y ∧ linked r (S \ {p}) y x := by
  have hxp : linked r S x p := by
    by_contra hn
    apply hinf x hx.1
    exact hfin.subset (fun y hy => linked_delete_of_not_linked r hsym hy hn)
  exact last_departure r (linked_symm r hsym hxp) hx.2

/-- One pruning block consists of a root and all finite components exposed
by deleting it. It is finite because each such component meets a finite
neighbor set. -/
def block (S : Set V) (p : V) : Set V :=
  {p} ∪ {x | x ∈ S \ {p} ∧ (comp r (S \ {p}) x).Finite}

lemma block_subset {S : Set V} {p : V} (hp : p ∈ S) : block r S p ⊆ S := by
  rintro x (h | h)
  · exact mem_singleton_iff.mp h ▸ hp
  · exact h.1.1

lemma block_finite (hsym : ∀ a b, r a b → r b a)
    (hdeg : ∀ p, {y | r p y}.Finite) {S : Set V}
    (hinf : ∀ x ∈ S, (comp r S x).Infinite) (p : V) :
    (block r S p).Finite := by
  let N : Set V := {y | r p y ∧ y ∈ S \ {p} ∧ (comp r (S \ {p}) y).Finite}
  have hN : N.Finite := (hdeg p).subset (fun _ h => h.1)
  have hU : (⋃ y ∈ N, comp r (S \ {p}) y).Finite :=
    hN.biUnion (fun y hy => hy.2.2)
  apply (finite_singleton p |>.union hU).subset
  rintro x (h | ⟨hx, hfin⟩)
  · exact Or.inl h
  · obtain ⟨y, hpy, hyx⟩ := finite_component_meets_root r hsym hinf hx hfin
    have he := comp_eq r hsym hyx
    exact Or.inr (mem_iUnion.mpr ⟨y, mem_iUnion.mpr
      ⟨⟨hpy, hyx.1, he.symm ▸ hfin⟩, hyx⟩⟩)

lemma block_component_closed (hsym : ∀ a b, r a b → r b a)
    {S : Set V} {p x y : V} (hx : x ∈ S \ {p})
    (hxy : linked r (S \ {p}) x y) :
    x ∈ block r S p ↔ y ∈ block r S p := by
  have he := comp_eq r hsym hxy
  constructor
  · rintro (h | h)
    · exact False.elim (hx.2 (mem_singleton_iff.mp h))
    · exact Or.inr ⟨hxy.2.1, he ▸ h.2⟩
  · rintro (h | h)
    · exact False.elim (hxy.2.1.2 (mem_singleton_iff.mp h))
    · exact Or.inr ⟨hx, he.symm ▸ h.2⟩

lemma residual_components_infinite (hsym : ∀ a b, r a b → r b a)
    {S : Set V} {p : V} :
    ∀ x ∈ S \ block r S p, (comp r (S \ block r S p) x).Infinite := by
  intro x hx
  have hxp : x ≠ p := fun h => hx.2 (Or.inl (mem_singleton_iff.mpr h))
  have hxd : x ∈ S \ {p} := ⟨hx.1, hxp⟩
  have hinf : (comp r (S \ {p}) x).Infinite := by
    intro hfin
    exact hx.2 (Or.inr ⟨hxd, hfin⟩)
  apply hinf.mono
  intro y hy
  have hnot (z : V) (hz : linked r (S \ {p}) x z) : z ∉ block r S p :=
    fun hzB => hx.2 ((block_component_closed r hsym hxd hz).mpr hzB)
  refine ⟨hx, ⟨hy.2.1.1, hnot y hy⟩, ?_⟩
  have hp := hy.2.2
  induction hp with
  | refl => exact .refl
  | @tail b c hxb he ih =>
      have hxb' : linked r (S \ {p}) x b := ⟨hxd, he.1, hxb⟩
      have hxc' : linked r (S \ {p}) x c := ⟨hxd, he.2.1, hxb.tail he⟩
      exact (ih hxb').tail ⟨⟨he.1.1, hnot b hxb'⟩, ⟨he.2.1.1, hnot c hxc'⟩, he.2.2⟩

lemma linked_of_comp_subset {S T : Set V} {a b : V}
    (hab : linked r S a b) (hT : comp r S a ⊆ T) : linked r T a b := by
  have haT := hT (linked_refl r hab.1)
  refine ⟨haT, hT hab, ?_⟩
  have hp := hab.2.2
  induction hp with
  | refl => exact .refl
  | @tail c d hac he ih =>
      have hac' : linked r S a c := ⟨hab.1, he.1, hac⟩
      have had' : linked r S a d := ⟨hab.1, he.2.1, hac.tail he⟩
      exact (ih hac').tail ⟨hT hac', hT had', he.2.2⟩

lemma block_linked (hsym : ∀ a b, r a b → r b a)
    {S : Set V} (hinf : ∀ x ∈ S, (comp r S x).Infinite)
    {p : V} (hp : p ∈ S) :
    ∀ x ∈ block r S p, linked r (block r S p) p x := by
  intro x hx
  have hpB : p ∈ block r S p := Or.inl (mem_singleton p)
  rcases hx with hx | ⟨hxd, hfin⟩
  · have hxp := mem_singleton_iff.mp hx
    subst x
    exact linked_refl r hpB
  · obtain ⟨y, hpy, hyx⟩ := finite_component_meets_root r hsym hinf hxd hfin
    have hsub : comp r (S \ {p}) y ⊆ block r S p := by
      intro z hyz
      have he := comp_eq r hsym (linked_trans r (linked_symm r hsym hyx) hyz)
      exact Or.inr ⟨hyz.2.1, he ▸ hfin⟩
    have hyB := hsub (linked_refl r hyx.1)
    exact linked_trans r ⟨hpB, hyB, .single ⟨hpB, hyB, hpy⟩⟩
      (linked_of_comp_subset r hyx hsub)

lemma block_has_remaining_neighbor (hsym : ∀ a b, r a b → r b a)
    (hdeg : ∀ p, {y | r p y}.Finite) {S : Set V}
    (hinf : ∀ x ∈ S, (comp r S x).Infinite) {p : V} (hp : p ∈ S) :
    ∃ y ∈ S \ block r S p, r p y := by
  have hfin := block_finite r hsym hdeg hinf p
  have hex : ∃ x ∈ comp r S p, x ∉ block r S p := by
    by_contra! hn
    exact hinf p hp (hfin.subset hn)
  obtain ⟨x, hpx, hxB⟩ := hex
  have hxp : x ≠ p := fun h => hxB (Or.inl (mem_singleton_iff.mpr h))
  obtain ⟨y, hpy, hyx⟩ := last_departure r hpx hxp
  refine ⟨y, ⟨hyx.1.1, ?_⟩, hpy⟩
  intro hyB
  exact hxB ((block_component_closed r hsym hyx.1 hyx).mp hyB)

section Sequence
variable {r : ℕ → ℕ → Prop}
  (hsym : ∀ a b, r a b → r b a)
  (hdeg : ∀ p, {y | r p y}.Finite)

private def State : Type := {S : Set ℕ // S.Nonempty ∧ ∀ x ∈ S, (comp r S x).Infinite}
private def root (s : State (r := r)) : ℕ := Nat.find s.property.1
private lemma root_mem (s : State (r := r)) : root s ∈ s.val := Nat.find_spec s.property.1
private def step (s : State (r := r)) : State (r := r) :=
  ⟨s.val \ block r s.val (root s),
    ⟨by
      obtain ⟨y, hy, _⟩ := block_has_remaining_neighbor r hsym hdeg s.property.2 (root_mem s)
      exact ⟨y, hy⟩,
      residual_components_infinite r hsym⟩⟩
private def stage (s : State (r := r)) : ℕ → State (r := r)
  | 0 => s
  | n+1 => step hsym hdeg (stage s n)
private def groups (s : State (r := r)) (n : ℕ) : Set ℕ :=
  block r (stage hsym hdeg s n).val (root (stage hsym hdeg s n))
private lemma stage_succ (s : State (r := r)) (n : ℕ) :
    (stage hsym hdeg s (n+1)).val = (stage hsym hdeg s n).val \ groups hsym hdeg s n := rfl
private lemma stage_antitone (s : State (r := r)) :
    Antitone (fun n => (stage hsym hdeg s n).val) := by
  apply antitone_nat_of_succ_le
  intro n
  exact sdiff_subset
private lemma stage_no_small (s : State (r := r)) (n : ℕ) :
    ∀ x < n, x ∉ (stage hsym hdeg s n).val := by
  induction n with
  | zero => omega
  | succ n ih =>
      intro x hx hxs
      have hxs' : x ∈ (stage hsym hdeg s n).val := hxs.1
      by_cases hxn : x < n
      · exact ih x hxn hxs'
      · have hxn : x = n := by omega
        subst x
        have hrootle : root (stage hsym hdeg s n) ≤ n :=
          Nat.find_min' _ hxs'
        have hrootge : n ≤ root (stage hsym hdeg s n) := by
          by_contra! hn
          exact ih _ hn (root_mem _)
        have hr : root (stage hsym hdeg s n) = n := by omega
        exact hxs.2 (Or.inl (mem_singleton_iff.mpr hr.symm))
private lemma groups_mem_iff (s : State (r := r)) (n x : ℕ) :
    x ∈ groups hsym hdeg s n ↔
      x ∈ (stage hsym hdeg s n).val ∧ x ∉ (stage hsym hdeg s (n+1)).val := by
  have hsub : groups hsym hdeg s n ⊆ (stage hsym hdeg s n).val :=
    block_subset r (root_mem _)
  rw [stage_succ]
  constructor
  · exact fun hx => ⟨hsub hx, fun hn => hn.2 hx⟩
  · rintro ⟨hx, hn⟩
    by_contra hxg
    exact hn ⟨hx, hxg⟩
private lemma groups_disjoint (s : State (r := r)) :
    Pairwise (fun i j => Disjoint (groups hsym hdeg s i) (groups hsym hdeg s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  have hi := (groups_mem_iff hsym hdeg s i x).mp hxi
  have hj := (groups_mem_iff hsym hdeg s j x).mp hxj
  by_cases hlt : i < j
  · exact hi.2 (stage_antitone hsym hdeg s (by omega) hj.1)
  · exact hj.2 (stage_antitone hsym hdeg s (by omega) hi.1)
private lemma groups_cover (s : State (r := r)) :
    (⋃ n, groups hsym hdeg s n) = s.val := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact stage_antitone hsym hdeg s (Nat.zero_le n)
      ((groups_mem_iff hsym hdeg s n x).mp hn).1
  · intro x hx
    have hex : ∃ n, x ∉ (stage hsym hdeg s n).val :=
      ⟨x+1, stage_no_small hsym hdeg s (x+1) x (Nat.lt_succ_self x)⟩
    let n := Nat.find hex
    have hn : x ∉ (stage hsym hdeg s n).val := Nat.find_spec hex
    have hnpos : 0 < n := by
      by_contra! hn0
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn0
      exact hn (hn0.symm ▸ hx)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    change x ∉ (stage hsym hdeg s n).val at hn
    rw [hm] at hn
    apply mem_iUnion.mpr
    refine ⟨m, (groups_mem_iff hsym hdeg s m x).mpr ⟨?_, hn⟩⟩
    by_contra hxprev
    have hmin := Nat.find_min' hex hxprev
    omega

include hsym hdeg in
/-- Every infinite connected locally finite graph on the naturals admits a
partition into finite connected blocks, indexed so each block has an edge
to a strictly later block. -/
theorem exists_finite_connected_grouping
    (hconn : ∀ i j, Relation.ReflTransGen r i j) :
    ∃ G : ℕ → Set ℕ,
      (∀ j, (G j).Finite ∧ ∃ p ∈ G j, ∀ x ∈ G j, linked r (G j) p x) ∧
      (⋃ j, G j) = univ ∧ Pairwise (fun i j => Disjoint (G i) (G j)) ∧
      ∀ j, ∃ k > j, ∃ x ∈ G j, ∃ y ∈ G k, r x y := by
  have hinf : ∀ x ∈ (univ : Set ℕ), (comp r univ x).Infinite := by
    intro x hx
    apply Set.infinite_univ.mono
    intro y _
    exact ⟨mem_univ _, mem_univ _, Relation.ReflTransGen.mono
      (fun a b hab => ⟨mem_univ _, mem_univ _, hab⟩) x y (hconn x y)⟩
  let s : State (r := r) := ⟨univ, ⟨univ_nonempty, hinf⟩⟩
  refine ⟨groups hsym hdeg s, ?_, groups_cover hsym hdeg s,
    groups_disjoint hsym hdeg s, ?_⟩
  · intro j
    let sj := stage hsym hdeg s j
    refine ⟨block_finite r hsym hdeg sj.property.2 (root sj), root sj,
      Or.inl (mem_singleton _), ?_⟩
    exact block_linked r hsym sj.property.2 (root_mem sj)
  · intro j
    let sj := stage hsym hdeg s j
    obtain ⟨y, hy, hpy⟩ :=
      block_has_remaining_neighbor r hsym hdeg sj.property.2 (root_mem sj)
    have hyinit : y ∈ s.val := mem_univ _
    rw [← groups_cover hsym hdeg s] at hyinit
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hyinit
    have hjk : j < k := by
      by_contra! hk
      have hnot := ((groups_mem_iff hsym hdeg s k y).mp hyk).2
      exact hnot (stage_antitone hsym hdeg s (Nat.add_le_add_right hk 1) hy)
    exact ⟨k, hjk, root sj, Or.inl (mem_singleton _), y, hyk, hpy⟩

end Sequence

end SmoothManifolds.NoncompactTopDegreeResults.GraphPruning

set_option autoImplicit false
noncomputable section
open Set
namespace SmoothManifolds.NoncompactTopDegreeResults
/-- Assigning each original member to at most one group preserves local
finiteness, without any bound on the sizes of the groups. -/
theorem locallyFinite_grouped {X ι κ : Type*} [TopologicalSpace X]
    (W : ι → Set X) (hW : LocallyFinite W) (G : κ → Set ι)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) :
    LocallyFinite (fun j => ⋃ i ∈ G j, W i) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hW x
  refine ⟨U, hxU, ?_⟩
  have hfiber (i : ι) : {j | i ∈ G j}.Finite := by
    apply Set.Subsingleton.finite
    intro j hj k hk
    by_contra hjk
    exact Set.disjoint_left.mp (hG hjk) hj hk
  apply (hU.biUnion (fun i _ => hfiber i)).subset
  rintro j ⟨y, hy, hyU⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨i, ⟨y, hyi, hyU⟩, hi⟩
end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData Set Filter
open scoped Topology
universe u

/-- Finite graph groups give connected precompact open unions. -/
theorem connected_precompact_group_unions
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (W : ℕ → Set X)
    (hW : ∀ i, IsOpen (W i) ∧ IsConnected (W i) ∧ IsCompact (closure (W i)))
    (G : ℕ → Set ℕ)
    (hG : ∀ j, (G j).Finite ∧ ∃ p ∈ G j,
      ∀ x ∈ G j, GraphPruning.linked (fun i l => (W i ∩ W l).Nonempty) (G j) p x) :
    ∀ j, IsOpen (⋃ i ∈ G j, W i) ∧ IsConnected (⋃ i ∈ G j, W i) ∧
      IsCompact (closure (⋃ i ∈ G j, W i)) := by
  intro j
  obtain ⟨hfin,p,hp,hconn⟩ := hG j
  have hsym : ∀ i l, (W i ∩ W l).Nonempty → (W l ∩ W i).Nonempty := by
    intro i l h
    exact ⟨h.choose,h.choose_spec.2,h.choose_spec.1⟩
  refine ⟨isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (hW i).1)), ?_, ?_⟩
  · apply IsConnected.biUnion_of_reflTransGen ⟨p,hp⟩ (fun i _ => (hW i).2.1)
    intro i hi l hl
    have hpath := GraphPruning.linked_trans _
      (GraphPruning.linked_symm _ hsym (hconn i hi)) (hconn l hl)
    exact Relation.ReflTransGen.mono (fun _ _ he => ⟨he.2.2,he.1⟩) i l hpath.2.2
  · have hc : IsCompact (⋃ i ∈ G j, closure (W i)) :=
      hfin.isCompact_biUnion (fun i _ => (hW i).2.2)
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hc.isClosed
    rintro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i,hi,subset_closure hxi⟩

/-- The complete connected escape cover from the corrected source argument.
No connectedness of arbitrary compact shells is presumed. -/
theorem exists_escape_cover {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [PreconnectedSpace M]
    (A : ModelData.TopologicalManifold n a M)
    (hnc : ¬ IsCompact (univ : Set M)) :
    ∃ V : ℕ → Set M,
      (∀ j, IsOpen (V j) ∧ IsConnected (V j) ∧ IsCompact (closure (V j))) ∧
      (⋃ j, V j) = univ ∧ LocallyFinite V ∧
      ∀ j, ∃ l > j, (V j ∩ V l).Nonempty := by
  classical
  letI := A.hausdorff
  obtain ⟨W,hW,hcover,hlf⟩ := exists_initial_cover A hnc
  let r : ℕ → ℕ → Prop := fun i j => (W i ∩ W j).Nonempty
  have hsym : ∀ i j, r i j → r j i := by
    rintro i j ⟨p,hpi,hpj⟩
    exact ⟨p,hpj,hpi⟩
  have hdeg : ∀ i, {j | r i j}.Finite :=
    finite_cover_neighbors W hlf (fun i => (hW i).2.2)
  have hconn : ∀ i j, Relation.ReflTransGen r i j :=
    cover_linked_of_connected W (fun i => (hW i).1)
      (fun i => (hW i).2.1.nonempty) hcover
  obtain ⟨G,hG,hGcover,hdisj,hlater⟩ :=
    GraphPruning.exists_finite_connected_grouping hsym hdeg hconn
  refine ⟨fun j => ⋃ i ∈ G j, W i,
    connected_precompact_group_unions W hW G hG, ?_,
    locallyFinite_grouped W hlf G hdisj, ?_⟩
  · apply eq_univ_of_forall
    intro p
    obtain ⟨i,hpi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
    obtain ⟨j,hij⟩ := mem_iUnion.mp (hGcover.symm ▸ mem_univ i)
    exact mem_iUnion.mpr ⟨j,mem_iUnion₂.mpr ⟨i,hij,hpi⟩⟩
  · intro j
    obtain ⟨l,hjl,i,hij,t,htl,p,hpi,hpt⟩ := hlater j
    exact ⟨l,hjl,p,mem_iUnion₂.mpr ⟨i,hij,hpi⟩,mem_iUnion₂.mpr ⟨t,htl,hpt⟩⟩

end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData CompactSupportData Set Filter
open scoped Topology
universe u v

/-- Localizing an arbitrary smooth form gives compactly supported smooth pieces.
The compactness comes from the precompact cover, not from the original form. -/
theorem exists_partition_pieces
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) {ι : Type v} (U : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ p, ∃ i, p ∈ U i)
    (hcpt : ∀ i, IsCompact (closure (U i)))
    (k : ℕ) (ω : K.forms k) :
    ∃ η : ι → K.forms k,
      (∀ i, IsCompact (sectionSupport (η i).val) ∧ sectionSupport (η i).val ⊆ U i) ∧
      LocallyFinite (fun i => sectionSupport (η i).val) ∧
      ∀ p, (∑ᶠ i, (η i).val p) = ω.val p := by
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S U hU hcover
  let η : ι → K.forms k := fun i => CompactSupportResults.multiplyForm K k (ρ i) (hρ.1 i) ω
  have hsupp (i : ι) : sectionSupport (η i).val ⊆ sectionSupport (ρ i) :=
    (CompactSupportResults.support_function_smul_subset (ρ i) ω.val).trans inter_subset_left
  refine ⟨η, ?_, hρ.2.2.1.subset hsupp, ?_⟩
  · intro i
    exact ⟨(hcpt i).of_isClosed_subset isClosed_closure
      ((hsupp i).trans ((hsub i).trans subset_closure)),
      (hsupp i).trans (hsub i)⟩
  · intro p
    change (∑ᶠ i, ρ i p • ω.val p) = ω.val p
    have hfin : Function.HasFiniteSupport (fun i => ρ i p) :=
      (hρ.2.2.1.point_finite p).subset (fun i hi => subset_closure hi)
    rw [← finsum_smul' hfin, hρ.2.2.2 p, one_smul]

end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData Set Filter
open scoped Topology
universe u
section TransferMass
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear mass commutes with each finite incoming sum. -/
theorem map_incomingTransfer (L : V →ₗ[ℝ] ℝ) (next : ℕ → ℕ)
    (t : ℕ → V) (j : ℕ) :
    L (incomingTransfer next t j) = incomingTransfer next (fun i => L (t i)) j := by
  classical
  simp [incomingTransfer, map_sum]

/-- The well-founded coefficients kill the mass of each corrected piece.
This requires unit mass of the actual transfer forms. -/
theorem corrected_transfer_mass (L : V →ₗ[ℝ] ℝ) (next : ℕ → ℕ)
    (η θ : ℕ → V) (hθ : ∀ j, L (θ j) = 1) (j : ℕ) :
    let c := transferCoefficients next (fun i => L (η i))
    L (η j + incomingTransfer next (fun i => c i • θ i) j - c j • θ j) = 0 := by
  dsimp only
  rw [map_sub, map_add, map_incomingTransfer]
  simp only [map_smul, smul_eq_mul, hθ, mul_one]
  exact corrected_mass_zero next (fun i => L (η i)) j
end TransferMass

section LocalFillings
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B) (k : ℕ)

/-- Construct all transfers and primitives from local zero-mass fillings.
The local filling property is explicit here and still must be derived from
compact-support exactness on genuine open submanifolds in the main proof. -/
theorem exact_of_local_zero_mass_fillings
    (V : ℕ → TopologicalSpace.Opens M) (hV : LocallyFinite (fun j => (V j : Set M)))
    (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (L : CompactSupportResults.supportedForms K ⊤ (k+1) →ₗ[ℝ] ℝ)
    (ω : K.forms (k+1))
    (η θ : ℕ → CompactSupportResults.supportedForms K ⊤ (k+1))
    (hη : ∀ j, ModelData.sectionSupport (η j).val.val ⊆ V j)
    (hθ : ∀ j, ModelData.sectionSupport (θ j).val.val ⊆ V j ∩ V (next j))
    (hunit : ∀ j, L (θ j) = 1)
    (hω : ∀ p, (∑ᶠ j, (η j).val.val p) = ω.val p)
    (hfill : ∀ j (γ : CompactSupportResults.supportedForms K ⊤ (k+1)),
      ModelData.sectionSupport γ.val.val ⊆ V j → L γ = 0 →
      ∃ β : K.forms k, ModelData.sectionSupport β.val ⊆ V j ∧ K.d k β = γ.val) :
    ω ∈ K.exact (k+1) := by
  classical
  let c := transferCoefficients next (fun i => L (η i))
  let τ : ℕ → CompactSupportResults.supportedForms K ⊤ (k+1) := fun i => c i • θ i
  let γ : ℕ → CompactSupportResults.supportedForms K ⊤ (k+1) :=
    fun j => η j + incomingTransfer next τ j - τ j
  have hτ (i : ℕ) : ModelData.sectionSupport (τ i).val.val ⊆ V i ∩ V (next i) :=
    (CompactSupportResults.support_smul_subset (c i) (θ i).val.val).trans (hθ i)
  have hγ (j : ℕ) : ModelData.sectionSupport (γ j).val.val ⊆ V j := by
    have he : (η j).val ∈ CompactSupportResults.supportedForms K (V j) (k+1) :=
      ⟨(η j).property.1, hη j⟩
    have ht (i : ℕ) (hi : next i = j) :
        (τ i).val ∈ CompactSupportResults.supportedForms K (V j) (k+1) :=
      ⟨(τ i).property.1, by simpa [hi] using (hτ i).trans inter_subset_right⟩
    have hout : (τ j).val ∈ CompactSupportResults.supportedForms K (V j) (k+1) :=
      ⟨(τ j).property.1, (hτ j).trans inter_subset_left⟩
    have hin : (incomingTransfer next τ j).val ∈
        CompactSupportResults.supportedForms K (V j) (k+1) := by
      unfold incomingTransfer
      rw [Submodule.coe_sum]
      apply Submodule.sum_mem
      intro i hi
      exact ht i (Finset.mem_filter.mp hi).2
    have hresult : (η j).val + (incomingTransfer next τ j).val - (τ j).val ∈
        CompactSupportResults.supportedForms K (V j) (k+1) := by
      exact @Submodule.sub_mem ℝ (K.forms (k+1)) inferInstance
        (Submodule.addCommGroup (K.forms (k+1))) (Submodule.module (K.forms (k+1)))
        (CompactSupportResults.supportedForms K (V j) (k+1))
        ((η j).val + (incomingTransfer next τ j).val) (τ j).val
        ((CompactSupportResults.supportedForms K (V j) (k+1)).add_mem he hin) hout
    exact hresult.2
  have hzero (j : ℕ) : L (γ j) = 0 :=
    corrected_transfer_mass L next η θ hunit j
  choose β hβ hd using fun j => hfill j (γ j) (hγ j) (hzero j)
  apply exact_of_locallyFinite_transfers K k next hn ω
    (fun j => (η j).val) (fun j => (τ j).val) β
    (hV.subset hη) (hV.subset (fun i => (hτ i).trans inter_subset_left))
    (hV.subset hβ) hω
  intro j
  rw [hd j]
  change ((η j + incomingTransfer next τ j - τ j).val) = _
  change (η j).val + (incomingTransfer next τ j).val - (τ j).val = _
  unfold incomingTransfer
  rw [Submodule.coe_sum]
/-- Once the actual local filling and normalized overlap forms are available,
the escape cover and smooth partition give unrestricted primitives for every
form. The two local ingredients remain explicit obligations of the main proof. -/
theorem all_exact_of_local_zero_mass_fillings
    (V : ℕ → TopologicalSpace.Opens M)
    (hV : LocallyFinite (fun j => (V j : Set M)))
    (hcover : ∀ p, ∃ j, p ∈ V j)
    (hcpt : ∀ j, IsCompact (closure (V j : Set M)))
    (next : ℕ → ℕ) (hn : ∀ i, i < next i)
    (L : CompactSupportResults.supportedForms K ⊤ (k+1) →ₗ[ℝ] ℝ)
    (θ : ℕ → CompactSupportResults.supportedForms K ⊤ (k+1))
    (hθ : ∀ j, ModelData.sectionSupport (θ j).val.val ⊆ V j ∩ V (next j))
    (hunit : ∀ j, L (θ j) = 1)
    (hfill : ∀ j (γ : CompactSupportResults.supportedForms K ⊤ (k+1)),
      ModelData.sectionSupport γ.val.val ⊆ V j → L γ = 0 →
      ∃ β : K.forms k, ModelData.sectionSupport β.val ⊆ V j ∧ K.d k β = γ.val) :
    (∀ ω : K.forms (k+1), ω ∈ K.exact (k+1)) ∧ Subsingleton (K.Cohomology (k+1)) := by
  have hall (ω : K.forms (k+1)) : ω ∈ K.exact (k+1) := by
    obtain ⟨η,hη,_,hω⟩ := exists_partition_pieces S C B K
      (fun j => (V j : Set M)) (fun j => (V j).isOpen) hcover hcpt (k+1) ω
    let ηc : ℕ → CompactSupportResults.supportedForms K ⊤ (k+1) :=
      fun j => ⟨η j, (hη j).1, Set.subset_univ _⟩
    exact exact_of_local_zero_mass_fillings K k V hV next hn L ω ηc θ
      (fun j => (hη j).2) hθ hunit hω hfill
  exact ⟨hall, cohomology_subsingleton_of_all_exact K (k+1) hall⟩
end LocalFillings
end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData Set Filter
  OrientationData BoundaryData LocalIntegrationData GlobalIntegrationData
open scoped Topology
universe u
section CompactMass
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} {U : TopologicalSpace.Opens M}

/-- Bundle a compact smooth top form in the original continuous integral domain. -/
def compactTopRepresentative (D : CompactCalculus K U) (ω : D.complex.Obj n) :
    CompactTopForm S where
  field := (D.inclusion.map n ω).val
  continuous := StokesResults.continuous_top_of_coefficients C _
    (ExteriorDerivativeResults.regular_continuous C n 0 _
      (ExteriorDerivativeResults.smooth_regular C n (B n) _ 0
        ((K.mem_forms _ _).mp (D.inclusion.map n ω).property)))
  compact_support := (CompactSupportResults.inclusion_support D n ω).1

/-- The actual integral is linear on each full compact-support subcomplex. -/
def compactIntegral (D : CompactCalculus K U) {o : Orientation S}
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) : D.complex.Obj n →ₗ[ℝ] ℝ where
  toFun ω := I (compactTopRepresentative D ω)
  map_add' α β := hI.1 _ _ _ (by
    change (D.inclusion.map n (α + β)).val =
      (D.inclusion.map n α).val + (D.inclusion.map n β).val
    rw [map_add]
    rfl)
  map_smul' r α := hI.2.1 r _ _ (by
    change (D.inclusion.map n (r • α)).val = r • (D.inclusion.map n α).val
    rw [map_smul]
    rfl)
end CompactMass

/-- The full compact exactness premise supplies an actual compact smooth
primitive, using the same integral as the source and the same ambient fields. -/
theorem exists_compact_primitive_of_zero_integral
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    {k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold (k+1) a M) (hb : intrinsicBoundary S = ∅)
    (o : Orientation S) (C : CotangentBundle S) (B : ∀ r, FormBundle C r)
    (K : Calculus C B) (D : CompactCalculus K ⊤)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (ω : D.complex.Obj (k+1)) (hz : compactIntegral D I hI ω = 0) :
    ∃ β : K.forms k, IsCompact (ModelData.sectionSupport β.val) ∧
      K.d k β = D.inclusion.map (k+1) ω := by
  have he := compact_exact_of_zero_integral hExact S hb o C B K D I hI ω
    (compactTopRepresentative D ω) rfl hz
  obtain ⟨β,hβ⟩ := he
  refine ⟨D.inclusion.map k β, (CompactSupportResults.inclusion_support D k β).1, ?_⟩
  exact (D.inclusion.comm k β).trans (congrArg (D.inclusion.map (k+1)) hβ)
end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  MayerVietorisData CompactSupportData OrientationData BoundaryData
  LocalIntegrationData GlobalIntegrationData
universe u
/-- Surjectivity of the full compact-support integration isomorphism supplies
an actual smooth compact representative with integral one. No compactness of
the manifold is required. Support localization to a smaller open manifold is
a separate geometric step. -/
theorem exists_unit_compact_top_form
    (hTop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M) (hb : intrinsicBoundary S = ∅)
    (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) :
    ∃ (ω : D.complex.Obj n) (μ : CompactTopForm S),
      μ.field = (D.inclusion.map n ω).val ∧ I μ = 1 := by
  obtain ⟨e,he⟩ := hTop S hb o C B K D I hI
  obtain ⟨ω,hω⟩ := (D.complex.boundaries n).mkQ_surjective (e.symm 1)
  obtain ⟨μ,hμ,hIμ⟩ := he ω
  refine ⟨ω.val,μ,hμ,?_⟩
  rw [← hIμ]
  change e ((D.complex.boundaries n).mkQ ω) = 1
  rw [hω, e.apply_symm_apply]
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData Set Filter
open scoped Topology
universe u v

section RestrictedSupport
variable {X : Type u} [TopologicalSpace X] {E : X → Type v} [∀ x, Zero (E x)]

/-- For an open inclusion, the closed support of the restriction is its preimage. -/
theorem sectionSupport_restrict (U : TopologicalSpace.Opens X) (f : ∀ x, E x) :
    sectionSupport (fun p : U => f p.val) = Subtype.val ⁻¹' sectionSupport f := by
  exact (U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val {p | f p ≠ 0}).symm

/-- A field supported inside U has exactly its original support after inclusion. -/
theorem sectionSupport_restrict_image (U : TopologicalSpace.Opens X) (f : ∀ x, E x)
    (hs : sectionSupport f ⊆ U) :
    Subtype.val '' sectionSupport (fun p : U => f p.val) = sectionSupport f := by
  rw [sectionSupport_restrict]
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact hq
  · intro p hp
    exact ⟨⟨p, hs hp⟩, hp, rfl⟩

/-- Ambient compact support contained in U is compact in the open-subspace topology. -/
theorem compact_sectionSupport_restrict (U : TopologicalSpace.Opens X) (f : ∀ x, E x)
    (hc : IsCompact (sectionSupport f)) (hs : sectionSupport f ⊆ U) :
    IsCompact (sectionSupport (fun p : U => f p.val)) := by
  rw [sectionSupport_restrict]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc
  intro p hp
  exact ⟨⟨p, hs hp⟩, rfl⟩
end RestrictedSupport

section OpenGeometry
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)

/-- Coordinate transport across an open inclusion is the identity in the
corresponding restricted chart, for any chosen intrinsic coordinate systems. -/
theorem open_inclusion_coordinates (R : SmoothManifold n a U)
    (hinc : IsSmoothMap R S Subtype.val) (p : U)
    (L : TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential R S Subtype.val p L)
    (d : ModelChart n a U) (c : ModelChart n a M)
    (hd : d ∈ R.smoothStructure.val) (hc : c ∈ S.smoothStructure.val)
    (hpd : p ∈ d.source) (hpc : p.val ∈ c.source)
    (hcoord : ∀ q : U, (d q).val = (c q.val).val)
    (K : TangentBundleData.FiberCoordinates R)
    (H : TangentBundleData.FiberCoordinates S) (v : TangentSpace R p) :
    H.equiv c hc p.val hpc (L v) = K.equiv d hd p hpd v := by
  have h := differential_jacobian R S Subtype.val hinc p L hL d c hd hc hpd hpc
    (K.equiv d hd p hpd) (H.equiv c hc p.val hpc)
    (K.isCoordinates d hd p hpd) (H.isCoordinates c hc p.val hpc)
    univ id isOpen_univ (mem_univ _) contDiff_id.contDiffOn
    (Filter.Eventually.of_forall hcoord) v
  simpa only [fderiv_id, ContinuousLinearMap.id_apply] using h

/-- Covector coordinate maps agree under the inverse dual of the actual
tangent inclusion. This is the algebraic bridge between the two cotangent bundles. -/
theorem open_inclusion_cotangent_coordinates (R : SmoothManifold n a U)
    (hinc : IsSmoothMap R S Subtype.val) (p : U)
    (E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : IsDifferential R S Subtype.val p E.toLinearMap)
    (d : ModelChart n a U) (c : ModelChart n a M)
    (hd : d ∈ R.smoothStructure.val) (hc : c ∈ S.smoothStructure.val)
    (hpd : p ∈ d.source) (hpc : p.val ∈ c.source)
    (hcoord : ∀ q : U, (d q).val = (c q.val).val)
    (A : CotangentBundle R) (C : CotangentBundle S) :
    letI := (cotangentSpace C).topology
    letI := (cotangentSpace A).topology
    ∀ (hpC : p.val ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩)
      (hpA : p ∈ (cotangentSpace A).bundle.baseSet ⟨d, hd⟩),
      ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p.val hpC).toLinearMap.comp
        E.symm.toLinearMap.dualMap =
      ((cotangentSpace A).bundle.fiberCoordinates ⟨d, hd⟩ p hpA).toLinearMap := by
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace A).topology
  intro hpC hpA
  apply LinearMap.ext
  intro α
  ext j
  change (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩)
    ⟨p.val, E.symm.toLinearMap.dualMap α⟩).2 j =
    (((cotangentSpace A).bundle.trivialization ⟨d, hd⟩) ⟨p, α⟩).2 j
  rw [Covectors.cotangent_coordinates C c hc p.val hpc,
    Covectors.cotangent_coordinates A d hd p hpd]
  change α (E.symm (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc p.val hpc j)) =
    α (CovectorData.coordinateVector A.tangent.fiberCoordinates d hd p hpd j)
  congr 1
  apply (A.tangent.fiberCoordinates.equiv d hd p hpd).injective
  have h := open_inclusion_coordinates S U R hinc p E.toLinearMap hE d c hd hc
    hpd hpc hcoord A.tangent.fiberCoordinates C.tangent.fiberCoordinates
    (E.symm (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc p.val hpc j))
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    CovectorData.coordinateVector] using h.symm

/-- The actual differential of an open inclusion is a linear equivalence. -/
theorem open_subset_differential (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val) (p : U) :
    ∃ E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val,
      IsDifferential R S Subtype.val p E.toLinearMap := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := U) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
        S.smoothStructure.property.1 U U.isOpen) ⟨⟨p⟩, c, hc, rfl⟩
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists R
  obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L, hL, _⟩ := differential_exists R S Subtype.val hinc p
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hp
  let E := K.equiv d hd p hpd
  let F := H.equiv c hc p.val hp
  have heq (v : TangentSpace R p) : F (L v) = E v := by
    have h := differential_jacobian R S Subtype.val hinc p L hL d c hd hc hpd hp
      E F (K.isCoordinates d hd p hpd) (H.isCoordinates c hc p.val hp)
      univ id isOpen_univ (mem_univ _) contDiff_id.contDiffOn
      (Filter.Eventually.of_forall (fun _ => rfl)) v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using h
  have hmap : (E.trans F.symm).toLinearMap = L := by
    apply LinearMap.ext
    intro v
    apply F.injective
    simpa using (heq v).symm
  refine ⟨E.trans F.symm, ?_⟩
  rw [hmap]
  exact hL

/-- An open submanifold of a boundaryless manifold has empty intrinsic boundary. -/
theorem open_subset_boundary_empty (hb : intrinsicBoundary S = ∅)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen)) :
    intrinsicBoundary R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := U) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
        S.smoothStructure.property.1 U U.isOpen) ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc
  have hface := (intrinsicBoundary_iff_chart R d hd p hpd).mp hp
  have hbase := (intrinsicBoundary_iff_chart S c hc p.val hpc).mpr hface
  simpa only [hb, Set.mem_empty_iff_false] using hbase

end OpenGeometry
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData Set Filter
open scoped Topology
universe u v

section OpenGeometry
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)

/-- The inverse-ray formula gives the orientation-preserving determinant identity. -/
theorem open_orientation_forward (R : SmoothManifold n a U)
    (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (o : Orientation S) (oU : Orientation R)
    (hinverse : ∀ p, oU.val p =
      Module.Ray.map (determinantMap n (E p).symm) (o.val p.val)) :
    ∀ p, Module.Ray.map (determinantMap n (E p)) (oU.val p) = o.val p.val := by
  intro p
  rw [hinverse p]
  have h := OrientationProducts.rayMap_determinant_symm_apply_apply
    (V := TangentSpace S p.val) (W := TangentSpace R p) n (E p).symm (o.val p.val)
  simpa only [LinearEquiv.symm_symm] using h

/-- The natural open submanifold, with its actual tangent inclusion and the
orientation transported through that inclusion. No connectedness is needed. -/
theorem exists_open_subset_oriented_geometry (hb : intrinsicBoundary S = ∅)
    (o : Orientation S) :
    ∃ R : SmoothManifold n a U,
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val U U.isOpen) ∧
      intrinsicBoundary R = ∅ ∧ IsSmoothMap R S Subtype.val ∧
      ∃ (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
        (oU : Orientation R),
        (∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap) ∧
        ∀ p, oU.val p = Module.Ray.map (determinantMap n (E p).symm) (o.val p.val) := by
  obtain ⟨R, _, hR, hinc⟩ := exists_openSubset_smoothManifold S U U.isOpen
  obtain ⟨E, hE⟩ := Classical.axiomOfChoice (open_subset_differential S U R hR hinc)
  have hcont := @OrientationProducts.pullbackRayField_continuous n a a U M inferInstance inferInstance R S Subtype.val hinc o E hE
  let oU : Orientation R := ⟨_, hcont⟩
  refine ⟨R, hR, open_subset_boundary_empty S U hb R hR, hinc, E, oU, hE, ?_⟩
  intro p
  rfl
end OpenGeometry
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData Set Filter
open scoped Topology
universe u v

section RestrictedPrimitive
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}

/-- Restricting and extending by zero recovers a field supported inside the domain. -/
theorem zeroExtend_restrict_of_support (U : TopologicalSpace.Opens M) (k : ℕ)
    (ω : Field S k) (hω : ModelData.sectionSupport ω ⊆ U) :
    zeroExtend (fun p : U => ω p.val) = ω := by
  classical
  funext p
  by_cases hp : p ∈ U
  · simp [zeroExtend, hp]
  · have hz : ω p = 0 := by
      by_contra hn
      exact hp (hω (subset_closure hn))
    simp [zeroExtend, hp, hz]

/-- A genuine compact restricted primitive becomes a primitive in the ambient
compact realization, retaining support inside the same open set. -/
theorem compact_exact_of_restricted_primitive (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (D : CompactCalculus K U) (k : ℕ)
    (ω : D.complex.Obj (k+1)) (β : RestrictedField S U k)
    (hβ : IsRestrictedForm (B k) U β) (hcβ : IsCompact (ModelData.sectionSupport β))
    (hdβ : HasRestrictedDerivative C U β
      (fun p => (D.inclusion.map (k+1) ω).val p.val)) :
    ω ∈ D.complex.exact (k+1) := by
  obtain ⟨hsmooth, hcompact, hsupp⟩ :=
    CompactSupportResults.zero_extension (B k) U β hβ hcβ
  let η : K.forms k := ⟨zeroExtend β, (K.mem_forms _ _).mpr hsmooth⟩
  have hsmall : ModelData.sectionSupport η.val ⊆ U := by
    change ModelData.sectionSupport (zeroExtend β) ⊆ U
    rw [hsupp]
    rintro p ⟨q, _, rfl⟩
    exact q.property
  obtain ⟨γ, hγ⟩ := (D.range k η).mp ⟨hcompact, hsmall⟩
  refine ⟨γ, ?_⟩
  apply D.injective (k+1)
  rw [← D.inclusion.comm, hγ]
  apply Subtype.ext
  change K.D k (zeroExtend β) = (D.inclusion.map (k+1) ω).val
  rw [CompactSupportResults.extension_derivative K U k β _ hβ hcβ hdβ]
  exact zeroExtend_restrict_of_support U (k+1) _
    (CompactSupportResults.inclusion_support D (k+1) ω).2
end RestrictedPrimitive

end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  FormPullbackData Set Filter
open scoped Topology
universe u
section OpenInverse
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  (R : SmoothManifold n a U)
  (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)

def intrinsicToRestricted (k : ℕ) (γ : Field R k) : RestrictedField S U k :=
  fun p => fiberPullback (V := TangentSpace S p.val) (W := TangentSpace R p) k (E p).symm.toLinearMap (γ p)

@[simp] theorem intrinsicToRestricted_pullback (k : ℕ) (γ : Field R k) (p : U) :
    fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) k (E p).toLinearMap (intrinsicToRestricted S U R E k γ p) = γ p := by
  change (exteriorPower.map k (E p).toLinearMap.dualMap)
    ((exteriorPower.map k (E p).symm.toLinearMap.dualMap) (γ p)) = _
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have hid : (E p).toLinearMap.dualMap.comp (E p).symm.toLinearMap.dualMap = LinearMap.id := by
    ext lam v
    exact congrArg lam ((E p).symm_apply_apply v)
  rw [hid, exteriorPower.map_id]
  rfl

@[simp] theorem intrinsicToRestricted_pullbackField (k : ℕ) (ω : Field S k) :
    intrinsicToRestricted S U R E k
      (pullbackField R S Subtype.val (fun p => (E p).toLinearMap) ω) =
      (fun p : U => ω p.val) := by
  funext p
  apply exteriorPower.map_injective_field (E p).dualMap.injective
  exact intrinsicToRestricted_pullback S U R E k
    (pullbackField R S Subtype.val (fun p => (E p).toLinearMap) ω) p

theorem sectionSupport_intrinsicToRestricted (k : ℕ) (γ : Field R k) :
    sectionSupport (intrinsicToRestricted S U R E k γ) = sectionSupport γ := by
  have hset : {p : U | intrinsicToRestricted S U R E k γ p ≠ 0} = {p : U | γ p ≠ 0} := by
    ext p
    apply not_congr
    constructor
    · intro h
      have ht := intrinsicToRestricted_pullback S U R E k γ p
      rw [h, map_zero] at ht
      exact ht.symm
    · intro h
      change (fiberPullback (V := TangentSpace S p.val) (W := TangentSpace R p)
        k (E p).symm.toLinearMap) (γ p) = 0
      rw [h, map_zero]
  exact congrArg closure hset

/-- Inverting the actual tangent inclusion transports intrinsic smooth forms
back to the ambient restricted exterior bundle. -/
theorem intrinsicToRestricted_smooth
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (C : CotangentBundle S) (A : CotangentBundle R) (k : ℕ)
    (B : FormBundle C k) (F : FormBundle A k)
    (γ : Field R k) (hγ : IsForm F γ) :
    IsRestrictedForm B U (intrinsicToRestricted S U R E k γ) := by
  classical
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace A).topology
  letI := B.space.topology
  letI := F.space.topology
  let Ω := openSubsetAtlas S.smoothStructure.val U U.isOpen
  have hΩ : IsContDiffAtlas (⊤ : ℕ∞) Ω :=
    SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
      S.smoothStructure.property.1 U U.isOpen
  have hsub : Ω ⊆ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension hΩ
  have hincΩ : ManifoldSmooth Ω S.smoothStructure.val Subtype.val := by
    intro p
    exact ⟨(hinc p).1, fun c hc d hd hp hpd =>
      (hinc p).2 c (hsub hc) d hd hp hpd⟩
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := U) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := hsub ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hp
  let z : U → Euclidean (n.choose k) := fun q =>
    ((F.space.bundle.trivialization ⟨d, hd⟩) ⟨q, γ q⟩).2
  have hzR : Frames.VectorSmoothAt R.smoothStructure.val z p := by
    apply (Frames.trivializationCoordinates_smoothAt F.space.bundle ⟨d, hd⟩
      ⟨p, γ p⟩ (by rw [F.baseSet, Covectors.cotangent_baseSet]; exact hpd)).comp
      (g := fun q => (⟨q, γ q⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun x => Fiber (TangentSpace R x) k)))
      F.space.bundle.totalManifold.smoothStructure.property.1.1 (hγ p)
  have hz : Frames.VectorSmoothAt Ω z p :=
    ⟨hzR.1, fun c hc hp => hzR.2 c (hsub hc) hp⟩
  let Q : Euclidean (n.choose k) →ₗ[ℝ] Euclidean (n.choose k) :=
    B.modelEquiv.toLinearMap.comp F.modelEquiv.symm.toLinearMap
  have hv := hz.postcomp Q.toContinuousLinearMap.contDiff
  apply Frames.smoothAt_from_trivialization B.space.bundle hΩ ⟨c, hc⟩
    (by rw [B.baseSet, Covectors.cotangent_baseSet]; exact hp)
    (hincΩ p) hv (fun _ => rfl)
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds hp)] with q hq
  have hqd : q ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hq
  have hqC : q.val ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hq
  have hqA : q ∈ (cotangentSpace A).bundle.baseSet ⟨d, hd⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hqd
  have he := open_inclusion_cotangent_coordinates S U R hinc q (E q) (hE q)
    d c hd hc hqd hq (fun _ => rfl) A C hqC hqA
  rw [FormPullbackResults.form_coordinates C k B c hc q.val hq]
  change B.modelEquiv
    ((exteriorPower.map k
      ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ q.val hqC).toLinearMap)
      ((exteriorPower.map k (E q).symm.toLinearMap.dualMap) (γ q))) =
    B.modelEquiv (F.modelEquiv.symm (z q))
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, he]
  rw [show z q = F.modelEquiv
    ((exteriorPower.map k
      ((cotangentSpace A).bundle.fiberCoordinates ⟨d, hd⟩ q hqA).toLinearMap) (γ q)) from
    FormPullbackResults.form_coordinates A k F d hd q hqd (γ q)]
  rw [LinearEquiv.symm_apply_apply]

/-- The genuine restricted differential agrees with the intrinsic derivative
on the open manifold after pullback through its actual tangent inclusion. -/
theorem restricted_derivative_from_intrinsic
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (A : CotangentBundle R) (F : ∀ k, FormBundle A k) (J : Calculus A F)
    (k : ℕ) (β : RestrictedField S U k)
    (hβ : IsRestrictedForm (B k) U β) (γ : J.forms k)
    (hγ : ∀ p, fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) k (E p).toLinearMap (β p) = γ.val p)
    (η : RestrictedField S U (k+1))
    (hη : ∀ p, fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) (k+1) (E p).toLinearMap (η p) = (J.d k γ).val p) :
    HasRestrictedDerivative C U β η := by
  classical
  obtain ⟨O⟩ := OpenForms.openCalculus_exists K U
  let ξ := OpenForms.realize O k β hβ
  let δ := O.field (k+1) (O.complex.d k ξ)
  have hd : HasRestrictedDerivative C U β δ := by
    have hd := O.coordinates k ξ
    simpa only [ξ, OpenForms.field_realize] using hd
  have heq : δ = η := by
    funext p
    apply exteriorPower.map_injective_field (E p).dualMap.injective
    change fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) (k+1) (E p).toLinearMap (δ p) =
      fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) (k+1) (E p).toLinearMap (η p)
    obtain ⟨α, hα, hgerm⟩ := OpenForms.exists_global_germ (B k) U β hβ p
    rw [OpenForms.restricted_derivative_eq_global K U β δ hd α hα p hgerm]
    have hsm := FormPullbackResults.pullback_smooth R S A C Subtype.val hinc
      (fun q => (E q).toLinearMap) hE k (F k) (B k) α hα
    have hevent : ∀ᶠ q in 𝓝 p,
        pullbackField R S Subtype.val (fun q => (E q).toLinearMap) α q = γ.val q := by
      filter_upwards [continuous_subtype_val.continuousAt.eventually hgerm] with q hq
      change fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (E q).toLinearMap (α q.val) = γ.val q
      rw [hq]
      simpa only [zeroExtend, dite_eq_left q.property] using hγ q
    have hloc := ExteriorDerivativeResults.axioms_locality A F J.D J.axioms k
      (pullbackField R S Subtype.val (fun q => (E q).toLinearMap) α) γ.val
      hsm ((J.mem_forms _ _).mp γ.property) p hevent
    have hnat := congrFun (ExteriorDerivativeResults.smooth_naturality R S A C F B
      J.D K.D J.axioms K.axioms Subtype.val hinc (fun q => (E q).toLinearMap) hE k α hα) p
    exact hnat.trans (hloc.trans (hη p).symm)
  exact heq ▸ hd

/-- The inverse field transport intertwines the intrinsic smooth differential
and the genuine ambient restricted differential. -/
theorem intrinsicToRestricted_derivative
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (A : CotangentBundle R) (F : ∀ k, FormBundle A k) (J : Calculus A F)
    (k : ℕ) (γ : J.forms k) :
    HasRestrictedDerivative C U (intrinsicToRestricted S U R E k γ.val)
      (intrinsicToRestricted S U R E (k+1) (J.d k γ).val) := by
  exact restricted_derivative_from_intrinsic S U R E hinc hE C B K A F J k
    (intrinsicToRestricted S U R E k γ.val)
    (intrinsicToRestricted_smooth S U R E hR hinc hE C A k (B k) (F k) γ.val
      ((J.mem_forms _ _).mp γ.property)) γ
    (intrinsicToRestricted_pullback S U R E k γ.val)
    (intrinsicToRestricted S U R E (k+1) (J.d k γ).val)
    (intrinsicToRestricted_pullback S U R E (k+1) (J.d k γ).val)

/-- A compact intrinsic smooth form on an arbitrary open submanifold extends
to an ambient compact smooth form, with its exact support image and the actual
intrinsic differential preserved under zero extension. -/
theorem exists_ambient_extension_of_intrinsic
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (A : CotangentBundle R) (F : ∀ k, FormBundle A k) (J : Calculus A F)
    (k : ℕ) (γ : J.forms k) (hcγ : IsCompact (sectionSupport γ.val)) :
    ∃ ω : K.forms k,
      sectionSupport ω.val = Subtype.val '' sectionSupport γ.val ∧
      IsCompact (sectionSupport ω.val) ∧ sectionSupport ω.val ⊆ U ∧
      pullbackField R S Subtype.val (fun p => (E p).toLinearMap) ω.val = γ.val ∧
      (K.d k ω).val = zeroExtend
        (intrinsicToRestricted S U R E (k+1) (J.d k γ).val) := by
  classical
  let β := intrinsicToRestricted S U R E k γ.val
  have hβ : IsRestrictedForm (B k) U β :=
    intrinsicToRestricted_smooth S U R E hR hinc hE C A k (B k) (F k) γ.val
      ((J.mem_forms _ _).mp γ.property)
  have hsβ : sectionSupport β = sectionSupport γ.val :=
    sectionSupport_intrinsicToRestricted S U R E k γ.val
  have hcβ : IsCompact (sectionSupport β) := hsβ.symm ▸ hcγ
  obtain ⟨hsm, hc, hs⟩ := CompactSupportResults.zero_extension (B k) U β hβ hcβ
  let ω : K.forms k := ⟨zeroExtend β, (K.mem_forms _ _).mpr hsm⟩
  have hsω : sectionSupport ω.val = Subtype.val '' sectionSupport γ.val := by
    exact hs.trans (congrArg (fun T : Set U => Subtype.val '' T) hsβ)
  refine ⟨ω, hsω, hc, ?_, ?_, ?_⟩
  · rw [hsω]
    rintro p ⟨q, hq, rfl⟩
    exact q.property
  · funext p
    change fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val)
      k (E p).toLinearMap (zeroExtend β p.val) = γ.val p
    simpa only [zeroExtend, dite_eq_left p.property] using
      intrinsicToRestricted_pullback S U R E k γ.val p
  · exact CompactSupportResults.extension_derivative K U k β _ hβ hcβ
      (intrinsicToRestricted_derivative S U R E hR hinc hE C B K A F J k γ)

end OpenInverse
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  FormPullbackData Set Filter
open scoped Topology
universe u

/-- Fiberwise pullback by an isomorphism of tangent spaces is injective. -/
theorem fiberPullback_injective_of_equiv {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (k : ℕ) (E : V ≃ₗ[ℝ] W) :
    Function.Injective (fiberPullback k E.toLinearMap) := by
  exact exteriorPower.map_injective_field E.dualMap.injective

section OpenInput
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  (R : SmoothManifold n a U)
  (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)

/-- Pullback through the actual tangent inclusion preserves the full closed
support in the open subspace. -/
theorem sectionSupport_open_pullback (k : ℕ) (ω : Field S k) :
    sectionSupport (pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω) =
      Subtype.val ⁻¹' sectionSupport ω := by
  have hz (p : U) :
      pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω p = 0 ↔ ω p.val = 0 := by
    constructor
    · intro h
      apply exteriorPower.map_injective_field (n := k)
        (f := (E p).toLinearMap.dualMap) (E p).dualMap.injective
      simpa only [FormPullbackData.pullbackField, fiberPullback, map_zero] using h
    · intro h
      change (exteriorPower.map k (E p).toLinearMap.dualMap) (ω p.val) = 0
      rw [h, map_zero]
  change closure {p : U | pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω p ≠ 0} =
    Subtype.val ⁻¹' closure {p : M | ω p ≠ 0}
  have heq : {p : U | pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω p ≠ 0} =
      Subtype.val ⁻¹' {p : M | ω p ≠ 0} := by
    ext p
    exact not_congr (hz p)
  rw [heq]
  exact (U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val {p : M | ω p ≠ 0}).symm

/-- Compact ambient support contained in the open domain stays compact after
intrinsic pullback. -/
theorem compact_sectionSupport_open_pullback (k : ℕ) (ω : Field S k)
    (hc : IsCompact (sectionSupport ω)) (hs : sectionSupport ω ⊆ U) :
    IsCompact (sectionSupport
      (pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω)) := by
  rw [sectionSupport_open_pullback]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc
  intro p hp
  exact ⟨⟨p, hs hp⟩, rfl⟩

/-- A compact smooth ambient form supported in U is a genuine element of the
full intrinsic compact complex on the open submanifold. -/
theorem exists_compact_open_pullback
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (A : CotangentBundle R) (F : ∀ k, FormBundle A k) (J : Calculus A F)
    (D : CompactCalculus J ⊤) (k : ℕ) (ω : K.forms k)
    (hc : IsCompact (sectionSupport ω.val)) (hs : sectionSupport ω.val ⊆ U) :
    ∃ ζ : D.complex.Obj k,
      (D.inclusion.map k ζ).val =
        pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω.val := by
  let ξ : J.forms k := ⟨
    pullbackField R S Subtype.val (k := k) (fun p => (E p).toLinearMap) ω.val,
    (J.mem_forms k _).mpr (FormPullbackResults.pullback_smooth R S A C Subtype.val
      hinc (fun p => (E p).toLinearMap) hE k (F k) (B k) ω.val
      ((K.mem_forms k _).mp ω.property))⟩
  obtain ⟨ζ, hζ⟩ := (D.range k ξ).mp
    ⟨compact_sectionSupport_open_pullback S U R E k ω.val hc hs, subset_univ _⟩
  exact ⟨ζ, congrArg Subtype.val hζ⟩

end OpenInput
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  FormPullbackData OrientationData BoundaryData LocalIntegrationData GlobalIntegrationData Set Filter
open scoped Topology
universe u

/-- An exact class in the full compact complex has an actual compact smooth
primitive whose ambient closed support stays in that prescribed open set. -/
theorem exists_supported_primitive_of_exact
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ r, FormBundle C r}
    (K : Calculus C B) (U : TopologicalSpace.Opens M) (D : CompactCalculus K U)
    (k : ℕ) (ω : D.complex.Obj (k+1)) (hω : ω ∈ D.complex.exact (k+1)) :
    ∃ β : K.forms k, IsCompact (ModelData.sectionSupport β.val) ∧
      ModelData.sectionSupport β.val ⊆ U ∧ K.d k β = D.inclusion.map (k+1) ω := by
  obtain ⟨β, hβ⟩ := hω
  exact ⟨D.inclusion.map k β, (CompactSupportResults.inclusion_support D k β).1,
    (CompactSupportResults.inclusion_support D k β).2,
    (D.inclusion.comm k β).trans (congrArg (D.inclusion.map (k+1)) hβ)⟩

/-- Compact zero-integral exactness on the genuine connected open submanifold
produces exactness in the ambient compact complex supported in that same open set. -/
theorem compact_exact_of_open_pullback_zero
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    {k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (k+1) a M) (U : TopologicalSpace.Opens M) [ConnectedSpace U]
    (R : SmoothManifold (k+1) a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hbR : intrinsicBoundary R = ∅) (oR : Orientation R)
    (hinc : IsSmoothMap R S Subtype.val)
    (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (C : CotangentBundle S) (B : ∀ r, FormBundle C r) (K : Calculus C B)
    (A : CotangentBundle R) (F : ∀ r, FormBundle A r) (J : Calculus A F)
    (D : CompactCalculus K U) (DU : CompactCalculus J ⊤)
    (I : CompactTopForm R → ℝ) (hI : IsIntegral oR I)
    (ω : D.complex.Obj (k+1)) (ζ : DU.complex.Obj (k+1))
    (hζ : (DU.inclusion.map (k+1) ζ).val =
      pullbackField R S Subtype.val (k := k+1) (fun p => (E p).toLinearMap)
        (D.inclusion.map (k+1) ω).val)
    (hz : compactIntegral DU I hI ζ = 0) :
    ω ∈ D.complex.exact (k+1) := by
  obtain ⟨γ, hcγ, hdγ⟩ := exists_compact_primitive_of_zero_integral
    hExact R hbR oR A F J DU I hI ζ hz
  let β : RestrictedField S U k := intrinsicToRestricted S U R E k γ.val
  have hβ : IsRestrictedForm (B k) U β :=
    intrinsicToRestricted_smooth S U R E hR hinc hE C A k (B k) (F k) γ.val
      ((J.mem_forms k _).mp γ.property)
  have hcβ : IsCompact (ModelData.sectionSupport β) := by
    change IsCompact (sectionSupport (intrinsicToRestricted S U R E k γ.val))
    rw [sectionSupport_intrinsicToRestricted]
    exact hcγ
  have hdβ : HasRestrictedDerivative C U β
      (fun p => (D.inclusion.map (k+1) ω).val p.val) := by
    apply restricted_derivative_from_intrinsic S U R E hinc hE C B K A F J k β hβ γ
      (intrinsicToRestricted_pullback S U R E k γ.val)
      (fun p => (D.inclusion.map (k+1) ω).val p.val)
    intro p
    have hh := congrArg (fun q : J.forms (k+1) => q.val p) hdγ
    have hzeta := congrFun hζ p
    exact hzeta.symm.trans hh.symm
  exact compact_exact_of_restricted_primitive K U D k ω β hβ hcβ hdβ

end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  FormPullbackData Set Filter
open scoped Topology
universe u

/-- Compatibility of the original integrals under an oriented open inclusion.
This intermediate proposition is proved by `open_integral_compatibility` below. -/
def OpenIntegralCompatibility {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S) (I : CompactTopForm S → ℝ) : Prop :=
  ∀ (U : TopologicalSpace.Opens M) (R : SmoothManifold n a U)
    (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val) (oR : Orientation R),
    R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen) →
    IsSmoothMap R S Subtype.val →
    (∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap) →
    (∀ p, Module.Ray.map (determinantMap n (E p)) (oR.val p) = o.val p.val) →
    ∀ (IR : CompactTopForm R → ℝ), IsIntegral oR IR →
    ∀ (μ : CompactTopForm S) (ν : CompactTopForm R),
      sectionSupport μ.field ⊆ U →
      ν.field = pullbackField R S Subtype.val (fun p => (E p).toLinearMap) μ.field →
      I μ = IR ν

/-- A unit-integral compact top form can be placed inside any nonempty open
set once the actual integral comparison for open inclusions is available. -/
theorem exists_unit_supported_in_open
    (hTop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (hb : intrinsicBoundary S = ∅)
    (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (hCompat : OpenIntegralCompatibility S o I)
    (W : TopologicalSpace.Opens M) (hW : (W : Set M).Nonempty) :
    ∃ θ : CompactSupportResults.supportedForms K ⊤ n,
      sectionSupport θ.val.val ⊆ W ∧
      compactIntegral (CompactSupportResults.supportedCalculus K ⊤) I hI θ = 1 := by
  classical
  letI := S.topologicalManifold.hausdorff
  letI := _root_.SmoothManifolds.TopologicalManifold.locallyCompactSpace S.topologicalManifold
  letI := _root_.SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  obtain ⟨p, hp⟩ := hW
  obtain ⟨V, ⟨hoV, hpV, hconnV, hcV⟩, hVW⟩ :=
    (connected_precompact_basis p).mem_iff.mp (W.isOpen.mem_nhds hp)
  let U : TopologicalSpace.Opens M := ⟨V, hoV⟩
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnV
  obtain ⟨R, hR, hbR, hinc, E, oR, hE, hoRinv⟩ :=
    exists_open_subset_oriented_geometry S U hb o
  have hoR := open_orientation_forward S U R E o oR hoRinv
  obtain ⟨A⟩ := BundleOperations.exists_cotangent R
  let F : ∀ k, FormBundle A k := fun k => (ExteriorAlgebraResults.exists_formBundle A k).some
  obtain ⟨J⟩ := DeRhamResults.complex_exists A F
  let D := CompactSupportResults.supportedCalculus J ⊤
  obtain ⟨IR, hIR, _⟩ := GlobalIntegrationResults.exists_integral R oR
  obtain ⟨ζ, ν, hν, hunit⟩ := exists_unit_compact_top_form hTop R hbR oR A F J D IR hIR
  let γ := D.inclusion.map n ζ
  have hcγ : IsCompact (sectionSupport γ.val) :=
    (CompactSupportResults.inclusion_support D n ζ).1
  obtain ⟨ω, hsω, hcω, hωU, hpull, hdω⟩ :=
    exists_ambient_extension_of_intrinsic S U R E hR hinc hE C B K A F J n γ hcγ
  let θ : CompactSupportResults.supportedForms K ⊤ n := ⟨ω, hcω, subset_univ _⟩
  let μ := compactTopRepresentative (CompactSupportResults.supportedCalculus K ⊤) θ
  have hμU : sectionSupport μ.field ⊆ U := hωU
  have hfields : ν.field =
      pullbackField R S Subtype.val (fun p => (E p).toLinearMap) μ.field :=
    hν.trans hpull.symm
  have hintegral : I μ = IR ν := hCompat U R E oR hR hinc hE hoR IR hIR μ ν hμU hfields
  exact ⟨θ, hωU.trans hVW, hintegral.trans hunit⟩

end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  FormPullbackData Set Filter
open scoped Topology
universe u

/-- The actual local compact-support filling statement used by transfer
summation, after the genuine open-inclusion integral comparison is supplied. -/
theorem exists_supported_primitive_of_open_integral_compatibility
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    {k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (k+1) a M) (hb : intrinsicBoundary S = ∅)
    (o : Orientation S) (C : CotangentBundle S) (B : ∀ r, FormBundle C r)
    (K : Calculus C B) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (hCompat : OpenIntegralCompatibility S o I)
    (U : TopologicalSpace.Opens M) (hconn : IsConnected (U : Set M))
    (ω : K.forms (k+1)) (hcω : IsCompact (ModelData.sectionSupport ω.val))
    (hsω : ModelData.sectionSupport ω.val ⊆ U)
    (hz : compactIntegral (CompactSupportResults.supportedCalculus K ⊤) I hI
      ⟨ω, hcω, subset_univ _⟩ = 0) :
    ∃ β : K.forms k, IsCompact (ModelData.sectionSupport β.val) ∧
      ModelData.sectionSupport β.val ⊆ U ∧ K.d k β = ω := by
  classical
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨R, hR, hbR, hinc, E, oR, hE, hoRinv⟩ :=
    exists_open_subset_oriented_geometry S U hb o
  have hoR := open_orientation_forward S U R E o oR hoRinv
  obtain ⟨A⟩ := BundleOperations.exists_cotangent R
  let F : ∀ r, FormBundle A r := fun r => (ExteriorAlgebraResults.exists_formBundle A r).some
  obtain ⟨J⟩ := DeRhamResults.complex_exists A F
  let DU := CompactSupportResults.supportedCalculus J ⊤
  obtain ⟨IR, hIR, _⟩ := GlobalIntegrationResults.exists_integral R oR
  obtain ⟨ζ, hζ⟩ := exists_compact_open_pullback S U R E hinc hE C B K A F J DU
    (k+1) ω hcω hsω
  let D := CompactSupportResults.supportedCalculus K U
  let ωU : D.complex.Obj (k+1) := ⟨ω, hcω, hsω⟩
  let μ := compactTopRepresentative (CompactSupportResults.supportedCalculus K ⊤)
    ⟨ω, hcω, subset_univ _⟩
  let ν := compactTopRepresentative DU ζ
  have hμU : ModelData.sectionSupport μ.field ⊆ U := hsω
  have hν : ν.field =
      FormPullbackData.pullbackField R S Subtype.val (k := k+1) (fun p => (E p).toLinearMap) μ.field := hζ
  have heq := hCompat U R E oR hR hinc hE hoR IR hIR μ ν hμU hν
  have hzζ : compactIntegral DU IR hIR ζ = 0 := by
    change IR ν = 0
    rw [← heq]
    exact hz
  have hexact : ωU ∈ D.complex.exact (k+1) :=
    compact_exact_of_open_pullback_zero hExact S U R hR hbR oR hinc E hE C B K
      A F J D DU IR hIR ωU ζ hζ hzζ
  exact exists_supported_primitive_of_exact K U D k ωU hexact
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData FormPullbackData
  LocalIntegrationData GlobalIntegrationData Set Filter
open scoped Topology
universe u
section OpenCoefficient
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  (R : SmoothManifold n a U) (hinc : IsSmoothMap R S Subtype.val)
  (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
  (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)

include hinc hE

/-- Corresponding coordinates assign the same coefficient to intrinsic
pullback and the original ambient top form. -/
theorem topCoefficient_open_pullback
    (K : TangentBundleData.FiberCoordinates R) (H : TangentBundleData.FiberCoordinates S)
    (d : ModelChart n a U) (c : ModelChart n a M)
    (hd : d ∈ R.smoothStructure.val) (hc : c ∈ S.smoothStructure.val)
    (p : U) (hpd : p ∈ d.source) (hpc : p.val ∈ c.source)
    (hcoord : ∀ q : U, (d q).val = (c q.val).val) (ω : Field S n) :
    topCoefficient K d hd p hpd
      (FormPullbackData.pullbackField R S Subtype.val (k := n) (fun p => (E p).toLinearMap) ω) =
      topCoefficient H c hc p.val hpc ω := by
  have hframes :
      (fun i => E p (CovectorData.coordinateVector K d hd p hpd i)) =
        CovectorData.coordinateVector H c hc p.val hpc := by
    funext i
    apply (H.equiv c hc p.val hpc).injective
    have he := open_inclusion_coordinates S U R hinc p (E p).toLinearMap (hE p)
      d c hd hc hpd hpc hcoord K H (CovectorData.coordinateVector K d hd p hpd i)
    simpa only [CovectorData.coordinateVector, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using he
  change evaluate (TangentSpace R p) n
    (fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) n (E p).toLinearMap
      (ω p.val)) (CovectorData.coordinateVector K d hd p hpd) = _
  rw [FormPullbackResults.evaluate_fiberPullback]
  change evaluate (TangentSpace S p.val) n (ω p.val)
    (fun i => E p (CovectorData.coordinateVector K d hd p hpd i)) = _
  rw [hframes]
  rfl

/-- With ambient support inside U, the restricted chart has exactly the same
unsigned model coefficient, including the points outside its smaller target. -/
theorem modelCoefficient_open_pullback
    (K : TangentBundleData.FiberCoordinates R) (H : TangentBundleData.FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hne : Nonempty U)
    (hd : c.subtypeRestr hne ∈ R.smoothStructure.val)
    (ω : Field S n) (hs : ModelData.sectionSupport ω ⊆ U) :
    modelCoefficient K (c.subtypeRestr hne) hd
      (FormPullbackData.pullbackField R S Subtype.val (k := n) (fun p => (E p).toLinearMap) ω) =
      modelCoefficient H c hc ω := by
  funext x
  by_cases hx : x ∈ (c.subtypeRestr hne).target
  · have hcx : x ∈ c.target := c.subtypeRestr_target_subset hne hx
    have heq : ((c.subtypeRestr hne).symm x).val = c.symm x :=
      c.subtypeRestr_symm_apply hne hx
    have hpc : ((c.subtypeRestr hne).symm x).val ∈ c.source := by
      rw [heq]
      exact c.map_target hcx
    have hcoef := topCoefficient_open_pullback S U R hinc E hE K H
      (c.subtypeRestr hne) c hd hc ((c.subtypeRestr hne).symm x)
      ((c.subtypeRestr hne).map_target hx) hpc (fun _ => rfl) ω
    simpa only [modelCoefficient, dif_pos hx, dif_pos hcx, heq] using hcoef
  · by_cases hcx : x ∈ c.target
    · have hnotU : c.symm x ∉ U := by
        intro hu
        have hin := c.map_subtype_source hne (x := ⟨c.symm x, hu⟩) (c.map_target hcx)
        exact hx (by simpa only [c.right_inv hcx] using hin)
      have hz : ω (c.symm x) = 0 := by
        by_contra hn
        exact hnotU (hs (subset_closure hn))
      simp only [modelCoefficient, dif_neg hx, dif_pos hcx]
      simp [topCoefficient, hz]
    · simp only [modelCoefficient, dif_neg hx, dif_neg hcx]
end OpenCoefficient
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  FormPullbackData Set Filter
open scoped Topology BigOperators
universe u v
section Integral
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  (R : SmoothManifold n a U)
  (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)

/-- Corresponding restricted charts have the same orientation sign. -/
theorem open_inclusion_chart_sign
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (o : Orientation S) (oU : Orientation R)
    (ho : ∀ p, Module.Ray.map (determinantMap n (E p)) (oU.val p) = o.val p.val)
    (s : SignedCharts S) (t : SignedCharts R)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts oU.val t)
    (K : FiberCoordinates R) (H : FiberCoordinates S)
    (d : ModelChart n a U) (c : ModelChart n a M)
    (hd : d ∈ R.smoothStructure.val) (hc : c ∈ S.smoothStructure.val)
    (p : U) (hpd : p ∈ d.source) (hpc : p.val ∈ c.source)
    (hcoord : ∀ q : U, (d q).val = (c q.val).val) :
    signValue (t.sign d hd ⟨p, hpd⟩) = signValue (s.sign c hc ⟨p.val, hpc⟩) := by
  have hm : ((K.equiv d hd p hpd).symm.trans
      ((E p).trans (H.equiv c hc p.val hpc))).toLinearMap =
      (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n) := by
    apply LinearMap.ext
    intro v
    change H.equiv c hc p.val hpc (E p ((K.equiv d hd p hpd).symm v)) = v
    have hh := open_inclusion_coordinates S U R hinc p (E p).toLinearMap (hE p)
      d c hd hc hpd hpc hcoord K H ((K.equiv d hd p hpd).symm v)
    exact hh.trans ((K.equiv d hd p hpd).apply_symm_apply v)
  have h := DiffeomorphismLocalResults.coordinate_sign R S Subtype.val E oU o t s ht hs
    K H d c hd hc p hpd hpc
  simpa [orientationSign, ho p, hm, signValue] using h.symm
/-- Extending the restricted chart coefficient by zero preserves the signed
model integrand whenever the ambient field is supported inside the open set. -/
theorem modelSignedCoefficient_open_pullback
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (o : Orientation S) (oU : Orientation R)
    (ho : ∀ p, Module.Ray.map (determinantMap n (E p)) (oU.val p) = o.val p.val)
    (s : SignedCharts S) (t : SignedCharts R)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts oU.val t)
    (K : FiberCoordinates R) (H : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hne : Nonempty U)
    (hd : c.subtypeRestr hne ∈ R.smoothStructure.val)
    (ω : Field S n) (hω : ModelData.sectionSupport ω ⊆ U) :
    modelSignedCoefficient t K (c.subtypeRestr hne) hd
      (pullbackField R S Subtype.val (fun p => (E p).toLinearMap) ω) =
      modelSignedCoefficient s H c hc ω := by
  funext x
  by_cases hx : x ∈ (c.subtypeRestr hne).target
  · have hcx : x ∈ c.target := c.subtypeRestr_target_subset hne hx
    have heq : ((c.subtypeRestr hne).symm x).val = c.symm x :=
      c.subtypeRestr_symm_apply hne hx
    have hpc : ((c.subtypeRestr hne).symm x).val ∈ c.source := by
      rw [heq]
      exact c.map_target hcx
    have hcoef := topCoefficient_open_pullback S U R hinc E hE K H
      (c.subtypeRestr hne) c hd hc ((c.subtypeRestr hne).symm x)
      ((c.subtypeRestr hne).map_target hx) hpc (fun _ => rfl) ω
    have hsign := open_inclusion_chart_sign S U R E hinc hE o oU ho s t hs ht K H
      (c.subtypeRestr hne) c hd hc ((c.subtypeRestr hne).symm x)
      ((c.subtypeRestr hne).map_target hx) hpc (fun _ => rfl)
    have hm := congrArg₂ (fun a b : ℝ => a*b) hsign hcoef
    simpa only [modelSignedCoefficient, dif_pos hx, dif_pos hcx, heq] using hm
  · by_cases hcx : x ∈ c.target
    · have hnotU : c.symm x ∉ U := by
        intro hu
        have hin := c.map_subtype_source hne (x := ⟨c.symm x, hu⟩) (c.map_target hcx)
        exact hx (by simpa only [c.right_inv hcx] using hin)
      have hz : ω (c.symm x) = 0 := by
        by_contra hn
        exact hnotU (hω (subset_closure hn))
      simp only [modelSignedCoefficient, dif_neg hx, dif_pos hcx]
      simp [topCoefficient, hz]
    · simp only [modelSignedCoefficient, dif_neg hx, dif_neg hcx]

/-- Coordinate integration is unchanged by an oriented open inclusion, using
the actual signed integrands and without any compactness or smoothness shortcut. -/
theorem open_subset_coordinateIntegral
    (hinc : IsSmoothMap R S Subtype.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (o : Orientation S) (oU : Orientation R)
    (ho : ∀ p, Module.Ray.map (determinantMap n (E p)) (oU.val p) = o.val p.val)
    (s : SignedCharts S) (t : SignedCharts R)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts oU.val t)
    (K : FiberCoordinates R) (H : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hne : Nonempty U)
    (hd : c.subtypeRestr hne ∈ R.smoothStructure.val)
    (ω : Field S n) (hω : ModelData.sectionSupport ω ⊆ U) :
    coordinateIntegral t K (c.subtypeRestr hne) hd
      (pullbackField R S Subtype.val (fun p => (E p).toLinearMap) ω) =
      coordinateIntegral s H c hc ω := by
  have hm := modelSignedCoefficient_open_pullback S U R E hinc hE o oU ho s t hs ht
    K H c hc hne hd ω hω
  unfold coordinateIntegral signedCoordinateCoefficient
  rw [hm]

end Integral
end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  LocalIntegrationData GlobalIntegrationData FormPullbackData Set Filter
open scoped Topology
universe u v

/-- A localization restricts to the natural open submanifold with the same
indices; the closed supports and their local finiteness pull back exactly. -/
theorem localization_open_pullback
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    {ι : Type v} (c : ι → ModelChart n a M) (ρ : ι → M → ℝ)
    (μ : CompactTopForm S) (ν : CompactTopForm R)
    (hν : ν.field = FormPullbackData.pullbackField R S Subtype.val (k := n)
      (fun p => (E p).toLinearMap) μ.field)
    (hρ : IsLocalization c ρ μ) (hne : Nonempty U) :
    IsLocalization (fun i => (c i).subtypeRestr hne) (fun i p => ρ i p.val) ν := by
  have hsupp (i : ι) : ModelData.sectionSupport (fun p : U => ρ i p.val) =
      Subtype.val ⁻¹' ModelData.sectionSupport (ρ i) := sectionSupport_restrict U (ρ i)
  have hνsupp : ModelData.sectionSupport ν.field = Subtype.val ⁻¹' ModelData.sectionSupport μ.field := by
    rw [hν]
    exact sectionSupport_open_pullback S U R E n μ.field
  refine ⟨fun i => (hρ.1 i).comp continuous_subtype_val, ?_, ?_, ?_⟩
  · apply (hρ.2.1.preimage_continuous continuous_subtype_val).subset
    intro i p hp
    rwa [hsupp i] at hp
  · intro i p hp
    rw [hsupp i] at hp
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hρ.2.2.1 i hp
  · obtain ⟨V, hV, hμV, hsum⟩ := hρ.2.2.2
    refine ⟨Subtype.val ⁻¹' V, hV.preimage continuous_subtype_val, ?_, ?_⟩
    · intro p hp
      rw [hνsupp] at hp
      exact hμV hp
    · intro p hp
      exact hsum p.val hp

/-- Corresponding restricted charts belong to the natural maximal smooth atlas. -/
theorem open_chart_mem
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hne : Nonempty U) :
    c.subtypeRestr hne ∈ R.smoothStructure.val := by
  rw [hR]
  exact subset_maximalExtension
    (SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
      S.smoothStructure.property.1 U U.isOpen) ⟨hne, c, hc, rfl⟩
end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  FormPullbackData Set Filter
open scoped Topology
universe u

/-- Integration over an oriented open submanifold agrees with ambient
integration of the same compact form. Both are the original signed integrals;
localization reduces the comparison to corresponding restricted charts. -/
theorem open_integral_compatibility
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) :
    OpenIntegralCompatibility S o I := by
  classical
  intro U R E oR hR hinc hE ho IR hIR μ ν hμU hν
  by_cases hne : Nonempty U
  · obtain ⟨p0⟩ := hne
    obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
    obtain ⟨t, ht, _⟩ := LocalIntegrationResults.orientation_signs R oR
    obtain ⟨H⟩ := TangentBundle.fiberCoordinates_exists S
    obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists R
    let ι := {c : ModelChart n a M // c ∈ S.smoothStructure.val}
    let c : ι → ModelChart n a M := Subtype.val
    let d : ι → ModelChart n a U := fun i => (c i).subtypeRestr (s := U) ⟨p0⟩
    have hd (i : ι) : d i ∈ R.smoothStructure.val := by
      rw [hR]
      exact subset_maximalExtension
        (SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
          S.smoothStructure.property.1 U U.isOpen) ⟨⟨p0⟩,c i,i.property,rfl⟩
    obtain ⟨ρ, hρ⟩ := GlobalIntegrationResults.exists_chart_localization S μ
    have hρR : IsLocalization d (fun i p => ρ i p.val) ν :=
      localization_open_pullback S U R E c ρ μ ν hν hρ ⟨p0⟩
    rw [GlobalIntegrationResults.localization S o I hI s hs H c (fun i => i.property) ρ μ hρ,
      GlobalIntegrationResults.localization R oR IR hIR t ht K d hd
        (fun i p => ρ i p.val) ν hρR]
    apply finsum_congr
    intro i
    have hweighted : sectionSupport (fun p => ρ i p • μ.field p) ⊆ U :=
      ((GlobalIntegrationResults.weight_support S n μ.field (ρ i)).trans inter_subset_right).trans hμU
    have heq := open_subset_coordinateIntegral S U R E hinc hE o oR ho s t hs ht K H
      (c i) i.property ⟨p0⟩ (hd i) (fun p => ρ i p • μ.field p) hweighted
    have hfield :
        pullbackField R S Subtype.val (k := n) (fun p => (E p).toLinearMap)
          (fun p => ρ i p • μ.field p) = (fun p => ρ i p.val • ν.field p) := by
      funext p
      rw [hν]
      change fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val)
        n (E p).toLinearMap (ρ i p.val • μ.field p.val) =
        ρ i p.val • fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val)
          n (E p).toLinearMap (μ.field p.val)
      exact map_smul _ _ _
    simpa only [hfield] using heq.symm
  · have hempty (p : U) : False := hne ⟨p⟩
    have hzμ : μ.field = 0 := by
      funext p
      by_contra hn
      exact hempty ⟨p,hμU (subset_closure hn)⟩
    have hzν : ν.field = 0 := by
      funext p
      exact False.elim (hempty p)
    rw [StokesResults.integral_zero_field o I hI μ hzμ,
      StokesResults.integral_zero_field oR IR hIR ν hzν]

end SmoothManifolds.NoncompactTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
open ModelData AtlasData MapData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData CompactSupportData DifferentialData
  BoundaryData OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  FormPullbackData Set Filter
open scoped Topology
universe u

/-- Assembly under an explicit global open-inclusion integral compatibility
hypothesis. This is an intermediate theorem, not the original target binding. -/
theorem top_degree_of_open_integral_compatibility
    (hTop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (hCompat : ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
      (S : SmoothManifold n a M) (o : Orientation S) (I : CompactTopForm S → ℝ),
      IsIntegral o I → OpenIntegralCompatibility S o I) :
    Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u} := by
  intro n a M _ _ S hb o hnc C B K
  cases n with
  | zero => exact False.elim (hnc (zero_dimensional_compact S.topologicalManifold))
  | succ k =>
    obtain ⟨I, hI, _⟩ := GlobalIntegrationResults.exists_integral S o
    have hcompat := hCompat S o I hI
    let L := compactIntegral (CompactSupportResults.supportedCalculus K ⊤) I hI
    obtain ⟨W,hW,hcover,hlf,hlater⟩ := exists_escape_cover S.topologicalManifold hnc
    let V : ℕ → TopologicalSpace.Opens M := fun j => ⟨W j, (hW j).1⟩
    choose next hn hnext using hlater
    have hex (j : ℕ) : ∃ θ : CompactSupportResults.supportedForms K ⊤ (k+1),
        sectionSupport θ.val.val ⊆ V j ∩ V (next j) ∧ L θ = 1 :=
      exists_unit_supported_in_open hTop S hb o C B K I hI hcompat
        (V j ⊓ V (next j)) (hnext j)
    choose θ hθ hunit using hex
    have hcoverV : ∀ p, ∃ j, p ∈ V j := by
      intro p
      change ∃ j, p ∈ W j
      apply mem_iUnion.mp
      rw [hcover]
      exact mem_univ p
    apply all_exact_of_local_zero_mass_fillings K k V hlf hcoverV
      (fun j => (hW j).2.2) next hn L θ hθ hunit
    intro j γ hs hz
    obtain ⟨β, hcβ, hβ, hdβ⟩ :=
      exists_supported_primitive_of_open_integral_compatibility hExact S hb o C B K I hI hcompat (V j)
      (hW j).2.1 γ.val γ.property.1 hs hz
    exact ⟨β,hβ,hdβ⟩

end SmoothManifolds.NoncompactTopDegreeResults

set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.NoncompactTopDegreeResults
universe u

/-- Conditional derivation with precisely the owner's five full upstream
premises in the frozen order. The original closed target remains undefined. -/
theorem top_degree_conditional
    (_hCompactComparison :
      Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (_hCompactTopDegree :
      Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (hExact :
      Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (hTop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (_hZero : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u} :=
  top_degree_of_open_integral_compatibility hTop hExact open_integral_compatibility

end SmoothManifolds.NoncompactTopDegreeResults

universe v8_closure_042a367abaef0929_u0
theorem _root_.«SmoothManifolds».«NoncompactTopDegreeResults».«top_degree» : _root_.«Specs».«SmoothManifolds».«DeRham».«NoncompactTopDegree».«top_degreeType».{v8_closure_042a367abaef0929_u0} :=
  @_root_.«SmoothManifolds».«NoncompactTopDegreeResults».«top_degree_conditional».{v8_closure_042a367abaef0929_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_042a367abaef0929_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_042a367abaef0929_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_042a367abaef0929_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_042a367abaef0929_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_042a367abaef0929_u0})
