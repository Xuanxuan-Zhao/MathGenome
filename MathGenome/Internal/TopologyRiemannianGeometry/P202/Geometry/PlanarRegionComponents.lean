import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionComponents
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Applications.JordanBrouwer
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Complementary components of a planar region, paper.tex 4773–4787. -/
noncomputable section
open Set Topology Metric
open scoped ContDiff

namespace P202.PlanarRegionComponents
open P202Specs.PlanarRegionTopology
open P202.PlanarRegionTopology

/-- The subset represented by an actual connected-component class. -/
def componentSet {X : Type*} [TopologicalSpace X] (K : Set X)
    (a : ConnectedComponents K) : Set X :=
  Subtype.val '' {x : K | ConnectedComponents.mk x = a}

theorem componentSet_mk {X : Type*} [TopologicalSpace X] {K : Set X} (x : K) :
    componentSet K (ConnectedComponents.mk x) = connectedComponentIn K x.val := by
  unfold componentSet
  rw [connectedComponentIn_eq_image x.property]
  congr 1
  ext y
  exact ConnectedComponents.coe_eq_coe'

theorem mem_componentSet {X : Type*} [TopologicalSpace X] {K : Set X}
    {a : ConnectedComponents K} {x : K} :
    x.val ∈ componentSet K a ↔ ConnectedComponents.mk x = a := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (Subtype.ext heq : y = x) ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem componentSet_subset {X : Type*} [TopologicalSpace X] (K : Set X)
    (a : ConnectedComponents K) : componentSet K a ⊆ K := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem componentSet_connected {X : Type*} [TopologicalSpace X] (K : Set X)
    (a : ConnectedComponents K) : IsConnected (componentSet K a) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  rw [componentSet_mk]
  exact isConnected_connectedComponentIn_iff.mpr x.property

theorem componentSet_open {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hK : IsOpen K) (a : ConnectedComponents K) :
    IsOpen (componentSet K a) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  rw [componentSet_mk]
  exact hK.connectedComponentIn

theorem componentSet_disjoint {X : Type*} [TopologicalSpace X] {K : Set X}
    {a b : ConnectedComponents K} (h : a ≠ b) :
    Disjoint (componentSet K a) (componentSet K b) := by
  apply disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ hy
  exact h (hx.symm.trans (mem_componentSet.mp hy))

/-- Exact two-component data gives actual open sides with their prescribed
common frontier. -/
theorem two_sides_of_components {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {K : Set X} (hK : IsClosed K)
    (e : ConnectedComponents (Kᶜ : Set X) ≃ Fin 2)
    (hfront : ∀ x ∈ Kᶜ, frontier (connectedComponentIn Kᶜ x) = K) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Kᶜ ∧ frontier A = K ∧ frontier B = K := by
  let A := componentSet Kᶜ (e.symm 0)
  let B := componentSet Kᶜ (e.symm 1)
  refine ⟨A, B, componentSet_open hK.isOpen_compl _,
    componentSet_open hK.isOpen_compl _, componentSet_connected _ _,
    componentSet_connected _ _, componentSet_disjoint ?_, ?_, ?_, ?_⟩
  · exact e.symm.injective.ne (by decide)
  · apply Subset.antisymm
    · exact union_subset (componentSet_subset _ _) (componentSet_subset _ _)
    · intro x hx
      let hx' := e (ConnectedComponents.mk (⟨x, hx⟩ : (Kᶜ : Set X)))
      have hcases : hx' = 0 ∨ hx' = 1 := by omega
      rcases hcases with h | h
      · refine Or.inl ⟨⟨x, hx⟩, ?_, rfl⟩
        apply e.injective
        simpa [hx'] using h
      · refine Or.inr ⟨⟨x, hx⟩, ?_, rfl⟩
        apply e.injective
        simpa [hx'] using h
  · obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm 0)
    change frontier (componentSet Kᶜ (e.symm 0)) = K
    rw [← hx, componentSet_mk]
    exact hfront _ x.property
  · obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm 1)
    change frontier (componentSet Kᶜ (e.symm 1)) = K
    rw [← hx, componentSet_mk]
    exact hfront _ x.property

/-- The sphere adapters are applied to the actual parametrization. -/
theorem sphericalJordanSeparation : Expected.sphericalJordanSeparation := by
  intro c
  obtain ⟨h⟩ := compactificationSphere
  obtain ⟨q⟩ := parameterCircleSphere
  let f : P202.Duality.NeighborhoodCohomology.Sphere 1 →
      P202.Duality.NeighborhoodCohomology.Sphere 2 :=
    fun z => h (c.parametrization (q.symm z))
  have hf : Topology.IsEmbedding f :=
    h.isEmbedding.comp (OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      ((jordanCurve_embedding c).comp q.symm.isEmbedding))
  obtain ⟨⟨e⟩, he⟩ := P202.JordanBrouwer.separation 2 (by omega) f hf
  letI := P202.JordanBrouwer.sphere_locallyConnected 2
  obtain ⟨A, B, hA, hB, hcA, hcB, hd, hu, hfA, hfB⟩ :=
    two_sides_of_components (P202.JordanBrouwer.sphere_range_closed hf) e he
  have hrange : range f = h '' sphericalTrace c := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨_, ⟨q.symm t, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨q t, by simp [f]⟩
  have hp : h ⁻¹' range f = sphericalTrace c := by
    rw [hrange, preimage_image_eq _ h.injective]
  refine ⟨h ⁻¹' A, h ⁻¹' B, hA.preimage h.continuous, hB.preimage h.continuous,
    h.isConnected_preimage.mpr hcA, h.isConnected_preimage.mpr hcB,
    hd.preimage _, ?_, ?_, ?_⟩
  · rw [← preimage_union, hu, preimage_compl, hp]
  · rw [← h.preimage_frontier, hfA, hp]
  · rw [← h.preimage_frontier, hfB, hp]

/-- A connected open subset whose frontier is excluded from the ambient set
is a whole component, rather than only a connected subset of one. -/
theorem component_of_frontier_excluded {X : Type*} [TopologicalSpace X]
    {K A : Set X} (hA : IsOpen A) (hcA : IsConnected A) (hAK : A ⊆ K)
    (hf : Disjoint (frontier A) K) :
    ∃ a : ConnectedComponents K, componentSet K a = A := by
  obtain ⟨x, hx⟩ := hcA.nonempty
  refine ⟨ConnectedComponents.mk (⟨x, hAK hx⟩ : K), ?_⟩
  rw [componentSet_mk]
  apply Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hA
    · exact ⟨x, mem_connectedComponentIn (hAK hx), hx⟩
    · intro y hy
      by_contra hyA
      exact disjoint_left.mp hf
        (hA.frontier_eq.symm ▸ ⟨hy.1, hyA⟩)
        (connectedComponentIn_subset K x hy.2)
  · exact hcA.isPreconnected.subset_connectedComponentIn hx hAK

theorem sphericalCarrier_eq_closure (R : PlanarRegion) :
    sphericalCarrier R = closure ((fun x : Plane => (x : OnePoint Plane)) '' R.domain) := by
  apply Subset.antisymm
  · exact image_closure_subset_closure_image OnePoint.continuous_coe
  · exact closure_minimal (image_mono subset_closure)
      (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closure, R.compact_closure⟩)

theorem sphericalTrace_subset_carrier (R : PlanarRegion) (i : Fin R.boundaryCount) :
    sphericalTrace (R.curve i) ⊆ sphericalCarrier R := by
  apply image_mono
  intro x hx
  exact frontier_subset_closure (R.boundary_eq.symm ▸ mem_iUnion.mpr ⟨i, hx⟩)

theorem domain_disjoint_trace (R : PlanarRegion) (i : Fin R.boundaryCount) :
    Disjoint R.domain (R.curve i).trace := by
  apply disjoint_left.mpr
  intro x hx hc
  have hf : x ∈ frontier R.domain := R.boundary_eq.symm ▸ mem_iUnion.mpr ⟨i, hc⟩
  exact hf.2 (R.open_domain.interior_eq.symm ▸ hx)

theorem spherical_domain_subset_compl_trace (R : PlanarRegion) (i : Fin R.boundaryCount) :
    (fun x : Plane => (x : OnePoint Plane)) '' R.domain ⊆ (sphericalTrace (R.curve i))ᶜ := by
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have heq' := OnePoint.coe_injective heq
  exact disjoint_left.mp (domain_disjoint_trace R i) hx (heq' ▸ hy)

/-- A connected domain is on a single side of each individual Jordan curve;
the other side has no points even in the closure of the domain. -/
theorem outside_component_for_curve (R : PlanarRegion) (i : Fin R.boundaryCount) :
    ∃ a : ConnectedComponents (SphericalComplement R),
      frontier (componentSet (SphericalComplement R) a) = sphericalTrace (R.curve i) := by
  obtain ⟨A, B, hA, hB, hcA, hcB, hd, hu, hfA, hfB⟩ :=
    sphericalJordanSeparation (R.curve i)
  have hdom := (R.connected_domain.image _ OnePoint.continuous_coe.continuousOn).isPreconnected
  have hsub : (fun x : Plane => (x : OnePoint Plane)) '' R.domain ⊆ A ∪ B :=
    hu.symm ▸ spherical_domain_subset_compl_trace R i
  have make (E F : Set (OnePoint Plane)) (hE : IsOpen E) (hcE : IsConnected E)
      (hdis : Disjoint E F) (hdomF :
        (fun x : Plane => (x : OnePoint Plane)) '' R.domain ⊆ F)
      (hfront : frontier E = sphericalTrace (R.curve i)) :
      ∃ a : ConnectedComponents (SphericalComplement R),
        frontier (componentSet (SphericalComplement R) a) = sphericalTrace (R.curve i) := by
    have hclosure : sphericalCarrier R ⊆ Eᶜ := by
      rw [sphericalCarrier_eq_closure]
      exact closure_minimal (fun x hx hE => disjoint_left.mp hdis hE (hdomF hx))
        hE.isClosed_compl
    have hEK : E ⊆ SphericalComplement R := by
      intro x hx hK
      exact hclosure hK hx
    have hfrontK : Disjoint (frontier E) (SphericalComplement R) := by
      rw [hfront]
      exact disjoint_compl_right.mono_left (sphericalTrace_subset_carrier R i)
    obtain ⟨a, ha⟩ := component_of_frontier_excluded hE hcE hEK hfrontK
    exact ⟨a, by rw [ha, hfront]⟩
  rcases hdom.subset_or_subset hA hB hd hsub with h | h
  · exact make B A hB hcB hd.symm h hfB
  · exact make A B hA hcA hd h hfA

/-- The nonempty disjoint traces distinguish the corresponding components. -/
theorem curveOutsideComponents : Expected.curveOutsideComponents := by
  intro R
  classical
  choose a ha using outside_component_for_curve R
  have hinj : Function.Injective a := by
    intro i j hij
    have htrace : sphericalTrace (R.curve i) = sphericalTrace (R.curve j) := by
      rw [← ha i, ← ha j, hij]
    have heq : (R.curve i).trace = (R.curve j).trace :=
      (Set.image_injective.mpr OnePoint.coe_injective) htrace
    by_contra hne
    obtain ⟨x, hx⟩ := trace_nonempty (R.curve i)
    exact disjoint_left.mp (R.disjoint_curves hne) hx (heq ▸ hx)
  exact ⟨⟨a, hinj⟩, ha⟩

private instance compactifiedPlane_locallyConnected : LocallyConnectedSpace (OnePoint Plane) := by
  obtain ⟨h⟩ := compactificationSphere
  letI := P202.JordanBrouwer.sphere_locallyConnected 2
  exact h.locallyConnectedSpace

theorem sphericalCarrier_closed (R : PlanarRegion) : IsClosed (sphericalCarrier R) :=
  OnePoint.isClosed_image_coe.mpr ⟨isClosed_closure, R.compact_closure⟩

theorem sphericalComplement_open (R : PlanarRegion) : IsOpen (SphericalComplement R) :=
  (sphericalCarrier_closed R).isOpen_compl

theorem componentSet_subset_of_meets {X : Type*} [TopologicalSpace X]
    {K L : Set X} {a : ConnectedComponents K} (hL : IsPreconnected L) (hLK : L ⊆ K)
    (hmeet : (L ∩ componentSet K a).Nonempty) : L ⊆ componentSet K a := by
  obtain ⟨x, hxL, hxA⟩ := hmeet
  have hxa : ConnectedComponents.mk (⟨x, hLK hxL⟩ : K) = a := mem_componentSet.mp hxA
  rw [← hxa, componentSet_mk]
  exact hL.subset_connectedComponentIn hxL hLK

/-- Every frontier point of a complementary component is a point of the
original domain frontier, so it is on one of the specified curves. -/
theorem component_frontier_subset_boundary (R : PlanarRegion)
    (a : ConnectedComponents (SphericalComplement R)) :
    frontier (componentSet (SphericalComplement R) a) ⊆
      (fun x : Plane => (x : OnePoint Plane)) '' R.boundary := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  rw [componentSet_mk]
  intro y hy
  have hyK := P202.JordanBrouwer.frontier_component_subset
    (sphericalCarrier_closed R) x.property hy
  obtain ⟨p, hp, rfl⟩ := hyK
  refine ⟨p, ?_, rfl⟩
  rw [PlanarRegion.boundary, R.open_domain.frontier_eq]
  refine ⟨hp, ?_⟩
  intro hpU
  have hopen : IsOpen ((fun z : Plane => (z : OnePoint Plane)) '' R.domain) :=
    OnePoint.isOpen_image_coe.mpr R.open_domain
  obtain ⟨z, hzU, hzC⟩ := mem_closure_iff.mp (frontier_subset_closure hy)
    _ hopen (mem_image_of_mem _ hpU)
  apply connectedComponentIn_subset (SphericalComplement R) x.val hzC
  obtain ⟨w, hw, rfl⟩ := hzU
  exact mem_image_of_mem _ (subset_closure hw)

/-- The connected local outside neighborhoods exhaust the complementary
components. No collar and no precomputed component count is used. -/
theorem outside_components_surjective (R : PlanarRegion)
    (a : Fin R.boundaryCount → ConnectedComponents (SphericalComplement R))
    (ha : ∀ i, frontier (componentSet (SphericalComplement R) (a i)) =
      sphericalTrace (R.curve i)) : Function.Surjective a := by
  intro b
  let Q := componentSet (SphericalComplement R) b
  have hQne : Q.Nonempty := (componentSet_connected _ b).nonempty
  have hQnot : Q ≠ univ := by
    intro heq
    obtain ⟨p, hp⟩ := R.connected_domain.nonempty
    have hpQ : (p : OnePoint Plane) ∈ Q := heq ▸ mem_univ _
    exact componentSet_subset _ _ hpQ (mem_image_of_mem _ (subset_closure hp))
  obtain ⟨y, hy⟩ := nonempty_frontier_iff.mpr ⟨hQne, hQnot⟩
  obtain ⟨p, hp, rfl⟩ := component_frontier_subset_boundary R b hy
  have hp' : p ∈ ⋃ i, (R.curve i).trace := R.boundary_eq ▸ hp
  obtain ⟨i, hpi⟩ := mem_iUnion.mp hp'
  have hpQ : (p : OnePoint Plane) ∈ frontier Q := hy
  have hpA : (p : OnePoint Plane) ∈ frontier (componentSet (SphericalComplement R) (a i)) := by
    rw [ha i]
    exact mem_image_of_mem _ hpi
  obtain ⟨N, hN, hpN, _, _, hcN⟩ := R.one_sided p hp univ isOpen_univ (mem_univ _)
  let L : Set (OnePoint Plane) :=
    (fun z : Plane => (z : OnePoint Plane)) '' (N \ R.carrier)
  have hcL : IsConnected L := hcN.image _ OnePoint.continuous_coe.continuousOn
  have hLK : L ⊆ SphericalComplement R := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    exact hz.2 (OnePoint.coe_injective heq ▸ hw)
  have hmeet (d : ConnectedComponents (SphericalComplement R))
      (hpD : (p : OnePoint Plane) ∈ frontier (componentSet (SphericalComplement R) d)) :
      (L ∩ componentSet (SphericalComplement R) d).Nonempty := by
    obtain ⟨z, hzN, hzD⟩ := mem_closure_iff.mp (frontier_subset_closure hpD)
      _ (OnePoint.isOpen_image_coe.mpr hN) (mem_image_of_mem _ hpN)
    obtain ⟨w, hwN, rfl⟩ := hzN
    have hwK : w ∉ R.carrier := by
      intro hw
      exact componentSet_subset _ _ hzD (mem_image_of_mem _ hw)
    exact ⟨_, ⟨w, ⟨hwN, hwK⟩, rfl⟩, hzD⟩
  have hsubA := componentSet_subset_of_meets hcL.isPreconnected hLK (hmeet (a i) hpA)
  obtain ⟨z, hzL, hzb⟩ := hmeet b hpQ
  have hza : z ∈ componentSet (SphericalComplement R) (a i) := hsubA hzL
  have hzK := hLK hzL
  exact ⟨i, ((mem_componentSet (x := ⟨z, hzK⟩)).mp hza).symm.trans
    ((mem_componentSet (x := ⟨z, hzK⟩)).mp hzb)⟩

/-- Exact component count and boundary matching for the spherical complement. -/
theorem sphericalComponents : Expected.sphericalComponents := by
  intro R
  obtain ⟨e, he⟩ := curveOutsideComponents R
  have hsurj := outside_components_surjective R e he
  exact ⟨Equiv.ofBijective e ⟨e.injective, hsurj⟩, he⟩

theorem connected_compl_closedBall (r : ℝ) (hr : 0 < r) :
    IsConnected (Metric.closedBall (0 : Plane) r)ᶜ := by
  have hdim : 1 < Module.rank ℝ Plane := by
    simp [← Module.finrank_eq_rank, Plane]
  have hc : IsConnected ((Ioi r) ×ˢ Metric.sphere (0 : Plane) 1) :=
    isConnected_Ioi.prod (isConnected_sphere hdim 0 (by norm_num))
  have him : (fun z : ℝ × Plane => z.1 • z.2) ''
      ((Ioi r) ×ˢ Metric.sphere (0 : Plane) 1) = (Metric.closedBall (0 : Plane) r)ᶜ := by
    ext v
    constructor
    · rintro ⟨⟨s, w⟩, ⟨hs, hw⟩, rfl⟩
      have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        hw', mul_one, not_le]
      simpa [abs_of_pos (hr.trans hs)] using hs
    · intro hv
      have hv' : r < ‖v‖ := by simpa using hv
      have hpos : 0 < ‖v‖ := hr.trans hv'
      refine ⟨(‖v‖, ‖v‖⁻¹ • v), ⟨hv', ?_⟩, ?_⟩
      · simp [mem_sphere_zero_iff_norm, norm_smul, abs_of_pos hpos, hpos.ne']
      · simp [smul_smul, hpos.ne']
  rw [← him]
  exact hc.image _ (by fun_prop)

/-- Removing infinity from a connected open subset of the compactified
plane leaves a connected planar subset. The punctured neighborhood used
here is the exterior of a sufficiently large closed ball. -/
theorem planarPart_connected_of_infty
    {A : Set (OnePoint Plane)} (hA : IsOpen A) (hcA : IsConnected A)
    (hinfty : (OnePoint.infty : OnePoint Plane) ∈ A) : IsConnected (planarPart A) := by
  let P := planarPart A
  have hP : IsOpen P := hA.preimage OnePoint.continuous_coe
  have hPc : IsCompact Pᶜ := (OnePoint.isOpen_iff_of_mem' hinfty).mp hA |>.1
  obtain ⟨r, hr, hbound⟩ := hPc.isBounded.subset_closedBall_lt 0 (0 : Plane)
  have hLP : (Metric.closedBall (0 : Plane) r)ᶜ ⊆ P := by
    intro x hx
    by_contra hxP
    exact hx (hbound hxP)
  have hcL := connected_compl_closedBall r hr
  obtain ⟨x, hx⟩ := hcL.nonempty
  let Q := connectedComponentIn P x
  have hLQ : (Metric.closedBall (0 : Plane) r)ᶜ ⊆ Q :=
    hcL.isPreconnected.subset_connectedComponentIn hx hLP
  have hQ : IsOpen Q := hP.connectedComponentIn
  have hQcompact : IsCompact Qᶜ :=
    (isCompact_closedBall (0 : Plane) r).of_isClosed_subset hQ.isClosed_compl
      (by intro z hz; by_contra hzball; exact hz (hLQ hzball))
  let E : Set (OnePoint Plane) := (fun z : Plane => (z : OnePoint Plane)) '' Q ∪ {OnePoint.infty}
  have hPE : (fun z : Plane => (z : OnePoint Plane)) ⁻¹' E = Q := by
    change ((↑) : Plane → OnePoint Plane) ⁻¹' (((↑) : Plane → OnePoint Plane) '' Q ∪ {OnePoint.infty}) = Q
    rw [preimage_union, preimage_image_eq _ OnePoint.coe_injective,
      OnePoint.coe_preimage_infty, union_empty]
  have hE : IsOpen E := by
    apply OnePoint.isOpen_def.mpr
    rw [hPE]
    exact ⟨fun _ => hQcompact, hQ⟩
  have hsubset : A ⊆ E := by
    apply hcA.isPreconnected.subset_of_closure_inter_subset hE
    · exact ⟨OnePoint.infty, hinfty, Or.inr (mem_singleton _)⟩
    · intro z hz
      by_cases hzinfty : z = OnePoint.infty
      · exact Or.inr hzinfty
      · obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hzinfty
        have hwclosure : w ∈ closure Q := by
          have hcl : closure E = closure ((fun z : Plane => (z : OnePoint Plane)) '' Q) ∪
              {OnePoint.infty} := by
            change closure (((↑) : Plane → OnePoint Plane) '' Q ∪ {OnePoint.infty}) = _
            rw [closure_union, OnePoint.isClosed_infty.closure_eq]
          rw [hcl] at hz
          have hw : (w : OnePoint Plane) ∈
              closure ((fun z : Plane => (z : OnePoint Plane)) '' Q) :=
            hz.1.resolve_right (OnePoint.coe_ne_infty w)
          exact (OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image Q) ▸ hw
        have hwP : w ∈ P := hz.2
        exact Or.inl ⟨w, P202.JordanBrouwer.closure_component_inter_subset (hLP hx) ⟨hwclosure, hwP⟩, rfl⟩
  have hPQ : P = Q := by
    apply Subset.antisymm
    · intro w hw
      have := hsubset hw
      change (w : OnePoint Plane) ∈ E at this
      exact hPE ▸ this
    · exact connectedComponentIn_subset P x
  rw [show planarPart A = Q from hPQ]
  exact isConnected_connectedComponentIn_iff.mpr (hLP hx)

theorem planarPart_connected
    {A : Set (OnePoint Plane)} (hA : IsOpen A) (hcA : IsConnected A) :
    IsConnected (planarPart A) := by
  by_cases hinfty : (OnePoint.infty : OnePoint Plane) ∈ A
  · exact planarPart_connected_of_infty hA hcA hinfty
  · exact hcA.preimage_of_isOpenMap OnePoint.coe_injective OnePoint.isOpenMap_coe
      (by intro z hz; exact OnePoint.ne_infty_iff_exists.mp (by intro h; exact hinfty (h ▸ hz)))

theorem planarPart_unbounded_of_infty {A : Set (OnePoint Plane)} (hA : IsOpen A)
    (hinfty : (OnePoint.infty : OnePoint Plane) ∈ A) :
    ¬Bornology.IsBounded (planarPart A) := by
  intro hb
  have hc : IsCompact (planarPart A)ᶜ := (OnePoint.isOpen_iff_of_mem' hinfty).mp hA |>.1
  have hbu := hb.union hc.isBounded
  rw [union_compl_self] at hbu
  exact NormedSpace.unbounded_univ ℝ Plane hbu

theorem planarPart_bounded_of_not_infty {A : Set (OnePoint Plane)}
    (hfront : (OnePoint.infty : OnePoint Plane) ∉ frontier A)
    (hinfty : (OnePoint.infty : OnePoint Plane) ∉ A) :
    Bornology.IsBounded (planarPart A) := by
  have hcl : (OnePoint.infty : OnePoint Plane) ∉ closure A := by
    rw [closure_eq_self_union_frontier]
    exact fun h => h.elim hinfty hfront
  have hc : IsCompact (planarPart (closure A)) :=
    ((OnePoint.isClosed_iff_of_notMem hcl).mp isClosed_closure).2
  exact hc.isBounded.subset (preimage_mono subset_closure)

/-- Order the two spherical sides by their membership of infinity. -/
theorem sphericalJordanSides (c : RegularJordanCurve) : Nonempty (SphericalJordanSides c) := by
  obtain ⟨A, B, hA, hB, hcA, hcB, hd, hu, hfA, hfB⟩ := sphericalJordanSeparation c
  have hi : (OnePoint.infty : OnePoint Plane) ∈ A ∪ B :=
    hu.symm ▸ OnePoint.infty_notMem_image_coe
  rcases hi with hi | hi
  · exact ⟨⟨B, A, hB, hA, hcB, hcA, hd.symm, (union_comm B A).trans hu, hfB, hfA,
      fun h => disjoint_left.mp hd hi h, hi⟩⟩
  · exact ⟨⟨A, B, hA, hB, hcA, hcB, hd, hu, hfA, hfB,
      fun h => disjoint_left.mp hd h hi, hi⟩⟩

theorem planar_frontier_side {c : RegularJordanCurve} {A : Set (OnePoint Plane)}
    (hfront : frontier A = sphericalTrace c) : frontier (planarPart A) = c.trace := by
  change frontier (((↑) : Plane → OnePoint Plane) ⁻¹' A) = c.trace
  rw [← OnePoint.isOpenMap_coe.preimage_frontier_eq_frontier_preimage
    OnePoint.continuous_coe, hfront]
  exact preimage_image_eq _ OnePoint.coe_injective

theorem spherical_side_bounded {c : RegularJordanCurve} (J : SphericalJordanSides c) :
    Bornology.IsBounded (planarPart J.boundedSide) := by
  apply planarPart_bounded_of_not_infty _ J.infinity_not_bounded
  rw [J.bounded_frontier]
  exact OnePoint.infty_notMem_image_coe

theorem planarJordanSeparation : Expected.planarJordanSeparation := by
  intro c
  obtain ⟨J⟩ := sphericalJordanSides c
  refine ⟨planarPart J.boundedSide, planarPart J.unboundedSide,
    J.bounded_open.preimage OnePoint.continuous_coe,
    J.unbounded_open.preimage OnePoint.continuous_coe,
    planarPart_connected J.bounded_open J.bounded_connected,
    planarPart_connected J.unbounded_open J.unbounded_connected,
    spherical_side_bounded J,
    planarPart_unbounded_of_infty J.unbounded_open J.infinity_unbounded,
    J.disjoint.preimage _, ?_, planar_frontier_side J.bounded_frontier,
    planar_frontier_side J.unbounded_frontier⟩
  change _ ⁻¹' J.boundedSide ∪ _ ⁻¹' J.unboundedSide = _
  rw [← preimage_union, J.union_eq, preimage_compl]
  congr 1
  exact preimage_image_eq _ OnePoint.coe_injective

/-- A connected open set with exactly the Jordan frontier must be an entire
Jordan side. Equality of frontiers rules out any additional holes. -/
theorem eq_jordan_side {c : RegularJordanCurve} (J : SphericalJordanSides c)
    {Q : Set (OnePoint Plane)} (hQ : IsOpen Q) (hcQ : IsConnected Q)
    (hsub : Q ⊆ (sphericalTrace c)ᶜ) (hfQ : frontier Q = sphericalTrace c) :
    Q = J.boundedSide ∨ Q = J.unboundedSide := by
  have eq_side (E : Set (OnePoint Plane)) (hcE : IsConnected E)
      (hEQ : Q ⊆ E) (hEC : E ⊆ (sphericalTrace c)ᶜ) : Q = E := by
    apply Subset.antisymm hEQ
    apply hcE.isPreconnected.subset_of_closure_inter_subset hQ
    · obtain ⟨x, hx⟩ := hcQ.nonempty
      exact ⟨x, hEQ hx, hx⟩
    · intro x hx
      by_contra hxQ
      have hxf : x ∈ frontier Q := hQ.frontier_eq.symm ▸ ⟨hx.1, hxQ⟩
      exact hEC hx.2 (hfQ ▸ hxf)
  have hcover : Q ⊆ J.boundedSide ∪ J.unboundedSide := J.union_eq.symm ▸ hsub
  rcases hcQ.isPreconnected.subset_or_subset J.bounded_open J.unbounded_open J.disjoint hcover with h | h
  · exact Or.inl (eq_side _ J.bounded_connected h
      (fun x hx => J.union_eq ▸ Or.inl hx))
  · exact Or.inr (eq_side _ J.unbounded_connected h
      (fun x hx => J.union_eq ▸ Or.inr hx))

/-- The unique actual component containing infinity. -/
def infinityComponent (R : PlanarRegion) : ConnectedComponents (SphericalComplement R) :=
  ConnectedComponents.mk ⟨OnePoint.infty, OnePoint.infty_notMem_image_coe⟩

theorem infinity_mem_component_iff (R : PlanarRegion)
    (a : ConnectedComponents (SphericalComplement R)) :
    (OnePoint.infty : OnePoint Plane) ∈ componentSet (SphericalComplement R) a ↔
      a = infinityComponent R := by
  rw [mem_componentSet (x := ⟨OnePoint.infty, OnePoint.infty_notMem_image_coe⟩)]
  exact eq_comm

/-- Construction of all the geometric complement data, independently of any
collar, surface charts or induced orientation choice. -/
theorem complementData : Expected.complementData := by
  intro R
  classical
  obtain ⟨e, he⟩ := sphericalComponents R
  let J (i : Fin R.boundaryCount) : SphericalJordanSides (R.curve i) :=
    Classical.choice (sphericalJordanSides (R.curve i))
  let Q (i : Fin R.boundaryCount) := sphericalComponentSet R (e i)
  let outer := e.symm (infinityComponent R)
  have hinf (i : Fin R.boundaryCount) :
      (OnePoint.infty : OnePoint Plane) ∈ Q i ↔ i = outer := by
    change _ ∈ componentSet (SphericalComplement R) (e i) ↔ _
    rw [infinity_mem_component_iff]
    exact e.apply_eq_iff_eq_symm_apply
  have hside (i : Fin R.boundaryCount) :
      Q i = (J i).boundedSide ∨ Q i = (J i).unboundedSide := by
    apply eq_jordan_side (J i) (componentSet_open (sphericalComplement_open R) _)
      (componentSet_connected _ _) _ (he i)
    exact (componentSet_subset _ _).trans (compl_subset_compl.mpr (sphericalTrace_subset_carrier R i))
  have hQ (i : Fin R.boundaryCount) :
      Q i = if i = outer then (J i).unboundedSide else (J i).boundedSide := by
    split_ifs with hi
    · rcases hside i with h | h
      · exact False.elim ((J i).infinity_not_bounded (h ▸ (hinf i).mpr hi))
      · exact h
    · rcases hside i with h | h
      · exact h
      · exact False.elim (hi ((hinf i).mp (h.symm ▸ (J i).infinity_unbounded)))
  let S : BoundarySides R :=
    { boundedSide := fun i => planarPart (J i).boundedSide
      unboundedSide := fun i => planarPart (J i).unboundedSide
      bounded_open := fun i => (J i).bounded_open.preimage OnePoint.continuous_coe
      unbounded_open := fun i => (J i).unbounded_open.preimage OnePoint.continuous_coe
      bounded_connected := fun i => planarPart_connected (J i).bounded_open (J i).bounded_connected
      unbounded_connected := fun i => planarPart_connected (J i).unbounded_open (J i).unbounded_connected
      bounded := fun i => spherical_side_bounded (J i)
      unbounded := fun i => planarPart_unbounded_of_infty (J i).unbounded_open (J i).infinity_unbounded
      sides_disjoint := fun i => (J i).disjoint.preimage _
      sides_union := fun i => by
        change _ ⁻¹' (J i).boundedSide ∪ _ ⁻¹' (J i).unboundedSide = _
        rw [← preimage_union, (J i).union_eq, preimage_compl]
        congr 1
        exact preimage_image_eq _ OnePoint.coe_injective
      bounded_frontier := fun i => planar_frontier_side (J i).bounded_frontier
      unbounded_frontier := fun i => planar_frontier_side (J i).unbounded_frontier
      outer := outer
      domain_side := by
        intro i p hp
        have hpC := spherical_domain_subset_compl_trace R i (mem_image_of_mem _ hp)
        have hpcover : (p : OnePoint Plane) ∈ (J i).boundedSide ∪ (J i).unboundedSide :=
          (J i).union_eq.symm ▸ hpC
        have hpQ : (p : OnePoint Plane) ∉ Q i := by
          intro h
          exact componentSet_subset (SphericalComplement R) (e i) h
            (mem_image_of_mem _ (subset_closure hp))
        rw [hQ i] at hpQ
        split_ifs at hpQ ⊢ with hi
        · exact hpcover.resolve_right hpQ
        · exact hpcover.resolve_left hpQ }
  refine ⟨{
    sides := S
    component := e
    frontier_component := he
    planar_component := ?_
    infinity_iff := hinf
    unbounded_iff := ?_ }⟩
  · intro i
    change planarPart (Q i) = if i = outer then planarPart (J i).unboundedSide else planarPart (J i).boundedSide
    rw [hQ i]
    split_ifs <;> rfl
  · intro i
    change ¬Bornology.IsBounded (planarPart (Q i)) ↔ i = outer
    rw [hQ i]
    split_ifs with hi
    · exact ⟨fun _ => hi, fun _ => S.unbounded i⟩
    · exact ⟨fun h => False.elim (h (S.bounded i)), fun h => False.elim (hi h)⟩


/-- Finite join sets leave genuine smooth parameters, so the normal test is
not vacuous. -/
theorem exists_parameter_not_join (c : RegularJordanCurve) :
    ∃ t : ℝ, (t : ParameterCircle) ∉ c.joins := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : Infinite ParameterCircle := (AddCircle.equivIco (1 : ℝ) 0).infinite_iff.mpr
    (Set.infinite_coe_iff.mpr (Set.Ico_infinite (by norm_num)))
  obtain ⟨u, hu⟩ := c.joins.exists_notMem
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective u
  exact ⟨t, hu⟩

theorem hasSideOnLeft_mono {A B : Set Plane} {c : RegularJordanCurve} {s : ℝ}
    (hAB : A ⊆ B) (hA : HasSideOnLeft A c s) : HasSideOnLeft B c s := by
  intro t ht
  obtain ⟨ε, hε, htest⟩ := hA t ht
  exact ⟨ε, hε, fun r hr hrε => hAB (htest r hr hrε)⟩

theorem not_hasSideOnLeft_of_disjoint {A B : Set Plane} {c : RegularJordanCurve} {s : ℝ}
    (hd : Disjoint A B) (hA : HasSideOnLeft A c s) : ¬HasSideOnLeft B c s := by
  intro hB
  obtain ⟨t, ht⟩ := exists_parameter_not_join c
  obtain ⟨ε, hε, htestA⟩ := hA t ht
  obtain ⟨δ, hδ, htestB⟩ := hB t ht
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hre : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrd : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  exact disjoint_left.mp hd (htestA r hr hre) (htestB r hr hrd)

theorem boundedSideOnLeft : Expected.boundedSideOnLeft := by
  intro R S s hs i
  by_cases hi : i = S.outer
  · have hsub : R.domain ⊆ S.boundedSide i := by simpa [hi] using S.domain_side i
    exact ⟨fun _ => hi, fun _ => hasSideOnLeft_mono hsub (hs i).2⟩
  · have hsub : R.domain ⊆ S.unboundedSide i := by simpa [hi] using S.domain_side i
    have hnot := not_hasSideOnLeft_of_disjoint (S.sides_disjoint i).symm
      (hasSideOnLeft_mono hsub (hs i).2)
    exact ⟨fun h => False.elim (hnot h), fun h => False.elim (hi h)⟩


namespace SmoothNormal

theorem realLift_deriv_ne_zero (c : RegularJordanCurve) (t : ℝ)
    (ht : (t : ParameterCircle) ∉ c.joins) :
    deriv (realLift c.parametrization) t ≠ 0 := by
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hnon⟩ := c.regular_joins t
  have hlt : t - δ < t := by linarith
  have hti : t ∈ Ioo (t - δ) (t + δ) := by constructor <;> linarith
  have htc : t ∈ Icc (t - δ) t := ⟨hlt.le, le_rfl⟩
  have hd : DifferentiableAt ℝ (realLift c.parametrization) t :=
    (c.smooth_off_joins t ht).differentiableAt (by simp)
  have hld : DifferentiableAt ℝ l t :=
    ((hl.contDiffAt (isOpen_Ioo.mem_nhds hti))).differentiableAt (by simp)
  have hu : UniqueDiffWithinAt ℝ (Icc (t - δ) t) t :=
    uniqueDiffOn_Icc hlt t htc
  have heq : deriv l t = deriv (realLift c.parametrization) t := by
    rw [← hld.derivWithin hu, ← hd.derivWithin hu]
    exact derivWithin_congr hel (hel htc)
  exact heq ▸ hnl

private theorem sumsq_ne_zero {v : Plane} (hv : v ≠ 0) :
    v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
  intro h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
  apply hv
  ext i
  fin_cases i <;> simp_all

def normalFrame (v : Plane) (hv : v ≠ 0) : (ℝ × ℝ) ≃L[ℝ] Plane :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun z => z.1 • v + z.2 • quarterTurn v
    invFun := fun w =>
      ((w 0 * v 0 + w 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2),
        (-w 0 * v 1 + w 1 * v 0) / (v 0 ^ 2 + v 1 ^ 2))
    map_add' := by intro z w; simp [add_smul, add_add_add_comm]
    map_smul' := by intro a z; simp [smul_add, mul_smul]
    left_inv := by
      intro z
      ext <;> simp [quarterTurn] <;> field_simp [sumsq_ne_zero hv] <;> ring
    right_inv := by
      intro w
      ext i
      fin_cases i <;> simp [quarterTurn] <;> field_simp [sumsq_ne_zero hv] <;> ring }

@[simp] theorem normalFrame_apply (v : Plane) (hv : v ≠ 0) (z : ℝ × ℝ) :
  normalFrame v hv z = z.1 • v + z.2 • quarterTurn v := rfl

/-- The fixed-normal extension of a smooth regular arc is locally invertible. -/
theorem normal_chart {f : ℝ → Plane} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ f t) (hv : deriv f t ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) Plane,
      (t, 0) ∈ e.source ∧
      ∀ z : ℝ × ℝ, e z = f z.1 + z.2 • quarterTurn (deriv f t) := by
  let v := deriv f t
  let F : (ℝ × ℝ) → Plane := fun z => f z.1 + z.2 • quarterTurn v
  have hdiff : DifferentiableAt ℝ f t := hf.differentiableAt (by simp)
  have hF : ContDiffAt ℝ ∞ F (t, 0) := by
    apply ContDiffAt.add
    · exact hf.comp (t, 0) contDiffAt_fst
    · exact contDiffAt_snd.smul contDiffAt_const
  have hdF : HasFDerivAt F (normalFrame v hv : (ℝ × ℝ) →L[ℝ] Plane) (t, 0) := by
    have h1 := hdiff.hasDerivAt.hasFDerivAt.comp (t, (0 : ℝ)) (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, (0 : ℝ))))
    have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := (t, (0 : ℝ)))).smul_const (quarterTurn v)
    have heq : (normalFrame v hv : (ℝ × ℝ) →L[ℝ] Plane) =
        (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (quarterTurn v) := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    rw [heq]
    exact h1.add h2
  refine ⟨hF.toOpenPartialHomeomorph F hdF (by simp),
    hF.mem_toOpenPartialHomeomorph_source hdF (by simp), ?_⟩
  intro z
  rfl


theorem local_trace_isolation (c : RegularJordanCurve) (t δ : ℝ) (hδ : 0 < δ) :
    ∃ O : Set Plane, IsOpen O ∧ realLift c.parametrization t ∈ O ∧
      O ∩ c.trace ⊆ realLift c.parametrization '' Ioo (t - δ) (t + δ) := by
  let S : Set ParameterCircle := (fun s : ℝ => (s : ParameterCircle)) '' Ioo (t - δ) (t + δ)
  have hS : IsOpen S := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨O, hO, hEq⟩ :=
    (P202.PlanarRegionTopology.jordanCurve_embedding c).isInducing.image_eq_isOpen_inter_range hS
  refine ⟨O, hO, ?_, ?_⟩
  · have hmem : c.parametrization (t : ParameterCircle) ∈ c.parametrization '' S := by
      exact ⟨(t : ParameterCircle), ⟨t, ⟨by linarith, by linarith⟩, rfl⟩, rfl⟩
    rw [hEq] at hmem
    exact hmem.1
  · intro x hx
    have hx' : x ∈ c.parametrization '' S := by
      rw [hEq]
      exact hx
    rcases hx' with ⟨s, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, rfl⟩

private theorem rectangle_subset_ball (t r : ℝ) :
    Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ Metric.ball (t, (0 : ℝ)) r := by
  intro z hz
  rcases hz with ⟨⟨hl, hu⟩, ⟨hl', hu'⟩⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · simpa only [Real.dist_eq, sub_zero, abs_lt] using And.intro hl' hu'

/-- Shrinking a fixed-normal chart excludes all other pieces of the Jordan trace. -/
theorem trace_rectangle (c : RegularJordanCurve) (t : ℝ) (n : Plane)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (ht : (t, 0) ∈ e.source)
    (he : ∀ z : ℝ × ℝ, e z = realLift c.parametrization z.1 + z.2 • n) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      Ioo (t - δ) (t + δ) ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ z ∈ Ioo (t - δ) (t + δ) ×ˢ Ioo (-ε) ε,
        e z ∈ c.trace ↔ z.2 = 0 := by
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds ht)
  have hline : ∀ u ∈ Ioo (t-a) (t+a), (u, 0) ∈ e.source := by
    intro u hu
    exact hball (rectangle_subset_ball t a ⟨hu, by constructor <;> linarith⟩)
  obtain ⟨O, hO, hpO, htrace⟩ := local_trace_isolation c t a ha
  have htO : (t, 0) ∈ e.source ∩ e ⁻¹' O := by
    refine ⟨ht, ?_⟩
    simpa only [mem_preimage, he, zero_smul, add_zero] using hpO
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp
    ((e.isOpen_inter_preimage hO).mem_nhds htO)
  refine ⟨r, r, hr, hr, ?_, ?_⟩
  · exact (rectangle_subset_ball t r).trans (hrball.trans inter_subset_left)
  · intro z hz
    have hzO := hrball (rectangle_subset_ball t r hz)
    constructor
    · intro hztrace
      obtain ⟨u, hu, heu⟩ := htrace ⟨hzO.2, hztrace⟩
      have heq : e z = e (u, 0) := by
        calc e z = realLift c.parametrization u := heu.symm
             _ = e (u, 0) := by simp only [he, zero_smul, add_zero]
      exact congrArg Prod.snd (e.injOn hzO.1 (hline u hu) heq)
    · intro hz0
      refine ⟨(z.1 : ParameterCircle), ?_⟩
      simp only [he, hz0, zero_smul, add_zero, realLift]

namespace ChartSides

variable {X : Type*} [TopologicalSpace X]

theorem rectangle_sides (e : OpenPartialHomeomorph (ℝ × ℝ) X)
    (t δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hrect : Ioo (t-δ) (t+δ) ×ˢ Ioo (-ε) ε ⊆ e.source)
    (A B T : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hd : Disjoint A B) (hu : A ∪ B = Tᶜ)
    (hfA : frontier A = T) (hfB : frontier B = T)
    (htrace : ∀ z ∈ Ioo (t-δ) (t+δ) ×ˢ Ioo (-ε) ε, e z ∈ T ↔ z.2 = 0) :
    (e '' (Ioo (t-δ) (t+δ) ×ˢ Ioo 0 ε) ⊆ A ∧
      e '' (Ioo (t-δ) (t+δ) ×ˢ Ioo (-ε) 0) ⊆ B) ∨
    (e '' (Ioo (t-δ) (t+δ) ×ˢ Ioo 0 ε) ⊆ B ∧
      e '' (Ioo (t-δ) (t+δ) ×ˢ Ioo (-ε) 0) ⊆ A) := by
  let I := Ioo (t-δ) (t+δ)
  let P := I ×ˢ Ioo 0 ε
  let N := I ×ˢ Ioo (-ε) 0
  let W := I ×ˢ Ioo (-ε) ε
  have htI : t ∈ I := by constructor <;> linarith
  have h0 : (t, (0 : ℝ)) ∈ W := ⟨htI, by constructor <;> linarith⟩
  have hPW : P ⊆ W := by rintro z ⟨hzI, hz⟩; exact ⟨hzI, by constructor <;> linarith [hz.1, hz.2]⟩
  have hNW : N ⊆ W := by rintro z ⟨hzI, hz⟩; exact ⟨hzI, by constructor <;> linarith [hz.1, hz.2]⟩
  have hcP : IsPreconnected (e '' P) :=
    ((isConnected_Ioo (by linarith : t-δ < t+δ)).prod (isConnected_Ioo hε)).isPreconnected.image e
      (e.continuousOn.mono (hPW.trans hrect))
  have hcN : IsPreconnected (e '' N) :=
    ((isConnected_Ioo (by linarith : t-δ < t+δ)).prod (isConnected_Ioo (by linarith : -ε < 0))).isPreconnected.image e
      (e.continuousOn.mono (hNW.trans hrect))
  have hsubP : e '' P ⊆ A ∪ B := by
    rw [hu]
    rintro _ ⟨z, hz, rfl⟩ hT
    have hz0 := (htrace z (hPW hz)).mp hT
    exact (ne_of_gt hz.2.1) hz0
  have hsubN : e '' N ⊆ A ∪ B := by
    rw [hu]
    rintro _ ⟨z, hz, rfl⟩ hT
    have hz0 := (htrace z (hNW hz)).mp hT
    exact (ne_of_lt hz.2.2) hz0
  have hnot (E F : Set X) (hFopen : IsOpen F) (hF : frontier F = T)
      (hEF : Disjoint E F) (hP : e '' P ⊆ E) (hN : e '' N ⊆ E) : False := by
    have hT : e (t, 0) ∈ frontier F := hF.symm ▸ (htrace _ h0).mpr rfl
    have hopen : IsOpen (e '' W) := e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hrect
    obtain ⟨x, hxW, hxF⟩ := mem_closure_iff.mp hT.1 (e '' W) hopen ⟨(t, 0), h0, rfl⟩
    obtain ⟨z, hzW, rfl⟩ := hxW
    have hnT : e z ∉ T := by
      rw [← hF]
      exact fun h => h.2 (hFopen.interior_eq.symm ▸ hxF)
    have hnzero : z.2 ≠ 0 := fun hz0 => hnT ((htrace z hzW).mpr hz0)
    rcases lt_or_gt_of_ne hnzero with hz | hz
    · exact disjoint_left.mp hEF (hN ⟨z, ⟨hzW.1, hzW.2.1, hz⟩, rfl⟩) hxF
    · exact disjoint_left.mp hEF (hP ⟨z, ⟨hzW.1, hz, hzW.2.2⟩, rfl⟩) hxF
  rcases hcP.subset_or_subset hA hB hd hsubP with hp | hp <;>
    rcases hcN.subset_or_subset hA hB hd hsubN with hn | hn
  · exact (hnot A B hB hfB hd hp hn).elim
  · exact Or.inl ⟨hp, hn⟩
  · exact Or.inr ⟨hp, hn⟩
  · exact (hnot B A hA hfA hd.symm hp hn).elim

end ChartSides

def NormalRayDichotomy (c : RegularJordanCurve) (A B : Set Plane) : Prop :=
  ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
    ∃ ε : ℝ, 0 < ε ∧
      ((∀ r : ℝ, 0 < r → r < ε →
          realLift c.parametrization t + r • quarterTurn (deriv (realLift c.parametrization) t) ∈ A ∧
          realLift c.parametrization t + (-r) • quarterTurn (deriv (realLift c.parametrization) t) ∈ B) ∨
       (∀ r : ℝ, 0 < r → r < ε →
          realLift c.parametrization t + r • quarterTurn (deriv (realLift c.parametrization) t) ∈ B ∧
          realLift c.parametrization t + (-r) • quarterTurn (deriv (realLift c.parametrization) t) ∈ A))

theorem normalRayDichotomy_symm {c : RegularJordanCurve} {A B : Set Plane}
    (h : NormalRayDichotomy c A B) : NormalRayDichotomy c B A := by
  intro t ht
  obtain ⟨ε, hε, h⟩ := h t ht
  exact ⟨ε, hε, h.symm⟩

theorem switch_forward {c : RegularJordanCurve} {A B : Set Plane}
    (hd : Disjoint A B) (hl : NormalRayDichotomy c A B)
    {s : ℝ} (hs : s = 1 ∨ s = -1) (hA : HasSideOnLeft A c s) :
    HasSideOnLeft B c (-s) := by
  intro t ht
  obtain ⟨ε, hε, hl⟩ := hl t ht
  obtain ⟨δ, hδ, hA⟩ := hA t ht
  have hr : 0 < min ε δ / 2 := half_pos (lt_min hε hδ)
  have hre : min ε δ / 2 < ε :=
    (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrd : min ε δ / 2 < δ :=
    (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  rcases hs with rfl | rfl
  · rcases hl with hl | hl
    · refine ⟨ε, hε, ?_⟩
      intro r hr hre
      simpa using (hl r hr hre).2
    · have hbad := (hl (min ε δ / 2) hr hre).1
      have hgood := hA (min ε δ / 2) hr hrd
      simp only [one_smul] at hgood
      exact False.elim (disjoint_left.mp hd hgood hbad)
  · rcases hl with hl | hl
    · have hbad := (hl (min ε δ / 2) hr hre).2
      have hgood := hA (min ε δ / 2) hr hrd
      simp only [neg_smul, one_smul, smul_neg] at hgood
      simp only [neg_smul] at hbad
      exact False.elim (disjoint_left.mp hd hgood hbad)
    · refine ⟨ε, hε, ?_⟩
      intro r hr hre
      simpa using (hl r hr hre).1

theorem normalSwitch_of_dichotomy {c : RegularJordanCurve} {A B : Set Plane}
    (hd : Disjoint A B) (hl : NormalRayDichotomy c A B)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    HasSideOnLeft A c s ↔ HasSideOnLeft B c (-s) := by
  constructor
  · exact switch_forward hd hl hs
  · intro hB
    have hsign : -s = 1 ∨ -s = -1 := by
      rcases hs with h | h <;> simp [h]
    have h := switch_forward hd.symm (normalRayDichotomy_symm hl) hsign hB
    simpa only [neg_neg] using h

/-- At a regular parameter, opposite short normal rays lie in opposite
Jordan sides. Both local half-rectangles meet distinct global sides because
the entire trace is the frontier of each side. -/
theorem normalRayDichotomy (c : RegularJordanCurve) (A B : Set Plane)
    (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B)
    (hu : A ∪ B = c.traceᶜ) (hfA : frontier A = c.trace) (hfB : frontier B = c.trace) :
    NormalRayDichotomy c A B := by
  intro t ht
  obtain ⟨e, he0, he⟩ := normal_chart (c.smooth_off_joins t ht) (realLift_deriv_ne_zero c t ht)
  obtain ⟨δ, ε, hδ, hε, hrect, htrace⟩ := trace_rectangle c t
    (quarterTurn (deriv (realLift c.parametrization) t)) e he0 he
  have htI : t ∈ Ioo (t-δ) (t+δ) := by constructor <;> linarith
  have hside := ChartSides.rectangle_sides e t δ ε hδ hε hrect A B c.trace hA hB hd hu hfA hfB htrace
  refine ⟨ε, hε, ?_⟩
  have hp (E : Set Plane)
      (hE : e '' (Ioo (t-δ) (t+δ) ×ˢ Ioo 0 ε) ⊆ E)
      (r : ℝ) (hr : 0 < r) (hre : r < ε) :
      realLift c.parametrization t + r • quarterTurn (deriv (realLift c.parametrization) t) ∈ E := by
    rw [← he (t, r)]
    exact hE ⟨(t, r), ⟨htI, hr, hre⟩, rfl⟩
  have hn (E : Set Plane)
      (hE : e '' (Ioo (t-δ) (t+δ) ×ˢ Ioo (-ε) 0) ⊆ E)
      (r : ℝ) (hr : 0 < r) (hre : r < ε) :
      realLift c.parametrization t + (-r) • quarterTurn (deriv (realLift c.parametrization) t) ∈ E := by
    rw [← he (t, -r)]
    exact hE ⟨(t, -r), ⟨htI, by constructor <;> linarith⟩, rfl⟩
  rcases hside with ⟨hpa, hnb⟩ | ⟨hpb, hna⟩
  · exact Or.inl (fun r hr hre => ⟨hp A hpa r hr hre, hn B hnb r hr hre⟩)
  · exact Or.inr (fun r hr hre => ⟨hp B hpb r hr hre, hn A hna r hr hre⟩)

end SmoothNormal

/-- Reversing the normal direction interchanges the two Jordan sides. -/
theorem normalSwitch : Expected.normalSwitch := by
  intro c A B hA hB _ _ hd hu hfA hfB s hs
  exact SmoothNormal.normalSwitch_of_dichotomy hd
    (SmoothNormal.normalRayDichotomy c A B hA hB hd hu hfA hfB) s hs

/-- Assembly of the component data and both orientation characterizations
from the local normal-switch theorem. -/
theorem componentsAssembly : Expected.componentsAssembly := by
  intro hswitch R
  obtain ⟨S⟩ := complementData R
  refine ⟨S, fun s hs i => ⟨boundedSideOnLeft R S.sides s hs i, ?_⟩⟩
  let A := S.sides.boundedSide i
  let B := S.sides.unboundedSide i
  have hswap (r : ℝ) (hr : r = 1 ∨ r = -1) :
      HasSideOnLeft A (R.curve i) r ↔ HasSideOnLeft B (R.curve i) (-r) :=
    hswitch (R.curve i) A B (S.sides.bounded_open i) (S.sides.unbounded_open i)
      (S.sides.bounded_connected i) (S.sides.unbounded_connected i)
      (S.sides.sides_disjoint i) (S.sides.sides_union i)
      (S.sides.bounded_frontier i) (S.sides.unbounded_frontier i) r hr
  by_cases hi : i = S.sides.outer
  · have hpos : HasSideOnLeft A (R.curve i) (s i) :=
      (boundedSideOnLeft R S.sides s hs i).mpr hi
    have hnegB := (hswap (s i) (hs i).1).mp hpos
    have hnot := not_hasSideOnLeft_of_disjoint (S.sides.sides_disjoint i).symm hnegB
    exact ⟨fun h => False.elim (hnot h), fun h => False.elim (h hi)⟩
  · have hsub : R.domain ⊆ B := by simpa [B, hi] using S.sides.domain_side i
    have hposB := hasSideOnLeft_mono hsub (hs i).2
    have hsign : -s i = 1 ∨ -s i = -1 := by
      rcases (hs i).1 with h | h <;> simp [h]
    have hnegA : HasSideOnLeft A (R.curve i) (-s i) :=
      (hswap (-s i) hsign).mpr (by simpa only [neg_neg] using hposB)
    exact ⟨fun _ => hi, fun _ => hnegA⟩

/-- The complete complementary-component and universal boundary-orientation
conclusion under the original planar-region hypotheses. -/
theorem complementComponents : Expected.complementComponents :=
  componentsAssembly normalSwitch

end P202.PlanarRegionComponents
