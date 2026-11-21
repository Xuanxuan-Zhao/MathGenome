import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.IrrationalOrbitLeaf
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.IrrationalLine
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.IrrationalOrbitLeaf
open ModelData AtlasData MapData SphereTorusData IrrationalLineData
  BundleOperationsData CovectorData DistributionData LeafData GlobalLeafData
  Set Filter
open scoped Topology

/-- Local smooth inverses make the image open in the target's given topology. -/
theorem isOpen_range_of_local_inverse {k : ℕ} {N P : Type}
    [TopologicalSpace N] [TopologicalSpace P]
    (R : SmoothManifold k .euclidean N) (T : SmoothManifold k .euclidean P)
    (g : N → P) (hg : ∀ x, HasLocalSmoothInverse R T g x) :
    IsOpen (range g) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, rfl⟩
  obtain ⟨h, hx, _, heq, _, _⟩ := hg x
  have hxt : g x ∈ h.target := by rw [← heq hx]; exact h.map_source hx
  apply mem_of_superset (h.open_target.mem_nhds hxt)
  intro y hy
  refine ⟨h.symm y, ?_⟩
  rw [← heq (h.map_target hy), h.right_inv hy]

/-- A bijection whose local inverses are smooth has a smooth global inverse. -/
theorem diffeomorph_of_bijective_local_inverse {k : ℕ} {N P : Type}
    [TopologicalSpace N] [TopologicalSpace P]
    (R : SmoothManifold k .euclidean N) (T : SmoothManifold k .euclidean P)
    (g : N → P) (hs : IsSmoothMap R T g) (hb : Function.Bijective g)
    (hl : ∀ x, HasLocalSmoothInverse R T g x) :
    ∃ h : MapData.Diffeomorph R.smoothStructure.val T.smoothStructure.val,
      ∀ x, h.toEquiv x = g x := by
  let e := Equiv.ofBijective g hb
  refine ⟨⟨e, hs, ?_⟩, fun _ => rfl⟩
  intro y
  obtain ⟨h, hx, _, heq, _, hback⟩ := hl (e.symm y)
  have hyt : y ∈ h.target := by
    have hh := h.map_source hx
    rwa [heq hx, show g (e.symm y) = y from e.apply_symm_apply y] at hh
  apply manifoldContDiffAt_congr (hback y hyt)
  filter_upwards [h.open_target.mem_nhds hyt] with z hz
  apply hb.1
  rw [← heq (h.map_target hz), h.right_inv hz]
  exact (e.apply_symm_apply z).symm

/-- The open translated orbits partition the connected intrinsic leaf. -/
theorem orbit_leaf : Specs.SmoothManifolds.Ch08.IrrationalOrbitLeaf.orbit_leafType := by
  intro α hα S Q _hS _hQ C D hfamily A _hA T hconn huniv
  letI := leafTopology A 1 (0 : FlatTorus 2)
  letI : ConnectedSpace (leafSet A 1 (0 : FlatTorus 2)) := hconn
  have hzero : irrationalLine α 0 ∈ leafSet A 1 (0 : FlatTorus 2) := by
    rw [IrrationalLine.line_zero]
    exact Relation.EqvGen.refl _
  have hint : IsIntegralImmersion D S (irrationalLine α) := by
    simpa only [zero_add] using hfamily 0
  obtain ⟨g, hg, _⟩ := huniv S (irrationalLine α) hint 0 hzero
  have hglocal : ∀ t, HasLocalSmoothInverse S T g t := hg.2.2.2.2 rfl
  have hginj : Function.Injective g := by
    intro x y hxy
    apply IrrationalLine.injective α hα
    rw [← hg.2.1 x, ← hg.2.1 y, hxy]
  let O : Set (leafSet A 1 (0 : FlatTorus 2)) := {q | q.val ∈ lineRange α}
  have hOrange : O = range g := by
    ext q
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, Subtype.ext ((hg.2.1 t).trans ht)⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, (hg.2.1 t).symm⟩
  have hOopen : IsOpen O := by
    rw [hOrange]
    exact isOpen_range_of_local_inverse S T g hglocal
  have hcopen : IsOpen Oᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hqzero : q.val + irrationalLine α 0 ∈ leafSet A 1 (0 : FlatTorus 2) := by
      simpa only [IrrationalLine.line_zero, add_zero] using q.property
    obtain ⟨f, hf, _⟩ := huniv S (fun t => q.val + irrationalLine α t)
      (hfamily q.val) 0 hqzero
    have hfopen := isOpen_range_of_local_inverse S T f (hf.2.2.2.2 rfl)
    have hqf : q ∈ range f := by
      refine ⟨0, Subtype.ext ?_⟩
      simpa only [IrrationalLine.line_zero, add_zero] using hf.2.1 0
    apply mem_of_superset (hfopen.mem_nhds hqf)
    rintro r ⟨t, rfl⟩ hr
    obtain ⟨s, hs⟩ := hr
    apply hq
    refine ⟨s - t, ?_⟩
    rw [IrrationalLine.line_sub, hs, hf.2.1 t]
    exact add_sub_cancel_right _ _
  have hOuniv : O = univ :=
    (IsClopen.eq_univ ⟨by simpa only [compl_compl] using hcopen.isClosed_compl, hOopen⟩
      ⟨g 0, by rw [hOrange]; exact mem_range_self 0⟩)
  have hgsurj : Function.Surjective g := by
    intro q
    have hq : q ∈ O := by rw [hOuniv]; exact mem_univ q
    rwa [hOrange] at hq
  constructor
  · ext p
    constructor
    · intro hp
      obtain ⟨t, ht⟩ := hgsurj ⟨p, hp⟩
      exact ⟨t, (hg.2.1 t).symm.trans (congrArg Subtype.val ht)⟩
    · rintro ⟨t, rfl⟩
      rw [← hg.2.1 t]
      exact (g t).property
  · obtain ⟨h, hh⟩ := diffeomorph_of_bijective_local_inverse S T g hg.1
      ⟨hginj, hgsurj⟩ hglocal
    exact ⟨h, fun t => (congrArg Subtype.val (hh t)).trans (hg.2.1 t)⟩
end SmoothManifolds.IrrationalOrbitLeaf
