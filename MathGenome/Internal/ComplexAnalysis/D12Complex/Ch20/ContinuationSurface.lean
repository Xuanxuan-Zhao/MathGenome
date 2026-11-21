import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.ContinuationSurface
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.Surfaces
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.ContinuationSurface
open GermTopology Surfaces

namespace Definitions
abbrev obtainable : Specs.D12Complex.Ch20.ContinuationSurface.obtainable_type :=
  ContinuationSurface.obtainable
abbrev continuationSet : Specs.D12Complex.Ch20.ContinuationSurface.continuationSet_type :=
  ContinuationSurface.continuationSet
abbrev Component : Specs.D12Complex.Ch20.ContinuationSurface.Component_type :=
  ContinuationSurface.Component
abbrev projection : Specs.D12Complex.Ch20.ContinuationSurface.projection_type :=
  ContinuationSurface.projection
abbrev evaluation : Specs.D12Complex.Ch20.ContinuationSurface.evaluation_type :=
  ContinuationSurface.evaluation
end Definitions

theorem continuationSet_eq_pathComponent :
    Specs.D12Complex.Ch20.ContinuationSurface.continuationSet_eq_pathComponent_type := by
  intro Ω hΩ p
  ext q
  constructor
  · rintro ⟨γ, hγ, Φ, hc, hp, hq⟩
    exact ⟨⟨⟨lift γ hγ Φ,
      (isContinuation_iff_continuous_lift Ω γ hγ (Φ 0) Φ).mp hc |>.2.2.2⟩,
      hp, hq⟩⟩
  · rintro ⟨c⟩
    let γ : unitInterval → ℂ := fun t => (c t).1
    have hγ : ∀ t, γ t ∈ Ω := fun t => (c t).1.property
    let Φ : GermFamily γ := fun t => (c t).2
    have hlift : lift γ hγ Φ = c := rfl
    refine ⟨γ, hγ, Φ, ?_, c.source, c.target⟩
    apply (isContinuation_iff_continuous_lift Ω γ hγ (Φ 0) Φ).mpr
    exact ⟨hΩ, continuous_subtype_val.comp
      ((continuous_projection Ω hΩ.2.1).comp c.continuous), rfl, hlift ▸ c.continuous⟩

open private germ_eq_propagates from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations

/-- Connected function-element neighborhoods are path connected. -/
lemma basicSet_isPathConnected {Ω : Set ℂ} (e : FunctionElement)
    (he : e.domain ⊆ Ω) : IsPathConnected (basicSet Ω e) := by
  have hD : IsPathConnected e.domain :=
    e.isDomain.2.1.isConnected_iff_isPathConnected.mp ⟨e.isDomain.1, e.isDomain.2.2⟩
  have hr : Set.range (sectionMap e he) = basicSet Ω e := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact sectionMap_mem e he z
    · rintro ⟨hz, hq⟩
      refine ⟨⟨q.1, hz⟩, ?_⟩
      cases q
      simp only [sectionMap]
      congr 1
      exact hq.symm
  have : PathConnectedSpace e.domain := isPathConnected_iff_pathConnectedSpace.mp hD
  rw [← hr]
  exact isPathConnected_range (continuous_sectionMap Ω e he)

/-- Local path connectedness is proved for the full germ space without any
countability assertion. -/
lemma germSpace_locallyPathConnected (Ω : Set ℂ) (hΩ : IsOpen Ω) :
    LocallyPathConnectedSpace (Space Ω) := by
  apply LocallyPathConnectedSpace.of_bases
    (fun _ => (isTopologicalBasis Ω hΩ).nhds_hasBasis)
  rintro q B ⟨⟨e, he, rfl⟩, _⟩
  exact basicSet_isPathConnected e he

theorem continuationSet_isOpen :
    Specs.D12Complex.Ch20.ContinuationSurface.continuationSet_isOpen_type := by
  intro Ω hΩ p
  let := germSpace_locallyPathConnected Ω hΩ.2.1
  rw [continuationSet_eq_pathComponent Ω hΩ p]
  exact IsOpen.pathComponent p

theorem component_connected :
    Specs.D12Complex.Ch20.ContinuationSurface.component_connected_type := by
  intro Ω hΩ p
  apply isConnected_iff_connectedSpace.mp
  rw [continuationSet_eq_pathComponent Ω hΩ p]
  exact isPathConnected_pathComponent.isConnected

/-- Identity uniqueness on a common disk separates unequal germs in one fibre. -/
theorem germSpace_hausdorff :
    Specs.D12Complex.Ch20.ContinuationSurface.germSpace_hausdorff_type := by
  intro Ω hΩ
  constructor
  intro p q hpq
  by_cases hab : p.1 = q.1
  · rcases p with ⟨a, g⟩
    rcases q with ⟨b, k⟩
    dsimp at hab
    subst b
    obtain ⟨e, he, heg⟩ := exists_functionElement (a : ℂ) g
    obtain ⟨d, hd, hdk⟩ := exists_functionElement (a : ℂ) k
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
      (((e.holomorphic.1.inter d.holomorphic.1).inter hΩ).mem_nhds
        ⟨⟨he, hd⟩, a.property⟩)
    let eB := diskElement e a r hr (fun z hz => (hsub hz).1.1)
    let dB := diskElement d a r hr (fun z hz => (hsub hz).1.2)
    have heΩ : eB.domain ⊆ Ω := fun z hz => (hsub hz).2
    have hdΩ : dB.domain ⊆ Ω := fun z hz => (hsub hz).2
    refine ⟨basicSet Ω eB, basicSet Ω dB,
      isOpen_basicSet eB heΩ, isOpen_basicSet dB hdΩ,
      ⟨Metric.mem_ball_self hr, heg.symm⟩,
      ⟨Metric.mem_ball_self hr, hdk.symm⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨hz, hze⟩ ⟨hz', hzd⟩
    have hf : HolomorphicOn (Metric.ball (a : ℂ) r) e.toFun := eB.holomorphic
    have hg : HolomorphicOn (Metric.ball (a : ℂ) r) d.toFun := dB.holomorphic
    have hG := germ_eq_propagates Metric.isOpen_ball Metric.isPreconnected_ball hf hg
      hz (Metric.mem_ball_self hr)
      (congrArg Subtype.val (hze.symm.trans hzd))
    have hgd : e.germAt a he = d.germAt a hd := Subtype.ext hG
    apply hpq
    exact congrArg (Sigma.mk a) (heg.symm.trans (hgd.trans hdk))
  · obtain ⟨U, V, hU, hV, hp, hq, hdis⟩ := t2_separation hab
    refine ⟨GermTopology.projection Ω ⁻¹' U, GermTopology.projection Ω ⁻¹' V,
      hU.preimage (continuous_projection Ω hΩ),
      hV.preimage (continuous_projection Ω hΩ), hp, hq, hdis.preimage _⟩

/-- All nonempty complex disks, before extracting a countable subbasis. -/
def ballDomains : Set (Set ℂ) :=
  {U | ∃ (a : ℂ) (r : ℝ), 0 < r ∧ U = Metric.ball a r}

lemma ballDomains_basis : TopologicalSpace.IsTopologicalBasis ballDomains := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨a, r, hr, rfl⟩
    exact Metric.isOpen_ball
  · intro z U hz hU
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
    exact ⟨Metric.ball z r, ⟨z, r, hr, rfl⟩, Metric.mem_ball_self hr, hsub⟩

/-- Patches are actual sets of quotient germs. Total representatives that differ
outside their disks therefore determine the same patch. -/
def DiskPatch (Ω : Set ℂ) (D : Set (Set ℂ)) :=
  {B : Set (Space Ω) // ∃ e : FunctionElement,
    e.domain ∈ D ∧ e.domain ⊆ Ω ∧ B = basicSet Ω e}

namespace DiskPatch
variable {Ω : Set ℂ} {D : Set (Set ℂ)}

def element (P : DiskPatch Ω D) : FunctionElement := P.property.choose
lemma domain_mem (P : DiskPatch Ω D) : P.element.domain ∈ D := P.property.choose_spec.1
lemma domain_subset (P : DiskPatch Ω D) : P.element.domain ⊆ Ω :=
  P.property.choose_spec.2.1
lemma coe_eq (P : DiskPatch Ω D) : P.val = basicSet Ω P.element :=
  P.property.choose_spec.2.2
lemma isOpen (P : DiskPatch Ω D) : IsOpen P.val := by
  rw [P.coe_eq]
  exact isOpen_basicSet P.element P.domain_subset
lemma isPathConnected (P : DiskPatch Ω D) : IsPathConnected P.val := by
  rw [P.coe_eq]
  exact basicSet_isPathConnected P.element P.domain_subset
lemma convex_domain (P : DiskPatch Ω D) (hD : D ⊆ ballDomains) :
    Convex ℝ P.element.domain := by
  obtain ⟨a, r, _, h⟩ := hD P.domain_mem
  rw [h]
  exact convex_ball a r

/-- One fixed disk patch meets at most one patch over a given disk. Connectedness
of the intersection of two disks is essential here. -/
lemma neighbor_unique (hD : D ⊆ ballDomains) (P Q R : DiskPatch Ω D)
    (hQ : (P.val ∩ Q.val).Nonempty) (hR : (P.val ∩ R.val).Nonempty)
    (hdom : Q.element.domain = R.element.domain) : Q = R := by
  obtain ⟨x, hxP, hxQ⟩ := hQ
  obtain ⟨y, hyP, hyR⟩ := hR
  rw [P.coe_eq] at hxP hyP
  rw [Q.coe_eq] at hxQ
  rw [R.coe_eq] at hyR
  obtain ⟨hxP, hgxP⟩ := hxP
  obtain ⟨hxQ, hgxQ⟩ := hxQ
  obtain ⟨hyP, hgyP⟩ := hyP
  obtain ⟨hyR, hgyR⟩ := hyR
  have hyQ : (y.1 : ℂ) ∈ Q.element.domain := hdom.symm ▸ hyR
  let U := P.element.domain ∩ Q.element.domain
  have ho : IsOpen U := P.element.holomorphic.1.inter Q.element.holomorphic.1
  have hf : HolomorphicOn U P.element.toFun :=
    ⟨ho, fun z hz => P.element.holomorphic.2 z hz.1⟩
  have hg : HolomorphicOn U Q.element.toFun :=
    ⟨ho, fun z hz => Q.element.holomorphic.2 z hz.2⟩
  have heqy := germ_eq_propagates ho
    ((P.convex_domain hD).inter (Q.convex_domain hD)).isPreconnected hf hg
    ⟨hxP, hxQ⟩ ⟨hyP, hyQ⟩ (congrArg Subtype.val (hgxP.symm.trans hgxQ))
  have hQyRy : (Q.element.toFun : Germ (𝓝 (y.1 : ℂ)) ℂ) =
      (R.element.toFun : Germ (𝓝 (y.1 : ℂ)) ℂ) :=
    heqy.symm.trans (congrArg Subtype.val (hgyP.symm.trans hgyR))
  have hfR : HolomorphicOn Q.element.domain R.element.toFun := hdom.symm ▸ R.element.holomorphic
  apply Subtype.ext
  rw [Q.coe_eq, R.coe_eq]
  ext z
  constructor
  · rintro ⟨hz, hzg⟩
    refine ⟨hdom ▸ hz, hzg.trans (Subtype.ext ?_)⟩
    exact germ_eq_propagates Q.element.holomorphic.1 Q.element.isDomain.2.2
      Q.element.holomorphic hfR hyQ hz hQyRy
  · rintro ⟨hz, hzg⟩
    have hzQ : (z.1 : ℂ) ∈ Q.element.domain := hdom.symm ▸ hz
    refine ⟨hzQ, hzg.trans (Subtype.ext ?_)⟩
    exact (germ_eq_propagates Q.element.holomorphic.1 Q.element.isDomain.2.2
      Q.element.holomorphic hfR hyQ hzQ hQyRy).symm

lemma neighbors_countable (hD : D ⊆ ballDomains) (hc : D.Countable)
    (P : DiskPatch Ω D) : {Q : DiskPatch Ω D | (P.val ∩ Q.val).Nonempty}.Countable := by
  apply Set.MapsTo.countable_of_injOn (f := fun Q : DiskPatch Ω D => Q.element.domain)
    (t := D) (fun Q _ => Q.domain_mem) _ hc
  intro Q hQ R hR heq
  exact neighbor_unique hD P Q R hQ hR heq

end DiskPatch

lemma exists_diskPatch {Ω : Set ℂ} (hΩ : IsOpen Ω) {D : Set (Set ℂ)}
    (hD : D ⊆ ballDomains) (hb : TopologicalSpace.IsTopologicalBasis D) (p : Space Ω) :
    ∃ P : DiskPatch Ω D, p ∈ P.val := by
  obtain ⟨e, he, hp⟩ := exists_basicSet Ω hΩ p
  obtain ⟨ha, hpg⟩ := hp
  obtain ⟨U, hUD, haU, hUsub⟩ := hb.exists_subset_of_mem_open ha e.holomorphic.1
  obtain ⟨a, r, hr, hU⟩ := hD hUD
  let d : FunctionElement :=
    { domain := U
      isDomain := ⟨⟨p.1, haU⟩, hb.isOpen hUD, hU ▸ Metric.isPreconnected_ball⟩
      toFun := e.toFun
      holomorphic := ⟨hb.isOpen hUD, fun z hz => e.holomorphic.2 z (hUsub hz)⟩ }
  exact ⟨⟨basicSet Ω d, d, hUD, hUsub.trans he, rfl⟩, haU, hpg⟩

/-- A locally countably branching overlap graph supplies a countable open cover
of one path component. This proof does not enumerate the full germ space. -/
lemma countable_patch_cover (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω) :
    ∃ (D : Set (Set ℂ)) (C : Set (DiskPatch Ω D)), C.Countable ∧
      (∀ P ∈ C, P.val ⊆ continuationSet Ω p) ∧
      continuationSet Ω p = ⋃ P ∈ C, P.val := by
  obtain ⟨D, hD, hcD, hbD⟩ := ballDomains_basis.exists_countable
  obtain ⟨P₀, hp₀⟩ := exists_diskPatch hΩ.2.1 hD hbD p
  let N : ℕ → Set (DiskPatch Ω D) := fun n =>
    Nat.rec {P₀} (fun _ prev => {Q | ∃ P ∈ prev, (P.val ∩ Q.val).Nonempty}) n
  have hN0 : N 0 = {P₀} := rfl
  have hNs (n : ℕ) : N (n + 1) = {Q | ∃ P ∈ N n, (P.val ∩ Q.val).Nonempty} := rfl
  have hcN : ∀ n, (N n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton _
    | succ n ih =>
      have hEq : N (n+1) = ⋃ P ∈ N n, {Q | (P.val ∩ Q.val).Nonempty} := by
        ext Q
        simp only [hNs, mem_ofPred_eq, mem_iUnion, exists_prop]
      rw [hEq]
      exact ih.biUnion fun P _ => P.neighbors_countable hD hcD
  let C := ⋃ n, N n
  have hcC : C.Countable := countable_iUnion hcN
  have hreach : ∀ n, ∀ P ∈ N n, P.val ⊆ pathComponent p := by
    intro n
    induction n with
    | zero =>
      intro P hP
      have hP' : P = P₀ := hP
      subst P
      exact P₀.isPathConnected.subset_pathComponent hp₀
    | succ n ih =>
      rintro Q ⟨P, hP, x, hxP, hxQ⟩ y hy
      exact (ih P hP hxP).trans (Q.isPathConnected.mem_pathComponent hxQ hy)
  let U : Set (Space Ω) := ⋃ P ∈ C, P.val
  have hUo : IsOpen U := isOpen_iUnion fun P => isOpen_iUnion fun _ => P.isOpen
  have hpU : p ∈ U := mem_iUnion.mpr ⟨P₀,
    mem_iUnion.mpr ⟨mem_iUnion.mpr ⟨0, mem_singleton P₀⟩, hp₀⟩⟩
  have hUc : IsClosed U := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨Q, hxQ⟩ := exists_diskPatch hΩ.2.1 hD hbD x
    apply mem_of_superset (Q.isOpen.mem_nhds hxQ)
    intro y hyQ hyU
    obtain ⟨P, hPC, hyP⟩ := mem_iUnion₂.mp hyU
    obtain ⟨n, hn⟩ := mem_iUnion.mp hPC
    have hQ : Q ∈ N (n+1) := ⟨P, hn, y, hyP, hyQ⟩
    exact hx (mem_iUnion₂.mpr ⟨Q, mem_iUnion.mpr ⟨n+1, hQ⟩, hxQ⟩)
  have heq : continuationSet Ω p = U := by
    rw [continuationSet_eq_pathComponent Ω hΩ p]
    apply Subset.antisymm
    · exact (pathComponent_subset_component p).trans
        ((show IsClopen U from ⟨hUc, hUo⟩).connectedComponent_subset hpU)
    · rintro x hx
      obtain ⟨P, hPC, hxP⟩ := mem_iUnion₂.mp hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hPC
      exact hreach n P hn hxP
  refine ⟨D, C, hcC, ?_, heq⟩
  intro P hP x hx
  rw [heq]
  exact mem_iUnion₂.mpr ⟨P, hP, hx⟩

/-- Projection coordinates on a function-element patch contained in the
continuation component. The values outside the chart target are immaterial. -/
def componentChart (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (e : FunctionElement) (he : e.domain ⊆ Ω)
    (hs : basicSet Ω e ⊆ continuationSet Ω p) : ComplexChart (Component Ω p) := by
  classical
  have hp : p ∈ continuationSet Ω p := by
    rw [continuationSet_eq_pathComponent Ω hΩ p]
    exact mem_pathComponent_self p
  let inv : ℂ → Component Ω p := fun z =>
    if hz : z ∈ e.domain then
      ⟨sectionMap e he ⟨z, hz⟩, hs (sectionMap_mem e he ⟨z, hz⟩)⟩
    else ⟨p, hp⟩
  refine ⟨{
    toFun := fun q => (q.val.1 : ℂ)
    invFun := inv
    source := {q | q.val ∈ basicSet Ω e}
    target := e.domain
    map_source' := fun q hq => hq.choose
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := (isOpen_basicSet e he).preimage continuous_subtype_val
    open_target := e.holomorphic.1
    continuousOn_toFun := (continuous_subtype_val.comp
      ((continuous_projection Ω hΩ.2.1).comp continuous_subtype_val)).continuousOn
    continuousOn_invFun := ?_ }, e.isDomain⟩
  · intro z hz
    simp only [inv, dite_eq_left hz]
    exact sectionMap_mem e he ⟨z, hz⟩
  · rintro q ⟨hz, hq⟩
    dsimp [inv]
    rw [dite_eq_left hz]
    apply Subtype.ext
    cases q with
    | mk q hq' =>
      cases q with
      | mk a g =>
        dsimp at *
        exact congrArg (Sigma.mk a) hq.symm
  · intro z hz
    simp [inv, hz, sectionMap]
  · rw [continuousOn_iff_continuous_domRestrict]
    have hrestrict : (fun z : e.domain => inv z) =
        (fun z : e.domain => (⟨sectionMap e he z,
          hs (sectionMap_mem e he z)⟩ : Component Ω p)) := by
      funext z
      simp only [inv, dite_eq_left z.property]
    change Continuous (fun z : e.domain => inv z)
    rw [hrestrict]
    exact (continuous_sectionMap Ω e he).subtype_mk _

@[simp] lemma componentChart_apply (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (e : FunctionElement) (he : e.domain ⊆ Ω)
    (hs : basicSet Ω e ⊆ continuationSet Ω p) (q : Component Ω p) :
    (componentChart Ω hΩ p e he hs).val q = (projection Ω p q : ℂ) := rfl

@[simp] lemma componentChart_source (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (e : FunctionElement) (he : e.domain ⊆ Ω)
    (hs : basicSet Ω e ⊆ continuationSet Ω p) :
    (componentChart Ω hΩ p e he hs).val.source = {q | q.val ∈ basicSet Ω e} := rfl

@[simp] lemma componentChart_target (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (e : FunctionElement) (he : e.domain ⊆ Ω)
    (hs : basicSet Ω e ⊆ continuationSet Ω p) :
    (componentChart Ω hΩ p e he hs).val.target = e.domain := rfl

/-- Projection charts have identity transition functions on the actual overlaps. -/
lemma projection_charts_compatible {Ω : Set ℂ} {p : Space Ω}
    (e f : ComplexChart (Component Ω p))
    (he : ∀ q, e.val q = (projection Ω p q : ℂ))
    (hf : ∀ q, f.val q = (projection Ω p q : ℂ)) : CompatibleCharts e f := by
  have ht : ∀ e f : ComplexChart (Component Ω p),
      (∀ q, e.val q = (projection Ω p q : ℂ)) →
      (∀ q, f.val q = (projection Ω p q : ℂ)) →
      EqOn (e.val.symm.trans f.val) id (e.val.symm.trans f.val).source := by
    intro e f he hf z hz
    change f.val (e.val.symm z) = z
    rw [hf, ← he]
    exact e.val.right_inv hz.1
  let t := e.val.symm.trans f.val
  have hforward : HolomorphicOn t.source t := by
    refine ⟨t.open_source, fun z hz => ?_⟩
    exact differentiableAt_id.congr_of_eventuallyEq
      ((ht e f he hf).eventuallyEq_of_mem (t.open_source.mem_nhds hz))
  have hback : HolomorphicOn t.target t.symm := by
    refine ⟨t.open_target, fun z hz => ?_⟩
    have hEq : EqOn t.symm id t.target := ht f e hf he
    exact differentiableAt_id.congr_of_eventuallyEq
      (hEq.eventuallyEq_of_mem (t.open_target.mem_nhds hz))
  exact ⟨hforward, hback, t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩

/-- The countable patch cover produces actual complex charts, not merely a
cardinality bound on fibres or a basis for an unrelated topology. -/
lemma countable_element_atlas (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω) :
    ∃ A : Set (ComplexChart (Component Ω p)), A.Countable ∧ IsAtlas A ∧
      ∀ c ∈ A, ∃ (e : FunctionElement) (he : e.domain ⊆ Ω)
        (hs : basicSet Ω e ⊆ continuationSet Ω p),
        c = componentChart Ω hΩ p e he hs := by
  obtain ⟨D, C, hcC, hsub, hcov⟩ := countable_patch_cover Ω hΩ p
  let chart : C → ComplexChart (Component Ω p) := fun P =>
    componentChart Ω hΩ p P.val.element P.val.domain_subset
      (P.val.coe_eq ▸ hsub P.val P.property)
  refine ⟨Set.range chart, ?_, ?_, ?_⟩
  · have : Countable C := hcC.to_subtype
    exact countable_range chart
  · constructor
    · intro q
      have hqcov : q.val ∈ ⋃ P ∈ C, P.val := by
        rw [← hcov]
        exact q.property
      obtain ⟨P, hPC, hqP⟩ := mem_iUnion₂.mp hqcov
      refine ⟨chart ⟨P, hPC⟩, ⟨⟨P, hPC⟩, rfl⟩, ?_⟩
      change q.val ∈ basicSet Ω P.element
      rwa [← P.coe_eq]
    · rintro e ⟨P, rfl⟩ f ⟨Q, rfl⟩
      exact projection_charts_compatible _ _ (fun _ => rfl) (fun _ => rfl)
  · rintro e ⟨P, rfl⟩
    exact ⟨P.val.element, P.val.domain_subset,
      P.val.coe_eq ▸ hsub P.val P.property, rfl⟩

theorem countable_projection_atlas :
    Specs.D12Complex.Ch20.ContinuationSurface.countable_projection_atlas_type := by
  intro Ω hΩ p
  obtain ⟨A, hc, hA, hrep⟩ := countable_element_atlas Ω hΩ p
  refine ⟨A, hc, hA, ?_⟩
  intro c hc q _
  obtain ⟨e, he, hs, rfl⟩ := hrep c hc
  rfl

lemma secondCountable_of_atlas {X : Type*} [TopologicalSpace X]
    {A : Set (ComplexChart X)} (hc : A.Countable) (hA : IsAtlas A) :
    SecondCountableTopology X := by
  have : Countable A := hc.to_subtype
  let U : A → Set X := fun e => e.val.val.source
  have (e : A) : SecondCountableTopology (U e) :=
    e.val.val.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := U) (fun e => e.val.val.open_source)
  apply eq_univ_of_forall
  intro x
  obtain ⟨e, he, hx⟩ := hA.1 x
  exact mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩

lemma continuous_component_projection (Ω : Set ℂ) (hΩ : IsOpen Ω) (p : Space Ω) :
    Continuous (projection Ω p) :=
  (continuous_projection Ω hΩ).comp continuous_subtype_val

lemma evaluation_eq_on_patch {Ω : Set ℂ} {p : Space Ω} (e : FunctionElement)
    (q : Component Ω p) (hq : q.val ∈ basicSet Ω e) :
    evaluation Ω p q = e.toFun (q.val.1 : ℂ) := by
  obtain ⟨ha, hg⟩ := hq
  change q.val.2.value = _
  rw [hg]
  exact germValue_ofFunction _ _ _ _ _

lemma continuous_evaluation (Ω : Set ℂ) (hΩ : IsOpen Ω) (p : Space Ω) :
    Continuous (evaluation Ω p) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨e, he, hq⟩ := exists_basicSet Ω hΩ q.val
  have heq : evaluation Ω p =ᶠ[𝓝 q] fun x => e.toFun (x.val.1 : ℂ) :=
    Filter.eventually_of_mem
      (((isOpen_basicSet e he).preimage continuous_subtype_val).mem_nhds hq)
      (fun x hx => evaluation_eq_on_patch e x hx)
  have hbase : ContinuousAt (fun x : Component Ω p => (x.val.1 : ℂ)) q :=
    (continuous_subtype_val.comp (continuous_component_projection Ω hΩ p)).continuousAt
  have hcomp : ContinuousAt (fun x : Component Ω p => e.toFun (x.val.1 : ℂ)) q :=
    (e.holomorphic.2 _ hq.choose).continuousAt.comp
      (f := fun x : Component Ω p => (x.val.1 : ℂ)) hbase
  exact hcomp.congr_of_eventuallyEq heq

lemma evaluation_in_chart (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (e : FunctionElement) (he : e.domain ⊆ Ω)
    (hs : basicSet Ω e ⊆ continuationSet Ω p) :
    HolomorphicOn (componentChart Ω hΩ p e he hs).val.target
      (evaluation Ω p ∘ (componentChart Ω hΩ p e he hs).val.symm) := by
  let c := componentChart Ω hΩ p e he hs
  have heq : EqOn (evaluation Ω p ∘ c.val.symm) e.toFun e.domain := by
    intro z hz
    have hcs := c.val.map_target hz
    rw [Function.comp_apply, evaluation_eq_on_patch e _ hcs]
    congr 1
    exact c.val.right_inv hz
  refine ⟨e.holomorphic.1, fun z hz => ?_⟩
  exact (e.holomorphic.2 z hz).congr_of_eventuallyEq
    (heq.eventuallyEq_of_mem (e.holomorphic.1.mem_nhds hz))

lemma projection_coordinate_identity (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (c : ComplexChart (Component Ω p))
    (hc : ∀ q ∈ c.val.source, c.val q = (projection Ω p q : ℂ)) :
    EqOn (coordinateMap c (planeChart Ω hΩ) (projection Ω p)) id c.val.target := by
  intro z hz
  rw [coordinateMap, planeChart_apply, ← hc _ (c.val.map_target hz)]
  exact c.val.right_inv hz

lemma projection_coordinate_holomorphic (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω)
    (c : ComplexChart (Component Ω p))
    (hc : ∀ q ∈ c.val.source, c.val q = (projection Ω p q : ℂ)) :
    HolomorphicOn c.val.target (coordinateMap c (planeChart Ω hΩ) (projection Ω p)) := by
  refine ⟨c.val.open_target, fun z hz => ?_⟩
  exact differentiableAt_id.congr_of_eventuallyEq
    ((projection_coordinate_identity Ω hΩ p c hc).eventuallyEq_of_mem
      (c.val.open_target.mem_nhds hz))

/-- The complete continuation-surface theorem, with the same atlas for the
projection and evaluation conclusions. -/
theorem continuation_surface :
    Specs.D12Complex.Ch20.ContinuationSurface.continuation_surface_type := by
  intro Ω hΩ p
  obtain ⟨A, hcA, hA, hrep⟩ := countable_element_atlas Ω hΩ p
  let := germSpace_hausdorff Ω hΩ.2.1
  let S : RiemannSurface (Component Ω p) :=
    ⟨component_connected Ω hΩ p, inferInstance, secondCountable_of_atlas hcA hA, A, hA⟩
  obtain ⟨T, hT⟩ := plane_domain_surface Ω hΩ
  have hcoords : ∀ c ∈ A, ∀ q ∈ c.val.source,
      c.val q = (projection Ω p q : ℂ) := by
    intro c hc q _
    obtain ⟨e, he, hs, rfl⟩ := hrep c hc
    rfl
  have hTmem : planeChart Ω hΩ ∈ T.atlas := by rw [hT]; exact mem_singleton _
  have hcont := continuous_component_projection Ω hΩ.2.1 p
  refine ⟨S, T, hcA, hT, hcoords, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c, hc, hq⟩ := hA.1 q
    refine ⟨hcont.continuousAt, c, hc, planeChart Ω hΩ, hTmem, hq, ?_, ?_⟩
    · rw [planeChart_source]; trivial
    · exact ⟨c.val.target, c.val.map_source hq,
        projection_coordinate_holomorphic Ω hΩ p c (hcoords c hc)⟩
  · intro q
    obtain ⟨c, hc, hq⟩ := hA.1 q
    have hid := projection_coordinate_identity Ω hΩ p c (hcoords c hc)
    refine ⟨c, hc, planeChart Ω hΩ, hTmem, hq, ?_,
      c.val.target, c.val.target, id, c.val.map_source hq, ?_, ?_, ?_⟩
    · rw [planeChart_source]; trivial
    · intro z hz
      exact ⟨hz, by rw [planeChart_source]; trivial⟩
    · rw [planeChart_target]
      intro z hz
      have hmem := (projection Ω p (c.val.symm z)).property
      rwa [← hcoords c hc _ (c.val.map_target hz), c.val.right_inv hz] at hmem
    · refine ⟨projection_coordinate_holomorphic Ω hΩ p c (hcoords c hc),
        ⟨c.val.open_target, fun _ _ => differentiableAt_id⟩, ?_,
        fun _ hz => hz, fun z hz => hid hz, fun z hz => hid hz⟩
      intro z hz
      rw [hid hz]
      exact hz
  · refine ⟨continuous_evaluation Ω hΩ.2.1 p, ?_⟩
    intro c hc
    obtain ⟨e, he, hs, rfl⟩ := hrep c hc
    exact evaluation_in_chart Ω hΩ p e he hs

end D12Complex.ContinuationSurface
