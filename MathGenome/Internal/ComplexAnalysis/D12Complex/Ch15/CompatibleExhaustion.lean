import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.CompatibleExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.CompactExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

open Set
open scoped Topology

noncomputable section

namespace D12Complex.Ch15

/-- Complement of the union of components that meet a designated forbidden set. -/
def componentHull {X : Type*} [TopologicalSpace X] (C A : Set X) : Set X :=
  (⋃ q ∈ C, connectedComponentIn Aᶜ q)ᶜ

lemma subset_componentHull {X : Type*} [TopologicalSpace X] (C A : Set X) :
    A ⊆ componentHull C A := by
  intro x hx
  simp only [componentHull, mem_compl_iff, mem_iUnion, not_exists]
  intro q hq h
  exact connectedComponentIn_subset Aᶜ q h hx

lemma componentHull_disjoint {X : Type*} [TopologicalSpace X] {C A : Set X}
    (hCA : C ⊆ Aᶜ) : componentHull C A ⊆ Cᶜ := by
  intro x hx hxC
  exact hx (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxC, mem_connectedComponentIn (hCA hxC)⟩⟩)

lemma isClosed_componentHull {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (C : Set X) {A : Set X} (hA : IsClosed A) : IsClosed (componentHull C A) := by
  exact (isOpen_iUnion fun q => isOpen_iUnion fun _ => hA.isOpen_compl.connectedComponentIn).isClosed_compl

/-- Filling whole components never splits any of the components that remain. -/
lemma componentHull_complement_component {X : Type*} [TopologicalSpace X]
    {C A : Set X} {p : X} (hp : p ∈ (componentHull C A)ᶜ) :
    connectedComponentIn (componentHull C A)ᶜ p = connectedComponentIn Aᶜ p := by
  have hcomp : (componentHull C A)ᶜ ⊆ Aᶜ := compl_subset_compl.mpr (subset_componentHull C A)
  apply subset_antisymm (connectedComponentIn_mono _ hcomp)
  have hp' : ∃ q ∈ C, p ∈ connectedComponentIn Aᶜ q := by
    simpa only [componentHull, compl_compl, mem_iUnion, exists_prop] using hp
  obtain ⟨q, hq, hpq⟩ := hp'
  have heq := connectedComponentIn_eq hpq
  have hsub : connectedComponentIn Aᶜ p ⊆ (componentHull C A)ᶜ := by
    intro x hx
    simpa only [componentHull, compl_compl, mem_iUnion, exists_prop] using
      (show ∃ q ∈ C, x ∈ connectedComponentIn Aᶜ q from ⟨q, hq, heq.symm ▸ hx⟩)
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn (hcomp hp)) hsub

lemma componentHull_relative_property {X : Type*} [TopologicalSpace X]
    {C A : Set X} (hCA : C ⊆ Aᶜ) :
    ∀ p ∈ (componentHull C A)ᶜ,
      (connectedComponentIn (componentHull C A)ᶜ p ∩ C).Nonempty := by
  intro p hp
  rw [componentHull_complement_component hp]
  have hp' : ∃ q ∈ C, p ∈ connectedComponentIn Aᶜ q := by
    simpa only [componentHull, compl_compl, mem_iUnion, exists_prop] using hp
  obtain ⟨q, hq, hpq⟩ := hp'
  exact ⟨q, (connectedComponentIn_eq hpq) ▸ mem_connectedComponentIn (hCA hq), hq⟩

lemma relativeFill_contains (Ω L : Set ℂ) : L ⊆ relativeFill Ω L := subset_union_left

lemma relativeFill_subset {Ω L : Set ℂ} (hL : L ⊆ Ω) : relativeFill Ω L ⊆ Ω := by
  rintro z (hz | ⟨C, hC, hz⟩)
  · exact hL hz
  · obtain ⟨_, _, _, _, hCΩ⟩ := hC
    exact hCΩ hz

/-- The two accepted charts give local connectedness also at infinity. -/
lemma sphere_locallyConnected : LocallyConnectedSpace RiemannSphere := by
  classical
  have hcharts : ∀ p : RiemannSphere,
      ∃ e : OpenPartialHomeomorph RiemannSphere ℂ, p ∈ e.source := by
    intro p
    by_cases hp : p = sphereInfty
    · obtain ⟨hs, ht, e, he⟩ := infinityChart_homeomorph
      refine ⟨⟨e, he ▸ hs, he ▸ ht⟩, ?_⟩
      change p ∈ e.toPartialEquiv.source
      rw [he, hp]
      exact fun h => OnePoint.coe_ne_infty (0 : ℂ) h.symm
    · obtain ⟨hs, ht, e, he⟩ := finiteChart_homeomorph
      refine ⟨⟨e, he ▸ hs, he ▸ ht⟩, ?_⟩
      change p ∈ e.toPartialEquiv.source
      rw [he]
      exact hp
  apply locallyConnectedSpace_iff_connected_subsets.2
  intro p U hU
  obtain ⟨e, hp⟩ := hcharts p
  have hV : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e p) := by
    apply Filter.inter_mem (e.open_target.mem_nhds (e.map_source hp))
    have hU' : U ∈ 𝓝 (e.symm (e p)) := by simpa only [e.left_inv hp] using hU
    exact (e.continuousAt_symm (e.map_source hp)).preimage_mem_nhds hU'
  let V := connectedComponentIn (e.target ∩ e.symm ⁻¹' U) (e p)
  have hVsub : V ⊆ e.target ∩ e.symm ⁻¹' U := connectedComponentIn_subset _ _
  refine ⟨e.symm '' V, ?_, ?_, ?_⟩
  · have hv := e.symm.image_mem_nhds (e.map_source hp) (connectedComponentIn_mem_nhds hV)
    simpa only [e.left_inv hp] using hv
  · exact isPreconnected_connectedComponentIn.image _
      (e.continuousOn_symm.mono (hVsub.trans inter_subset_left))
  · rintro x ⟨y, hy, rfl⟩
    exact (hVsub hy).2

/-- Spherical relative hull, written back in the finite plane. -/
def sphericalRelativeHull (Ω L : Set ℂ) : Set ℂ :=
  sphereFinite ⁻¹' componentHull (sphereFinite '' Ω)ᶜ (sphereFinite '' L)

lemma image_sphericalRelativeHull {Ω L : Set ℂ} (hLΩ : L ⊆ Ω) :
    sphereFinite '' sphericalRelativeHull Ω L =
      componentHull (sphereFinite '' Ω)ᶜ (sphereFinite '' L) := by
  apply image_preimage_eq_iff.mpr
  intro p hp
  have hpΩ := componentHull_disjoint (compl_subset_compl.mpr (image_mono hLΩ)) hp
  have hpΩ' : p ∈ sphereFinite '' Ω := by simpa only [mem_compl_iff, not_not] using hpΩ
  exact hpΩ'.imp fun z hz => hz.2

lemma sphericalRelativeHull_compact {Ω L : Set ℂ} (hL : IsCompact L) (hLΩ : L ⊆ Ω) :
    IsCompact (sphericalRelativeHull Ω L) := by
  let := sphere_locallyConnected
  have hclosed : IsClosed (sphereFinite '' L) := (hL.image continuous_sphereFinite).isClosed
  have hc := (isClosed_componentHull (sphereFinite '' Ω)ᶜ hclosed).isCompact
  rw [← image_sphericalRelativeHull hLΩ] at hc
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff.mpr hc

lemma sphericalRelativeHull_contains (Ω L : Set ℂ) : L ⊆ sphericalRelativeHull Ω L := by
  intro z hz
  exact subset_componentHull _ _ (mem_image_of_mem _ hz)

lemma sphericalRelativeHull_subset {Ω L : Set ℂ} (hLΩ : L ⊆ Ω) :
    sphericalRelativeHull Ω L ⊆ Ω := by
  intro z hz
  have h := componentHull_disjoint (compl_subset_compl.mpr (image_mono hLΩ)) hz
  have h' : sphereFinite z ∈ sphereFinite '' Ω := by simpa using h
  exact OnePoint.coe_injective.mem_set_image.mp h'

lemma sphericalRelativeHull_holeProperty {Ω L : Set ℂ} (hLΩ : L ⊆ Ω) :
    HasRelativeHoleProperty Ω (sphericalRelativeHull Ω L) := by
  unfold HasRelativeHoleProperty
  rw [image_sphericalRelativeHull hLΩ]
  exact componentHull_relative_property (compl_subset_compl.mpr (image_mono hLΩ))


lemma closedGridCell_compact (δ : ℝ) (a : ℤ × ℤ) : IsCompact (closedGridCell δ a) := by
  have h := (isCompact_Icc : IsCompact (Icc ((a.1 : ℝ) * δ) (((a.1 : ℝ) + 1) * δ))).reProdIm
    (isCompact_Icc : IsCompact (Icc ((a.2 : ℝ) * δ) (((a.2 : ℝ) + 1) * δ)))
  convert h using 1
  ext z
  simp only [closedGridCell, Complex.mem_reProdIm, mem_Icc, mem_ofPred_eq]
  tauto

lemma gridUnion_compact (δ : ℝ) (s : Finset (ℤ × ℤ)) : IsCompact (gridUnion δ s) :=
  s.isCompact_biUnion (fun a _ => closedGridCell_compact δ a)

/-- Boundary points of a complementary component are in the original closed set. -/
lemma closure_complement_component_subset (L : Set ℂ) (z : ℂ) (hL : IsClosed L) :
    closure (connectedComponentIn Lᶜ z) ⊆ L ∪ connectedComponentIn Lᶜ z := by
  intro x hx
  by_cases hxL : x ∈ L
  · exact Or.inl hxL
  · have hU : IsOpen (connectedComponentIn Lᶜ x) := hL.isOpen_compl.connectedComponentIn
    obtain ⟨y, hyx, hyz⟩ := mem_closure_iff.mp hx _ hU (mem_connectedComponentIn hxL)
    have heq : connectedComponentIn Lᶜ x = connectedComponentIn Lᶜ z :=
      (connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hyz).symm
    exact Or.inr (heq ▸ mem_connectedComponentIn hxL)

lemma selectedHole_closure {Ω L C : Set ℂ} (hL : IsCompact L) (hLΩ : L ⊆ Ω)
    (hC : C ∈ selectedHoles Ω L) : IsCompact (closure C) ∧ closure C ⊆ Ω := by
  obtain ⟨z, hz, rfl, hb, hCΩ⟩ := hC
  exact ⟨hb.isCompact_closure,
    (closure_complement_component_subset L z hL.isClosed).trans (union_subset hLΩ hCΩ)⟩

lemma relativeFill_compact_of_finite {Ω L : Set ℂ} (hL : IsCompact L) (hLΩ : L ⊆ Ω)
    (hfin : (selectedHoles Ω L).Finite) : IsCompact (relativeFill Ω L) := by
  have heq : relativeFill Ω L = L ∪ ⋃ C ∈ selectedHoles Ω L, closure C := by
    apply subset_antisymm
    · rintro x (hx | ⟨C, hC, hx⟩)
      · exact Or.inl hx
      · exact Or.inr (mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨hC, subset_closure hx⟩⟩)
    · rintro x (hx | hx)
      · exact Or.inl hx
      · obtain ⟨C, hC, hx⟩ := mem_iUnion₂.mp hx
        have hCsave := hC
        obtain ⟨z, hz, hCeq, _, _⟩ := hC
        rw [hCeq] at hx
        rcases closure_complement_component_subset L z hL.isClosed hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr ⟨C, hCsave, hCeq ▸ hx⟩
  rw [heq]
  exact hL.union (hfin.isCompact_biUnion fun C hC => (selectedHole_closure hL hLΩ hC).1)

/-- The components left after the selection have not been cut into smaller pieces. -/
lemma relativeFill_complement_component {Ω L : Set ℂ} {z : ℂ} (hz : z ∉ relativeFill Ω L) :
    connectedComponentIn (relativeFill Ω L)ᶜ z = connectedComponentIn Lᶜ z := by
  have hzL : z ∉ L := fun h => hz (Or.inl h)
  apply subset_antisymm (connectedComponentIn_mono _ (compl_subset_compl.mpr (relativeFill_contains Ω L)))
  have hsub : connectedComponentIn Lᶜ z ⊆ (relativeFill Ω L)ᶜ := by
    intro x hx hxf
    rcases hxf with hxL | ⟨C, hC, hxC⟩
    · exact connectedComponentIn_subset Lᶜ z hx hxL
    · have hCsave := hC
      obtain ⟨w, hw, hCeq, _, _⟩ := hC
      have heq : connectedComponentIn Lᶜ z = C := by
        rw [hCeq]
        exact (connectedComponentIn_eq hx).trans (connectedComponentIn_eq (hCeq ▸ hxC)).symm
      exact hz (Or.inr ⟨C, hCsave, heq ▸ mem_connectedComponentIn hzL⟩)
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzL) hsub

lemma finite_preimage_compact {B : Set RiemannSphere} (hB : IsCompact B)
    (hInf : sphereInfty ∉ B) : IsCompact (sphereFinite ⁻¹' B) := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff.mpr
  change IsCompact (sphereFinite '' (sphereFinite ⁻¹' B))
  have heq : sphereFinite '' (sphereFinite ⁻¹' B) = B := by
    apply image_preimage_eq_iff.mpr
    intro p hp
    exact OnePoint.ne_infty_iff_exists.mp (by
      intro h
      subst p
      exact hInf hp)
  rwa [heq]

/-- An unbounded plane set accumulates at the added point. -/
lemma infty_mem_closure_image_of_unbounded {C : Set ℂ} (hC : ¬ Bornology.IsBounded C) :
    sphereInfty ∈ closure (sphereFinite '' C) := by
  by_contra hInf
  have hcomp := finite_preimage_compact (isClosed_closure.isCompact) hInf
  apply hC
  exact hcomp.isBounded.subset (fun z hz => subset_closure (mem_image_of_mem _ hz))

/-- All the necessary remaining components meet Ωᶜ, with infinity handling the unbounded case. -/
lemma relativeFill_holeProperty (Ω L : Set ℂ) : HasRelativeHoleProperty Ω (relativeFill Ω L) := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    exact ⟨sphereInfty, mem_connectedComponentIn hp, OnePoint.infty_notMem_image_coe⟩
  | coe z =>
    have hz : z ∉ relativeFill Ω L := by
      intro h
      exact hp (mem_image_of_mem sphereFinite h)
    have hzL : z ∈ Lᶜ := fun h => hz (Or.inl h)
    let C := connectedComponentIn Lᶜ z
    have hzC : z ∈ C := mem_connectedComponentIn hzL
    have hCsub : C ⊆ (relativeFill Ω L)ᶜ := by
      change connectedComponentIn Lᶜ z ⊆ _
      rw [← relativeFill_complement_component hz]
      exact connectedComponentIn_subset _ _
    have hCconn : IsPreconnected (sphereFinite '' C) :=
      isPreconnected_connectedComponentIn.image _ continuous_sphereFinite.continuousOn
    have hCplane : sphereFinite '' C ⊆ (sphereFinite '' relativeFill Ω L)ᶜ := by
      rintro p ⟨x, hx, rfl⟩ hp
      exact hCsub hx (OnePoint.coe_injective.mem_set_image.mp hp)
    by_cases hb : Bornology.IsBounded C
    · have hnot : ¬ C ⊆ Ω := by
        intro hsub
        exact hz (Or.inr ⟨C, ⟨z, hzL, rfl, hb, hsub⟩, hzC⟩)
      obtain ⟨w, hwC, hwΩ⟩ := Set.not_subset.mp hnot
      refine ⟨sphereFinite w, ?_, ?_⟩
      · exact hCconn.subset_connectedComponentIn (mem_image_of_mem _ hzC) hCplane
          (mem_image_of_mem _ hwC)
      · exact fun h => hwΩ (OnePoint.coe_injective.mem_set_image.mp h)
    · have hInf := infty_mem_closure_image_of_unbounded hb
      have hc : IsPreconnected (insert sphereInfty (sphereFinite '' C)) :=
        hCconn.subset_closure (subset_insert _ _) (insert_subset hInf subset_closure)
      have hsub : insert sphereInfty (sphereFinite '' C) ⊆ (sphereFinite '' relativeFill Ω L)ᶜ :=
        insert_subset OnePoint.infty_notMem_image_coe hCplane
      exact ⟨sphereInfty, hc.subset_connectedComponentIn
        (mem_insert_of_mem _ (mem_image_of_mem _ hzC)) hsub (mem_insert _ _),
        OnePoint.infty_notMem_image_coe⟩


/-- A finite union of preconnected sets has only finitely many connected components. -/
lemma finite_components_of_finite_preconnected_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Finite ι] (V : ι → Set X) (hV : ∀ i, IsPreconnected (V i)) :
    {C | ∃ z ∈ ⋃ i, V i, C = connectedComponentIn (⋃ i, V i) z}.Finite := by
  classical
  let f : {i : ι // (V i).Nonempty} → Set X := fun i =>
    connectedComponentIn (⋃ j, V j) i.property.choose
  apply (Set.finite_range f).subset
  rintro C ⟨z, hz, rfl⟩
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
  let i' : {i : ι // (V i).Nonempty} := ⟨i, ⟨z, hzi⟩⟩
  have hsub : V i ⊆ connectedComponentIn (⋃ j, V j) z :=
    (hV i).subset_connectedComponentIn hzi (subset_iUnion V i)
  exact ⟨i', (connectedComponentIn_eq (hsub i'.property.choose_spec)).symm⟩

private def cellOutside (δ : ℝ) (a : ℤ × ℤ) (k : Fin 4) : Set ℂ :=
  if k = 0 then {z | z.re < (a.1 : ℝ) * δ}
  else if k = 1 then {z | ((a.1 : ℝ) + 1) * δ < z.re}
  else if k = 2 then {z | z.im < (a.2 : ℝ) * δ}
  else {z | ((a.2 : ℝ) + 1) * δ < z.im}

private lemma cellOutside_convex (δ : ℝ) (a : ℤ × ℤ) (k : Fin 4) :
    Convex ℝ (cellOutside δ a k) := by
  fin_cases k
  · exact convex_halfSpace_re_lt _
  · exact convex_halfSpace_re_gt _
  · exact convex_halfSpace_im_lt _
  · exact convex_halfSpace_im_gt _

private lemma cell_compl_eq (δ : ℝ) (a : ℤ × ℤ) :
    (closedGridCell δ a)ᶜ = ⋃ k : Fin 4, cellOutside δ a k := by
  ext z
  simp only [mem_compl_iff, closedGridCell, mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hz
    simp only [not_and_or, not_le] at hz
    rcases hz with h | h | h | h
    · exact ⟨0, by simpa [cellOutside] using h⟩
    · exact ⟨1, by simpa [cellOutside] using h⟩
    · exact ⟨2, by simpa [cellOutside] using h⟩
    · exact ⟨3, by simpa [cellOutside] using h⟩
  · rintro ⟨k, hk⟩
    fin_cases k <;> simp [cellOutside] at hk <;> rintro ⟨h1, h2, h3, h4⟩ <;> linarith

/-- Distributing the four outside half-planes gives a finite convex cover of the complement. -/
lemma gridUnion_finite_components (δ : ℝ) (s : Finset (ℤ × ℤ)) :
    {C | ∃ z ∈ (gridUnion δ s)ᶜ, C = connectedComponentIn (gridUnion δ s)ᶜ z}.Finite := by
  classical
  let V : (s → Fin 4) → Set ℂ := fun k => ⋂ a : s, cellOutside δ a (k a)
  have heq : (gridUnion δ s)ᶜ = ⋃ k, V k := by
    ext z
    simp only [gridUnion, mem_compl_iff, mem_iUnion, not_exists, exists_prop,
      not_and, V, mem_iInter]
    constructor
    · intro hz
      have hex : ∀ a : s, ∃ k : Fin 4, z ∈ cellOutside δ a k := by
        intro a
        have hza : z ∈ (closedGridCell δ a)ᶜ := hz a a.property
        rw [cell_compl_eq] at hza
        exact mem_iUnion.mp hza
      exact ⟨fun a => (hex a).choose, fun a => (hex a).choose_spec⟩
    · rintro ⟨k, hk⟩ a ha hza
      have hzout := hk ⟨a, ha⟩
      have hzcompl : z ∈ (closedGridCell δ a)ᶜ := by
        rw [cell_compl_eq]
        exact mem_iUnion.mpr ⟨k ⟨a, ha⟩, hzout⟩
      exact hzcompl hza
  rw [heq]
  exact finite_components_of_finite_preconnected_cover V
    (fun k => (convex_iInter fun (a : s) => cellOutside_convex δ a (k a)).isPreconnected)

lemma selectedHoles_gridUnion_finite (Ω : Set ℂ) (δ : ℝ) (s : Finset (ℤ × ℤ)) :
    (selectedHoles Ω (gridUnion δ s)).Finite := by
  apply (gridUnion_finite_components δ s).subset
  rintro C ⟨z, hz, hC, _, _⟩
  exact ⟨z, hz, hC⟩

theorem filling : Specs.D12Complex.Ch15.CompatibleExhaustion.filling_type := by
  intro Ω _ δ _ s hLΩ
  have hL := gridUnion_compact δ s
  exact ⟨selectedHoles_gridUnion_finite Ω δ s,
    fun C hC => selectedHole_closure hL hLΩ hC,
    relativeFill_compact_of_finite hL hLΩ (selectedHoles_gridUnion_finite Ω δ s),
    relativeFill_subset hLΩ, relativeFill_holeProperty Ω (gridUnion δ s)⟩


private def gridBlock (δ : ℝ) (x : ℂ) : Finset (ℤ × ℤ) :=
  Finset.Icc (⌊x.re / δ⌋ - 2, ⌊x.im / δ⌋ - 2) (⌊x.re / δ⌋ + 2, ⌊x.im / δ⌋ + 2)

private lemma floor_coordinate_cell {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (⌊u / δ⌋ : ℝ) * δ ≤ u ∧ u < ((⌊u / δ⌋ : ℝ) + 1) * δ :=
  ⟨(le_div_iff₀ hδ).mp (Int.floor_le _), (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one _)⟩

private lemma floor_coordinate_near {δ x y : ℝ} (hδ : 0 < δ) (h : |y - x| < δ) :
    ⌊x / δ⌋ - 2 ≤ ⌊y / δ⌋ ∧ ⌊y / δ⌋ ≤ ⌊x / δ⌋ + 2 := by
  have h' : |y / δ - x / δ| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hδ]
    exact (div_lt_one hδ).mpr h
  have hxl := Int.floor_le (x / δ)
  have hxu := Int.lt_floor_add_one (x / δ)
  have hy := abs_lt.mp h'
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith
  · apply Int.floor_le_iff.mpr
    push_cast
    linarith

private lemma ball_subset_gridBlock {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    Metric.ball x δ ⊆ gridUnion δ (gridBlock δ x) := by
  intro y hy
  have hd : ‖y - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hre : |y.re - x.re| < δ := by
    have hle := Complex.abs_re_le_norm (y-x)
    simpa only [Complex.sub_re] using hle.trans_lt hd
  have him : |y.im - x.im| < δ := by
    have hle := Complex.abs_im_le_norm (y-x)
    simpa only [Complex.sub_im] using hle.trans_lt hd
  have hr := floor_coordinate_near hδ hre
  have hi := floor_coordinate_near hδ him
  have ha : (⌊y.re / δ⌋, ⌊y.im / δ⌋) ∈ gridBlock δ x := by
    exact Finset.mem_Icc.mpr ⟨⟨hr.1, hi.1⟩, ⟨hr.2, hi.2⟩⟩
  apply mem_iUnion₂.mpr ⟨_, ha, ?_⟩
  have hr' := floor_coordinate_cell hδ y.re
  have hi' := floor_coordinate_cell hδ y.im
  exact ⟨hr'.1, hr'.2.le, hi'.1, hi'.2.le⟩

private lemma coordinate_block_bound {δ x u : ℝ} {i : ℤ} (hδ : 0 < δ)
    (hi : ⌊x / δ⌋ - 2 ≤ i ∧ i ≤ ⌊x / δ⌋ + 2)
    (hu : (i : ℝ) * δ ≤ u ∧ u ≤ ((i : ℝ) + 1) * δ) : |u - x| ≤ 3 * δ := by
  have hx := floor_coordinate_cell hδ x
  have hil : (⌊x / δ⌋ : ℝ) - 2 ≤ (i : ℝ) := by exact_mod_cast hi.1
  have hiu : (i : ℝ) ≤ (⌊x / δ⌋ : ℝ) + 2 := by exact_mod_cast hi.2
  have hl := mul_le_mul_of_nonneg_right hil hδ.le
  have hh := mul_le_mul_of_nonneg_right hiu hδ.le
  apply abs_le.mpr
  constructor <;> nlinarith

private lemma gridBlock_subset_ball {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    gridUnion δ (gridBlock δ x) ⊆ Metric.ball x (7 * δ) := by
  intro w hw
  obtain ⟨a, ha, hw⟩ := mem_iUnion₂.mp hw
  have ha' := Finset.mem_Icc.mp ha
  have hr := coordinate_block_bound hδ ⟨ha'.1.1, ha'.2.1⟩ ⟨hw.1, hw.2.1⟩
  have hi := coordinate_block_bound hδ ⟨ha'.1.2, ha'.2.2⟩ ⟨hw.2.2.1, hw.2.2.2⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (w-x)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  linarith

/-- A finite union of cells of one common square grid gives an interior compact neighborhood. -/
lemma exists_grid_neighborhood {Ω S : Set ℂ} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ s : Finset (ℤ × ℤ), S ⊆ interior (gridUnion δ s) ∧ gridUnion δ s ⊆ Ω := by
  classical
  obtain ⟨ε, hε, hεΩ⟩ := hS.exists_thickening_subset_open hΩ hSΩ
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcover : S ⊆ ⋃ x : S, Metric.ball (x : ℂ) δ := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, Metric.mem_ball_self hδ⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : S => Metric.ball (x : ℂ) δ)
    (fun _ => Metric.isOpen_ball) hcover
  let s := t.biUnion (fun x : S => gridBlock δ x)
  have hsub (x : S) (hx : x ∈ t) : gridUnion δ (gridBlock δ x) ⊆ gridUnion δ s := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, Finset.mem_biUnion.mpr ⟨x,hx,ha⟩, hza⟩
  refine ⟨δ, hδ, s, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    exact interior_maximal ((ball_subset_gridBlock hδ y).trans (hsub y hyt)) Metric.isOpen_ball hxy
  · intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    obtain ⟨x, _, hax⟩ := Finset.mem_biUnion.mp ha
    have hzball := gridBlock_subset_ball hδ (x : ℂ) (mem_iUnion₂.mpr ⟨a,hax,hza⟩)
    apply hεΩ
    apply Metric.ball_subset_thickening x.property ε
    exact (Metric.ball_subset_ball (by dsimp [δ]; linarith)) hzball


lemma relativeFill_empty (Ω : Set ℂ) : relativeFill Ω ∅ = ∅ := by
  have hholes : selectedHoles Ω ∅ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro C hC
    obtain ⟨z, _, rfl, hb, _⟩ := hC
    have heq : connectedComponentIn (∅ : Set ℂ)ᶜ z = univ := by
      simpa using (isPreconnected_univ.connectedComponentIn (mem_univ z))
    rw [heq] at hb
    exact NormedSpace.unbounded_univ ℝ ℂ hb
  simp [relativeFill, hholes]

/-- One stage of the construction, applicable also to a previous filled stage. -/
lemma exists_compatible_enlargement {Ω S : Set ℂ} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω) :
    ∃ K : Set ℂ, (IsCompact K ∧ K ⊆ Ω ∧ HasRelativeHoleProperty Ω K ∧ IsFilledGrid Ω K) ∧
      S ⊆ interior K := by
  obtain ⟨δ,hδ,s,hSint,hLΩ⟩ := exists_grid_neighborhood hΩ hS hSΩ
  obtain ⟨_,_,hc,hs,hh⟩ := filling Ω hΩ δ hδ s hLΩ
  refine ⟨relativeFill Ω (gridUnion δ s), ⟨hc,hs,hh,δ,hδ,s,hLΩ,rfl⟩, ?_⟩
  exact hSint.trans (interior_mono (relativeFill_contains Ω _))

/-- The compatible compact exhaustion of d12:15-01. -/
theorem compatible_exhaustion : Specs.D12Complex.Ch15.CompatibleExhaustion.compatible_exhaustion_type := by
  intro Ω hΩ
  classical
  let Good : Set ℂ → Prop := fun K =>
    IsCompact K ∧ K ⊆ Ω ∧ HasRelativeHoleProperty Ω K ∧ IsFilledGrid Ω K
  have hempty : Good ∅ := by
    refine ⟨isCompact_empty, empty_subset _, ?_, ?_⟩
    · rw [← relativeFill_empty Ω]
      exact relativeFill_holeProperty Ω ∅
    · refine ⟨1, zero_lt_one, ∅, ?_, ?_⟩
      · simp [gridUnion]
      · simp [gridUnion, relativeFill_empty]
  let T := {K : Set ℂ // Good K}
  let initial : T := ⟨∅,hempty⟩
  have hstep (n : ℕ) (K : T) : ∃ K' : T,
      (K : Set ℂ) ∪ Ch11.compactExhaustionStage Ω (n+1) ⊆ interior (K' : Set ℂ) := by
    have hc : IsCompact ((K : Set ℂ) ∪ Ch11.compactExhaustionStage Ω (n+1)) :=
      K.property.1.union (Ch11.CompactExhaustion.compact Ω hΩ (n+1) (by omega))
    have hs : (K : Set ℂ) ∪ Ch11.compactExhaustionStage Ω (n+1) ⊆ Ω :=
      union_subset K.property.2.1 (fun _ hz => hz.1)
    obtain ⟨K',hgood,hsub⟩ := exists_compatible_enlargement hΩ hc hs
    exact ⟨⟨K',hgood⟩,hsub⟩
  choose next hnext using hstep
  let K : ℕ → T := Nat.rec initial next
  have hnest (n : ℕ) : (K n).val ⊆ interior (K (n+1)).val := by
    change (K n).val ⊆ interior (next n (K n)).val
    intro x hx
    exact hnext n (K n) (Or.inl hx)
  have hmono : Monotone (fun n => (K n).val) :=
    monotone_nat_of_le_succ fun n => (hnest n).trans interior_subset
  refine ⟨fun n => (K n).val, rfl, ?_, hnest, ?_⟩
  · intro n
    exact (K n).property
  · intro S hS hSΩ
    obtain ⟨j,hj,hSj⟩ := Ch11.CompactExhaustion.cofinal Ω hΩ S hS hSΩ
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    refine ⟨m+1, ?_⟩
    intro n hn x hx
    apply hmono hn
    apply interior_subset
    exact hnext m (K m) (Or.inr (hSj hx))

end D12Complex.Ch15
