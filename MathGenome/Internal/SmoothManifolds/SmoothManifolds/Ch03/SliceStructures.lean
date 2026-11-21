import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SliceStructures
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryImmersion
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas

namespace SmoothManifolds.SliceStructures
open ModelData AtlasData MapData BoundaryData MapClassData SliceData Set
open scoped Topology ContDiff
universe u v

theorem sliceProjection_embedding :
    Specs.SmoothManifolds.Ch03.SliceStructures.sliceProjection_embeddingType := by
  intro k n hkn x
  funext i
  simp [sliceProjection, sliceEmbedding, i.isLt]

theorem sliceEmbedding_injective :
    Specs.SmoothManifolds.Ch03.SliceStructures.sliceEmbedding_injectiveType := by
  intro k n hkn x y h
  simpa only [sliceProjection_embedding hkn] using congrArg (sliceProjection hkn) h

theorem sliceEmbedding_self (n : ℕ) (x : Euclidean n) : sliceEmbedding n n x = x := by
  funext i
  simp [sliceEmbedding, i.isLt]

theorem coordinateSlice_zero :
    Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_zeroType := by
  intro n q
  have hmodel : modelSet 0 q = univ := by cases q <;> rfl
  ext x
  simp only [coordinateSlice, hmodel, mem_image, mem_univ, true_and, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    funext i
    simp [sliceEmbedding]
  · intro hx
    subst x
    exact ⟨0, by funext i; simp [sliceEmbedding]⟩

theorem coordinateSlice_full :
    Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType := by
  intro n q
  simp only [coordinateSlice, sliceEmbedding_self, image_id']

theorem halfSlice_positive :
    Specs.SmoothManifolds.Ch03.SliceStructures.halfSlice_positiveType.{u} := by
  intro k n N _ s d h
  exact h.2.1 rfl

theorem circle_frontier :
    Specs.SmoothManifolds.Ch03.SliceStructures.circle_frontierType := by
  exact frontier_sphere (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num)

/-- All slice inclusions have smooth ambient extensions, including k = 0. -/
theorem contDiff_sliceEmbedding (k n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sliceEmbedding k n) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j.val < k
  · simpa only [sliceEmbedding, dite_eq_left h] using
      (contDiff_apply ℝ (fun _ : Fin k => ℝ) ⟨j.val, h⟩)
  · simpa only [sliceEmbedding, dite_eq_right h] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean k => (0 : ℝ)))

theorem contDiff_sliceProjection {k n : ℕ} (hkn : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞) (sliceProjection hkn) :=
  contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin n => ℝ) (i.castLE hkn))

theorem embedding_projection_of_mem {k n : ℕ} (hkn : k ≤ n) {q : ModelKind}
    {z : Euclidean n} (hz : z ∈ coordinateSlice k n q) :
    sliceProjection hkn z ∈ modelSet k q ∧
      sliceEmbedding k n (sliceProjection hkn z) = z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [sliceProjection_embedding]
  exact ⟨hx, rfl⟩

/-- The homeomorphism-to-range field of the accepted embedding definition
implies the usual topological embedding, with no compactness assumption. -/
theorem isEmbedding_of_range_homeomorph {P : Type u} {N : Type v}
    [TopologicalSpace P] [TopologicalSpace N] {f : P → N}
    (h : ∃ e : P ≃ₜ range f, ∀ x, (e x).val = f x) : Topology.IsEmbedding f := by
  obtain ⟨e, he⟩ := h
  have hf : f = Subtype.val ∘ e := funext (fun x => (he x).symm)
  rw [hf]
  exact Topology.IsEmbedding.subtypeVal.comp e.isEmbedding

/-- An open source neighborhood of an embedding can be cut out by an ambient
open set. This is the step that excludes other pieces of the submanifold. -/
theorem embedding_open_cut {P : Type u} {N : Type v}
    [TopologicalSpace P] [TopologicalSpace N] {f : P → N}
    (hf : Topology.IsEmbedding f) {U : Set P} (hU : IsOpen U) :
    ∃ W : Set N, IsOpen W ∧ f ⁻¹' W = U ∧ f '' U = range f ∩ W := by
  obtain ⟨W, hW, hpre⟩ := hf.isInducing.isOpen_iff.mp hU
  refine ⟨W, hW, hpre, ?_⟩
  rw [← hpre, image_preimage_eq_inter_range, inter_comm]

/-- The inclusion of a model into its ambient coordinate slice. -/
def modelInsertion (k n : ℕ) (q : ModelKind) (z : ModelSpace k q) :
    ModelSpace n .euclidean := ⟨sliceEmbedding k n z.val, mem_univ _⟩

theorem continuous_modelInsertion (k n : ℕ) (q : ModelKind) :
    Continuous (modelInsertion k n q) :=
  ((contDiff_sliceEmbedding k n).continuous.comp continuous_subtype_val).subtype_mk _

section RestrictedCharts
variable {k n : ℕ} {q : ModelKind} {N : Type u} [TopologicalSpace N]
  {s : Set N} (d : ModelChart n .euclidean N) (hs : IsSliceChart s k q d)
include hs

theorem slice_coordinates (p : s) (hp : p.val ∈ d.source) :
    sliceProjection hs.1 (d p.val).val ∈ modelSet k q ∧
      sliceEmbedding k n (sliceProjection hs.1 (d p.val).val) = (d p.val).val := by
  have hz : d p.val ∈ d '' (s ∩ d.source) := ⟨p.val, ⟨p.property, hp⟩, rfl⟩
  rw [hs.2.2] at hz
  exact embedding_projection_of_mem hs.1 hz.2

theorem slice_inverse_mem (z : ModelSpace k q) (hz : modelInsertion k n q z ∈ d.target) :
    d.symm (modelInsertion k n q z) ∈ s := by
  have hslice : modelInsertion k n q z ∈ d '' (s ∩ d.source) := by
    rw [hs.2.2]
    exact ⟨hz, ⟨z.val, z.property, rfl⟩⟩
  obtain ⟨y, hy, hdy⟩ := hslice
  rw [← hdy, d.left_inv hy.2]
  exact hy.1

/-- A projected slice point, with a harmless default outside the source. -/
noncomputable def sliceChartPoint (p : s) : ModelSpace k q := by
  classical
  exact if hp : p.val ∈ d.source then
    ⟨sliceProjection hs.1 (d p.val).val, (slice_coordinates d hs p hp).1⟩
  else (⟨(0 : Euclidean k), by
    cases q with
    | euclidean => exact mem_univ _
    | halfSpace =>
      cases k with
      | zero => exact mem_univ _
      | succ k => exact (le_rfl : (0 : ℝ) ≤ 0)⟩ : ModelSpace k q)

theorem sliceChartPoint_val (p : s) (hp : p.val ∈ d.source) :
    (sliceChartPoint d hs p).val = sliceProjection hs.1 (d p.val).val := by
  simp only [sliceChartPoint, dite_eq_left hp]

theorem insertion_sliceChartPoint (p : s) (hp : p.val ∈ d.source) :
    modelInsertion k n q (sliceChartPoint d hs p) = d p.val := by
  apply Subtype.ext
  change sliceEmbedding k n (sliceChartPoint d hs p).val = _
  rw [sliceChartPoint_val d hs p hp]
  exact (slice_coordinates d hs p hp).2

/-- The chart exists with exactly the subspace topology. The nonemptiness
condition only supplies a value for the inverse outside its chart target. -/
noncomputable def restrictedSliceChart
    (hne : Nonempty {p : s // p.val ∈ d.source}) : ModelChart k q s := by
  classical
  exact {
    toFun := sliceChartPoint d hs
    invFun z := if hz : modelInsertion k n q z ∈ d.target then
      ⟨d.symm (modelInsertion k n q z), slice_inverse_mem d hs z hz⟩
      else (Classical.choice hne).val
    source := Subtype.val ⁻¹' d.source
    target := modelInsertion k n q ⁻¹' d.target
    map_source' p hp := by
      change modelInsertion k n q (sliceChartPoint d hs p) ∈ d.target
      rw [insertion_sliceChartPoint d hs p hp]
      exact d.map_source hp
    map_target' z hz := by
      change modelInsertion k n q z ∈ d.target at hz
      simp only [dite_eq_left hz]
      exact d.symm.map_source hz
    left_inv' p hp := by
      have hi := insertion_sliceChartPoint d hs p hp
      have hz : modelInsertion k n q (sliceChartPoint d hs p) ∈ d.target := by
        rw [hi]; exact d.map_source hp
      simp only [dite_eq_left hz]
      apply Subtype.ext
      change d.symm (modelInsertion k n q (sliceChartPoint d hs p)) = p.val
      rw [hi, d.left_inv hp]
    right_inv' z hz := by
      change modelInsertion k n q z ∈ d.target at hz
      simp only [dite_eq_left hz]
      apply Subtype.ext
      rw [sliceChartPoint_val d hs
        (⟨d.symm (modelInsertion k n q z), slice_inverse_mem d hs z hz⟩ : s)
        (d.symm.map_source hz)]
      change sliceProjection hs.1 (d (d.symm (modelInsertion k n q z))).val = z.val
      rw [d.right_inv hz]
      exact sliceProjection_embedding hs.1 z.val
    open_source := d.open_source.preimage continuous_subtype_val
    open_target := d.open_target.preimage (continuous_modelInsertion k n q)
    continuousOn_toFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      have hc : ContinuousOn (fun p : s => sliceProjection hs.1 (d p.val).val)
          (Subtype.val ⁻¹' d.source) :=
        (contDiff_sliceProjection hs.1).continuous.comp_continuousOn
        (continuous_subtype_val.comp_continuousOn
          (d.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h)))
      exact hc.congr (fun p hp => sliceChartPoint_val d hs p hp)
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (d.symm.continuousOn.comp (continuous_modelInsertion k n q).continuousOn
        (fun _ h => h)).congr
      intro z hz
      change modelInsertion k n q z ∈ d.target at hz
      simp only [Function.comp_apply, dite_eq_left hz]
  }

theorem restrictedSliceChart_isSliceRestriction
    (hne : Nonempty {p : s // p.val ∈ d.source}) :
    IsSliceRestriction hs.1 d (restrictedSliceChart d hs hne) :=
  ⟨rfl, rfl, fun p hp => sliceChartPoint_val d hs p hp⟩

end RestrictedCharts

/-- Two possibly mixed-model charts compatible with the same maximal smooth
atlas have smooth coordinate transition germs in both directions. -/
theorem compatibleChart_transition {k : ℕ} {a q q' : ModelKind}
    {P : Type u} [TopologicalSpace P] (S : SmoothManifold k a P)
    (c : ModelChart k q P) (d : ModelChart k q' P)
    (hc : CompatibleChart S c) (hd : CompatibleChart S d)
    (p : P) (hp : p ∈ c.source) (hp' : p ∈ d.source) :
    ChartContDiffAt ⊤ c d id p := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  exact LocalCoordinateExtension.comp (hd e he p hp' hpe).2 (hc e he p hp hpe).1

theorem compatibleChart_restrOpen {k : ℕ} {a q : ModelKind}
    {P : Type u} [TopologicalSpace P] (S : SmoothManifold k a P)
    (c : ModelChart k q P) (hc : CompatibleChart S c)
    (U : Set P) (hU : IsOpen U) : CompatibleChart S (c.restrOpen U hU) := by
  intro e he p hp hpe
  exact hc e he p hp.1 hpe

/-- A smooth Euclidean change of ambient coordinates produces a compatible
chart even when the original uniform model is a half-space. -/
theorem compatibleChart_of_change {n : ℕ} {b : ModelKind}
    {N : Type u} [TopologicalSpace N] (T : SmoothManifold n b N)
    (e : ModelChart n b N) (he : e ∈ T.smoothStructure.val)
    (c : ModelChart n .euclidean N)
    (h : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h h.source)
    (hhi : ContDiffOn ℝ (⊤ : ℕ∞) h.symm h.target)
    (hsub : c.source ⊆ e.source)
    (hform : ∀ y ∈ c.source, (e y).val ∈ h.source ∧ (c y).val = h (e y).val) :
    CompatibleChart T c := by
  intro d hd p hp hpd
  have hpe := hsub hp
  have hec : ChartContDiffAt ⊤ e c id p := by
    refine ⟨h.source, h.open_source, (hform p hp).1, h, hh, ?_⟩
    filter_upwards [c.open_source.mem_nhds hp] with y hy
    exact (hform y hy).2.symm
  have hce : ChartContDiffAt ⊤ c e id p := by
    have hct : (c p).val ∈ h.target := by
      rw [(hform p hp).2]
      exact h.map_source (hform p hp).1
    refine ⟨h.target, h.open_target, hct, h.symm, hhi, ?_⟩
    filter_upwards [c.open_source.mem_nhds hp] with y hy
    rw [(hform y hy).2, h.left_inv (hform y hy).1]
    rfl
  exact ⟨LocalCoordinateExtension.comp
      (chartContDiffAt_of_compatible (T.smoothStructure.property.1.2 e he d hd) hpe hpd) hce,
    LocalCoordinateExtension.comp hec
      (chartContDiffAt_of_compatible (T.smoothStructure.property.1.2 d hd e he) hpd hpe)⟩

theorem restrictedSliceChart_inclusion {k n : ℕ} {q : ModelKind}
    {N : Type u} [TopologicalSpace N] {s : Set N}
    (d : ModelChart n .euclidean N) (hs : IsSliceChart s k q d)
    (hne : Nonempty {p : s // p.val ∈ d.source}) (p : s) (hp : p.val ∈ d.source) :
    ChartContDiffAt ⊤ (restrictedSliceChart d hs hne) d Subtype.val p := by
  refine ⟨univ, isOpen_univ, mem_univ _, sliceEmbedding k n,
    (contDiff_sliceEmbedding k n).contDiffOn, ?_⟩
  filter_upwards [(d.open_source.preimage continuous_subtype_val).mem_nhds hp] with y hy
  exact congrArg Subtype.val (insertion_sliceChartPoint d hs y hy)

theorem restrictedSliceChart_projection {k n : ℕ} {q : ModelKind}
    {N : Type u} [TopologicalSpace N] {s : Set N}
    (d : ModelChart n .euclidean N) (hs : IsSliceChart s k q d)
    (hne : Nonempty {p : s // p.val ∈ d.source}) (p : s) (hp : p.val ∈ d.source) :
    LocalCoordinateExtension ⊤ (fun y : s => (d y.val).val)
      (fun y => ((restrictedSliceChart d hs hne) y).val) p := by
  refine ⟨univ, isOpen_univ, mem_univ _, sliceProjection hs.1,
    (contDiff_sliceProjection hs.1).contDiffOn, ?_⟩
  filter_upwards [(d.open_source.preimage continuous_subtype_val).mem_nhds hp] with y hy
  exact (sliceChartPoint_val d hs y hy).symm

/-- The transition of projected slice charts is an ambient transition composed
with the linear slice inclusion and projection. This works across the face. -/
theorem restrictedSliceChart_transition {k n : ℕ} {a q q' : ModelKind}
    {N : Type u} [TopologicalSpace N] (T : SmoothManifold n a N) {s : Set N}
    (d d' : ModelChart n .euclidean N)
    (hd : CompatibleChart T d) (hd' : CompatibleChart T d')
    (hs : IsSliceChart s k q d) (hs' : IsSliceChart s k q' d')
    (hne : Nonempty {p : s // p.val ∈ d.source})
    (hne' : Nonempty {p : s // p.val ∈ d'.source})
    (p : s) (hp : p.val ∈ d.source) (hp' : p.val ∈ d'.source) :
    ChartContDiffAt ⊤ (restrictedSliceChart d hs hne)
      (restrictedSliceChart d' hs' hne') id p := by
  have hmid : LocalCoordinateExtension ⊤ (fun y : s => (d y.val).val)
      (fun y => (d' y.val).val) p :=
    LocalCoordinateExtension.precomp
      (compatibleChart_transition T d d' hd hd' p.val hp hp')
      continuous_subtype_val.continuousAt rfl
  exact (restrictedSliceChart_projection d' hs' hne' p hp').comp
    (hmid.comp (restrictedSliceChart_inclusion d hs hne p hp))

/-- Once an embedding has inclusion coordinates on a source chart, shrink the
ambient chart to make its intersection with the *whole* image exactly a slice.
No product shape of either chart target is assumed. -/
theorem localize_embedding_slice {k n : ℕ} {q : ModelKind}
    {P : Type u} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (f : P → N) (hf : Topology.IsEmbedding f)
    (e : ModelChart k q P) (d : ModelChart n .euclidean N)
    (p : P) (hp : p ∈ e.source) (hkn : k ≤ n)
    (hq : q = .halfSpace → 0 < k)
    (hmap : MapsTo f e.source d.source)
    (hform : ∀ x ∈ e.source, (d (f x)).val = sliceEmbedding k n (e x).val) :
    ∃ (A : Set N) (hA : IsOpen A),
      f p ∈ (d.restrOpen A hA).source ∧
        IsSliceChart (range f) k q (d.restrOpen A hA) := by
  obtain ⟨W, hW, hpre, _⟩ := embedding_open_cut hf e.open_source
  obtain ⟨U, hU, hEq⟩ := e.open_target.image_val
  have heU (x : P) (hx : x ∈ e.source) : (e x).val ∈ U := by
    have ht : (e x).val ∈ Subtype.val '' e.target := ⟨e x, e.map_source hx, rfl⟩
    rw [hEq] at ht
    exact ht.1
  have hUe (u : ModelSpace k q) (hu : u.val ∈ U) : u ∈ e.target := by
    have ht : u.val ∈ Subtype.val '' e.target := by
      rw [hEq]
      exact ⟨hu, u.property⟩
    obtain ⟨v, hv, hval⟩ := ht
    have hvu : v = u := Subtype.ext hval
    exact hvu ▸ hv
  let g : N → Euclidean k := fun y => sliceProjection hkn (d y).val
  have hg : ContinuousOn g d.source :=
    (contDiff_sliceProjection hkn).continuous.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn d.continuousOn)
  let A := (d.source ∩ g ⁻¹' U) ∩ W
  have hA : IsOpen A := (hg.isOpen_inter_preimage d.open_source hU).inter hW
  have hfxW (x : P) (hx : x ∈ e.source) : f x ∈ W := by
    change x ∈ f ⁻¹' W
    rwa [hpre]
  have hfxA (x : P) (hx : x ∈ e.source) : f x ∈ A := by
    refine ⟨⟨hmap hx, ?_⟩, hfxW x hx⟩
    change sliceProjection hkn (d (f x)).val ∈ U
    rw [hform x hx, sliceProjection_embedding hkn]
    exact heU x hx
  refine ⟨A, hA, ⟨hmap hp, hfxA p hp⟩, hkn, hq, ?_⟩
  ext z
  constructor
  · rintro ⟨y, ⟨⟨x, rfl⟩, hy⟩, rfl⟩
    have hx : x ∈ e.source := by
      rw [← hpre]
      exact hy.2.2
    refine ⟨(d.restrOpen A hA).map_source hy, ?_⟩
    change (d (f x)).val ∈ coordinateSlice k n q
    exact ⟨(e x).val, (e x).property, (hform x hx).symm⟩
  · rintro ⟨hz, u, hu, hzu⟩
    have hsym := (d.restrOpen A hA).symm.map_source hz
    have hdz : d ((d.restrOpen A hA).symm z) = z :=
      (d.restrOpen A hA).right_inv hz
    have huU : u ∈ U := by
      have ht := hsym.2.1.2
      change sliceProjection hkn (d ((d.restrOpen A hA).symm z)).val ∈ U at ht
      rw [hdz, ← hzu, sliceProjection_embedding hkn] at ht
      exact ht
    let u' : ModelSpace k q := ⟨u, hu⟩
    have hu'e : u' ∈ e.target := hUe u' huU
    let x := e.symm u'
    have hxe : x ∈ e.source := e.symm.map_source hu'e
    have hcoord : d (f x) = z := by
      apply Subtype.ext
      rw [hform x hxe, e.right_inv hu'e]
      exact hzu
    exact ⟨f x, ⟨⟨x, rfl⟩, ⟨hmap hxe, hfxA x hxe⟩⟩, hcoord⟩

theorem exists_sliceRestriction :
    Specs.SmoothManifolds.Ch03.SliceStructures.exists_sliceRestrictionType.{u} := by
  intro k n q N _ s d hs hne
  exact ⟨hs.1, restrictedSliceChart d hs hne,
    restrictedSliceChart_isSliceRestriction d hs hne⟩

theorem projected_slice_transitions :
    Specs.SmoothManifolds.Ch03.SliceStructures.projected_slice_transitionsType.{u} := by
  intro k n a q q' N _ T s d d' hd hd' hs hs' hne hne'
  refine ⟨hs.1, restrictedSliceChart d hs hne, restrictedSliceChart d' hs' hne',
    restrictedSliceChart_isSliceRestriction d hs hne,
    restrictedSliceChart_isSliceRestriction d' hs' hne', ?_⟩
  intro p hp hp'
  exact restrictedSliceChart_transition T d d' hd hd' hs hs' hne hne' p hp hp'

/-- The empty submanifold requires no chart, but still has a unique maximal
atlas and an embedding into every ambient manifold. -/
theorem empty_slice_structure :
    Specs.SmoothManifolds.Ch03.SliceStructures.empty_slice_structureType.{u} := by
  intro n a b N _ T k
  letI := T.topologicalManifold.hausdorff
  letI := T.topologicalManifold.secondCountable
  let z : ModelSpace k a := ⟨0, by
    cases a with
    | euclidean => exact mem_univ _
    | halfSpace => cases k with
      | zero => exact mem_univ _
      | succ k => exact (le_rfl : (0 : ℝ) ≤ 0)⟩
  have hA : IsMaximalContDiffAtlas ⊤
      (∅ : Set (ModelChart k a (∅ : Set N))) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro p; exact p.property.elim
    · intro c hc; exact hc.elim
    · intro B _ _
      apply eq_empty_iff_forall_notMem.mpr
      intro c _
      exact (c.symm z).property
  let S : SmoothManifold k a (∅ : Set N) := {
    topologicalManifold := {
      hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := ∅
      covers := fun p => p.property.elim }
    smoothStructure := ⟨∅, hA⟩ }
  refine ⟨S, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro p; exact p.property.elim
    · intro p; exact p.property.elim
    · intro p; exact p.property.elim
    · exact ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩
  · intro R
    apply Subtype.ext
    ext c
    exact (c.symm z).property.elim

/-- Regard an ordinary open Euclidean chart as a chart in the canonical
Euclidean model subtype. -/
noncomputable def euclideanModelChart {n : ℕ} {N : Type u} [TopologicalSpace N]
    (d : OpenPartialHomeomorph N (Euclidean n)) : ModelChart n .euclidean N :=
  d.transHomeomorph (Homeomorph.Set.univ (Euclidean n)).symm

@[simp] theorem euclideanModelChart_val {n : ℕ} {N : Type u} [TopologicalSpace N]
    (d : OpenPartialHomeomorph N (Euclidean n)) (x : N) :
    (euclideanModelChart d x).val = d x := rfl

@[simp] theorem euclideanModelChart_source {n : ℕ} {N : Type u} [TopologicalSpace N]
    (d : OpenPartialHomeomorph N (Euclidean n)) :
    (euclideanModelChart d).source = d.source := rfl

/-- Concatenation agrees with the prescribed first-coordinate slice convention. -/
theorem appendCoordinates_zero (k l : ℕ) (x : Euclidean k) :
    appendCoordinates k l (x, 0) = sliceEmbedding k (k + l) x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [sliceEmbedding, i.isLt]
  · simp [sliceEmbedding, Nat.not_lt.mpr (Nat.le_add_right k i.val)]

/-- A source-coordinate-preserving immersion normal form. The source can be
on its face or in its interior. Only the target point is required to be interior.
The original source coordinates are retained, so the half-space inequality is
retained as well. -/
theorem immersion_coordinates {k n : ℕ} {a b : ModelKind}
    {P : Type u} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold k a P) (T : SmoothManifold n b N) (f : P → N)
    (hf : IsSmoothMap S T f) (p : P) (hi : IsImmersionAt S T f p)
    (hfp : f p ∈ manifoldInterior T) :
    k ≤ n ∧ ∃ e : ModelChart k a P, e ∈ S.smoothStructure.val ∧ p ∈ e.source ∧
      ∃ d : ModelChart n .euclidean N, CompatibleChart T d ∧ f p ∈ d.source ∧
      ∃ V : Set P, IsOpen V ∧ p ∈ V ∧ V ⊆ e.source ∧
        ∀ x ∈ V, f x ∈ d.source ∧ (d (f x)).val = sliceEmbedding k n (e x).val := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd, hpdi⟩ := hfp
  obtain ⟨U, hU, hepU, g, hg, heq⟩ := (hf p).2 e he d hd hp hpd
  have hdg := ((hg.contDiffAt (hU.mem_nhds hepU)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hderiv : FiniteRegularityData.chartDerivative e d f p = fderiv ℝ g (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨g, hdg, heq⟩
  have hf1 := manifoldContDiff_of_le ⊤ 1 _ _ f le_top hf
  have hgi : Function.Injective (fderiv ℝ g (e p).val) := by
    rw [← hderiv]
    exact (MapClasses.chart_invariants S T f hf1 p e d he hd hp hpd).2.1.mp hi
  have Hform := BoundaryImmersion.euclidean_immersion ⊤ le_top
    g U hU hg (e p).val hepU _ hdg hgi
  have hkn := Hform.1
  obtain ⟨l, hn⟩ := Nat.exists_eq_add_of_le hkn
  subst n
  rw [Nat.add_sub_cancel_left] at Hform
  obtain ⟨_, h, hhs, hhi, O, hO, hepO, hform⟩ := Hform
  let B := appendCoordinates k l
  let H := h.transHomeomorph B.toHomeomorph
  let D := InteriorInverse.ambientChart d
  let c := euclideanModelChart (D.trans H)
  have hpD : f p ∈ D.source := ⟨hpd, hpdi⟩
  have hpc : f p ∈ c.source := by
    rw [euclideanModelChart_source]
    refine ⟨hpD, ?_⟩
    change (d (f p)).val ∈ H.source
    have hgp : g (e p).val = (d (f p)).val := heq.eq_of_nhds
    simpa [H, hgp] using (hform _ hepO).1
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H H.source := by
    simpa [H] using B.contDiff.comp_contDiffOn hhs
  have hHi : ContDiffOn ℝ (⊤ : ℕ∞) H.symm H.target := by
    exact hhi.comp B.symm.contDiff.contDiffOn (fun _ hz => hz)
  have hc : CompatibleChart T c := compatibleChart_of_change T d hd c H hH hHi
    (fun _ hx => (show _ ∈ (D.trans H).source from
      (euclideanModelChart_source (D.trans H)) ▸ hx).1.1)
    (fun _ hx => ⟨(show _ ∈ (D.trans H).source from
      (euclideanModelChart_source (D.trans H)) ▸ hx).2, rfl⟩)
  have hecont : ContinuousAt (fun y => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hnhds : ∀ᶠ x in 𝓝 p, x ∈ e.source ∧ f x ∈ c.source ∧
      (e x).val ∈ O ∧ g (e x).val = (d (f x)).val := by
    filter_upwards [e.open_source.mem_nhds hp,
      (hf p).1.preimage_mem_nhds (c.open_source.mem_nhds hpc),
      hecont.preimage_mem_nhds (hO.mem_nhds hepO), heq] with x hx hfx hxO heqx
    exact ⟨hx, hfx, hxO, heqx⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  refine ⟨hkn, e, he, hp, c, hc, hpc, V, hV, hpV,
    fun x hx => (hVsub hx).1, ?_⟩
  intro x hx
  obtain ⟨_, hfxc, hxO, heqx⟩ := hVsub hx
  refine ⟨hfxc, ?_⟩
  change B (h (d (f x)).val) = _
  rw [← heqx, (hform _ hxO).2]
  exact appendCoordinates_zero k l (e x).val

/-- Empty intrinsic boundary puts every ambient point in the manifold interior,
independently of the uniform model kind used by its atlas. -/
theorem interior_of_boundary_empty {n : ℕ} {b : ModelKind}
    {N : Type u} [TopologicalSpace N] (T : SmoothManifold n b N)
    (hT : intrinsicBoundary T = ∅) (y : N) : y ∈ manifoldInterior T := by
  change y ∈ SmoothManifolds.manifoldInterior T
  rw [← compl_intrinsicBoundary T, hT]
  simp

/-- An embedded manifold is a full coordinate slice at its interior points. -/
theorem interior_slice :
    Specs.SmoothManifolds.Ch03.SliceStructures.interior_sliceType.{u,v} := by
  intro k n a b P N _ _ S T f hT hf p hpi
  obtain ⟨hkn, e, he, hp, d, hd, hpd, V, hV, hpV, hVe, hform⟩ :=
    immersion_coordinates S T f hf.1 p (hf.2.2.1 p) (interior_of_boundary_empty T hT (f p))
  have hpei : (e p).val ∈ interior (modelSet k a) := by
    have hnp : p ∉ intrinsicBoundary S := by
      change p ∈ SmoothManifolds.manifoldInterior S at hpi
      rwa [← compl_intrinsicBoundary S] at hpi
    by_contra hh
    exact hnp ⟨e, he, hp, (mem_modelFace_iff_not_mem_interior (e p)).mpr hh⟩
  let c := (euclideanModelChart (InteriorInverse.ambientChart e)).restrOpen V hV
  have hpc : p ∈ c.source := by
    exact ⟨⟨hp, hpei⟩, hpV⟩
  obtain ⟨A, hA, hpA, hs⟩ := localize_embedding_slice f
    (isEmbedding_of_range_homeomorph hf.2.2.2) c d p hpc hkn
    (fun h => ModelKind.noConfusion h)
    (fun x hx => (hform x hx.2).1) (fun x hx => (hform x hx.2).2)
  exact ⟨d.restrOpen A hA, compatibleChart_restrOpen T d hd A hA, hpA, hs⟩

/-- An embedded manifold is a genuine half-slice at its intrinsic boundary,
with the projected point on the face of that half-slice. -/
theorem boundary_slice :
    Specs.SmoothManifolds.Ch03.SliceStructures.boundary_sliceType.{u,v} := by
  intro k n a b P N _ _ S T f hT hf p hpb
  obtain ⟨hkn, e, he, hp, d, hd, hpd, V, hV, hpV, hVe, hform⟩ :=
    immersion_coordinates S T f hf.1 p (hf.2.2.1 p) (interior_of_boundary_empty T hT (f p))
  have hface := (intrinsicBoundary_iff_chart S e he p hp).mp hpb
  cases a with
  | euclidean => exact hface.elim
  | halfSpace =>
    have hk : 0 < k := by
      cases k with
      | zero => exact hface.elim
      | succ k => exact Nat.zero_lt_succ k
    let c := e.restrOpen V hV
    have hpc : p ∈ c.source := ⟨hp, hpV⟩
    obtain ⟨A, hA, hpA, hs⟩ := localize_embedding_slice f
      (isEmbedding_of_range_homeomorph hf.2.2.2) c d p hpc hkn (fun _ => hk)
      (fun x hx => (hform x hx.2).1) (fun x hx => (hform x hx.2).2)
    refine ⟨d.restrOpen A hA, compatibleChart_restrOpen T d hd A hA, hpA, hs, hkn, ?_⟩
    change sliceProjection hkn (d (f p)).val ∈ halfSpaceFace k
    rw [(hform p hpV).2, sliceProjection_embedding]
    exact hface

/-- Smoothness of an inclusion can be tested in a second immersed structure
on the same subspace. The local retraction is the linear slice projection
following the smooth ambient change of coordinates. -/
theorem smooth_identity_of_immersed_inclusions {k n : ℕ} {a a' b : ModelKind}
    {N : Type u} [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (S : SmoothManifold k a s) (R : SmoothManifold k a' s)
    (hT : intrinsicBoundary T = ∅) (hS : IsSmoothMap S T Subtype.val)
    (hR : IsSmoothMap R T Subtype.val) (hRi : IsImmersion R T Subtype.val) :
    IsSmoothMap S R id := by
  intro p
  obtain ⟨hkn, e, he, hp, d, hd, hpd, V, hV, hpV, hVe, hform⟩ :=
    immersion_coordinates R T Subtype.val hR p (hRi p)
      (interior_of_boundary_empty T hT p.val)
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨j, hj, hpj⟩ := T.smoothStructure.property.1.1 p.val
  have hjd : LocalCoordinateExtension ⊤ (fun y : s => (j y.val).val)
      (fun y => (d y.val).val) p :=
    LocalCoordinateExtension.precomp
      (ι := fun y : N => (j y).val) (f := fun y : N => (d y).val)
      (hd j hj p.val hpd hpj).2 continuous_subtype_val.continuousAt rfl
  have hcd : ChartContDiffAt ⊤ c d Subtype.val p :=
    LocalCoordinateExtension.comp hjd ((hS p).2 c hc j hj hpc hpj)
  have hde : LocalCoordinateExtension ⊤ (fun y : s => (d y.val).val)
      (fun y => (e y).val) p := by
    refine ⟨univ, isOpen_univ, mem_univ _, sliceProjection hkn,
      (contDiff_sliceProjection hkn).contDiffOn, ?_⟩
    filter_upwards [hV.mem_nhds hpV] with y hy
    rw [(hform y hy).2, sliceProjection_embedding]
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ S.smoothStructure.property.1
    R.smoothStructure.property.1 id p).mpr
  exact ⟨continuousAt_id, c, hc, e, he, hpc, hp,
    LocalCoordinateExtension.comp hde hcd⟩

/-- The identity identifies any two embedded structures on the fixed subspace,
including when they use different permitted global model kinds. -/
theorem embedded_structure_identity :
    Specs.SmoothManifolds.Ch03.SliceStructures.embedded_structure_identityType.{u} := by
  intro k n a a' b N _ T s S R hT hS hR
  exact ⟨smooth_identity_of_immersed_inclusions T s S R hT hS.1 hR.1 hR.2.2.1,
    smooth_identity_of_immersed_inclusions T s R S hT hR.1 hS.1 hS.2.2.1⟩

/-- In the same model kind the identification by the identity is literal
 equality of maximal atlases, with the same subspace topology. -/
theorem embedded_structure_eq {k n : ℕ} {a b : ModelKind}
    {N : Type u} [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (S R : SmoothManifold k a s) (hT : intrinsicBoundary T = ∅)
    (hS : IsSmoothEmbedding S T Subtype.val) (hR : IsSmoothEmbedding R T Subtype.val) :
    S.smoothStructure = R.smoothStructure := by
  have hid := embedded_structure_identity T s S R hT hS hR
  have hU : IsContDiffAtlas ⊤ (S.smoothStructure.val ∪ R.smoothStructure.val) := by
    refine ⟨?_, ?_⟩
    · intro p
      obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
      exact ⟨c, Or.inl hc, hp⟩
    · intro c hc d hd
      rcases hc with hc | hc <;> rcases hd with hd | hd
      · exact S.smoothStructure.property.1.2 c hc d hd
      · exact contDiffCompatible_of_germs
          (fun p hp hp' => (hid.1 p).2 c hc d hd hp hp')
          (fun p hp hp' => (hid.2 p).2 d hd c hc hp hp')
      · exact contDiffCompatible_of_germs
          (fun p hp hp' => (hid.2 p).2 c hc d hd hp hp')
          (fun p hp hp' => (hid.1 p).2 d hd c hc hp hp')
      · exact R.smoothStructure.property.1.2 c hc d hd
  apply Subtype.ext
  exact (S.smoothStructure.property.2 _ hU subset_union_left).symm.trans
    (R.smoothStructure.property.2 _ hU subset_union_right)

/-- A refinement uses a smaller source and has smooth changes in both directions,
allowing the two charts to have different model kinds. -/
def RefinesChart {k : ℕ} {a q : ModelKind} {P : Type u} [TopologicalSpace P]
    (c : ModelChart k a P) (d : ModelChart k q P) : Prop :=
  ∀ p ∈ c.source, p ∈ d.source ∧
    ChartContDiffAt ⊤ c d id p ∧ ChartContDiffAt ⊤ d c id p

/-- A full chart can locally be expressed in the half-space model. Translation
moves the chosen point to the all-ones vector, strictly inside the model.
No positive-dimension hypothesis is needed. -/
theorem halfSpace_refinement {k : ℕ} {P : Type u} [TopologicalSpace P]
    (c : ModelChart k .euclidean P) (p : P) (hp : p ∈ c.source) :
    ∃ d : ModelChart k .halfSpace P, p ∈ d.source ∧ RefinesChart d c := by
  let v : Euclidean k := 1 - (c p).val
  let C := (InteriorInverse.ambientChart c).transHomeomorph (Homeomorph.addRight v)
  let I := InteriorInverse.modelInteriorChart k .halfSpace
  let d := C.trans I.symm
  have hOne : (1 : Euclidean k) ∈ interior (modelSet k .halfSpace) := by
    let z : ModelSpace k .halfSpace :=
      ⟨1, by cases k <;> norm_num [ModelData.modelSet, ModelData.halfSpaceSet]⟩
    have hz : z.val ∉ modelFace k .halfSpace := by
      cases k <;> simp [z, BoundaryData.modelFace, halfSpaceFace]
    exact not_not.mp (mt (mem_modelFace_iff_not_mem_interior z).mpr hz)
  have hCp : C p = 1 := by
    change (c p).val + (1 - (c p).val) = 1
    abel
  have hpC : p ∈ C.source := by
    refine ⟨hp, ?_⟩
    change (c p).val ∈ interior (ModelData.modelSet k .euclidean)
    simp [ModelData.modelSet]
  have hpd : p ∈ d.source := by
    refine ⟨hpC, ?_⟩
    change C p ∈ interior (modelSet k .halfSpace)
    rwa [hCp]
  have hdval (y : P) (hy : y ∈ d.source) : (d y).val = (c y).val + v := by
    exact I.right_inv hy.2
  refine ⟨d, hpd, ?_⟩
  intro y hy
  refine ⟨hy.1.1, ?_, ?_⟩
  · refine ⟨univ, isOpen_univ, mem_univ _, (fun z => z - v),
      (contDiff_id.sub contDiff_const).contDiffOn, ?_⟩
    filter_upwards [d.open_source.mem_nhds hy] with z hz
    rw [hdval z hz, add_sub_cancel_right]
    rfl
  · refine ⟨univ, isOpen_univ, mem_univ _, (fun z => z + v),
      (contDiff_id.add contDiff_const).contDiffOn, ?_⟩
    filter_upwards [d.open_source.mem_nhds hy] with z hz
    exact (hdval z hz).symm

/-- Every permitted mixed chart has a local refinement in the fixed global model. -/
theorem model_refinement {k : ℕ} {a q : ModelKind} {P : Type u} [TopologicalSpace P]
    (c : ModelChart k q P) (hq : q = .euclidean ∨ q = a)
    (p : P) (hp : p ∈ c.source) :
    ∃ d : ModelChart k a P, p ∈ d.source ∧ RefinesChart d c := by
  rcases hq with rfl | rfl
  · cases a with
    | euclidean =>
      exact ⟨c, hp, fun y hy => ⟨hy,
        LocalCoordinateExtension.self _ _ _, LocalCoordinateExtension.self _ _ _⟩⟩
    | halfSpace => exact halfSpace_refinement c p hp
  · exact ⟨c, hp, fun y hy => ⟨hy,
      LocalCoordinateExtension.self _ _ _, LocalCoordinateExtension.self _ _ _⟩⟩

/-- A smooth coordinate left inverse proves injectivity of the full differential,
including at a face. Its ambient extension need not preserve any half-space. -/
theorem immersion_of_coordinate_retraction {k n : ℕ} {a b : ModelKind}
    {P : Type u} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold k a P) (T : SmoothManifold n b N) (f : P → N)
    (hf : IsSmoothMap S T f) (p : P)
    (c : ModelChart k a P) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (hret : LocalCoordinateExtension ⊤ (fun y => (d (f y)).val) (fun y => (c y).val) p) :
    IsImmersionAt S T f p := by
  obtain ⟨F, hF, heF⟩ := FiniteRegularity.chartDerivative_exists ⊤ le_top c d f p
    ((hf p).2 c hc d hd hp hfp)
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hret
  have hGd := ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hbase : F (c p).val = (d (f p)).val := heF.eq_of_nhds
  have hGd' : HasFDerivAt G (fderiv ℝ G (d (f p)).val) (F (c p).val) := by
    rw [hbase]
    exact hGd
  have hcomp := FiniteRegularity.coordinateDerivative_eq c (fun y => (c y).val) p hp
    ((fderiv ℝ G (d (f p)).val).comp (FiniteRegularityData.chartDerivative c d f p))
    ⟨G ∘ F, hGd'.comp _ hF, (heF.fun_comp G).trans heG⟩
  change FiniteRegularityData.chartDerivative c c id p = _ at hcomp
  rw [FiniteRegularity.chartDerivative_id c p hp] at hcomp
  have hJ : Function.Injective (FiniteRegularityData.chartDerivative c d f p) := by
    intro x y hxy
    have hh := congrArg (fderiv ℝ G (d (f p)).val) hxy
    have heq (v : Euclidean k) := congrArg (fun L : Euclidean k →L[ℝ] Euclidean k => L v) hcomp
    exact (heq x).trans (hh.trans (heq y).symm)
  exact (MapClasses.chart_invariants S T f
    (manifoldContDiff_of_le ⊤ 1 _ _ f le_top hf) p c d hc hd hp hfp).2.1.mpr hJ

/-- Charts in a fixed model obtained by refining the projected ambient slices. -/
def sliceAtlas {k n : ℕ} {a b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N) : Set (ModelChart k a s) :=
  {c | ∃ (q : ModelKind), (q = .euclidean ∨ q = a) ∧
    ∃ (d : ModelChart n .euclidean N), CompatibleChart T d ∧
    ∃ (hs : IsSliceChart s k q d) (hne : Nonempty {p : s // p.val ∈ d.source}),
      RefinesChart c (restrictedSliceChart d hs hne)}

theorem sliceAtlas_cover {k n : ℕ} {a b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N) (h : HasSliceCharts T s k a) :
    IsAtlas (sliceAtlas (k := k) (a := a) T s) := by
  intro p
  obtain ⟨q, hq, d, hd, hp, hs⟩ := h.2 p.val p.property
  let hne : Nonempty {p : s // p.val ∈ d.source} := ⟨⟨p, hp⟩⟩
  obtain ⟨c, hc, href⟩ := model_refinement (restrictedSliceChart d hs hne) hq p hp
  exact ⟨c, ⟨q, hq, d, hd, hs, hne, href⟩, hc⟩

theorem sliceAtlas_transition {k n : ℕ} {a b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (c c' : ModelChart k a s) (hc : c ∈ sliceAtlas T s) (hc' : c' ∈ sliceAtlas T s)
    (p : s) (hp : p ∈ c.source) (hp' : p ∈ c'.source) :
    ChartContDiffAt ⊤ c c' id p := by
  obtain ⟨q, hq, d, hd, hs, hne, hrc⟩ := hc
  obtain ⟨q', hq', d', hd', hs', hne', hrc'⟩ := hc'
  have h1 := hrc p hp
  have h2 := hrc' p hp'
  exact LocalCoordinateExtension.comp h2.2.2 (LocalCoordinateExtension.comp
    (restrictedSliceChart_transition T d d' hd hd' hs hs' hne hne' p h1.1 h2.1) h1.2.1)

theorem sliceAtlas_isContDiffAtlas {k n : ℕ} {a b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (h : HasSliceCharts T s k a) : IsContDiffAtlas ⊤ (sliceAtlas (k := k) (a := a) T s) := by
  refine ⟨sliceAtlas_cover T s h, ?_⟩
  intro c hc c' hc'
  exact contDiffCompatible_of_germs (sliceAtlas_transition T s c c' hc hc')
    (sliceAtlas_transition T s c' c hc' hc)

/-- Inclusion and a smooth coordinate retraction in every refined slice chart. -/
theorem sliceAtlas_inclusion_retraction {k n : ℕ} {a b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (c : ModelChart k a s) (hc : c ∈ sliceAtlas T s) (p : s) (hp : p ∈ c.source)
    (e : ModelChart n b N) (he : e ∈ T.smoothStructure.val) (hpe : p.val ∈ e.source) :
    ChartContDiffAt ⊤ c e Subtype.val p ∧
    LocalCoordinateExtension ⊤ (fun y : s => (e y.val).val) (fun y => (c y).val) p := by
  obtain ⟨q, hq, d, hd, hs, hne, hrc⟩ := hc
  have hr := hrc p hp
  have hde : LocalCoordinateExtension ⊤ (fun y : s => (d y.val).val)
      (fun y => (e y.val).val) p :=
    LocalCoordinateExtension.precomp (hd e he p.val hr.1 hpe).1 continuousAt_subtype_val rfl
  have hed : LocalCoordinateExtension ⊤ (fun y : s => (e y.val).val)
      (fun y => (d y.val).val) p :=
    LocalCoordinateExtension.precomp (hd e he p.val hr.1 hpe).2 continuousAt_subtype_val rfl
  exact ⟨LocalCoordinateExtension.comp hde (LocalCoordinateExtension.comp
      (restrictedSliceChart_inclusion d hs hne p hr.1) hr.2.1),
    LocalCoordinateExtension.comp hr.2.2 (LocalCoordinateExtension.comp
      (restrictedSliceChart_projection d hs hne p hr.1) hed)⟩

/-- Construct the induced atlas on the actual subspace, then maximize it.
The linear projection gives a left inverse to the full inclusion differential. -/
theorem exists_slice_manifold {k n : ℕ} {a b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (h : HasSliceCharts T s k a) :
    ∃ S : SmoothManifold k a s, IsSmoothEmbedding S T Subtype.val ∧
      S.smoothStructure.val = maximalExtension ⊤ (sliceAtlas (k := k) (a := a) T s) := by
  let : T2Space N := T.topologicalManifold.hausdorff
  let : SecondCountableTopology N := T.topologicalManifold.secondCountable
  have hA := sliceAtlas_isContDiffAtlas T s h
  let S : SmoothManifold k a s := {
    topologicalManifold := ⟨inferInstance, inferInstance, _, hA.1⟩
    smoothStructure := ⟨_, maximalExtension_isMaximal hA⟩ }
  have hf : IsSmoothMap S T Subtype.val := by
    intro p
    obtain ⟨c, hc, hp⟩ := hA.1 p
    obtain ⟨e, he, hpe⟩ := T.smoothStructure.property.1.1 p.val
    apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ S.smoothStructure.property.1
      T.smoothStructure.property.1 Subtype.val p).mpr
    exact ⟨continuousAt_subtype_val, c, subset_maximalExtension hA hc,
      e, he, hp, hpe, (sliceAtlas_inclusion_retraction T s c hc p hp e he hpe).1⟩
  refine ⟨S, ⟨hf, Subtype.val_injective, ?_, ?_⟩, rfl⟩
  · intro p
    obtain ⟨c, hc, hp⟩ := hA.1 p
    obtain ⟨e, he, hpe⟩ := T.smoothStructure.property.1.1 p.val
    exact immersion_of_coordinate_retraction S T Subtype.val hf p c e
      (subset_maximalExtension hA hc) he hp hpe
      (sliceAtlas_inclusion_retraction T s c hc p hp e he hpe).2
  · exact ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩

/-- Compatibility with the generating chart cover suffices for compatibility
with its maximal smooth extension, also for charts of a different model kind. -/
theorem compatibleChart_of_generating_atlas {k : ℕ} {a q : ModelKind}
    {P : Type u} [TopologicalSpace P] (S : SmoothManifold k a P)
    (A : Set (ModelChart k a P)) (hA : IsAtlas A)
    (hS : S.smoothStructure.val = maximalExtension ⊤ A)
    (c : ModelChart k q P)
    (hc : ∀ e ∈ A, ∀ p, p ∈ c.source → p ∈ e.source →
      ChartContDiffAt ⊤ c e id p ∧ ChartContDiffAt ⊤ e c id p) :
    CompatibleChart S c := by
  intro d hd p hp hpd
  obtain ⟨e, he, hpe⟩ := hA p
  have hde : ContDiffCompatible ⊤ d e := by
    rw [hS] at hd
    exact hd e he
  obtain ⟨hce, hec⟩ := hc e he p hp hpe
  exact ⟨LocalCoordinateExtension.comp
      (chartContDiffAt_of_compatible (contDiffCompatible_symm hde) hpe hpd) hce,
    LocalCoordinateExtension.comp hec (chartContDiffAt_of_compatible hde hpd hpe)⟩


/-- Every ambient slice chart gives compatible coordinates on the induced structure. -/
theorem sliceRestriction_compatible {k n : ℕ} {a b q : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (h : HasSliceCharts T s k a) (S : SmoothManifold k a s)
    (hS : S.smoothStructure.val = maximalExtension ⊤ (sliceAtlas (k := k) (a := a) T s))
    (d : ModelChart n .euclidean N) (hd : CompatibleChart T d)
    (hs : IsSliceChart s k q d) (hne : Nonempty {p : s // p.val ∈ d.source}) :
    CompatibleChart S (restrictedSliceChart d hs hne) := by
  apply compatibleChart_of_generating_atlas S _ (sliceAtlas_cover T s h) hS
  intro c hc p hp hpc
  obtain ⟨q', hq', d', hd', hs', hne', hrc⟩ := hc
  have hr := hrc p hpc
  exact ⟨LocalCoordinateExtension.comp hr.2.2
      (restrictedSliceChart_transition T d d' hd hd' hs hs' hne hne' p hp hr.1),
    LocalCoordinateExtension.comp
      (restrictedSliceChart_transition T d' d hd' hd hs' hs hne' hne p hr.1 hp) hr.2.1⟩

/-- The slice criterion constructs the unique embedded smooth structure on
exactly the given subset and its subspace topology. -/
theorem slice_structure :
    Specs.SmoothManifolds.Ch03.SliceStructures.slice_structureType.{u} := by
  intro k n a b N _ T s hT h
  obtain ⟨S, hSE, hS⟩ := exists_slice_manifold T s h
  refine ⟨S, hSE, ?_, ?_⟩
  · intro q d hq hd hs hne
    exact ⟨hs.1, restrictedSliceChart d hs hne,
      restrictedSliceChart_isSliceRestriction d hs hne,
      sliceRestriction_compatible T s h S hS d hd hs hne⟩
  · intro R hR
    exact embedded_structure_eq T s R S hT hR hSE

noncomputable section CircleExample

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def planeModelHomeomorph : Plane ≃ₜ ModelSpace 2 .euclidean :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.Set.univ _).symm

def planeModelChart : ModelChart 2 .euclidean Plane :=
  planeModelHomeomorph.toOpenPartialHomeomorph

@[simp] theorem planeModelChart_val (x : Plane) :
    (planeModelChart x).val = EuclideanSpace.equiv (Fin 2) ℝ x := rfl

private theorem planeModelChart_compatible :
    ContDiffCompatible (⊤ : ℕ∞) planeModelChart planeModelChart := by
  constructor <;> intro x hx
  · refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    intro y hy hyU
    change y.val = (planeModelChart (planeModelChart.symm y)).val
    exact congrArg Subtype.val (planeModelHomeomorph.apply_symm_apply y).symm
  · refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    intro y hy hyU
    change y.val = (planeModelChart (planeModelChart.symm y)).val
    exact congrArg Subtype.val (planeModelHomeomorph.apply_symm_apply y).symm

private theorem planeModelAtlas :
    IsContDiffAtlas (⊤ : ℕ∞) ({planeModelChart} : Set (ModelChart 2 .euclidean Plane)) := by
  refine ⟨fun p => ⟨planeModelChart, mem_singleton _, mem_univ _⟩, ?_⟩
  intro c hc d hd
  rw [mem_singleton_iff] at hc hd
  subst c d
  exact planeModelChart_compatible

noncomputable def standardPlaneManifold : SmoothManifold 2 .euclidean Plane where
  topologicalManifold := {
    hausdorff := inferInstance
    secondCountable := inferInstance
    atlas := {planeModelChart}
    covers := planeModelAtlas.1 }
  smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {planeModelChart},
    maximalExtension_isMaximal planeModelAtlas⟩

theorem standardPlaneManifold_chart : HasStandardPlaneChart standardPlaneManifold := by
  refine ⟨planeModelChart, subset_maximalExtension planeModelAtlas (mem_singleton _), rfl, ?_⟩
  exact fun _ => rfl

/-- Inversion omits its center and is its own smooth inverse there. -/
def inversionPartialHomeomorph (c : Plane) : OpenPartialHomeomorph Plane Plane where
  toFun := EuclideanGeometry.inversion c 1
  invFun := EuclideanGeometry.inversion c 1
  source := {c}ᶜ
  target := {c}ᶜ
  map_source' x hx := by
    simpa only [mem_compl_iff, mem_singleton_iff,
      EuclideanGeometry.inversion_eq_center (by norm_num : (1:ℝ) ≠ 0)] using hx
  map_target' x hx := by
    simpa only [mem_compl_iff, mem_singleton_iff,
      EuclideanGeometry.inversion_eq_center (by norm_num : (1:ℝ) ≠ 0)] using hx
  left_inv' x hx := EuclideanGeometry.inversion_inversion c (by norm_num) x
  right_inv' x hx := EuclideanGeometry.inversion_inversion c (by norm_num) x
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun := continuousOn_const.inversion continuousOn_const continuousOn_id
    (by simpa only [mem_compl_iff, mem_singleton_iff] using (fun x (hx : x ∈ ({c}ᶜ : Set Plane)) => hx))
  continuousOn_invFun := continuousOn_const.inversion continuousOn_const continuousOn_id
    (by simpa only [mem_compl_iff, mem_singleton_iff] using (fun x (hx : x ∈ ({c}ᶜ : Set Plane)) => hx))

theorem contDiffOn_inversionPartialHomeomorph (c : Plane) :
    ContDiffOn ℝ (⊤ : ℕ∞) (inversionPartialHomeomorph c) ({c}ᶜ) :=
  contDiffOn_const.inversion contDiffOn_const contDiffOn_id (fun _ hx => hx)

def circlePole (s : ℝ) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,s]

def circleInversionValue (s : ℝ) (x : Plane) : Euclidean 2 :=
  EuclideanSpace.equiv (Fin 2) ℝ
    (EuclideanGeometry.inversion (circlePole s) 1 x - (1/2:ℝ) • circlePole s)

def circleInversionChart (s : ℝ) : ModelChart 2 .euclidean Plane :=
  (inversionPartialHomeomorph (circlePole s)).trans
    ((Homeomorph.subRight ((1/2:ℝ) • circlePole s)).trans
      planeModelHomeomorph).toOpenPartialHomeomorph

@[simp] theorem circleInversionChart_val (s : ℝ) (x : Plane) :
    (circleInversionChart s x).val = circleInversionValue s x := rfl

@[simp] theorem circleInversionChart_source (s : ℝ) :
    (circleInversionChart s).source = {circlePole s}ᶜ := by
  simp [circleInversionChart, inversionPartialHomeomorph]


def circleInversionCoordinates (s : ℝ) :
    OpenPartialHomeomorph (Euclidean 2) (Euclidean 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph.toOpenPartialHomeomorph.trans
    ((inversionPartialHomeomorph (circlePole s)).trans
      ((Homeomorph.subRight ((1/2:ℝ) • circlePole s)).trans
        (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph).toOpenPartialHomeomorph)

@[simp] theorem circleInversionCoordinates_source (s : ℝ) :
    (circleInversionCoordinates s).source =
      {x | (EuclideanSpace.equiv (Fin 2) ℝ).symm x ≠ circlePole s} := by
  ext x
  simp [circleInversionCoordinates, inversionPartialHomeomorph]

private theorem circleInversionCoordinates_smooth (s : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (circleInversionCoordinates s)
      (circleInversionCoordinates s).source := by
  have hinv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Euclidean 2 => EuclideanGeometry.inversion (circlePole s) 1
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm x))
      (circleInversionCoordinates s).source :=
    contDiffOn_const.inversion contDiffOn_const
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffOn
      (by intro x hx; simpa only [circleInversionCoordinates_source, mem_ofPred_eq] using hx)
  exact (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp_contDiffOn
    (hinv.sub contDiffOn_const)

private theorem circleInversionCoordinates_inverse_smooth (s : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (circleInversionCoordinates s).symm
      (circleInversionCoordinates s).target := by
  have hne : ∀ x ∈ (circleInversionCoordinates s).target,
      (EuclideanSpace.equiv (Fin 2) ℝ).symm x + (1/2:ℝ) • circlePole s ≠ circlePole s := by
    intro x hx
    simpa [circleInversionCoordinates, inversionPartialHomeomorph] using hx
  have hinv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Euclidean 2 => EuclideanGeometry.inversion (circlePole s) 1
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm x + (1/2:ℝ) • circlePole s))
      (circleInversionCoordinates s).target :=
    contDiffOn_const.inversion contDiffOn_const
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffOn.add contDiffOn_const) hne
  exact (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp_contDiffOn hinv

theorem circleInversionChart_compatible (s : ℝ) :
    CompatibleChart standardPlaneManifold (circleInversionChart s) := by
  apply compatibleChart_of_change standardPlaneManifold planeModelChart
    (subset_maximalExtension planeModelAtlas (mem_singleton _))
    (circleInversionChart s) (circleInversionCoordinates s)
    (circleInversionCoordinates_smooth s) (circleInversionCoordinates_inverse_smooth s)
    (fun _ _ => mem_univ _)
  intro y hy
  refine ⟨?_, rfl⟩
  rw [circleInversionCoordinates_source]
  change (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ((EuclideanSpace.equiv (Fin 2) ℝ) y) ≠ circlePole s
  rw [ContinuousLinearEquiv.symm_apply_apply]
  simpa only [circleInversionChart_source, mem_compl_iff, mem_singleton_iff] using hy

lemma circleInversionValue_axis_iff (s : ℝ) (hs : s ^ 2 = 1) (x : Plane)
    (hx : x ≠ circlePole s) :
    circleInversionValue s x 1 = 0 ↔ x ∈ Metric.sphere 0 1 := by
  have hs0 : s ≠ 0 := by intro hz; rw [hz] at hs; norm_num at hs
  have hd0 : dist x (circlePole s) ≠ 0 := dist_ne_zero.mpr hx
  have hnx : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  have hdx : dist x (circlePole s) ^ 2 = (x 0) ^ 2 + (x 1 - s) ^ 2 := by
    rw [dist_eq_norm]
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, circlePole]
  have hcoord : circleInversionValue s x 1 =
      (1 / dist x (circlePole s)) ^ 2 * (x 1 - s) + s / 2 := by
    simp [circleInversionValue, EuclideanGeometry.inversion, circlePole]
    ring
  have hid : s * (‖x‖ ^ 2 - 1) =
      2 * (x 1 - s) + s * dist x (circlePole s) ^ 2 := by
    linear_combination s * hnx - s * hdx + (2 * x 1 - s) * hs
  rw [hcoord]
  rw [Metric.mem_sphere, dist_zero_right]
  constructor
  · intro hz
    have hz' := hz
    field_simp at hz'
    have hmul : s * (‖x‖ ^ 2 - 1) = 0 := by rw [hid]; nlinarith
    have hn2 : ‖x‖ ^ 2 = 1 := by rcases mul_eq_zero.mp hmul with hz | hz; exact (hs0 hz).elim; linarith
    nlinarith [norm_nonneg x]
  · intro hn
    have hnum : 2 * (x 1 - s) + s * dist x (circlePole s) ^ 2 = 0 := by
      rw [hn] at hid
      nlinarith [hid]
    field_simp
    nlinarith


theorem coordinateSlice_one_two_iff (z : Euclidean 2) :
    z ∈ coordinateSlice 1 2 .euclidean ↔ z 1 = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [sliceEmbedding]
  · intro hz
    refine ⟨(fun _ => z 0), mem_univ _, ?_⟩
    funext i
    fin_cases i <;> simp [sliceEmbedding, hz]

theorem circleInversionChart_slice (s : ℝ) (hs : s ^ 2 = 1) :
    IsSliceChart standardCircle 1 .euclidean (circleInversionChart s) := by
  refine ⟨by norm_num, (by intro h; cases h), ?_⟩
  ext z
  constructor
  · rintro ⟨x, ⟨hxS, hxD⟩, rfl⟩
    refine ⟨(circleInversionChart s).map_source hxD, ?_⟩
    apply (coordinateSlice_one_two_iff _).mpr
    apply (circleInversionValue_axis_iff s hs x _).mpr hxS
    simpa only [circleInversionChart_source, mem_compl_iff, mem_singleton_iff] using hxD
  · rintro ⟨hzD, hzS⟩
    refine ⟨(circleInversionChart s).symm z, ⟨?_,
      (circleInversionChart s).symm.map_source hzD⟩,
      (circleInversionChart s).right_inv hzD⟩
    have hxD := (circleInversionChart s).symm.map_source hzD
    change (circleInversionChart s).symm z ∈ (circleInversionChart s).source at hxD
    apply (circleInversionValue_axis_iff s hs _ _).mp
    · change ((circleInversionChart s) ((circleInversionChart s).symm z)).val 1 = 0
      rw [(circleInversionChart s).right_inv hzD]
      exact (coordinateSlice_one_two_iff _).mp hzS
    · simpa only [circleInversionChart_source, mem_compl_iff, mem_singleton_iff] using hxD

theorem standardCircle_hasSliceCharts :
    HasSliceCharts standardPlaneManifold standardCircle 1 .euclidean := by
  refine ⟨by norm_num, ?_⟩
  intro p hp
  have hne : circlePole 1 ≠ circlePole (-1) := by
    intro h
    have h' := congrArg (fun x : Plane => x 1) h
    norm_num [circlePole] at h'
  by_cases h : p = circlePole 1
  · refine ⟨.euclidean, Or.inl rfl, circleInversionChart (-1),
      circleInversionChart_compatible (-1), ?_, circleInversionChart_slice (-1) (by norm_num)⟩
    simpa only [circleInversionChart_source, mem_compl_iff, mem_singleton_iff, h] using hne
  · refine ⟨.euclidean, Or.inl rfl, circleInversionChart 1,
      circleInversionChart_compatible 1, ?_, circleInversionChart_slice 1 (by norm_num)⟩
    simpa only [circleInversionChart_source, mem_compl_iff, mem_singleton_iff] using h

theorem circle_boundary_distinction :
    Specs.SmoothManifolds.Ch03.SliceStructures.circle_boundary_distinctionType := by
  refine ⟨standardPlaneManifold, standardPlaneManifold_chart, ?_⟩
  obtain ⟨C, hC, hrest, huniq⟩ := slice_structure standardPlaneManifold standardCircle
    (intrinsicBoundary_euclidean standardPlaneManifold) standardCircle_hasSliceCharts
  exact ⟨C, hC, intrinsicBoundary_euclidean C, circle_frontier⟩


end CircleExample

end SmoothManifolds.SliceStructures
