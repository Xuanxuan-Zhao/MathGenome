import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.RegularDomains
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SliceStructures
namespace SmoothManifolds.RegularDomains
open ModelData AtlasData MapData BoundaryData MapClassData SliceData RegularDomainData
open Set Filter
open scoped Topology ContDiff
set_option linter.unusedVariables false
universe u v

/-- Pointwise form of the exact slice image equality, valid on the chart source. -/
theorem mem_iff_slice {k n : ℕ} {N : Type u} [TopologicalSpace N]
    {s : Set N} {q : ModelKind} {d : ModelChart n .euclidean N}
    (hd : IsSliceChart s k q d) {p : N} (hp : p ∈ d.source) :
    p ∈ s ↔ (d p).val ∈ coordinateSlice k n q := by
  constructor
  · intro hs
    have h : d p ∈ d '' (s ∩ d.source) := ⟨p, ⟨hs, hp⟩, rfl⟩
    rw [hd.2.2] at h
    exact h.2
  · intro hs
    have h : d p ∈ d '' (s ∩ d.source) := by
      rw [hd.2.2]
      exact ⟨d.map_source hp, hs⟩
    obtain ⟨x, hx, he⟩ := h
    have hxp : x = p := d.injOn hx.2 hp he
    exact hxp ▸ hx.1

/-- A full-dimensional Euclidean slice is an ambient open neighborhood. -/
theorem full_slice_source_subset
    (hfull : Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType)
    {n : ℕ} {N : Type u} [TopologicalSpace N] {s : Set N}
    {d : ModelChart n .euclidean N} (hd : IsSliceChart s n .euclidean d) :
    d.source ⊆ s := by
  intro p hp
  apply (mem_iff_slice hd hp).mpr
  rw [hfull]
  exact mem_univ _

/-- At the face of a full-dimensional half-slice, the subset has no ambient
interior. This uses an actual Euclidean open chart image. -/
theorem half_slice_face_not_interior
    (hfull : Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType)
    (hproj : Specs.SmoothManifolds.Ch03.SliceStructures.sliceProjection_embeddingType)
    {n : ℕ} {N : Type u} [TopologicalSpace N] {s : Set N}
    {d : ModelChart n .euclidean N} (hd : IsSliceChart s n .halfSpace d)
    {p : N} (hp : p ∈ d.source)
    (hface : ∃ hnn : n ≤ n, sliceProjection hnn (d p).val ∈ halfSpaceFace n) :
    p ∉ interior s := by
  have hemb (x : Euclidean n) : sliceEmbedding n n x = x := by
    funext i
    simp [sliceEmbedding, i.isLt]
  have hpr (hnn : n ≤ n) (x : Euclidean n) : sliceProjection hnn x = x := by
    simpa only [hemb] using hproj hnn x
  obtain ⟨hnn, hf⟩ := hface
  rw [hpr] at hf
  intro hpi
  let E := InteriorInverse.ambientChart d
  have hpE : p ∈ E.source := ⟨hp, by change (d p).val ∈ interior (modelSet n .euclidean); simp [ModelData.modelSet]⟩
  have hsub : E '' (E.source ∩ interior s) ⊆ modelSet n .halfSpace := by
    rintro z ⟨x, hx, rfl⟩
    have hs := (mem_iff_slice hd hx.1.1).mp (interior_subset hx.2)
    rw [hfull] at hs
    exact hs
  have hEi : (d p).val ∈ interior (modelSet n .halfSpace) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((E.isOpen_image_source_inter isOpen_interior).mem_nhds
        ⟨p, ⟨hpE, hpi⟩, rfl⟩) hsub)
  have hm : (d p).val ∈ modelSet n .halfSpace := interior_subset hEi
  exact (mem_modelFace_iff_not_mem_interior
    (⟨(d p).val, hm⟩ : ModelSpace n .halfSpace)).mp hf hEi

/-- The real coordinate chart by itself is a smooth atlas. -/
theorem realChart_isContDiffAtlas :
    IsContDiffAtlas (⊤ : ℕ∞) ({realChart} : Set (ModelChart 1 .euclidean ℝ)) := by
  refine ⟨fun x => ⟨realChart, mem_singleton _, mem_univ _⟩, ?_⟩
  intro c hc d hd
  rcases mem_singleton_iff.mp hc with rfl
  rcases mem_singleton_iff.mp hd with rfl
  constructor <;> intro x hx
  all_goals
    refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    intro y hy hyU
    apply congrArg Subtype.val
    apply Subtype.ext
    funext i
    change y.val i = y.val 0
    rw [Fin.eq_zero i]

/-- The full-dimensional embedding case; unlike a positive-codimension
submanifold, its intrinsic interior is open in the ambient space. -/
theorem topology_of_slice_criteria
    (hinterior : Specs.SmoothManifolds.Ch03.SliceStructures.interior_sliceType.{u,v})
    (hboundary : Specs.SmoothManifolds.Ch03.SliceStructures.boundary_sliceType.{u,v})
    (hfull : Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType)
    (hproj : Specs.SmoothManifolds.Ch03.SliceStructures.sliceProjection_embeddingType) :
    Specs.SmoothManifolds.Ch03.RegularDomains.regular_domain_topologyType.{u,v} := by
  intro m a b P M _ _ S T f hT hclosed hf
  have hforward (p : P) (hp : p ∈ manifoldInterior S) :
      f p ∈ interior (range f) := by
    obtain ⟨d, _, hpd, hs⟩ := hinterior S T f hT hf p hp
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (d.open_source.mem_nhds hpd) (full_slice_source_subset hfull hs))
  have hboundary_not (p : P) (hp : p ∈ intrinsicBoundary S) :
      f p ∉ interior (range f) := by
    obtain ⟨d, _, hpd, hs, hface⟩ := hboundary S T f hT hf p hp
    exact half_slice_face_not_interior hfull hproj hs hpd hface
  have hiff (p : P) : p ∈ manifoldInterior S ↔ f p ∈ interior (range f) := by
    refine ⟨hforward p, ?_⟩
    intro hfp
    by_contra hpi
    have hb : p ∈ intrinsicBoundary S := by
      have h : p ∉ (intrinsicBoundary S)ᶜ := by rwa [compl_intrinsicBoundary]
      exact not_not.mp h
    exact hboundary_not p hb hfp
  have hi : f '' manifoldInterior S = interior (range f) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hiff p).mp hp
    · intro hx
      obtain ⟨p, rfl⟩ := interior_subset hx
      exact ⟨p, (hiff p).mpr hx, rfl⟩
  refine ⟨hi, ?_⟩
  rw [frontier, hclosed.closure_eq]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨mem_range_self p, hboundary_not p hp⟩
  · rintro ⟨⟨p, rfl⟩, hp⟩
    refine ⟨p, ?_, rfl⟩
    by_contra hb
    have hi : p ∈ manifoldInterior S := by
      rw [← compl_intrinsicBoundary]
      exact hb
    exact hp ((hiff p).mp hi)

/-- The subset/inclusion specialization, with precisely the ambient subspace
topology used by `IsRegularDomain`. -/
theorem regular_domain_inclusion_topology
    (htop : Specs.SmoothManifolds.Ch03.RegularDomains.regular_domain_topologyType.{u,u})
    {m : ℕ} {a b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (d : Set M) (S : SmoothManifold m a d)
    (hT : intrinsicBoundary T = ∅) (hd : IsRegularDomain T d S) :
    Subtype.val '' manifoldInterior S = interior d ∧
      Subtype.val '' intrinsicBoundary S = frontier d := by
  have hrange : range (Subtype.val : d → M) = d := Subtype.range_coe
  simpa only [hrange] using
    htop S T Subtype.val hT (hrange.symm ▸ hd.1) hd.2

theorem standard_real_structure
    : Specs.SmoothManifolds.Ch03.RegularDomains.standard_real_structureType := by
  let A : Set (ModelChart 1 .euclidean ℝ) := {realChart}
  let R : SmoothManifold 1 .euclidean ℝ := {
    topologicalManifold := ⟨inferInstance, inferInstance, A, realChart_isContDiffAtlas.1⟩
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) A,
      maximalExtension_isMaximal realChart_isContDiffAtlas⟩ }
  exact ⟨R, subset_maximalExtension realChart_isContDiffAtlas (mem_singleton _)⟩

theorem regular_domain_topology
    : Specs.SmoothManifolds.Ch03.RegularDomains.regular_domain_topologyType.{u,v} := by
  exact topology_of_slice_criteria SliceStructures.interior_slice SliceStructures.boundary_slice
    SliceStructures.coordinateSlice_full SliceStructures.sliceProjection_embedding

theorem regular_value_empty_zero
    : Specs.SmoothManifolds.Ch03.RegularDomains.regular_value_empty_zeroType.{u} := by
  intro m b M _ T R f hf p hp
  have h : p ∈ f ⁻¹' {0} := hp
  rw [hf] at h
  exact h.elim

/-- A nonzero linear functional is nonzero on some standard coordinate vector. -/
theorem exists_nonzero_coordinate {m : ℕ} (L : Euclidean m →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i : Fin m, L (Pi.single i 1) ≠ 0 := by
  classical
  by_contra h
  have hall : ∀ i : Fin m, L (Pi.single i 1) = 0 := by simpa using h
  have hz : L.toLinearMap = 0 := (Pi.basisFun ℝ (Fin m)).ext (by simpa using hall)
  apply hL
  ext z
  exact congrArg (fun A : Euclidean m →ₗ[ℝ] ℝ => A z) hz

/-- Replace one coordinate by -F and permute it to the final coordinate.
The inverse function theorem applies because that coordinate partial is nonzero. -/
theorem euclidean_defining_coordinate {n : ℕ}
    (F : Euclidean (n + 1) → ℝ) (U : Set (Euclidean (n + 1))) (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) (x : Euclidean (n + 1)) (hx : x ∈ U)
    (hL : fderiv ℝ F x ≠ 0) :
    ∃ A : OpenPartialHomeomorph (Euclidean (n + 1)) (Euclidean (n + 1)),
      x ∈ A.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) A A.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) A.symm A.target ∧
      ∀ z ∈ A.source, A z (Fin.last n) = -F z := by
  classical
  let L := fderiv ℝ F x
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate L hL
  let G : Euclidean (n + 1) → Euclidean (n + 1) := fun z j => if j = i then -F z else z j
  let D : Euclidean (n + 1) →L[ℝ] Euclidean (n + 1) :=
    ContinuousLinearMap.pi (fun j => if j = i then -L else ContinuousLinearMap.proj j)
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G U := by
    apply contDiffOn_pi.mpr
    intro j
    by_cases hji : j = i
    · simpa only [G, if_pos hji] using hF.neg
    · simpa only [G, if_neg hji] using (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) j).contDiffOn
  have hdF : HasFDerivAt F L x :=
    ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdG : HasFDerivAt G D x := by
    apply hasFDerivAt_pi.mpr
    intro j
    by_cases hji : j = i
    · convert hdF.neg using 1 <;> simp [G, D, hji] <;> rfl
    · convert (ContinuousLinearMap.proj j : Euclidean (n + 1) →L[ℝ] ℝ).hasFDerivAt (x := x) using 1 <;> simp [G, D, hji] <;> rfl
  have hinj : Function.Injective D := by
    apply (injective_iff_map_eq_zero D).mpr
    intro z hz
    have hzi : L z = 0 := by
      have h := congrFun hz i
      simpa [D] using h
    have hzj (j : Fin (n + 1)) (hji : j ≠ i) : z j = 0 := by
      have h := congrFun hz j
      simpa [D, hji] using h
    have hsingle : z = z i • Pi.single i (1 : ℝ) := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [hzj j hji, Pi.single_eq_of_ne hji]
    have hzero : z i = 0 := by
      have h : z i * L (Pi.single i 1) = 0 := by
        calc
          z i * L (Pi.single i 1) = L (z i • Pi.single i 1) := by simp
          _ = L z := congrArg L hsingle.symm
          _ = 0 := hzi
      exact (mul_eq_zero.mp h).resolve_right hi
    rw [hsingle, hzero, zero_smul]
  have hbij : Function.Bijective D :=
    ⟨hinj, D.toLinearMap.injective_iff_surjective.mp hinj⟩
  obtain ⟨j, hxj, hj, hji⟩ := InteriorInverse.euclidean_inverse (⊤ : ℕ∞) (by simp)
    G U hU hG x hx D hdG hbij
  let j' := j.restrOpen U hU
  let P : Euclidean (n + 1) ≃L[ℝ] Euclidean (n + 1) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + 1) => ℝ) (Equiv.swap i (Fin.last n))
  let A := j'.transHomeomorph P.toHomeomorph
  refine ⟨A, ⟨hxj, hx⟩, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => P (j z)) j'.source
    rw [hj]
    exact P.contDiff.comp_contDiffOn (hG.mono inter_subset_right)
  · change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => j.symm (P.symm z)) A.target
    exact hji.comp P.symm.contDiff.contDiffOn (fun z hz => hz.1)
  · intro z hz
    change (P (j z)) (Fin.last n) = -F z
    rw [hj]
    simp [P, ContinuousLinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft,
      Equiv.piCongrLeft, G]

/-- Smooth Euclidean coordinate changes applied to an original interior chart
are compatible with all the original atlas charts in both directions. -/
theorem compatible_changed_chart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold n a M) (e : ModelChart n a M)
    (he : e ∈ T.smoothStructure.val)
    (A : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A A.source)
    (hAi : ContDiffOn ℝ (⊤ : ℕ∞) A.symm A.target) :
    let d : ModelChart n .euclidean M := ((InteriorInverse.ambientChart e).trans A).transHomeomorph
      (Homeomorph.Set.univ (Euclidean n)).symm
    CompatibleChart T d := by
  intro d c hc p hp hpc
  have hpe : p ∈ e.source := hp.1.1
  have heA : (e p).val ∈ A.source := hp.2
  have hAp : (d p).val ∈ A.target := A.map_source heA
  have hed : ChartContDiffAt (⊤ : ℕ∞) e d id p := by
    exact ⟨A.source, A.open_source, heA, A, hA, Eventually.of_forall (fun _ => rfl)⟩
  have hde : ChartContDiffAt (⊤ : ℕ∞) d e id p := by
    refine ⟨A.target, A.open_target, hAp, A.symm, hAi, ?_⟩
    filter_upwards [d.open_source.mem_nhds hp] with z hz
    exact A.left_inv hz.2
  have hce := chartContDiffAt_of_compatible
    (T.smoothStructure.property.1.2 c hc e he) hpc hpe
  have hec := chartContDiffAt_of_compatible
    (T.smoothStructure.property.1.2 e he c hc) hpe hpc
  exact ⟨_root_.SmoothManifolds.LocalCoordinateExtension.comp hec hde,
    _root_.SmoothManifolds.LocalCoordinateExtension.comp hed hce⟩


/-- An exact local membership test gives the full chart-image equality. -/
theorem isSliceChart_of_mem_iff {k n : ℕ} {q : ModelKind} {M : Type u}
    [TopologicalSpace M] {s : Set M} (d : ModelChart n .euclidean M)
    (hkn : k ≤ n) (hq : q = .halfSpace → 0 < k)
    (h : ∀ p ∈ d.source, p ∈ s ↔ (d p).val ∈ coordinateSlice k n q) :
    IsSliceChart s k q d := by
  refine ⟨hkn, hq, ?_⟩
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨d.map_source hp.2, (h p hp.2).mp hp.1⟩
  · rintro ⟨hz, hs⟩
    refine ⟨d.symm z, ⟨?_, d.map_target hz⟩, d.right_inv hz⟩
    apply (h _ (d.map_target hz)).mpr
    rwa [d.right_inv hz]

/-- Restricting an ambient chart to an open set preserves smooth compatibility. -/
theorem compatibleChart_restrOpen {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold n a M) (d : ModelChart n .euclidean M)
    (hd : CompatibleChart T d) (V : Set M) (hV : IsOpen V) :
    CompatibleChart T (d.restrOpen V hV) := by
  intro e he p hp hpe
  exact hd e he p hp.1 hpe

/-- Negative points have full Euclidean slice neighborhoods. -/
theorem negative_sublevel_chart
    (hfull : Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType)
    {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (f : M → ℝ) (hc : Continuous f)
    (hT : intrinsicBoundary T = ∅) (p : M) (hp : f p < 0) :
    ∃ d : ModelChart m .euclidean M, CompatibleChart T d ∧ p ∈ d.source ∧
      IsSliceChart (sublevel f) m .euclidean d := by
  have hpi : p ∈ manifoldInterior T := by simp [← compl_intrinsicBoundary, hT]
  obtain ⟨e, he, hpe, hpei⟩ := hpi
  let A := OpenPartialHomeomorph.refl (Euclidean m)
  let d₀ : ModelChart m .euclidean M := ((InteriorInverse.ambientChart e).trans A).transHomeomorph
    (Homeomorph.Set.univ (Euclidean m)).symm
  have hd₀ : CompatibleChart T d₀ := compatible_changed_chart T e he A contDiffOn_id contDiffOn_id
  let V := {x : M | f x < 0}
  have hV : IsOpen V := isOpen_lt hc continuous_const
  let d := d₀.restrOpen V hV
  refine ⟨d, compatibleChart_restrOpen T d₀ hd₀ V hV, ⟨⟨⟨hpe, hpei⟩, mem_univ _⟩, hp⟩, ?_⟩
  apply isSliceChart_of_mem_iff d le_rfl (by intro h; cases h)
  intro x hx
  rw [hfull]
  exact ⟨fun _ => mem_univ _, fun _ => (show f x ≤ 0 from le_of_lt hx.2)⟩

/-- Regular zeros yield half-slice charts and lie on their faces. The scalar
regularity comes from the canonical tangent differential, via its chart API. -/
theorem zero_sublevel_chart
    (hfull : Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType)
    {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ) (f : M → ℝ)
    (hT : intrinsicBoundary T = ∅) (hR : HasStandardRealChart R)
    (hf : IsSmoothMap T R f) (hr : IsRegularValue T R f 0) (p : M) (hp0 : f p = 0) :
    ∃ d : ModelChart m .euclidean M, CompatibleChart T d ∧ p ∈ d.source ∧
      IsSliceChart (sublevel f) m .halfSpace d ∧ (d p).val ∈ halfSpaceFace m := by
  have hpi : p ∈ manifoldInterior T := by simp [← compl_intrinsicBoundary, hT]
  obtain ⟨e, he, hpe, hpei⟩ := hpi
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := (hf p).2 e he realChart hR hpe (mem_univ _)
  have hdG : HasFDerivAt G (fderiv ℝ G (e p).val) (e p).val :=
    ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hDG : FiniteRegularityData.chartDerivative e realChart f p = fderiv ℝ G (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hpe _ ⟨G, hdG, heG⟩
  have hf1 : ManifoldContDiff 1 T.smoothStructure.val R.smoothStructure.val f :=
    manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f le_top hf
  have hsurj := (MapClasses.chart_invariants T R f hf1 p e realChart he hR hpe
    (mem_univ _)).2.2.mp (hr p hp0)
  rw [hDG] at hsurj
  obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
  let F : Euclidean m → ℝ := fun z => G z 0
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U :=
    (ContinuousLinearMap.proj (0 : Fin 1) : Euclidean 1 →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hdF : HasFDerivAt F
      ((ContinuousLinearMap.proj (0 : Fin 1)).comp (fderiv ℝ G (e p).val)) (e p).val :=
    (ContinuousLinearMap.proj (0 : Fin 1) : Euclidean 1 →L[ℝ] ℝ).hasFDerivAt.comp _ hdG
  have hL : fderiv ℝ F (e p).val ≠ 0 := by
    intro hz
    rw [hdF.fderiv] at hz
    have h := DFunLike.congr_fun hz v
    change fderiv ℝ G (e p).val v 0 = 0 at h
    rw [hv] at h
    exact one_ne_zero h
  cases m with
  | zero =>
    obtain ⟨i, _⟩ := exists_nonzero_coordinate _ hL
    exact Fin.elim0 i
  | succ n =>
    obtain ⟨A, hpA, hA, hAi, hlast⟩ := euclidean_defining_coordinate F U hU hF (e p).val hpU hL
    let d₀ : ModelChart (n + 1) .euclidean M :=
      ((InteriorInverse.ambientChart e).trans A).transHomeomorph
        (Homeomorph.Set.univ (Euclidean (n + 1))).symm
    have hd₀ : CompatibleChart T d₀ := compatible_changed_chart T e he A hA hAi
    obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp heG
    let d := d₀.restrOpen V hV
    have hlastf (z : M) (hz : z ∈ d.source) : (d z).val (Fin.last n) = -f z := by
      change A (e z).val (Fin.last n) = -f z
      rw [hlast (e z).val (show (e z).val ∈ A.source from hz.1.2)]
      have h := congrFun (hVsub hz.2) (0 : Fin 1)
      exact congrArg Neg.neg h
    have hpd : p ∈ d.source := ⟨⟨⟨hpe, hpei⟩, hpA⟩, hpV⟩
    refine ⟨d, compatibleChart_restrOpen T d₀ hd₀ V hV, hpd, ?_, ?_⟩
    · apply isSliceChart_of_mem_iff d le_rfl (fun _ => Nat.succ_pos _)
      intro z hz
      rw [hfull]
      change f z ≤ 0 ↔ 0 ≤ (d z).val (Fin.last n)
      rw [hlastf z hz]
      exact neg_nonneg.symm
    · change (d p).val (Fin.last n) = 0
      rw [hlastf p hpd, hp0, neg_zero]

/-- Boundary coordinates are invariant even for a compatible chart of the
other permitted model kind, without assuming that chart belongs to the atlas. -/
theorem boundary_iff_compatible_chart {m : ℕ} {a q : ModelKind} {P : Type u}
    [TopologicalSpace P] (S : SmoothManifold m a P) (c : ModelChart m q P)
    (hc : CompatibleChart S c) (p : P) (hp : p ∈ c.source) :
    p ∈ intrinsicBoundary S ↔ (c p).val ∈ modelFace m q := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  rw [intrinsicBoundary_iff_chart S e he p hpe]
  have h := hc e he p hp hpe
  exact modelFace_chart_independent e c p hpe hp h.2 h.1


/-- In full dimension the slice projection is the identity. -/
theorem full_sliceProjection
    (hproj : Specs.SmoothManifolds.Ch03.SliceStructures.sliceProjection_embeddingType)
    {m : ℕ} (hmm : m ≤ m) (x : Euclidean m) : sliceProjection hmm x = x := by
  have h : sliceEmbedding m m x = x := by funext i; simp [sliceEmbedding, i.isLt]
  simpa only [h] using hproj hmm x

/-- Purely ambient topology of a regular sublevel. Zero-dimensional regular
zeros are excluded by surjectivity itself, rather than a dimension assumption. -/
theorem regular_sublevel_ambient_topology
    (hfull : Specs.SmoothManifolds.Ch03.SliceStructures.coordinateSlice_fullType)
    (hproj : Specs.SmoothManifolds.Ch03.SliceStructures.sliceProjection_embeddingType)
    {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ) (f : M → ℝ)
    (hT : intrinsicBoundary T = ∅) (hR : HasStandardRealChart R)
    (hf : IsSmoothMap T R f) (hr : IsRegularValue T R f 0) :
    IsClosed (sublevel f) ∧ interior (sublevel f) = {x | f x < 0} ∧
      frontier (sublevel f) = f ⁻¹' {0} := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  have hclosed : IsClosed (sublevel f) := isClosed_le hc continuous_const
  have hi : interior (sublevel f) = {x | f x < 0} := by
    ext p
    constructor
    · intro hp
      have hle : p ∈ sublevel f := interior_subset hp
      change f p ≤ 0 at hle
      by_contra hnot
      have hp0 : f p = 0 := le_antisymm hle (le_of_not_gt hnot)
      obtain ⟨d, _, hpd, hs, hface⟩ := zero_sublevel_chart hfull T R f hT hR hf hr p hp0
      have hpr : sliceProjection (le_refl m) (d p).val ∈ halfSpaceFace m := by
        rwa [full_sliceProjection hproj]
      exact half_slice_face_not_interior hfull hproj hs hpd ⟨le_rfl, hpr⟩ hp
    · intro hp
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds hp)
        (fun q hq => (show f q ≤ 0 from le_of_lt hq))
  refine ⟨hclosed, hi, ?_⟩
  rw [frontier, hclosed.closure_eq, hi]
  ext p
  change (f p ≤ 0 ∧ ¬f p < 0) ↔ f p = 0
  exact ⟨fun h => le_antisymm h.1 (le_of_not_gt h.2), fun h => by simp [h]⟩

theorem regular_sublevel
    : Specs.SmoothManifolds.Ch03.RegularDomains.regular_sublevelType.{u} := by
  intro m b M _ T R f hT hR hf hr
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  have hcharts : HasSliceCharts T (sublevel f) m .halfSpace := by
    refine ⟨le_rfl, ?_⟩
    intro p hp
    by_cases hn : f p < 0
    · obtain ⟨d, hd, hpd, hs⟩ := negative_sublevel_chart SliceStructures.coordinateSlice_full T f hc hT p hn
      exact ⟨.euclidean, Or.inl rfl, d, hd, hpd, hs⟩
    · have hp0 : f p = 0 := le_antisymm hp (le_of_not_gt hn)
      obtain ⟨d, hd, hpd, hs, _⟩ := zero_sublevel_chart SliceStructures.coordinateSlice_full T R f hT hR hf hr p hp0
      exact ⟨.halfSpace, Or.inr rfl, d, hd, hpd, hs⟩
  obtain ⟨S, hEmb, hrestr, _⟩ := SliceStructures.slice_structure T (sublevel f) hT hcharts
  have hzero (p : sublevel f) (hp0 : f p.val = 0) : p ∈ intrinsicBoundary S := by
    obtain ⟨d, hd, hpd, hs, hface⟩ := zero_sublevel_chart SliceStructures.coordinateSlice_full T R f hT hR hf hr p.val hp0
    obtain ⟨hmm, c, hcr, hcomp⟩ := hrestr .halfSpace d (Or.inr rfl) hd hs ⟨⟨p, hpd⟩⟩
    have hpc : p ∈ c.source := by rw [hcr.1]; exact hpd
    apply (boundary_iff_compatible_chart S c hcomp p hpc).mpr
    have heq : (c p).val = (d p.val).val := by
      rw [hcr.2.2 p hpc, full_sliceProjection SliceStructures.sliceProjection_embedding]
    change (c p).val ∈ halfSpaceFace m
    rwa [heq]
  have hnegative (p : sublevel f) (hp : f p.val < 0) : p ∉ intrinsicBoundary S := by
    obtain ⟨d, hd, hpd, hs⟩ := negative_sublevel_chart SliceStructures.coordinateSlice_full T f hc hT p.val hp
    obtain ⟨hmm, c, hcr, hcomp⟩ := hrestr .euclidean d (Or.inl rfl) hd hs ⟨⟨p, hpd⟩⟩
    have hpc : p ∈ c.source := by rw [hcr.1]; exact hpd
    intro hb
    exact (boundary_iff_compatible_chart S c hcomp p hpc).mp hb
  have hboundary (p : sublevel f) : p ∈ intrinsicBoundary S ↔ f p.val = 0 := by
    refine ⟨?_, hzero p⟩
    intro hb
    by_contra hne
    have hlt : f p.val < 0 := lt_of_le_of_ne p.property hne
    exact hnegative p hlt hb
  have hi : Subtype.val '' manifoldInterior S = {x | f x < 0} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hnb : p ∉ intrinsicBoundary S := by
        rw [← mem_compl_iff, compl_intrinsicBoundary]
        exact hp
      have hne : f p.val ≠ 0 := fun h => hnb ((hboundary p).mpr h)
      exact lt_of_le_of_ne p.property hne
    · intro hx
      let p : sublevel f := ⟨x, (show f x ≤ 0 from le_of_lt hx)⟩
      refine ⟨p, ?_, rfl⟩
      rw [← compl_intrinsicBoundary]
      exact hnegative p hx
  have hb : Subtype.val '' intrinsicBoundary S = f ⁻¹' {0} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hboundary p).mp hp
    · intro hx
      have hx0 : f x = 0 := hx
      let p : sublevel f := ⟨x, by change f x ≤ 0; rw [hx0]⟩
      exact ⟨p, (hboundary p).mpr hx0, rfl⟩
  obtain ⟨hclosed, hai, hab⟩ := regular_sublevel_ambient_topology SliceStructures.coordinateSlice_full
    SliceStructures.sliceProjection_embedding T R f hT hR hf hr
  exact ⟨S, ⟨hclosed, hEmb⟩, hi, hb, hai, hab⟩

end SmoothManifolds.RegularDomains
