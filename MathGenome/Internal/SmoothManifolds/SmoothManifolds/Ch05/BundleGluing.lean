import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleGluing

namespace SmoothManifolds
open BundleData Bundle Set Filter TopologicalSpace
open scoped Topology
universe u v w z

abbrev SmoothCocycle := @BundleData.SmoothCocycle
abbrev SmoothVectorBundle := @BundleData.SmoothVectorBundle
abbrev LocalFrame := @BundleData.LocalFrame

namespace BundleData.SmoothCocycle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} (C : BundleData.SmoothCocycle S r ι)

/-- A cover supplies the pointwise preferred coordinate system even on an empty base. -/
noncomputable def indexAt (p : M) : ι := Classical.choose (C.covers p)

theorem mem_baseSet_indexAt (p : M) : p ∈ C.baseSet (C.indexAt p) :=
  Classical.choose_spec (C.covers p)

/-- Forget only smoothness: the exact same coordinate transitions construct the
underlying topological vector bundle. No countability assumption on ι is used. -/
noncomputable def toVectorBundleCore : VectorBundleCore ℝ M (Euclidean r) ι where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := C.indexAt
  mem_baseSet_at := C.mem_baseSet_indexAt
  coordChange i j p := (C.g i j p).toContinuousLinearMap
  coordChange_self i p hp v := by rw [C.self i p hp]; rfl
  continuousOn_coordChange i j p hp := (C.smooth i j p hp).1.continuousWithinAt
  coordChange_comp i j k p hp v :=
    congrArg (fun L : Euclidean r →L[ℝ] Euclidean r => L v)
      (C.comp i j k p hp.1.1 hp.1.2 hp.2)

/-- The coordinate change of the constructed bundle is precisely the input g_{ji}. -/
theorem localTriv_transition (i j : ι) (p : M)
    (hi : p ∈ C.baseSet i) (hj : p ∈ C.baseSet j) (v : Euclidean r) :
    (C.toVectorBundleCore.localTriv j
      ⟨p, (C.toVectorBundleCore.localTriv i).symm p v⟩).2 = C.g i j p v := by
  calc
    _ = (C.toVectorBundleCore.localTriv i).coordChangeL ℝ
        (C.toVectorBundleCore.localTriv j) p v :=
      (Trivialization.coordChangeL_apply _ _ ⟨hi, hj⟩ v).symm
    _ = _ := C.toVectorBundleCore.localTriv_coordChange_eq i j ⟨hi, hj⟩ v

theorem continuous_projection : Continuous C.toVectorBundleCore.proj :=
  C.toVectorBundleCore.continuous_proj

/-- Opposite coordinate changes are inverse on their actual overlap. -/
theorem inverse_transition (i j : ι) (p : M)
    (hi : p ∈ C.baseSet i) (hj : p ∈ C.baseSet j) :
    (C.g i j p).symm = C.g j i p := by
  apply ContinuousLinearEquiv.ext
  funext v
  apply (C.g i j p).injective
  have h := congrArg (fun L : Euclidean r →L[ℝ] Euclidean r => L v)
    (C.comp j i j p hj hi hj)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    C.self j p hj, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h.symm

/-- Hausdorffness follows from base separation and separation in a common
trivialization. Local Hausdorffness alone would not suffice. -/
theorem totalSpace_t2Space : T2Space C.toVectorBundleCore.TotalSpace := by
  letI : T2Space M := S.topologicalManifold.hausdorff
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hxy
  by_cases hbase : x.proj = y.proj
  · let e := C.toVectorBundleCore.localTriv (C.indexAt x.proj)
    have hx : x ∈ e.source := C.mem_baseSet_indexAt x.proj
    have hy : y ∈ e.source := by
      change y.proj ∈ C.baseSet (C.indexAt x.proj)
      rw [← hbase]
      exact C.mem_baseSet_indexAt x.proj
    have hne : e x ≠ e y := fun h => hxy (e.toOpenPartialHomeomorph.injOn hx hy h)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hne) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact C.continuous_projection.continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) C.continuous_projection.continuousAt

/-- A countable subcover is selected on the base, not on the arbitrary index
type. Each of its total-space charts is second countable. -/
theorem totalSpace_secondCountable : SecondCountableTopology C.toVectorBundleCore.TotalSpace := by
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  obtain ⟨J, hJ, hcover⟩ := isOpen_iUnion_countable C.baseSet C.isOpen_baseSet
  have hcover' : (⋃ i, C.baseSet i) = univ := by
    ext p
    simp only [mem_iUnion, mem_univ, iff_true]
    exact C.covers p
  letI : Countable J := hJ.to_subtype
  let U (j : J) := (C.toVectorBundleCore.localTriv j.val).source
  letI (j : J) : SecondCountableTopology (U j) :=
    (C.toVectorBundleCore.localTriv j.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U)
    (fun j => (C.toVectorBundleCore.localTriv j.val).open_source)
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  have hx : x.proj ∈ ⋃ i ∈ J, C.baseSet i := by rw [hcover, hcover']; trivial
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  exact ⟨⟨i, hi⟩, hxi⟩

end BundleData.SmoothCocycle


namespace BundleData
variable {n r : ℕ} {a k : ModelKind} {M : Type u} [TopologicalSpace M]
    {E : M → Type v} [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (C : ProductData.ProductCoordinates n a r .euclidean k)
    (e : Trivialization (Euclidean r) (TotalSpace.proj (F := Euclidean r) (E := E)))
    (c : ModelChart n a M)

@[simp] theorem mem_bundleChart_source (q : TotalSpace (Euclidean r) E) :
    q ∈ (bundleChart C e c).source ↔ q.proj ∈ e.baseSet ∧ q.proj ∈ c.source := by
  change (q ∈ e.source ∧ e q ∈ (ProductData.productChart C c (fiberChart r)).source) ↔ _
  rw [productChart_source]
  change (q ∈ e.source ∧ ((e q).1 ∈ c.source ∧ (e q).2 ∈ (fiberChart r).source)) ↔ _
  have hf : (fiberChart r).source = univ := rfl
  rw [hf]
  simp only [mem_univ, and_true]
  constructor
  · rintro ⟨hq, hc⟩
    exact ⟨e.mem_source.mp hq, e.coe_fst hq ▸ hc⟩
  · rintro ⟨hq, hc⟩
    exact ⟨e.mem_source.mpr hq, (e.coe_fst' hq).symm ▸ hc⟩

theorem bundleChart_val (q : TotalSpace (Euclidean r) E) (hq : q.proj ∈ e.baseSet) :
    ((bundleChart C e c) q).val = C.linearEquiv ((c q.proj).val, (e q).2) := by
  change C.linearEquiv ((c (e q).1).val, (e q).2) = _
  rw [e.coe_fst' hq]

end BundleData

namespace BundleData.SmoothVectorBundle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean r) F)]
  (B : BundleData.SmoothVectorBundle S r ι E)
  (D : BundleData.SmoothVectorBundle S r ι F)

/-- The linear coordinate map on a fiber of a specified trivialization. -/
noncomputable def fiberCoordinates (i : ι) (p : M) (hp : p ∈ B.baseSet i) :
    E p ≃ₗ[ℝ] Euclidean r := by
  letI := B.linear i
  exact (B.trivialization i).linearEquivAt ℝ p ((B.trivialization_baseSet i).symm ▸ hp)

@[simp] theorem fiberCoordinates_apply (i : ι) (p : M) (hp : p ∈ B.baseSet i) (v : E p) :
    B.fiberCoordinates i p hp v = ((B.trivialization i) ⟨p, v⟩).2 := rfl

@[simp] theorem fiberCoordinates_symm_apply (i : ι) (p : M) (hp : p ∈ B.baseSet i)
    (v : Euclidean r) :
    (B.fiberCoordinates i p hp).symm v = (B.trivialization i).symm p v := rfl

/-- Transitions act on the coordinates of every actual fiber vector. -/
theorem coordinates_transition {C : BundleData.SmoothCocycle S r ι} (hB : Realizes C B)
    (i j : ι) (p : M) (hi : p ∈ C.baseSet i) (hj : p ∈ C.baseSet j) (v : E p) :
    ((B.trivialization j) ⟨p, v⟩).2 =
      C.g i j p (((B.trivialization i) ⟨p, v⟩).2) := by
  have hiB : p ∈ B.baseSet i := (hB.1 i).symm ▸ hi
  have h := hB.2 i j p hi hj (B.fiberCoordinates i p hiB v)
  change ((B.trivialization j) ⟨p, (B.fiberCoordinates i p hiB).symm
    (B.fiberCoordinates i p hiB v)⟩).2 = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

/-- Two coordinate-preserving fiberwise equivalences are pointwise identical. -/
theorem preserving_ext (hbase : ∀ i, B.baseSet i = D.baseSet i)
    {f g : (p : M) → E p ≃ₗ[ℝ] F p}
    (hf : PreservesTrivializations B D f) (hg : PreservesTrivializations B D g) : f = g := by
  funext p
  apply LinearEquiv.ext
  intro v
  obtain ⟨i, hi⟩ := B.covers p
  have hiD : p ∈ D.baseSet i := hbase i ▸ hi
  apply (D.fiberCoordinates i p hiD).injective
  exact (hf i p hi v).trans (hg i p hi v).symm


/-- A map preserving the specified smooth trivializations is smooth. The two
realizations may choose different linear coordinates for the product model. -/
theorem smooth_of_preserves (hbase : ∀ i, B.baseSet i = D.baseSet i)
    {f : (p : M) → E p ≃ₗ[ℝ] F p} (hf : PreservesTrivializations B D f) :
    IsSmoothMap B.totalManifold D.totalManifold (fun q => ⟨q.proj, f q.proj q.snd⟩) := by
  let map : TotalSpace (Euclidean r) E → TotalSpace (Euclidean r) F :=
    fun q => ⟨q.proj, f q.proj q.snd⟩
  intro q
  obtain ⟨i, hi⟩ := B.covers q.proj
  have hiD : q.proj ∈ D.baseSet i := hbase i ▸ hi
  let e := B.trivialization i
  let d := D.trivialization i
  have hq : q ∈ e.source := e.mem_source.mpr ((B.trivialization_baseSet i).symm ▸ hi)
  have hev : ∀ᶠ q' : TotalSpace (Euclidean r) E in 𝓝 q,
      q'.proj ∈ B.baseSet i := by
    filter_upwards [e.open_source.mem_nhds hq] with q' hq'
    exact B.trivialization_baseSet i ▸ e.mem_source.mp hq' 
  have hdpre : map ⁻¹' d.source ∈ 𝓝 q := by
    filter_upwards [hev] with q' hq'
    exact d.mem_source.mpr ((D.trivialization_baseSet i).symm ▸ (hbase i ▸ hq'))
  have heq : d ∘ map =ᶠ[𝓝 q] e := by
    filter_upwards [hev] with q' hq'
    apply Prod.ext
    · exact (d.coe_fst' ((D.trivialization_baseSet i).symm ▸ (hbase i ▸ hq'))).trans
        (e.coe_fst' ((B.trivialization_baseSet i).symm ▸ hq')).symm
    · exact hf i q'.proj hq' q'.snd
  have hcont : ContinuousAt map q :=
    (d.toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hdpre).mpr
      ((e.toOpenPartialHomeomorph.continuousAt hq).congr_of_eventuallyEq heq)
  obtain ⟨c, hc, hqc⟩ := S.smoothStructure.property.1.1 q.proj
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    B.totalManifold.smoothStructure.property.1 D.totalManifold.smoothStructure.property.1
    map q).mpr
  refine ⟨hcont, bundleChart B.coordinates e c, B.chart_mem i c hc,
    bundleChart D.coordinates d c, D.chart_mem i c hc, ?_, ?_, ?_⟩
  · exact (mem_bundleChart_source _ _ _ _).mpr
      ⟨(B.trivialization_baseSet i).symm ▸ hi, hqc⟩
  · exact (mem_bundleChart_source _ _ _ _).mpr
      ⟨(D.trivialization_baseSet i).symm ▸ hiD, hqc⟩
  · let L := D.coordinates.linearEquiv.toContinuousLinearMap.comp
      B.coordinates.linearEquiv.symm.toContinuousLinearMap
    refine ⟨univ, isOpen_univ, mem_univ _, L, L.contDiff.contDiffOn, ?_⟩
    filter_upwards [hev] with q' hq'
    rw [bundleChart_val B.coordinates e c q' ((B.trivialization_baseSet i).symm ▸ hq'),
      bundleChart_val D.coordinates d c (map q')
        ((D.trivialization_baseSet i).symm ▸ (hbase i ▸ hq'))]
    change D.coordinates.linearEquiv
      (B.coordinates.linearEquiv.symm (B.coordinates.linearEquiv _)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg (fun v => D.coordinates.linearEquiv ((c q'.proj).val, v))
      (hf i q'.proj hq' q'.snd).symm

/-- The inverse of a coordinate-preserving equivalence preserves coordinates too. -/
theorem symm_preserves (hbase : ∀ i, B.baseSet i = D.baseSet i)
    {f : (p : M) → E p ≃ₗ[ℝ] F p} (hf : PreservesTrivializations B D f) :
    PreservesTrivializations D B (fun p => (f p).symm) := by
  intro i p hi v
  have hiB : p ∈ B.baseSet i := (hbase i).symm ▸ hi
  simpa only [LinearEquiv.apply_symm_apply] using
    (hf i p hiB ((f p).symm v)).symm

end BundleData.SmoothVectorBundle

namespace BundleData.SmoothCocycle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} (C : BundleData.SmoothCocycle S r ι)
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean r) F)]
  (B : BundleData.SmoothVectorBundle S r ι E)
  (D : BundleData.SmoothVectorBundle S r ι F)
  (hB : Realizes C B) (hD : Realizes C D)

/-- The only possible isomorphism: use identical coordinates in one common chart. -/
noncomputable def fiberIsomorphism (p : M) : E p ≃ₗ[ℝ] F p :=
  (B.fiberCoordinates (C.indexAt p) p ((hB.1 _).symm ▸ C.mem_baseSet_indexAt p)).trans
    (D.fiberCoordinates (C.indexAt p) p ((hD.1 _).symm ▸ C.mem_baseSet_indexAt p)).symm

theorem fiberIsomorphism_preserves :
    PreservesTrivializations B D (C.fiberIsomorphism B D hB hD) := by
  intro i p hi v
  have hiC : p ∈ C.baseSet i := hB.1 i ▸ hi
  have hk := C.mem_baseSet_indexAt p
  have hkD : p ∈ D.baseSet (C.indexAt p) := (hD.1 _).symm ▸ hk
  rw [D.coordinates_transition hD (C.indexAt p) i p hk hiC,
    B.coordinates_transition hB (C.indexAt p) i p hk hiC]
  congr 1
  change D.fiberCoordinates (C.indexAt p) p hkD
    (C.fiberIsomorphism B D hB hD p v) = _
  exact (D.fiberCoordinates (C.indexAt p) p hkD).apply_symm_apply _

end BundleData.SmoothCocycle



namespace BundleData.SmoothWithParameters
variable {n d : ℕ} {a b : ModelKind} {M : Type u} {Q : Type v}
  [TopologicalSpace M] [TopologicalSpace Q] {S : SmoothManifold n a M}
  {T : SmoothManifold d b Q} {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f g : M × V → Q} {U : Set M}

/-- Smoothness with vector parameters is local on the stated open base domain. -/
theorem congr (hU : IsOpen U) (hf : SmoothWithParameters S T f U)
    (heq : ∀ p : M × V, p.1 ∈ U → f p = g p) : SmoothWithParameters S T g U := by
  intro p hp
  have hloc : f =ᶠ[𝓝 p] g := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with q hq
    exact heq q hq
  obtain ⟨hcont, hcharts⟩ := hf p hp
  refine ⟨hcont.congr_of_eventuallyEq hloc.symm, ?_⟩
  intro c hc e he hpc hpe
  obtain ⟨W, hW, hpW, F, hF, hlocF⟩ :=
    hcharts c hc e he hpc (hloc.eq_of_nhds.symm ▸ hpe)
  exact ⟨W, hW, hpW, F, hF, hlocF.trans (hloc.fun_comp (fun q => (e q).val))⟩

end BundleData.SmoothWithParameters

namespace BundleData.SmoothCocycle
variable {n r : ℕ} {a k : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} (C : BundleData.SmoothCocycle S r ι)
  (P : ProductData.ProductCoordinates n a r .euclidean k)

theorem localTriv_apply_transition (i j : ι) (q : C.toVectorBundleCore.TotalSpace)
    (hi : q.proj ∈ C.baseSet i) (hj : q.proj ∈ C.baseSet j) :
    (C.toVectorBundleCore.localTriv j q).2 =
      C.g i j q.proj ((C.toVectorBundleCore.localTriv i q).2) := by
  have h := C.localTriv_transition i j q.proj hi hj
    ((C.toVectorBundleCore.localTriv i q).2)
  change (C.toVectorBundleCore.localTriv j
    ⟨q.proj, (C.toVectorBundleCore.localTriv i).symm q.proj
      ((C.toVectorBundleCore.localTriv i) ⟨q.proj, q.snd⟩).2⟩).2 = _ at h
  rw [Trivialization.symm_apply_apply_mk _ hi] at h
  exact h

/-- The actual local ambient extension of a total-space coordinate transition.
It has the form (x,v) ↦ (G(x), A(x)v), conjugated by P. -/
theorem bundleChart_transition (i j : ι) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (q : C.toVectorBundleCore.TotalSpace)
    (hq : q ∈ (bundleChart P (C.toVectorBundleCore.localTriv i) c).source)
    (hq' : q ∈ (bundleChart P (C.toVectorBundleCore.localTriv j) d).source) :
    ChartContDiffAt (⊤ : ℕ∞) (bundleChart P (C.toVectorBundleCore.localTriv i) c)
      (bundleChart P (C.toVectorBundleCore.localTriv j) d) id q := by
  obtain ⟨hi, hqc⟩ := (mem_bundleChart_source _ _ _ _).mp hq
  obtain ⟨hj, hqd⟩ := (mem_bundleChart_source _ _ _ _).mp hq'
  obtain ⟨U, hU, hUq, G, hG, heG⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hc d hd) hqc hqd
  obtain ⟨V, hV, hVq, A, hA, heA⟩ := (C.smooth i j q.proj ⟨hi, hj⟩).2 c hc hqc
  let W : Set (Euclidean (n + r)) :=
    (fun z => (P.linearEquiv.symm z).1) ⁻¹' (U ∩ V)
  have hfst : MapsTo (fun z => (P.linearEquiv.symm z).1) W U := fun _ hz => hz.1
  have hfst' : MapsTo (fun z => (P.linearEquiv.symm z).1) W V := fun _ hz => hz.2
  refine ⟨W, (hU.inter hV).preimage (continuous_fst.comp P.linearEquiv.symm.continuous), ?_,
    fun z => P.linearEquiv (G (P.linearEquiv.symm z).1,
      A (P.linearEquiv.symm z).1 (P.linearEquiv.symm z).2), ?_, ?_⟩
  · change (P.linearEquiv.symm
      ((bundleChart P (C.toVectorBundleCore.localTriv i) c) q).val).1 ∈ U ∩ V
    rw [bundleChart_val P _ c q hi, P.linearEquiv.symm_apply_apply]
    exact ⟨hUq, hVq⟩
  · apply P.linearEquiv.contDiff.contDiffOn.comp _ (mapsTo_univ _ _)
    exact (hG.comp P.linearEquiv.symm.contDiff.fst.contDiffOn hfst).prodMk
      ((hA.comp P.linearEquiv.symm.contDiff.fst.contDiffOn hfst').clm_apply
        P.linearEquiv.symm.contDiff.snd.contDiffOn)
  · have heG' := heG.comp_tendsto C.continuous_projection.continuousAt
    have heA' := heA.comp_tendsto C.continuous_projection.continuousAt
    filter_upwards [heG', heA',
      (C.toVectorBundleCore.localTriv i).open_source.mem_nhds hi,
      (C.toVectorBundleCore.localTriv j).open_source.mem_nhds hj] with q' hG' hA' hi' hj'
    change q'.proj ∈ C.baseSet i at hi'
    change q'.proj ∈ C.baseSet j at hj'
    simp only [id_eq]
    rw [bundleChart_val P (C.toVectorBundleCore.localTriv i) c q' hi',
      bundleChart_val P (C.toVectorBundleCore.localTriv j) d q' hj',
      P.linearEquiv.symm_apply_apply]
    change G (c q'.proj).val = (d q'.proj).val at hG'
    change A (c q'.proj).val = (C.g i j q'.proj).toContinuousLinearMap at hA'
    rw [hG', hA', C.localTriv_apply_transition i j q' hi' hj']
    rfl

/-- All combinations of a given bundle trivialization and a smooth base chart. -/
def totalAtlas : Set (ModelChart (n + r) k C.toVectorBundleCore.TotalSpace) :=
  {e | ∃ i c, c ∈ S.smoothStructure.val ∧
    e = bundleChart P (C.toVectorBundleCore.localTriv i) c}

theorem totalAtlas_isContDiffAtlas : IsContDiffAtlas (⊤ : ℕ∞) (C.totalAtlas P) := by
  constructor
  · intro q
    obtain ⟨i, hi⟩ := C.covers q.proj
    obtain ⟨c, hc, hqc⟩ := S.smoothStructure.property.1.1 q.proj
    exact ⟨_, ⟨i, c, hc, rfl⟩, (mem_bundleChart_source _ _ _ _).mpr ⟨hi, hqc⟩⟩
  · rintro _ ⟨i, c, hc, rfl⟩ _ ⟨j, d, hd, rfl⟩
    exact contDiffCompatible_of_germs (C.bundleChart_transition P i j c d hc hd)
      (C.bundleChart_transition P j i d c hd hc)

/-- The maximal smooth structure generated by the specified bundle charts.
Hausdorffness and second countability were established independently above. -/
noncomputable def totalSmoothManifold : SmoothManifold (n + r) k C.toVectorBundleCore.TotalSpace where
  topologicalManifold := ⟨C.totalSpace_t2Space, C.totalSpace_secondCountable,
    C.totalAtlas P, (C.totalAtlas_isContDiffAtlas P).1⟩
  smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) (C.totalAtlas P),
    maximalExtension_isMaximal (C.totalAtlas_isContDiffAtlas P)⟩

theorem totalChart_mem (i : ι) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    bundleChart P (C.toVectorBundleCore.localTriv i) c ∈
      (C.totalSmoothManifold P).smoothStructure.val :=
  subset_maximalExtension (C.totalAtlas_isContDiffAtlas P) ⟨i, c, hc, rfl⟩


/-- The projection is the first block in every total-space chart. -/
theorem projection_smooth : IsSmoothMap (C.totalSmoothManifold P) S C.toVectorBundleCore.proj := by
  intro q
  obtain ⟨i, hi⟩ := C.covers q.proj
  obtain ⟨c, hc, hqc⟩ := S.smoothStructure.property.1.1 q.proj
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    (C.totalSmoothManifold P).smoothStructure.property.1 S.smoothStructure.property.1
    C.toVectorBundleCore.proj q).mpr
  refine ⟨C.continuous_projection.continuousAt,
    bundleChart P (C.toVectorBundleCore.localTriv i) c, C.totalChart_mem P i c hc,
    c, hc, (mem_bundleChart_source _ _ _ _).mpr ⟨hi, hqc⟩, hqc,
    univ, isOpen_univ, mem_univ _, fun z => (P.linearEquiv.symm z).1,
    P.linearEquiv.symm.contDiff.fst.contDiffOn, ?_⟩
  filter_upwards [(C.toVectorBundleCore.localTriv i).open_source.mem_nhds hi] with q' hq'
  change q'.proj ∈ C.baseSet i at hq'
  rw [bundleChart_val P (C.toVectorBundleCore.localTriv i) c q' hq',
    P.linearEquiv.symm_apply_apply]

/-- Zero is represented by (x,0), also at a boundary point. -/
theorem zero_smooth : IsSmoothMap S (C.totalSmoothManifold P)
    (fun p => (⟨p, 0⟩ : C.toVectorBundleCore.TotalSpace)) := by
  intro p
  obtain ⟨i, hi⟩ := C.covers p
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 (C.totalSmoothManifold P).smoothStructure.property.1
    (fun p => (⟨p, 0⟩ : C.toVectorBundleCore.TotalSpace)) p).mpr
  refine ⟨(Trivialization.continuous_zeroSection ℝ (F := Euclidean r) (E := C.toVectorBundleCore.Fiber)).continuousAt,
    c, hc, bundleChart P (C.toVectorBundleCore.localTriv i) c, C.totalChart_mem P i c hc,
    hpc, (mem_bundleChart_source _ _ _ _).mpr ⟨hi, hpc⟩,
    univ, isOpen_univ, mem_univ _, fun z => P.linearEquiv (z, 0),
    (P.linearEquiv.contDiff.comp (contDiff_id.prodMk contDiff_const)).contDiffOn, ?_⟩
  filter_upwards [(C.isOpen_baseSet i).mem_nhds hi] with p' hp'
  rw [bundleChart_val P (C.toVectorBundleCore.localTriv i) c ⟨p', 0⟩ hp']
  change P.linearEquiv ((c p').val, 0) =
    P.linearEquiv ((c p').val, C.g (C.indexAt p') i p' 0)
  rw [map_zero]

/-- Every smooth fiber-coordinate formula gives a smooth local parametrization
of the total space. The proof composes ambient extensions of actual chart changes. -/
theorem inverseTrivialization_smoothWithParameters {V : Type w}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (i : ι) (h : V → Euclidean r)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    SmoothWithParameters S (C.totalSmoothManifold P)
      (fun q : M × V => (⟨q.1, (C.toVectorBundleCore.localTriv i).symm q.1 (h q.2)⟩ :
        C.toVectorBundleCore.TotalSpace)) (C.baseSet i) := by
  let e := C.toVectorBundleCore.localTriv i
  let f : M × V → C.toVectorBundleCore.TotalSpace :=
    fun q => ⟨q.1, e.symm q.1 (h q.2)⟩
  intro q hq
  have htarget : (q.1, h q.2) ∈ e.target := ⟨hq, mem_univ _⟩
  have hev : ∀ᶠ q' : M × V in 𝓝 q, q'.1 ∈ C.baseSet i :=
    continuous_fst.continuousAt.preimage_mem_nhds ((C.isOpen_baseSet i).mem_nhds hq)
  have hcont : ContinuousAt f q := by
    have hhparam : ContinuousAt (fun q : M × V => (q.1, h q.2)) q :=
      continuous_fst.continuousAt.prodMk (hh.continuous.continuousAt.comp
        continuous_snd.continuousAt)
    have hs : ContinuousAt e.toOpenPartialHomeomorph.symm (q.1, h q.2) :=
      e.toOpenPartialHomeomorph.continuousAt_symm htarget
    apply (hs.comp (f := fun q : M × V => (q.1, h q.2)) (x := q) hhparam).congr_of_eventuallyEq
    filter_upwards [hev] with q' hq'
    exact e.mk_symm hq' (h q'.2)
  refine ⟨hcont, ?_⟩
  intro c hc d hd hqc hqfd
  have hqfc : f q ∈ (bundleChart P e c).source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨hq, hqc⟩
  have hcoord := chartContDiffAt_of_compatible
    ((C.totalSmoothManifold P).smoothStructure.property.1.2
      _ (C.totalChart_mem P i c hc) d hd) hqfc hqfd
  obtain ⟨U, hU, hUq, G, hG, heG⟩ :=
    LocalCoordinateExtension.precomp hcoord hcont rfl
  let H : Euclidean n × V → Euclidean (n + r) := fun z => P.linearEquiv (z.1, h z.2)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    P.linearEquiv.contDiff.comp (contDiff_fst.prodMk (hh.comp contDiff_snd))
  have formula : ∀ q' : M × V, q'.1 ∈ C.baseSet i →
      H ((c q'.1).val, q'.2) = ((bundleChart P e c) (f q')).val := by
    intro q' hq'
    rw [bundleChart_val P e c (f q') hq']
    change P.linearEquiv ((c q'.1).val, h q'.2) =
      P.linearEquiv ((c q'.1).val, (e ⟨q'.1, e.symm q'.1 (h q'.2)⟩).2)
    rw [e.apply_mk_symm hq']
  refine ⟨H ⁻¹' U, hU.preimage hH.continuous, ?_, G ∘ H,
    hG.comp hH.contDiffOn (fun _ hz => hz), ?_⟩
  · change H ((c q.1).val, q.2) ∈ U
    rw [formula q hq]
    exact hUq
  · filter_upwards [heG, hev] with q' hG' hq'
    change G (H ((c q'.1).val, q'.2)) = (d (f q')).val
    rw [formula q' hq']
    exact hG'


/-- Addition is the smooth formula (x,v,w) ↦ (x,v+w) in each trivialization. -/
theorem add_smooth (i : ι) : SmoothWithParameters S (C.totalSmoothManifold P)
    (fun q : M × (Euclidean r × Euclidean r) =>
      (⟨q.1, (C.toVectorBundleCore.localTriv i).symm q.1 q.2.1 +
        (C.toVectorBundleCore.localTriv i).symm q.1 q.2.2⟩ : C.toVectorBundleCore.TotalSpace))
    (C.baseSet i) := by
  apply SmoothWithParameters.congr (C.isOpen_baseSet i)
    (C.inverseTrivialization_smoothWithParameters P i (fun v => v.1 + v.2)
      (contDiff_fst.add contDiff_snd))
  intro q hq
  apply congrArg (TotalSpace.mk (F := Euclidean r) q.1)
  simpa only [Trivialization.symmₗ_apply (C.toVectorBundleCore.localTriv i) (R := ℝ) hq] using
    ((C.toVectorBundleCore.localTriv i).symmₗ ℝ q.1).map_add q.2.1 q.2.2

/-- Scalar multiplication has the smooth coordinate formula (x,t,v) ↦ (x,tv). -/
theorem smul_smooth (i : ι) : SmoothWithParameters S (C.totalSmoothManifold P)
    (fun q : M × (ℝ × Euclidean r) =>
      (⟨q.1, q.2.1 • (C.toVectorBundleCore.localTriv i).symm q.1 q.2.2⟩ :
        C.toVectorBundleCore.TotalSpace)) (C.baseSet i) := by
  apply SmoothWithParameters.congr (C.isOpen_baseSet i)
    (C.inverseTrivialization_smoothWithParameters P i (fun v => v.1 • v.2)
      (contDiff_fst.smul contDiff_snd))
  intro q hq
  apply congrArg (TotalSpace.mk (F := Euclidean r) q.1)
  simpa only [Trivialization.symmₗ_apply (C.toVectorBundleCore.localTriv i) (R := ℝ) hq] using
    ((C.toVectorBundleCore.localTriv i).symmₗ ℝ q.1).map_smul q.2.1 q.2.2

end BundleData.SmoothCocycle

namespace BundleData.SmoothCocycle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} (C : BundleData.SmoothCocycle S r ι)
  (P : ProductData.ProductCoordinates n a r .euclidean
    (ProductData.productKind n a r .euclidean))

/-- The bundle assembled from C, with all its original trivializations. -/
noncomputable def gluedBundle : GluedBundle C where
  Fiber := C.toVectorBundleCore.Fiber
  addCommGroup p := inferInstance
  module p := inferInstance
  topology := inferInstanceAs (TopologicalSpace C.toVectorBundleCore.TotalSpace)
  bundle := {
    baseSet := C.baseSet
    covers := C.covers
    trivialization := C.toVectorBundleCore.localTriv
    trivialization_baseSet := fun _ => rfl
    linear := fun _ => inferInstance
    coordinates := P
    totalManifold := C.totalSmoothManifold P
    chart_mem := C.totalChart_mem P
    projection_smooth := C.projection_smooth P
    zero_smooth := C.zero_smooth P
    add_smooth := C.add_smooth P
    smul_smooth := C.smul_smooth P }
  realizes := ⟨fun _ => rfl, C.localTriv_transition⟩

end BundleData.SmoothCocycle

/-- M05.01 existence for every open-cover cocycle, with no countability,
nonemptiness, positive-rank or boundarylessness restriction. -/
theorem exists_gluedBundle :
    Specs.SmoothManifolds.Ch05.BundleGluing.exists_gluedBundleType.{u, v} := by
  intro n r a M inst S ι C
  obtain ⟨P⟩ := exists_productCoordinates (n := n) (m := r) (a := a) (b := .euclidean)
    (Or.inr (Or.inl rfl))
  exact ⟨C.gluedBundle P⟩




namespace BundleData.OverlapCocycle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} (C : OverlapCocycle S r ι)

/-- Identity junk values totalize the overlap functions, with no regularity
condition imposed outside their actual overlap. -/
noncomputable def totalTransition (i j : ι) (p : M) : Euclidean r ≃L[ℝ] Euclidean r := by
  classical
  exact if hp : p ∈ C.baseSet i ∩ C.baseSet j then C.g i j ⟨p, hp⟩
    else ContinuousLinearEquiv.refl ℝ _

theorem totalTransition_eq (i j : ι) (p : M) (hi : p ∈ C.baseSet i) (hj : p ∈ C.baseSet j) :
    C.totalTransition i j p = C.g i j ⟨p, hi, hj⟩ := by
  simp only [totalTransition, dite_eq_left (show p ∈ C.baseSet i ∩ C.baseSet j from ⟨hi, hj⟩)]

theorem totalTransition_smooth (i j : ι) :
    SmoothOnBase S (fun p => (C.totalTransition i j p).toContinuousLinearMap)
      (C.baseSet i ∩ C.baseSet j) := by
  intro p hp
  let x : ↥(C.baseSet i ∩ C.baseSet j) := ⟨p, hp⟩
  have hnhds := ((C.isOpen_baseSet i).inter (C.isOpen_baseSet j)).isOpenEmbedding_subtypeVal.map_nhds_eq x
  have heq : (fun q : ↥(C.baseSet i ∩ C.baseSet j) =>
      (C.totalTransition i j q.val).toContinuousLinearMap) =
        (fun q => (C.g i j q).toContinuousLinearMap) := by
    funext q
    rw [C.totalTransition_eq i j q.val q.property.1 q.property.2]
  constructor
  · change Tendsto (fun p => (C.totalTransition i j p).toContinuousLinearMap)
      (𝓝 p) (𝓝 (C.totalTransition i j p).toContinuousLinearMap)
    rw [← hnhds, tendsto_map'_iff]
    change Tendsto (fun q : ↥(C.baseSet i ∩ C.baseSet j) =>
      (C.totalTransition i j q.val).toContinuousLinearMap) _ _
    rw [heq, C.totalTransition_eq i j p hp.1 hp.2]
    exact (C.smooth i j x).1
  · intro c hc hpc
    obtain ⟨W, hW, hpW, F, hF, hloc⟩ := (C.smooth i j x).2 c hc hpc
    refine ⟨W, hW, hpW, F, hF, ?_⟩
    rw [← hnhds]
    change (fun q : ↥(C.baseSet i ∩ C.baseSet j) => F (c q.val).val) =ᶠ[𝓝 x]
      (fun q => (C.totalTransition i j q.val).toContinuousLinearMap)
    rw [heq]
    exact hloc

/-- Totalization is proved from the original overlap hypotheses, rather than
added as a hypothesis to the gluing theorem. -/
noncomputable def totalize : BundleData.SmoothCocycle S r ι where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  covers := C.covers
  g := C.totalTransition
  self i p hp := by rw [C.totalTransition_eq i i p hp hp]; exact C.self i p hp
  comp i j k p hi hj hk := by
    rw [C.totalTransition_eq j k p hj hk, C.totalTransition_eq i j p hi hj,
      C.totalTransition_eq i k p hi hk]
    exact C.comp i j k p hi hj hk
  smooth := C.totalTransition_smooth


/-- Totalization changes no realization condition on the actual overlaps. -/
theorem realizes_totalize_iff {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)] (B : BundleData.SmoothVectorBundle S r ι E) :
    Realizes C.totalize B ↔ RealizesOverlap C B := by
  constructor
  · rintro ⟨hbase, htr⟩
    refine ⟨hbase, ?_⟩
    intro i j p hi hj v
    have h := htr i j p hi hj v
    change _ = C.totalTransition i j p v at h
    rw [C.totalTransition_eq i j p hi hj] at h
    exact h
  · rintro ⟨hbase, htr⟩
    refine ⟨hbase, ?_⟩
    intro i j p hi hj v
    change _ = C.totalTransition i j p v
    rw [C.totalTransition_eq i j p hi hj]
    exact htr i j p hi hj v

end BundleData.OverlapCocycle

/-- The same construction accepts transition functions with only their original
source-overlap domains; the totalization agrees exactly on every overlap. -/
theorem exists_gluedBundle_fromOverlap :
    Specs.SmoothManifolds.Ch05.BundleGluing.exists_gluedBundle_fromOverlapType.{u, v} := by
  intro n r a M inst S ι C
  exact ⟨C.totalize, (fun _ => rfl), C.totalTransition_eq, exists_gluedBundle C.totalize⟩

/-- M05.01 uniqueness, for arbitrary realizations with the given transitions. -/
theorem exists_unique_bundleIsomorphism :
    Specs.SmoothManifolds.Ch05.BundleGluing.exists_unique_bundleIsomorphismType.{u, v, w, z} := by
  intro n r a M inst S ι C E F agE mE agF mF tE tF B D hB hD
  have hbase : ∀ i, B.baseSet i = D.baseSet i := fun i => (hB.1 i).trans (hD.1 i).symm
  let f := C.fiberIsomorphism B D hB hD
  have hf : PreservesTrivializations B D f := C.fiberIsomorphism_preserves B D hB hD
  refine ⟨f, ⟨B.smooth_of_preserves D hbase hf,
    D.smooth_of_preserves B (fun i => (hbase i).symm) (B.symm_preserves D hbase hf), hf⟩, ?_⟩
  intro g hg
  exact B.preserving_ext D hbase hg.2.2 hf


/-- The source's uniqueness theorem also starts from overlap-only transitions. -/
theorem exists_unique_bundleIsomorphism_fromOverlap :
    Specs.SmoothManifolds.Ch05.BundleGluing.exists_unique_bundleIsomorphism_fromOverlapType.{u, v, w, z} := by
  intro n r a M inst S ι C E F agE mE agF mF tE tF B D hB hD
  exact exists_unique_bundleIsomorphism C.totalize B D
    ((C.realizes_totalize_iff B).mpr hB) ((C.realizes_totalize_iff D).mpr hD)

end SmoothManifolds
