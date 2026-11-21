import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleGluing
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames

namespace SmoothManifolds
open ModelData AtlasData MapData ProductData BundleData FrameData Bundle Module Set Filter
open scoped Topology
universe u v w z

namespace FrameData.VectorSmoothAt
variable {n : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
  {A : Set (ModelChart n a X)} {V : Type v} {W : Type w} {Z : Type z}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {f : X → V} {g : X → W} {x : X}

theorem congr (hf : VectorSmoothAt A f x) {g : X → V}
    (h : f =ᶠ[𝓝 x] g) : VectorSmoothAt A g x := by
  refine ⟨hf.1.congr_of_eventuallyEq h.symm, ?_⟩
  intro c hc hx
  obtain ⟨U, hU, hxU, F, hF, he⟩ := hf.2 c hc hx
  exact ⟨U, hU, hxU, F, hF, he.trans h⟩

theorem const (A : Set (ModelChart n a X)) (v : V) (x : X) :
    VectorSmoothAt A (fun _ => v) x :=
  ⟨continuousAt_const, fun _ _ _ =>
    ⟨univ, isOpen_univ, mem_univ _, fun _ => v, contDiffOn_const, Filter.EventuallyEq.rfl⟩⟩

theorem postcompOn (hf : VectorSmoothAt A f x) {h : V → W} {s : Set V}
    (hs : IsOpen s) (hx : f x ∈ s) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h s) :
    VectorSmoothAt A (fun y => h (f y)) x := by
  refine ⟨(hh.continuousOn.continuousAt (hs.mem_nhds hx)).comp hf.1, ?_⟩
  intro c hc hxc
  obtain ⟨U, hU, hxU, F, hF, he⟩ := hf.2 c hc hxc
  refine ⟨U ∩ F ⁻¹' s, hF.continuousOn.isOpen_inter_preimage hU hs,
    ⟨hxU, ?_⟩, h ∘ F, hh.comp (hF.mono inter_subset_left) (fun _ hz => hz.2), ?_⟩
  · change F (c x).val ∈ s
    rw [he.eq_of_nhds]
    exact hx
  · exact he.fun_comp h

theorem postcomp (hf : VectorSmoothAt A f x) {h : V → W}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) : VectorSmoothAt A (fun y => h (f y)) x :=
  hf.postcompOn isOpen_univ (mem_univ _) hh.contDiffOn

theorem prod (hf : VectorSmoothAt A f x) (hg : VectorSmoothAt A g x) :
    VectorSmoothAt A (fun y => (f y, g y)) x := by
  refine ⟨hf.1.prodMk hg.1, ?_⟩
  intro c hc hx
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := hf.2 c hc hx
  obtain ⟨T, hT, hxT, G, hG, heG⟩ := hg.2 c hc hx
  refine ⟨U ∩ T, hU.inter hT, ⟨hxU, hxT⟩, fun z => (F z, G z),
    (hF.mono inter_subset_left).prodMk (hG.mono inter_subset_right), ?_⟩
  filter_upwards [heF, heG] with y hy hy'
  exact Prod.ext hy hy'

theorem pi {κ : Type*} [Fintype κ] {f : X → κ → V}
    (hf : ∀ j, VectorSmoothAt A (fun y => f y j) x) : VectorSmoothAt A f x := by
  classical
  refine ⟨continuousAt_pi.mpr (fun j => (hf j).1), ?_⟩
  intro c hc hx
  choose U hU hxU F hF he using fun j => (hf j).2 c hc hx
  refine ⟨⋂ j, U j, isOpen_iInter_of_finite hU, mem_iInter.mpr hxU,
    fun z j => F j z, contDiffOn_pi.mpr (fun j => (hF j).mono (iInter_subset _ j)), ?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with y hy
  exact funext hy

theorem clm_apply {f : X → V →L[ℝ] W} {g : X → V}
    (hf : VectorSmoothAt A f x) (hg : VectorSmoothAt A g x) :
    VectorSmoothAt A (fun y => f y (g y)) x :=
  (hf.prod hg).postcomp (contDiff_fst.clm_apply contDiff_snd)

theorem sum {κ : Type*} [Fintype κ] {f : κ → X → V}
    (hf : ∀ j, VectorSmoothAt A (f j) x) :
    VectorSmoothAt A (fun y => ∑ j, f j y) x := by
  exact (pi hf).postcomp (ContDiff.sum (fun j _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => V) j).contDiff))

/-- Inversion is used only on the open set of invertible operators. -/
theorem inverse [CompleteSpace V] {f : X → V →L[ℝ] W}
    (hf : VectorSmoothAt A f x) (hinv : (f x).IsInvertible) :
    VectorSmoothAt A (fun y => ContinuousLinearMap.inverse (f y)) x := by
  apply hf.postcompOn ContinuousLinearMap.isOpen_setOfPred_isInvertible hinv
  intro L hL
  exact hL.contDiffAt_map_inverse.contDiffWithinAt

/-- Vector-valued functions compose with chart-smooth maps. -/
theorem comp {m : ℕ} {b : ModelKind} {Y : Type w} [TopologicalSpace Y]
    {C : Set (ModelChart m b Y)} {g : X → Y} {f : Y → V}
    (hC : IsAtlas C) (hf : VectorSmoothAt C f (g x))
    (hg : ManifoldSmoothAt A C g x) : VectorSmoothAt A (fun y => f (g y)) x := by
  refine ⟨hf.1.comp hg.1, ?_⟩
  intro c hc hx
  obtain ⟨d, hd, hgd⟩ := hC (g x)
  obtain ⟨U, hU, hxU, G, hG, heG⟩ := hg.2 c hc d hd hx hgd
  obtain ⟨T, hT, hxT, F, hF, heF⟩ := hf.2 d hd hgd
  refine ⟨U ∩ G ⁻¹' T, hG.continuousOn.isOpen_inter_preimage hU hT,
    ⟨hxU, ?_⟩, F ∘ G, hF.comp (hG.mono inter_subset_left) (fun _ hy => hy.2), ?_⟩
  · change G (c x).val ∈ T
    rw [heG.eq_of_nhds]
    exact hxT
  · exact (heG.fun_comp F).trans (heF.comp_tendsto hg.1)

end FrameData.VectorSmoothAt

namespace FrameData
/-- Extend by zero only to supply total functions; assertions are local in U. -/
noncomputable def totalize {X : Type u} {V : Type v} [Zero V]
    {U : Set X} (f : U → V) (x : X) : V := by
  classical
  exact if h : x ∈ U then f ⟨x, h⟩ else 0

@[simp] theorem totalize_of_mem {X : Type u} {V : Type v} [Zero V]
    {U : Set X} (f : U → V) (x : X) (hx : x ∈ U) : FrameData.totalize f x = f ⟨x, hx⟩ := by
  unfold totalize
  rw [dite_eq_left hx]

/-- Reflection through the open-subspace inclusion preserves the full extension
convention, rather than merely derivatives within the subspace. -/
theorem VectorSmoothAt.totalize {n : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set (ModelChart n a X)} {U : Set X} (hU : IsOpen U)
    {f : U → V} {p : U} (hf : VectorSmoothAt (openSubsetAtlas A U hU) f p) :
    VectorSmoothAt A (FrameData.totalize f) p.val := by
  refine ⟨hU.isOpenEmbedding_subtypeVal.continuousAt_iff.mp ?_, ?_⟩
  · simpa only [Function.comp_def, totalize_of_mem f _ (Subtype.property _)] using hf.1
  · intro c hc hp
    let d := c.subtypeRestr (s := ⟨U, hU⟩) ⟨p⟩
    obtain ⟨W, hW, hpW, F, hF, heF⟩ := hf.2 d ⟨⟨p⟩, c, hc, rfl⟩ (by simpa [d] using hp)
    refine ⟨W, hW, hpW, F, hF, ?_⟩
    rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq p]
    change ∀ᶠ y : U in 𝓝 p, F (c y.val).val = FrameData.totalize f y.val
    change (fun y : U => F (c y.val).val) =ᶠ[𝓝 p] f at heF
    filter_upwards [heF] with y hy
    rw [totalize_of_mem f y.val y.property]
    exact hy
end FrameData


namespace Frames
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : BundleData.SmoothVectorBundle S r ι E) (U : Set M) (hU : IsOpen U)
  (b : BundleData.LocalFrame B U hU)

/-- The coefficients are unique, without any regularity assumption on s. -/
theorem section_expansion (s : (p : U) → E p.val) (p : U) :
    s p = ∑ j : Fin r, coefficients b s p j • b.section_ j p := by
  simp only [coefficients, ← b.basis_eq]
  exact ((b.basis p).sum_equivFun (s p)).symm

theorem frameLinearEquiv_apply (p : U) (v : Euclidean r) :
    frameLinearEquiv b p v = ∑ j : Fin r, v j • b.section_ j p := by
  simp only [frameLinearEquiv, Basis.equivFun_symm_apply, b.basis_eq]

theorem frameSynthesis_of_mem (q : M × Euclidean r) (hq : q.1 ∈ U) :
    frameSynthesis b q = ⟨q.1, frameLinearEquiv b ⟨q.1, hq⟩ q.2⟩ := by
  unfold frameSynthesis
  rw [dite_eq_left hq]

theorem frameAnalysis_of_mem (q : TotalSpace (Euclidean r) E) (hq : q.proj ∈ U) :
    frameAnalysis b q = (q.proj, (frameLinearEquiv b ⟨q.proj, hq⟩).symm q.snd) := by
  unfold frameAnalysis
  rw [dite_eq_left hq]

theorem analysis_synthesis (q : M × Euclidean r) (hq : q.1 ∈ U) :
    frameAnalysis b (frameSynthesis b q) = q := by
  rw [frameSynthesis_of_mem B U hU b q hq]
  rw [frameAnalysis_of_mem B U hU b _ hq]
  change (q.1, (frameLinearEquiv b ⟨q.1, hq⟩).symm (frameLinearEquiv b ⟨q.1, hq⟩ q.2)) = q
  rw [LinearEquiv.symm_apply_apply]

theorem synthesis_analysis (q : TotalSpace (Euclidean r) E) (hq : q.proj ∈ U) :
    frameSynthesis b (frameAnalysis b q) = q := by
  rw [frameAnalysis_of_mem B U hU b q hq]
  rw [frameSynthesis_of_mem B U hU b _ hq]
  change (⟨q.proj, frameLinearEquiv b ⟨q.proj, hq⟩
    ((frameLinearEquiv b ⟨q.proj, hq⟩).symm q.snd)⟩ : TotalSpace (Euclidean r) E) = q
  rw [LinearEquiv.apply_symm_apply]


/-- Coordinates of a section in any original bundle trivialization. -/
def sectionCoordinates (i : ι) (s : (p : U) → E p.val) (p : U) : Euclidean r :=
  ((B.trivialization i) (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E)).2

theorem sectionCoordinates_smoothAt (i : ι) (s : (p : U) → E p.val) (p : U)
    (hi : p.val ∈ B.baseSet i)
    (hs : ManifoldSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E)) p) :
    VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
      (sectionCoordinates B U i s) p := by
  let e := B.trivialization i
  have hi' : p.val ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hi
  have hev : ∀ᶠ y : U in 𝓝 p, y.val ∈ e.baseSet :=
    continuousAt_subtype_val.preimage_mem_nhds (e.open_baseSet.mem_nhds hi')
  refine ⟨((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr hi')).comp hs.1).snd, ?_⟩
  rintro _ ⟨hne, c, hc, rfl⟩ hp
  have hpc : p.val ∈ c.source := by simpa using hp
  have htarget : (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E) ∈
      (bundleChart B.coordinates e c).source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨hi', hpc⟩
  obtain ⟨W, hW, hpW, F, hF, heF⟩ := hs.2 _ ⟨hne, c, hc, rfl⟩ _
    (B.chart_mem i c hc) hp htarget
  refine ⟨W, hW, hpW, fun z => (B.coordinates.linearEquiv.symm (F z)).2,
    (B.coordinates.linearEquiv.symm.contDiff.snd.contDiffOn.comp hF (mapsTo_univ _ _)), ?_⟩
  filter_upwards [heF, hev] with y hy hyi
  change (B.coordinates.linearEquiv.symm (F (c y.val).val)).2 = _
  change F (c y.val).val = ((bundleChart B.coordinates e c) ⟨y.val, s y⟩).val at hy
  rw [hy, bundleChart_val B.coordinates e c _ hyi, B.coordinates.linearEquiv.symm_apply_apply]
  rfl

theorem smoothAt_of_sectionCoordinates (i : ι) (s : (p : U) → E p.val) (p : U)
    (hi : p.val ∈ B.baseSet i)
    (hs : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
      (sectionCoordinates B U i s) p) :
    ManifoldSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E)) p := by
  let e := B.trivialization i
  let f : U → TotalSpace (Euclidean r) E := fun p => ⟨p.val, s p⟩
  have hi' : p.val ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hi
  have hev : ∀ᶠ y : U in 𝓝 p, y.val ∈ e.baseSet :=
    continuousAt_subtype_val.preimage_mem_nhds (e.open_baseSet.mem_nhds hi')
  have hcont : ContinuousAt f p := by
    have hpair : ContinuousAt (fun y : U => (y.val, sectionCoordinates B U i s y)) p :=
      continuousAt_subtype_val.prodMk hs.1
    have ht : (p.val, sectionCoordinates B U i s p) ∈ e.target := e.mem_target.mpr hi'
    have hecont : ContinuousAt e.toOpenPartialHomeomorph.symm
        (p.val, sectionCoordinates B U i s p) :=
      e.toOpenPartialHomeomorph.continuousAt_symm ht
    have hh := hecont.comp (f := fun y : U => (y.val, sectionCoordinates B U i s y))
      (x := p) hpair
    apply hh.congr_of_eventuallyEq
    filter_upwards [hev] with y hy
    have heq : (y.val, sectionCoordinates B U i s y) = e (f y) := by
      apply Prod.ext
      · exact (e.coe_fst' (x := f y) hy).symm
      · rfl
    symm
    change e.toOpenPartialHomeomorph.symm (y.val, sectionCoordinates B U i s y) = f y
    rw [heq]
    exact e.toOpenPartialHomeomorph.left_inv (e.mem_source.mpr hy)
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := ⟨U, hU⟩) ⟨p⟩
  have hd : d ∈ openSubsetAtlas S.smoothStructure.val U hU := ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by simpa [d] using hpc
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    (openSubsetAtlas_isContDiffAtlas _ _ S.smoothStructure.property.1 U hU)
    B.totalManifold.smoothStructure.property.1 f p).mpr
  refine ⟨hcont, d, hd, bundleChart B.coordinates e c, B.chart_mem i c hc, hpd,
    (mem_bundleChart_source _ _ _ _).mpr ⟨hi', hpc⟩, ?_⟩
  obtain ⟨W, hW, hpW, F, hF, heF⟩ := hs.2 d hd hpd
  refine ⟨W, hW, hpW, fun z => B.coordinates.linearEquiv (z, F z),
    B.coordinates.linearEquiv.contDiff.contDiffOn.comp
      (contDiffOn_id.prodMk hF) (mapsTo_univ _ _), ?_⟩
  filter_upwards [heF, hev] with y hy hyi
  change B.coordinates.linearEquiv ((c y.val).val, F (c y.val).val) = _
  rw [bundleChart_val B.coordinates e c (f y) hyi]
  exact congrArg (fun v => B.coordinates.linearEquiv ((c y.val).val, v)) hy

/-- The columns of the frame in an existing bundle trivialization. -/
noncomputable def frameMatrix (i : ι) (p : U) : Euclidean r →L[ℝ] Euclidean r :=
  ∑ j : Fin r, (ContinuousLinearMap.proj j).smulRight
    (sectionCoordinates B U i (b.section_ j) p)

theorem frameMatrix_smoothAt (i : ι) (p : U) (hi : p.val ∈ B.baseSet i) :
    VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U hU) (frameMatrix B U hU b i) p := by
  apply FrameData.VectorSmoothAt.sum
  intro j
  exact (sectionCoordinates_smoothAt B U hU i (b.section_ j) p hi (b.smooth j p)).postcomp
    (contDiff_const.smulRight contDiff_id)

theorem frameMatrix_eq (i : ι) (p : U) (hi : p.val ∈ B.baseSet i) :
    frameMatrix B U hU b i p =
      ((frameLinearEquiv b p).trans (B.fiberCoordinates i p.val hi)).toContinuousLinearEquiv := by
  apply ContinuousLinearMap.ext
  intro v
  change (∑ j : Fin r, (ContinuousLinearMap.proj j).smulRight
    (sectionCoordinates B U i (b.section_ j) p)) v =
      B.fiberCoordinates i p.val hi (frameLinearEquiv b p v)
  rw [frameLinearEquiv_apply B U hU b]
  simp only [map_sum, map_smul, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    sectionCoordinates, BundleData.SmoothVectorBundle.fiberCoordinates_apply]

theorem frameMatrix_invertible (i : ι) (p : U) (hi : p.val ∈ B.baseSet i) :
    (frameMatrix B U hU b i p).IsInvertible := by
  rw [frameMatrix_eq B U hU b i p hi]
  exact ContinuousLinearMap.isInvertible_equiv

theorem frameMatrix_coefficients (i : ι) (s : (p : U) → E p.val) (p : U)
    (hi : p.val ∈ B.baseSet i) :
    frameMatrix B U hU b i p (coefficients b s p) = sectionCoordinates B U i s p := by
  rw [frameMatrix_eq B U hU b i p hi]
  change B.fiberCoordinates i p.val hi
    ((b.basis p).equivFun.symm ((b.basis p).equivFun (s p))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem inverse_frameMatrix_coordinates (i : ι) (s : (p : U) → E p.val) (p : U)
    (hi : p.val ∈ B.baseSet i) :
    ContinuousLinearMap.inverse (frameMatrix B U hU b i p) (sectionCoordinates B U i s p) =
      coefficients b s p := by
  rw [← frameMatrix_coefficients B U hU b i s p hi, frameMatrix_eq B U hU b i p hi,
    ContinuousLinearMap.inverse_equiv]
  exact ContinuousLinearEquiv.symm_apply_apply _ _

theorem smooth_section_iff_coefficients (s : (p : U) → E p.val) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, s p⟩ : TotalSpace (Euclidean r) E)) ↔
    ∀ j : Fin r, VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p => coefficients b s p j) := by
  constructor
  · intro hs j p
    obtain ⟨i, hi⟩ := B.covers p.val
    have hm := frameMatrix_smoothAt B U hU b i p hi
    have hc := sectionCoordinates_smoothAt B U hU i s p hi (hs p)
    have hinv := (hm.inverse (frameMatrix_invertible B U hU b i p hi)).clm_apply hc
    have hcoeff : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
        (coefficients b s) p := by
      apply hinv.congr
      have hopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
        (B.trivialization i).open_baseSet
      filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hopen.mem_nhds hi)] with y hy
      exact inverse_frameMatrix_coordinates B U hU b i s y hy
    exact hcoeff.postcomp (ContinuousLinearMap.proj j).contDiff
  · intro hc p
    obtain ⟨i, hi⟩ := B.covers p.val
    apply smoothAt_of_sectionCoordinates B U hU i s p hi
    have hm := frameMatrix_smoothAt B U hU b i p hi
    have hv : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U hU)
        (coefficients b s) p := FrameData.VectorSmoothAt.pi (fun j => hc j p)
    apply (hm.clm_apply hv).congr
    have hopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
      (B.trivialization i).open_baseSet
    filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hopen.mem_nhds hi)] with y hy
    exact frameMatrix_coefficients B U hU b i s y hy

theorem fiberAtlas_isContDiffAtlas (r : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) ({fiberChart r} : Set (ModelChart r .euclidean (Euclidean r))) := by
  constructor
  · intro v
    exact ⟨fiberChart r, mem_singleton _, mem_univ _⟩
  · rintro _ (rfl : _ = fiberChart r) _ (rfl : _ = fiberChart r)
    apply contDiffCompatible_of_germs <;> intro v _ _ <;>
      exact ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, Filter.EventuallyEq.rfl⟩

theorem trivialAtlas_isContDiffAtlas : IsContDiffAtlas (⊤ : ℕ∞) (trivialAtlas B) :=
  productAtlas_isContDiffAtlas B.coordinates _ _ _ S.smoothStructure.property.1
    (fiberAtlas_isContDiffAtlas r)

theorem trivialAtlas_fst_smooth : ManifoldSmooth (trivialAtlas B)
    S.smoothStructure.val (Prod.fst : M × Euclidean r → M) := by
  intro q
  obtain ⟨c, hc, hqc⟩ := S.smoothStructure.property.1.1 q.1
  apply (manifoldContDiffAt_iff_oneChart _ _ _ (trivialAtlas_isContDiffAtlas B)
    S.smoothStructure.property.1 Prod.fst q).mpr
  refine ⟨continuous_fst.continuousAt,
    productChart B.coordinates c (fiberChart r), ⟨c, hc, fiberChart r, mem_singleton _, rfl⟩,
    c, hc, ?_, hqc, univ, isOpen_univ, mem_univ _,
    fun z => (B.coordinates.linearEquiv.symm z).1,
    B.coordinates.linearEquiv.symm.contDiff.fst.contDiffOn, ?_⟩
  · rw [productChart_source]
    exact ⟨hqc, mem_univ _⟩
  · exact Filter.Eventually.of_forall (fun y => by
      change (B.coordinates.linearEquiv.symm (B.coordinates.linearEquiv ((c y.1).val, y.2))).1 = (c y.1).val
      exact congrArg Prod.fst (B.coordinates.linearEquiv.symm_apply_apply _))

theorem trivialAtlas_snd_smooth : VectorSmooth (trivialAtlas B)
    (Prod.snd : M × Euclidean r → Euclidean r) := by
  intro q
  refine ⟨continuous_snd.continuousAt, ?_⟩
  rintro _ ⟨c, hc, d, (rfl : d = fiberChart r), rfl⟩ _
  refine ⟨univ, isOpen_univ, mem_univ _, fun z => (B.coordinates.linearEquiv.symm z).2,
    B.coordinates.linearEquiv.symm.contDiff.snd.contDiffOn, ?_⟩
  exact Filter.Eventually.of_forall (fun y => by
    change (B.coordinates.linearEquiv.symm (B.coordinates.linearEquiv ((c y.1).val, y.2))).2 = y.2
    exact congrArg Prod.snd (B.coordinates.linearEquiv.symm_apply_apply _))

/-- Pairing a smooth base map with a smooth vector gives a map to the trivial bundle. -/
theorem smoothAt_to_trivial {d : ℕ} {k : ModelKind} {X : Type z} [TopologicalSpace X]
    {A : Set (ModelChart d k X)} {h : X → M} {v : X → Euclidean r} {x : X}
    (hh : ManifoldSmoothAt A S.smoothStructure.val h x) (hv : VectorSmoothAt A v x) :
    ManifoldSmoothAt A (trivialAtlas B) (fun y => (h y, v y)) x := by
  refine ⟨hh.1.prodMk hv.1, ?_⟩
  rintro c hc _ ⟨e, he, f, (rfl : f = fiberChart r), rfl⟩ hx hfx
  have hhe : h x ∈ e.source := (productChart_source B.coordinates e (fiberChart r) ▸ hfx).1
  obtain ⟨U, hU, hxU, G, hG, heG⟩ := hh.2 c hc e he hx hhe
  obtain ⟨T, hT, hxT, F, hF, heF⟩ := hv.2 c hc hx
  refine ⟨U ∩ T, hU.inter hT, ⟨hxU, hxT⟩,
    fun z => B.coordinates.linearEquiv (G z, F z),
    B.coordinates.linearEquiv.contDiff.contDiffOn.comp
      ((hG.mono inter_subset_left).prodMk (hF.mono inter_subset_right)) (mapsTo_univ _ _), ?_⟩
  filter_upwards [heG, heF] with y hy hy'
  rw [productChart_val]
  exact congrArg B.coordinates.linearEquiv (Prod.ext hy hy')

/-- The vector component of any given bundle trivialization is smooth where defined. -/
theorem trivializationCoordinates_smoothAt (i : ι) (q : TotalSpace (Euclidean r) E)
    (hi : q.proj ∈ B.baseSet i) :
    VectorSmoothAt B.totalManifold.smoothStructure.val
      (fun q : TotalSpace (Euclidean r) E => ((B.trivialization i) q).2) q := by
  let e := B.trivialization i
  have hi' : q.proj ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hi
  have hqe : q ∈ e.source := e.mem_source.mpr hi'
  refine ⟨(e.toOpenPartialHomeomorph.continuousAt hqe).snd, ?_⟩
  intro d hd hqd
  obtain ⟨c, hc, hqc⟩ := S.smoothStructure.property.1.1 q.proj
  have hqb : q ∈ (bundleChart B.coordinates e c).source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨hi', hqc⟩
  obtain ⟨W, hW, hqW, F, hF, heF⟩ := chartContDiffAt_of_compatible
    (B.totalManifold.smoothStructure.property.1.2 d hd _ (B.chart_mem i c hc)) hqd hqb
  refine ⟨W, hW, hqW, fun z => (B.coordinates.linearEquiv.symm (F z)).2,
    B.coordinates.linearEquiv.symm.contDiff.snd.contDiffOn.comp hF (mapsTo_univ _ _), ?_⟩
  filter_upwards [heF, e.open_source.mem_nhds hqe] with y hy hye
  rw [hy]
  change (B.coordinates.linearEquiv.symm ((bundleChart B.coordinates e c) y).val).2 = (e y).2
  rw [bundleChart_val B.coordinates e c y (e.mem_source.mp hye),
    B.coordinates.linearEquiv.symm_apply_apply]

/-- A smooth coordinate formula gives a smooth map into E. This lemma does not
assume continuity of that map: continuity is recovered using the trivialization. -/
theorem smoothAt_from_trivialization {d : ℕ} {k : ModelKind} {X : Type z} [TopologicalSpace X]
    {A : Set (ModelChart d k X)} (hA : IsContDiffAtlas (⊤ : ℕ∞) A)
    {h : X → M} {v : X → Euclidean r} {f : X → TotalSpace (Euclidean r) E} {x : X}
    (i : ι) (hi : h x ∈ B.baseSet i)
    (hh : ManifoldSmoothAt A S.smoothStructure.val h x) (hv : VectorSmoothAt A v x)
    (hproj : ∀ y, (f y).proj = h y)
    (hcoord : (fun y => ((B.trivialization i) (f y)).2) =ᶠ[𝓝 x] v) :
    ManifoldSmoothAt A B.totalManifold.smoothStructure.val f x := by
  let e := B.trivialization i
  have hi' : h x ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hi
  have hev : ∀ᶠ y in 𝓝 x, h y ∈ e.baseSet := hh.1.preimage_mem_nhds (e.open_baseSet.mem_nhds hi')
  have hcont : ContinuousAt f x := by
    have hecont : ContinuousAt e.toOpenPartialHomeomorph.symm (h x, v x) :=
      e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hi')
    apply (hecont.comp (f := fun y => (h y, v y)) (x := x) (hh.1.prodMk hv.1)).congr_of_eventuallyEq
    filter_upwards [hev, hcoord] with y hy hy'
    have hye : f y ∈ e.source := e.mem_source.mpr ((hproj y).symm ▸ hy)
    have heq : (h y, v y) = e (f y) := by
      apply Prod.ext
      · exact ((hproj y).symm.trans (e.coe_fst hye).symm)
      · exact hy'.symm
    change f y = e.toOpenPartialHomeomorph.symm (h y, v y)
    rw [heq]
    exact (e.toOpenPartialHomeomorph.left_inv hye).symm
  obtain ⟨c, hc, hxc⟩ := hA.1 x
  obtain ⟨d, hd, hxd⟩ := S.smoothStructure.property.1.1 (h x)
  have hfxd : f x ∈ (bundleChart B.coordinates e d).source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨(hproj x).symm ▸ hi', (hproj x).symm ▸ hxd⟩
  apply (manifoldContDiffAt_iff_oneChart _ _ _ hA
    B.totalManifold.smoothStructure.property.1 f x).mpr
  refine ⟨hcont, c, hc, bundleChart B.coordinates e d, B.chart_mem i d hd, hxc, hfxd, ?_⟩
  obtain ⟨U, hU, hxU, G, hG, heG⟩ := hh.2 c hc d hd hxc hxd
  obtain ⟨T, hT, hxT, F, hF, heF⟩ := hv.2 c hc hxc
  refine ⟨U ∩ T, hU.inter hT, ⟨hxU, hxT⟩,
    fun z => B.coordinates.linearEquiv (G z, F z),
    B.coordinates.linearEquiv.contDiff.contDiffOn.comp
      ((hG.mono inter_subset_left).prodMk (hF.mono inter_subset_right)) (mapsTo_univ _ _), ?_⟩
  filter_upwards [heG, heF, hev, hcoord] with y hy hy' hyi hycoord
  rw [bundleChart_val B.coordinates e d (f y) ((hproj y).symm ▸ hyi), hproj y]
  exact congrArg B.coordinates.linearEquiv (Prod.ext hy (hy'.trans hycoord.symm))

theorem frameAnalysis_smooth :
    ManifoldSmoothOn B.totalManifold.smoothStructure.val (trivialAtlas B)
      (frameAnalysis b) {q | q.proj ∈ U} := by
  intro q hq
  let p : U := ⟨q.proj, hq⟩
  obtain ⟨i, hi⟩ := B.covers q.proj
  have hmat := frameMatrix_smoothAt B U hU b i p hi
  have hinv := hmat.inverse (frameMatrix_invertible B U hU b i p hi)
  have hext := hinv.totalize hU
  have hbase := B.projection_smooth q
  have hcomp := FrameData.VectorSmoothAt.comp (g := TotalSpace.proj) (x := q)
    S.smoothStructure.property.1.1 hext hbase
  have hcoords := trivializationCoordinates_smoothAt B i q hi
  have hv := hcomp.clm_apply hcoords
  have hv' : VectorSmoothAt B.totalManifold.smoothStructure.val
      (fun y => (frameAnalysis b y).2) q := by
    apply hv.congr
    have hiopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
      (B.trivialization i).open_baseSet
    filter_upwards [hbase.1.preimage_mem_nhds ((hU.inter hiopen).mem_nhds ⟨hq, hi⟩)] with y hy
    rw [frameAnalysis_of_mem B U hU b y hy.1]
    change FrameData.totalize (fun p : U => ContinuousLinearMap.inverse (frameMatrix B U hU b i p))
      y.proj (((B.trivialization i) y).2) = (frameLinearEquiv b ⟨y.proj, hy.1⟩).symm y.snd
    rw [totalize_of_mem _ _ hy.1, frameMatrix_eq B U hU b i _ hy.2,
      ContinuousLinearMap.inverse_equiv]
    change (frameLinearEquiv b ⟨y.proj, hy.1⟩).symm
      ((B.fiberCoordinates i y.proj hy.2).symm (B.fiberCoordinates i y.proj hy.2 y.snd)) = _
    rw [LinearEquiv.symm_apply_apply]
  exact smoothAt_to_trivial B hbase hv'

theorem frameSynthesis_smooth :
    ManifoldSmoothOn (trivialAtlas B) B.totalManifold.smoothStructure.val
      (frameSynthesis b) (U ×ˢ univ) := by
  intro q hq
  let p : U := ⟨q.1, hq.1⟩
  obtain ⟨i, hi⟩ := B.covers q.1
  have hmat := (frameMatrix_smoothAt B U hU b i p hi).totalize hU
  have hbase := trivialAtlas_fst_smooth B q
  have hcomp := FrameData.VectorSmoothAt.comp (g := Prod.fst) (x := q)
    S.smoothStructure.property.1.1 hmat hbase
  have hv := hcomp.clm_apply (trivialAtlas_snd_smooth B q)
  apply smoothAt_from_trivialization B (trivialAtlas_isContDiffAtlas B) i hi hbase hv
    (fun _ => rfl)
  have hiopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
    (B.trivialization i).open_baseSet
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
    ((hU.inter hiopen).mem_nhds ⟨hq.1, hi⟩)] with y hy
  rw [frameSynthesis_of_mem B U hU b y hy.1]
  change ((B.trivialization i) ⟨y.1, frameLinearEquiv b ⟨y.1, hy.1⟩ y.2⟩).2 =
    FrameData.totalize (frameMatrix B U hU b i) y.1 y.2
  rw [totalize_of_mem _ _ hy.1, frameMatrix_eq B U hU b i _ hy.2]
  rfl

theorem frame_maps :
    (∀ p : U, ∀ v : Euclidean r,
      frameLinearEquiv b p v = ∑ j : Fin r, v j • b.section_ j p) ∧
    ManifoldSmoothOn B.totalManifold.smoothStructure.val (trivialAtlas B)
      (frameAnalysis b) {q | q.proj ∈ U} ∧
    ManifoldSmoothOn (trivialAtlas B) B.totalManifold.smoothStructure.val
      (frameSynthesis b) (U ×ˢ univ) ∧
    (∀ q : M × Euclidean r, q.1 ∈ U → frameAnalysis b (frameSynthesis b q) = q) ∧
    (∀ q : TotalSpace (Euclidean r) E, q.proj ∈ U →
      frameSynthesis b (frameAnalysis b q) = q) :=
  ⟨frameLinearEquiv_apply B U hU b, frameAnalysis_smooth B U hU b,
    frameSynthesis_smooth B U hU b, analysis_synthesis B U hU b, synthesis_analysis B U hU b⟩

/-- A global frame gives exactly its coefficient trivialization. -/
theorem globalFrame_trivialization (b : BundleData.LocalFrame B univ isOpen_univ) :
    ∃ t : SmoothTrivialization B, ∀ p : M,
      t.coordinates p = (frameLinearEquiv b ⟨p, mem_univ p⟩).symm := by
  let coordinates (p : M) : E p ≃ₗ[ℝ] Euclidean r :=
    (frameLinearEquiv b ⟨p, mem_univ p⟩).symm
  have hforward : (fun q : TotalSpace (Euclidean r) E =>
      (q.proj, coordinates q.proj q.snd)) = frameAnalysis b := by
    funext q
    exact (frameAnalysis_of_mem B univ isOpen_univ b q (mem_univ _)).symm
  have hinverse : (fun q : M × Euclidean r =>
      (⟨q.1, (coordinates q.1).symm q.2⟩ : TotalSpace (Euclidean r) E)) = frameSynthesis b := by
    funext q
    exact (frameSynthesis_of_mem B univ isOpen_univ b q (mem_univ _)).symm
  refine ⟨⟨coordinates, ?_, ?_⟩, fun _ => rfl⟩
  · rw [hforward]
    exact fun q => frameAnalysis_smooth B univ isOpen_univ b q (mem_univ _)
  · rw [hinverse]
    exact fun q => frameSynthesis_smooth B univ isOpen_univ b q ⟨mem_univ _, mem_univ _⟩

/-- The inverse images of the standard basis are a smooth global frame. -/
theorem trivialization_globalFrame (t : SmoothTrivialization B) :
    ∃ b : BundleData.LocalFrame B univ isOpen_univ,
      ∀ (p : M) (j : Fin r), b.section_ j ⟨p, mem_univ p⟩ =
        (t.coordinates p).symm (Pi.single j 1) := by
  classical
  let b : BundleData.LocalFrame B univ isOpen_univ := {
    section_ := fun j p => (t.coordinates p.val).symm (Pi.single j 1)
    basis := fun p => (Pi.basisFun ℝ (Fin r)).map (t.coordinates p.val).symm
    basis_eq := by
      intro p j
      simp only [Basis.map_apply, Pi.basisFun_apply]
    smooth := by
      intro j
      let f : M → TotalSpace (Euclidean r) E :=
        fun p => ⟨p, (t.coordinates p).symm (Pi.single j 1)⟩
      apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
        B.totalManifold.smoothStructure.val f univ isOpen_univ).mp
      have hinc : ManifoldSmooth S.smoothStructure.val (trivialAtlas B)
          (fun p : M => (p, Pi.single j 1)) := by
        intro p
        exact smoothAt_to_trivial B
          (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p)
          (FrameData.VectorSmoothAt.const _ _ _)
      have hcomp := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
        (trivialAtlas_isContDiffAtlas B).1 _ _ hinc t.smooth_inverse
      exact fun p _ => hcomp p }
  exact ⟨b, fun _ _ => rfl⟩

theorem smoothlyTrivial_iff_globalFrame :
    SmoothlyTrivial B ↔ Nonempty (BundleData.LocalFrame B univ isOpen_univ) := by
  constructor
  · rintro ⟨t⟩
    obtain ⟨b, _⟩ := trivialization_globalFrame B t
    exact ⟨b⟩
  · rintro ⟨b⟩
    obtain ⟨t, _⟩ := globalFrame_trivialization B b
    exact ⟨t⟩

end Frames

namespace Frames
/-- Rank zero requires neither a nonempty base nor a nonempty frame. -/
theorem rankZero {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean 0) E)]
    (B : BundleData.SmoothVectorBundle S 0 ι E) :
    (∀ p (v : E p), v = 0) ∧ Nonempty (BundleData.LocalFrame B univ isOpen_univ) ∧
      SmoothlyTrivial B := by
  classical
  have hzero : ∀ p (v : E p), v = 0 := by
    intro p v
    obtain ⟨i, hi⟩ := B.covers p
    apply (B.fiberCoordinates i p hi).injective
    exact Subsingleton.elim _ _
  let b : BundleData.LocalFrame B univ isOpen_univ := {
    section_ := fun j => Fin.elim0 j
    basis := by
      intro p
      let i := Classical.choose (B.covers p.val)
      have hi : p.val ∈ B.baseSet i := Classical.choose_spec (B.covers p.val)
      exact (Pi.basisFun ℝ (Fin 0)).map (B.fiberCoordinates i p.val hi).symm
    basis_eq := fun _ j => Fin.elim0 j
    smooth := fun j => Fin.elim0 j }
  exact ⟨hzero, ⟨b⟩, (smoothlyTrivial_iff_globalFrame B).mpr ⟨b⟩⟩

abbrev VectorSmoothAt := @FrameData.VectorSmoothAt
abbrev VectorSmooth := @FrameData.VectorSmooth
abbrev trivialAtlas := @FrameData.trivialAtlas
abbrev SmoothTrivialization := @FrameData.SmoothTrivialization
abbrev SmoothlyTrivial := @FrameData.SmoothlyTrivial
noncomputable abbrev coefficients := @FrameData.coefficients
noncomputable abbrev frameLinearEquiv := @FrameData.frameLinearEquiv
noncomputable abbrev frameSynthesis := @FrameData.frameSynthesis
noncomputable abbrev frameAnalysis := @FrameData.frameAnalysis
end Frames
end SmoothManifolds
