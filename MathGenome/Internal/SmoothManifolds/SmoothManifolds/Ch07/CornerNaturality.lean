import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.Stokes
import Mathlib.Analysis.Analytic.CPolynomial

/-! Global pullback and naturality of exterior differentiation on corner manifolds. -/
set_option autoImplicit false
noncomputable section
open scoped Topology Classical

namespace SmoothManifolds.CornerStokesResults
open ModelData CornerData CornerStokesData CornerFaceOrientations Set Filter
universe u

variable {n m r : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
variable {S : CornerManifold n M} {T : CornerManifold m N} {f : M → N}

private abbrev coordDomain (f : M → N) (c : CornerChart n M) (d : CornerChart m N) :=
  {x : Orthant n c.1 | x ∈ c.2.target ∧ f (c.2.symm x) ∈ d.2.source}

private theorem isOpen_coordDomain (hf : Continuous f) (c : CornerChart n M)
    (d : CornerChart m N) : IsOpen (coordDomain f c d) :=
  (hf.comp_continuousOn c.2.symm.continuousOn).isOpen_inter_preimage c.2.open_target d.2.open_source

private theorem mem_coordDomain {c : CornerChart n M} {d : CornerChart m N}
    {p : M} (hp : p ∈ c.2.source) (hd : f p ∈ d.2.source) :
    c.2 p ∈ coordDomain f c d :=
  ⟨c.2.map_source hp, by simpa only [c.2.left_inv hp] using hd⟩

private abbrev coordAmbient (f : M → N) (c : CornerChart n M) (d : CornerChart m N)
    (x : Euclidean n) : Euclidean m :=
  if hx : x ∈ orthantSet n c.1 then (d.2 (f (c.2.symm ⟨x, hx⟩))).val else 0

/-- The derivative of the actual coordinate representation on its relatively
open orthant domain, so it does not depend on a choice of ambient extension. -/
def cornerMapDerivative (f : M → N) (c : CornerChart n M) (d : CornerChart m N)
    (p : M) : Euclidean n →L[ℝ] Euclidean m :=
  fderivWithin ℝ (coordAmbient f c d) (Subtype.val '' coordDomain f c d) (c.2 p).val

private theorem cornerMapDerivative_extension
    {c : CornerChart n M} {d : CornerChart m N} {p : M}
    (hp : p ∈ c.2.source) (hd : f p ∈ d.2.source) (hf : Continuous f)
    {U : Set (Euclidean n)} (hU : IsOpen U) (hx : (c.2 p).val ∈ U)
    {F : Euclidean n → Euclidean m} (hF : DifferentiableAt ℝ F (c.2 p).val)
    (he : ∀ x : Orthant n c.1, x ∈ coordDomain f c d → x.val ∈ U →
      F x.val = (d.2 (f (c.2.symm x))).val) :
    cornerMapDerivative f c d p = fderiv ℝ F (c.2 p).val := by
  have hmem : (c.2 p).val ∈ Subtype.val '' coordDomain f c d :=
    ⟨c.2 p, mem_coordDomain hp hd, rfl⟩
  have heq : coordAmbient f c d =ᶠ[𝓝[Subtype.val '' coordDomain f c d] (c.2 p).val] F := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
    obtain ⟨x, hxd, rfl⟩ := hz
    simpa only [coordAmbient, x.property, dite_true] using (he x hxd hzU).symm
  unfold cornerMapDerivative
  rw [heq.fderivWithin_eq_of_mem hmem, hF.fderivWithin
    (uniqueDiffOn_orthantDomain (isOpen_coordDomain hf c d) _ hmem)]

private theorem cornerMap_extension (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    {c : CornerChart n M} {d : CornerChart m N} (hc : c ∈ S.atlas) (hd : d ∈ T.atlas)
    {p : M} (hp : p ∈ c.2.source) (hpd : f p ∈ d.2.source) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ (c.2 p).val ∈ U ∧
      ∃ F : Euclidean n → Euclidean m, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        ∀ x : Orthant n c.1, x ∈ coordDomain f c d → x.val ∈ U →
          F x.val = (d.2 (f (c.2.symm x))).val := by
  obtain ⟨U, hU, hx, F, hF, he⟩ := hf.2 c hc d hd ⟨c.2 p, mem_coordDomain hp hpd⟩
  exact ⟨U, hU, hx, F, hF, fun x hxd hxU => he ⟨x, hxd⟩ hxU⟩

private theorem cornerMapDerivative_source (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    {c e : CornerChart n M} {d : CornerChart m N}
    (he : e ∈ S.atlas) (hd : d ∈ T.atlas)
    {p : M} (hp : p ∈ c.2.source) (hpe : p ∈ e.2.source) (hpd : f p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans e.2).source (c.2.symm.trans e.2) (c.2 p)) :
    cornerMapDerivative f c d p =
      (cornerMapDerivative f e d p).comp (fderiv ℝ H.map (c.2 p).val) := by
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := cornerMap_extension hf he hd hpe hpd
  let O := (c.2.symm.trans e.2).source
  have hxO : c.2 p ∈ O := by
    refine ⟨c.2.map_source hp, ?_⟩
    change c.2.symm (c.2 p) ∈ e.2.source
    rwa [c.2.left_inv hp]
  have hHpoint : H.map (c.2 p).val = (e.2 p).val := by
    simpa only [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_symm,
      c.2.left_inv hp] using H.agrees (c.2 p) hxO H.mem_domain
  obtain ⟨W, hW, heW⟩ := isOpen_induced_iff.mp (c.2.symm.trans e.2).open_source
  have hxW : (c.2 p).val ∈ W := by
    change c.2 p ∈ Subtype.val ⁻¹' W
    rw [heW]
    exact hxO
  let V := (H.domain ∩ W) ∩ H.map ⁻¹' U
  have hV : IsOpen V :=
    (H.smooth.mono inter_subset_left).continuousOn.isOpen_inter_preimage
      (H.isOpen_domain.inter hW) hU
  have hxV : (c.2 p).val ∈ V :=
    ⟨⟨H.mem_domain, hxW⟩, by change H.map (c.2 p).val ∈ U; rwa [hHpoint]⟩
  have hFdiff := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hHdiff := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt
    (by simp)
  have hFdiff' : DifferentiableAt ℝ F (H.map (c.2 p).val) := hHpoint.symm ▸ hFdiff
  have heComp (x : Orthant n c.1) (hx : x ∈ coordDomain f c d) (hxV : x.val ∈ V) :
      (F ∘ H.map) x.val = (d.2 (f (c.2.symm x))).val := by
    have hxO : x ∈ O := by
      change x ∈ (c.2.symm.trans e.2).source
      rw [← heW]
      exact hxV.1.2
    have hxE : c.2.symm x ∈ e.2.source := hxO.2
    have heH : H.map x.val = (e.2 (c.2.symm x)).val := H.agrees x hxO hxV.1.1
    have hdE := mem_coordDomain hxE hx.2
    have hUe : (e.2 (c.2.symm x)).val ∈ U := heH ▸ hxV.2
    rw [Function.comp_apply, heH, heF _ hdE hUe, e.2.left_inv hxE]
  rw [cornerMapDerivative_extension hp hpd hf.1 hV hxV
      (hFdiff'.comp _ hHdiff) heComp,
    fderiv_comp _ hFdiff' hHdiff, hHpoint,
    cornerMapDerivative_extension hpe hpd hf.1 hU hxU hFdiff heF]

private theorem cornerMapDerivative_target (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    {c : CornerChart n M} {d e : CornerChart m N}
    (hc : c ∈ S.atlas) (hd : d ∈ T.atlas)
    {p : M} (hp : p ∈ c.2.source) (hpd : f p ∈ d.2.source) (hpe : f p ∈ e.2.source)
    (H : OrthantExtension (d.2.symm.trans e.2).source (d.2.symm.trans e.2) (d.2 (f p))) :
    cornerMapDerivative f c e p =
      (fderiv ℝ H.map (d.2 (f p)).val).comp (cornerMapDerivative f c d p) := by
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := cornerMap_extension hf hc hd hp hpd
  have hFpoint := heF (c.2 p) (mem_coordDomain hp hpd) hxU
  rw [c.2.left_inv hp] at hFpoint
  obtain ⟨W, hW, heW⟩ := isOpen_induced_iff.mp (isOpen_coordDomain hf.1 c d)
  have hxW : (c.2 p).val ∈ W := by
    change c.2 p ∈ Subtype.val ⁻¹' W
    rw [heW]
    exact mem_coordDomain hp hpd
  let V := (U ∩ W) ∩ F ⁻¹' H.domain
  have hV : IsOpen V :=
    (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter hW) H.isOpen_domain
  have hxV : (c.2 p).val ∈ V :=
    ⟨⟨hxU, hxW⟩, by change F (c.2 p).val ∈ H.domain; rw [hFpoint]; exact H.mem_domain⟩
  have hFdiff := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hHdiff := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt
    (by simp)
  have hHdiff' : DifferentiableAt ℝ H.map (F (c.2 p).val) := hFpoint.symm ▸ hHdiff
  have heComp (x : Orthant n c.1) (hx : x ∈ coordDomain f c e) (hxV : x.val ∈ V) :
      (H.map ∘ F) x.val = (e.2 (f (c.2.symm x))).val := by
    have hxd : x ∈ coordDomain f c d := by rw [← heW]; exact hxV.1.2
    have htrans : d.2 (f (c.2.symm x)) ∈ (d.2.symm.trans e.2).source := by
      refine ⟨d.2.map_source hxd.2, ?_⟩
      change d.2.symm (d.2 (f (c.2.symm x))) ∈ e.2.source
      rw [d.2.left_inv hxd.2]
      exact hx.2
    have hFz := heF x hxd hxV.1.1
    have hHF : (d.2 (f (c.2.symm x))).val ∈ H.domain := hFz ▸ hxV.2
    rw [Function.comp_apply, hFz, H.agrees _ htrans hHF]
    simp only [OpenPartialHomeomorph.trans_apply, d.2.left_inv hxd.2]
  rw [cornerMapDerivative_extension hp hpe hf.1 hV hxV
      (hHdiff'.comp _ hFdiff) heComp,
    fderiv_comp _ hHdiff' hFdiff, hFpoint,
    cornerMapDerivative_extension hp hpd hf.1 hU hxU hFdiff heF]

private def pullbackCoordinate (f : M → N) (ω : Form T r) (c : CornerChart n M)
    (d : CornerChart m N) (hd : d ∈ T.atlas) (p : M) (hp : f p ∈ d.2.source) :
    (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ :=
  (ω.field d hd ⟨f p, hp⟩).compContinuousLinearMap (cornerMapDerivative f c d p)

private theorem pullbackCoordinate_target (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    (ω : Form T r) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (d e : CornerChart m N) (hd : d ∈ T.atlas) (he : e ∈ T.atlas)
    (p : M) (hp : p ∈ c.2.source) (hpd : f p ∈ d.2.source) (hpe : f p ∈ e.2.source) :
    pullbackCoordinate f ω c d hd p hpd = pullbackCoordinate f ω c e he p hpe := by
  let H := cornerTransitionExtension d e (T.maximal.1.2 d hd e he) (f p) hpd hpe
  unfold pullbackCoordinate
  rw [ω.compatible d e hd he (f p) hpd hpe H,
    cornerMapDerivative_target hf hc hd hp hpd hpe H]
  ext v
  rfl

private def pullbackField (_hf : CornerMapContDiff (⊤ : ℕ∞) S T f) (ω : Form T r) :
    ChartField S r := fun c _ p =>
  let h := T.maximal.1.1 (f p.val)
  pullbackCoordinate f ω c (Classical.choose h) (Classical.choose_spec h).1 p.val
    (Classical.choose_spec h).2

private theorem pullbackField_in_chart (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    (ω : Form T r) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (d : CornerChart m N) (hd : d ∈ T.atlas) (p : c.2.source) (hpd : f p.val ∈ d.2.source) :
    pullbackField hf ω c hc p = pullbackCoordinate f ω c d hd p.val hpd := by
  let h := T.maximal.1.1 (f p.val)
  exact pullbackCoordinate_target hf ω c hc (Classical.choose h) d (Classical.choose_spec h).1
    hd p.val p.property (Classical.choose_spec h).2 hpd

/-- Pullback by a smooth map between corner manifolds, in every form degree. -/
def cornerPullback (hf : CornerMapContDiff (⊤ : ℕ∞) S T f) (ω : Form T r) : Form S r where
  field := pullbackField hf ω
  compatible := by
    intro c e hc he p hp hpe H
    obtain ⟨d, hd, hpd⟩ := T.maximal.1.1 (f p)
    rw [pullbackField_in_chart hf ω c hc d hd ⟨p,hp⟩ hpd,
      pullbackField_in_chart hf ω e he d hd ⟨p,hpe⟩ hpd]
    unfold pullbackCoordinate
    rw [cornerMapDerivative_source hf he hd hp hpe hpd H]
    ext v
    rfl

/-- In any two charts covering the source point and its image, global
pullback is composition with the actual coordinate differential. -/
theorem cornerPullback_in_chart (hf : CornerMapContDiff (⊤ : ℕ∞) S T f) (ω : Form T r)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (d : CornerChart m N) (hd : d ∈ T.atlas)
    (p : c.2.source) (hpd : f p.val ∈ d.2.source) :
    (cornerPullback hf ω).field c hc p =
      (ω.field d hd ⟨f p.val, hpd⟩).compContinuousLinearMap (cornerMapDerivative f c d p.val) :=
  pullbackField_in_chart hf ω c hc d hd p hpd

/-- A coordinate extension of the pullback that also computes its derivative
at the base point, using the corresponding target chart. -/
private theorem cornerPullback_extension (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    (ω : Form T r) (hω : IsRegularForm 1 ω) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (d : CornerChart m N) (hd : d ∈ T.atlas) (p : c.2.source) (hpd : f p.val ∈ d.2.source) :
    ∃ W : Set (Euclidean n), IsOpen W ∧ (c.2 p.val).val ∈ W ∧
      ∃ Φ : Euclidean n → (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ,
        ContDiffOn ℝ 1 Φ W ∧
        (∀ q : c.2.source, (c.2 q.val).val ∈ W → Φ (c.2 q.val).val =
          (cornerPullback hf ω).field c hc q) ∧
        extDeriv Φ (c.2 p.val).val =
          ((derivativeForm ω hω).field d hd ⟨f p.val, hpd⟩).compContinuousLinearMap
            (cornerMapDerivative f c d p.val) := by
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := cornerMap_extension hf hc hd p.property hpd
  obtain ⟨V, hV, hyV, G, hG, heG⟩ := hω d hd ⟨f p.val,hpd⟩
  have hFpoint := heF (c.2 p.val) (mem_coordDomain p.property hpd) hxU
  rw [c.2.left_inv p.property] at hFpoint
  obtain ⟨O, hO, heO⟩ := isOpen_induced_iff.mp (isOpen_coordDomain hf.1 c d)
  have hxO : (c.2 p.val).val ∈ O := by
    change c.2 p.val ∈ Subtype.val ⁻¹' O
    rw [heO]
    exact mem_coordDomain p.property hpd
  let W := (U ∩ O) ∩ F ⁻¹' V
  have hW : IsOpen W :=
    (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter hO) hV
  have hxW : (c.2 p.val).val ∈ W :=
    ⟨⟨hxU,hxO⟩, by change F (c.2 p.val).val ∈ V; rwa [hFpoint]⟩
  let Φ : Euclidean n → (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ := fun z =>
    (G (F z)).compContinuousLinearMap (fderiv ℝ F z)
  have hΦ : ContDiffOn ℝ 1 Φ W := by
    have hFG : ContDiffOn ℝ 1 (G ∘ F) W :=
      hG.comp ((hF.of_le (by simp)).mono (fun _ h => h.1.1)) (fun _ h => h.2)
    have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) W :=
      (hF.fderiv_of_isOpen hU (by simp)).mono (fun _ h => h.1.1)
    have hcomp : ContDiff ℝ 1 (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (Euclidean n →L[ℝ] Euclidean m) →
        ((Euclidean m) [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ] (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ) :=
      AnalyticOnNhd.contDiff (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ)
    exact ((hcomp.comp_contDiffOn hDF).clm_apply hFG)
  refine ⟨W, hW, hxW, Φ, hΦ, ?_, ?_⟩
  · intro q hqW
    have hcoord : c.2 q.val ∈ coordDomain f c d := by
      rw [← heO]
      exact hqW.1.2
    have hqd : f q.val ∈ d.2.source := by
      simpa only [c.2.left_inv q.property] using hcoord.2
    have hFq := heF (c.2 q.val) hcoord hqW.1.1
    rw [c.2.left_inv q.property] at hFq
    have hqV : (d.2 (f q.val)).val ∈ V := hFq ▸ hqW.2
    have hdiff := (hF.contDiffAt (hU.mem_nhds hqW.1.1)).differentiableAt (by simp)
    rw [cornerPullback_in_chart hf ω c hc d hd q hqd,
      cornerMapDerivative_extension q.property hqd hf.1 hU hqW.1.1 hdiff heF]
    dsimp only [Φ]
    rw [hFq, heG ⟨f q.val,hqd⟩ hqV]
  · have hFs := hF.contDiffAt (hU.mem_nhds hxU)
    have hGdiff : DifferentiableAt ℝ G (F (c.2 p.val).val) := by
      rw [hFpoint]
      exact (hG.contDiffAt (hV.mem_nhds hyV)).differentiableAt (by norm_num)
    have hnat := extDeriv_pullback hGdiff hFs (by simp)
    have hde := ambientForm_extension_derivative ω d hd ⟨f p.val,hpd⟩ V hV hyV G hG heG
    change _ = (extDerivWithin (ambientForm ω d hd) (Subtype.val '' d.2.target)
      (d.2 (f p.val)).val).compContinuousLinearMap _
    rw [hde, cornerMapDerivative_extension p.property hpd hf.1 hU hxU
      (hFs.differentiableAt (by simp)) heF]
    simpa only [Φ,hFpoint] using hnat

/-- A smooth corner map pulls a C¹ form back to a C¹ form. -/
theorem cornerPullback_regular (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    (ω : Form T r) (hω : IsRegularForm 1 ω) :
    IsRegularForm 1 (cornerPullback hf ω) := by
  intro c hc p
  obtain ⟨d, hd, hpd⟩ := T.maximal.1.1 (f p.val)
  obtain ⟨W, hW, hpW, Φ, hΦ, he, _⟩ := cornerPullback_extension hf ω hω c hc d hd p hpd
  exact ⟨W,hW,hpW,Φ,hΦ,he⟩

private theorem form_eq_of_field_eq (α β : Form S r) (h : α.field = β.field) : α = β := by
  cases α
  cases β
  cases h
  rfl

/-- Global exterior differentiation commutes with smooth pullback on corner
manifolds, at C¹ regularity and in every degree. -/
theorem cornerPullback_exteriorDerivative (hf : CornerMapContDiff (⊤ : ℕ∞) S T f)
    (ω : Form T r) (hω : IsRegularForm 1 ω) :
    cornerPullback hf (derivativeForm ω hω) =
      derivativeForm (cornerPullback hf ω) (cornerPullback_regular hf ω hω) := by
  apply form_eq_of_field_eq
  funext c hc p
  obtain ⟨d, hd, hpd⟩ := T.maximal.1.1 (f p.val)
  obtain ⟨W, hW, hpW, Φ, hΦ, he, hnat⟩ := cornerPullback_extension hf ω hω c hc d hd p hpd
  rw [cornerPullback_in_chart hf (derivativeForm ω hω) c hc d hd p hpd]
  change _ = extDerivWithin (ambientForm (cornerPullback hf ω) c hc)
    (Subtype.val '' c.2.target) (c.2 p.val).val
  rw [ambientForm_extension_derivative (cornerPullback hf ω) c hc p W hW hpW Φ hΦ he]
  exact hnat.symm

/-- Restriction to the canonical resolved face space is smooth pullback and
commutes with exterior differentiation at C¹ regularity in every degree. -/
theorem resolvedFace_exteriorDerivative {S : CornerManifold (n+1) M}
    {T : CornerManifold n (ResolvedFaceSpace S)}
    (hT : T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e})
    (ω : Form S r) (hω : IsRegularForm 1 ω) :
    let hf := Corners.face_projection_smooth S T hT
    cornerPullback hf (derivativeForm ω hω) =
      derivativeForm (cornerPullback hf ω) (cornerPullback_regular hf ω hω) :=
  cornerPullback_exteriorDerivative (Corners.face_projection_smooth S T hT) ω hω

end SmoothManifolds.CornerStokesResults
