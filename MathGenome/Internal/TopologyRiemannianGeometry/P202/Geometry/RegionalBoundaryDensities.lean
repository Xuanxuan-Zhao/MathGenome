import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Models
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.BoundaryGraphDirections
import Mathlib.Topology.Order.DenselyOrdered
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RegionalBoundaryDensities
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetLocalization

/-! Boundary transport for paper.tex 5107–5117. All helpers concern the
canonical tangent fibers, defining functions and covariant derivative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.PlanarRegionTopology

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

def boundarySideOfGerm {D E : Set M} {p : M}
    (b : BoundarySideAt (S := S) D p) (he : D =ᶠ[𝓝 p] E) :
    BoundarySideAt (S := S) E p := by
  let U := (mem_nhds_iff.mp he).choose
  have hU := (mem_nhds_iff.mp he).choose_spec
  exact {
    neighborhood := b.neighborhood ∩ U
    isOpen := b.isOpen.inter hU.2.1
    contains := ⟨b.contains, hU.2.2⟩
    definingFunction := b.definingFunction
    smooth := fun q hq => b.smooth q hq.1
    vanishes := b.vanishes
    region := fun q hq => (iff_of_eq (hU.1 hq.2)).symm.trans (b.region q hq.1)
    regular := b.regular }

theorem boundarySideOfGerm_normal (g : RiemannianMetric S)
    {D E : Set M} {p : M} (b : BoundarySideAt (S := S) D p)
    (he : D =ᶠ[𝓝 p] E) :
    boundaryNormal g (boundarySideOfGerm b he) = boundaryNormal g b := rfl

/-- Wherever the actual regional carrier contains a relative surface
neighborhood, its inward normal is the original surface inward normal. The
two defining functions are arbitrary; no conormal identity is assumed. -/
theorem boundaryNormal_eq_surfaceNormal_of_mem_nhds
    (g : RiemannianMetric S) {D : Set M} {p : M}
    (hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p)
    (bS : BoundarySideAt (S := S) univ p) (hD : D ∈ 𝓝 p) :
    boundaryNormal g b = boundaryNormal g bS := by
  have he : D =ᶠ[𝓝 p] (univ : Set M) := by
    filter_upwards [hD] with q hq
    exact propext (iff_of_true hq (mem_univ q))
  exact (boundarySideOfGerm_normal g b he).symm.trans
    (boundaryNormal_eq g hp bS (boundarySideOfGerm b he))

end P202.GlobalGaussBonnet.BoundaryDensities

/-! Defining-function comparison from genuine occupied sides. -/
namespace P202.GlobalGaussBonnet.BoundaryDensities
lemma forward_slope_tendsto {f : ℝ → ℝ} {r : ℝ}
    (hd : HasDerivWithinAt f r (Ici 0) 0) :
    Tendsto (slope f 0) (𝓝[>] 0) (𝓝 r) :=
  (hasDerivWithinAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono _ (fun t (ht : 0 < t) =>
      ⟨ht.le, by simpa only [mem_singleton_iff] using ne_of_gt ht⟩))

lemma eventually_pos_of_forward_derivative {f : ℝ → ℝ} {r : ℝ}
    (h0 : f 0 = 0) (hd : HasDerivWithinAt f r (Ici 0) 0) (hr : 0 < r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  filter_upwards [(forward_slope_tendsto hd).eventually (lt_mem_nhds hr),
    self_mem_nhdsWithin] with t ht htp
  simp only [slope_def_field, h0, sub_zero] at ht
  exact (div_pos_iff.mp ht).resolve_right (fun h => (not_lt_of_ge htp.le) h.2)
    |>.1

lemma nonneg_of_forward_derivative {f : ℝ → ℝ} {r : ℝ}
    (h0 : f 0 = 0) (hd : HasDerivWithinAt f r (Ici 0) 0)
    (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f t) : 0 ≤ r := by
  apply ge_of_tendsto (forward_slope_tendsto hd)
  filter_upwards [hf, self_mem_nhdsWithin] with t ht htp
  simp only [slope_def_field, h0, sub_zero]
  exact div_nonneg ht htp.le

lemma conormal_pos_smul_of_halfspace_inclusion {V : Type*}
    [AddCommGroup V] [Module ℝ V] (ℓ η : V →ₗ[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (hη : η ≠ 0)
    (hinc : ∀ v, 0 < ℓ v → 0 ≤ η v) :
    ∃ r : ℝ, 0 < r ∧ η = r • ℓ := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, ℓ w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hℓ (LinearMap.ext hn)
  let w := (ℓ w₀)⁻¹ • w₀
  have hw : ℓ w = 1 := by simp [w, hw₀]
  have hker (v : V) (hv : ℓ v = 0) : η v = 0 := by
    by_contra hn
    have hpos : 0 < ℓ (w - ((η w + 1) / η v) • v) := by
      simp [map_sub, hw, hv]
    have hbad := hinc _ hpos
    simp only [map_sub, map_smul, smul_eq_mul] at hbad
    rw [div_mul_cancel₀ _ hn] at hbad
    linarith
  have hformula (v : V) : η v = η w * ℓ v := by
    have hz : ℓ (v - ℓ v • w) = 0 := by simp [map_sub, hw]
    have he := hker _ hz
    rw [map_sub, map_smul, smul_eq_mul] at he
    linarith
  have hnonneg : 0 ≤ η w := hinc _ (by rw [hw]; norm_num)
  have hne : η w ≠ 0 := by
    intro hz
    apply hη
    ext v
    change η v = 0
    rw [hformula, hz, zero_mul]
  refine ⟨η w, lt_of_le_of_ne' hnonneg hne, ?_⟩
  ext v
  exact hformula v

open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Every tangent at an original interior point admits a genuine forward
curve, including an interior point of a half-space model. The affine line
need stay in the model only in a neighborhood of zero. -/
lemma exists_forward_curve (p : M)
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (v : TangentSpace S p) :
    ∃ c : ℝ → M, CurveRepresentsDerivation S p .forward c v := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := SmoothManifolds.coordinateDerivationEquiv S p e he hp
  have hi : (e p).val ∈ interior (modelSet 2 kind) := by
    by_contra hn
    exact hpint ((SmoothManifolds.intrinsicBoundary_iff_chart S e he p hp).mpr
      ((SmoothManifolds.mem_modelFace_iff_not_mem_interior (e p)).mpr hn))
  let A : ℝ → Euclidean 2 := fun t => (e p).val + t • E v
  have hA0 : A 0 = (e p).val := by simp [A]
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hAs : ContDiff ℝ (⊤ : ℕ∞) A :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hAd : HasDerivAt A (E v) 0 := by
    simpa [A] using ((hasDerivAt_id (0 : ℝ)).smul_const (E v)).const_add (e p).val
  have hmodel : ∀ᶠ t in 𝓝 (0 : ℝ), A t ∈ modelSet 2 kind := by
    apply hAc.continuousAt.preimage_mem_nhds
    rw [hA0]
    exact mem_interior_iff_mem_nhds.mp hi
  let q : ℝ → ModelSpace 2 kind := fun t =>
    if h : A t ∈ modelSet 2 kind then ⟨A t, h⟩ else e p
  have hqval : (fun t => (q t).val) =ᶠ[𝓝 (0 : ℝ)] A := by
    filter_upwards [hmodel] with t ht
    simp only [q, dite_eq_left ht]
  have hq0 : q 0 = e p := by
    apply Subtype.ext
    exact hqval.eq_of_nhds.trans hA0
  have hqc : ContinuousAt q 0 := by
    apply tendsto_subtype_rng.mpr
    exact hAc.continuousAt.congr_of_eventuallyEq hqval
  let c : ℝ → M := fun t => e.symm (q t)
  have hc0 : c 0 = p := by dsimp [c]; rw [hq0, e.left_inv hp]
  have hcc : ContinuousAt c 0 :=
    (e.symm.continuousAt (by rw [hq0]; exact e.map_source hp)).comp hqc
  have hct : Tendsto c (𝓝 (0 : ℝ)) (𝓝 p) := by
    simpa only [ContinuousAt, hc0] using hcc
  have hec : (fun t => (e (c t)).val) =ᶠ[𝓝 (0 : ℝ)] A := by
    have hqt := hqc.eventually
      (e.open_target.mem_nhds (by rw [hq0]; exact e.map_source hp))
    filter_upwards [hqt, hqval] with t ht hval
    change (e (e.symm (q t))).val = A t
    rw [e.right_inv ht, hval]
  have hcs : CurveSmoothAt S p .forward c := by
    refine ⟨hc0, hcc.continuousWithinAt, ?_⟩
    intro d hd hpd
    obtain ⟨U, hU, hpU, F, hF, heF⟩ := SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 e he d hd) hp hpd
    refine ⟨A ⁻¹' U, hU.preimage hAc, ?_, F ∘ A,
      hF.comp hAs.contDiffOn (fun _ ht => ht), ?_⟩
    · change A 0 ∈ U
      rwa [hA0]
    · exact ((heF.comp_tendsto hct).symm.trans (hec.fun_comp F)).filter_mono
        nhdsWithin_le_nhds
  have hd : HasDerivWithinAt (fun t => (e (c t)).val) (E v) (Ici 0) 0 :=
    (hAd.congr_of_eventuallyEq hec).hasDerivWithinAt
  obtain ⟨w, hw, _⟩ := SmoothManifolds.exists_curve_derivation_of_chart S p e he hp
    .forward c hcs (E v) hd
  have heq : w = v := by
    apply E.injective
    exact funext (SmoothManifolds.curve_coordinate_values S p e he hp .forward c w hw (E v) hd)
  exact ⟨c, heq ▸ hw⟩

lemma side_scalarDerivative_on_curve {D : Set M} {p : M}
    (b : BoundarySideAt (S := S) D p) (v : TangentSpace S p)
    (c : ℝ → M) (hc : CurveRepresentsDerivation S p .forward c v) :
    HasDerivWithinAt (b.definingFunction ∘ c)
      (scalarDerivative S b.definingFunction p v) (Ici 0) 0 := by
  have hsm := b.smooth p b.contains
  have hrep : Germ.ofFun b.definingFunction = (scalarGerm S b.definingFunction p).val := by
    simp only [scalarGerm, dite_eq_left hsm]
  exact hc.2 (scalarGerm S b.definingFunction p) b.definingFunction hrep

lemma side_conormal_nonneg_of_germ_inclusion {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hinc : ∀ᶠ q in 𝓝 p, q ∈ D → q ∈ E)
    (v : TangentSpace S p) (hv : 0 < scalarDerivative S b.definingFunction p v) :
    0 ≤ scalarDerivative S a.definingFunction p v := by
  obtain ⟨c, hc⟩ := exists_forward_curve p hpint v
  have hct : Tendsto c (𝓝[Ici 0] 0) (𝓝 p) := by
    simpa only [ContinuousWithinAt, hc.1.1, curveParameterSet] using hc.1.2.1
  have hct' : Tendsto c (𝓝[>] 0) (𝓝 p) := hct.mono_left
    (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hb0 : (b.definingFunction ∘ c) 0 = 0 := hc.1.1 ▸ b.vanishes
  have ha0 : (a.definingFunction ∘ c) 0 = 0 := hc.1.1 ▸ a.vanishes
  have hbpos := eventually_pos_of_forward_derivative hb0
    (side_scalarDerivative_on_curve b v c hc) hv
  apply nonneg_of_forward_derivative ha0 (side_scalarDerivative_on_curve a v c hc)
  filter_upwards [hbpos, hct'.eventually (b.isOpen.mem_nhds b.contains),
    hct'.eventually (a.isOpen.mem_nhds a.contains), hct'.eventually hinc] with t ht hbt hat hinc
  exact (a.region (c t) hat).mp (hinc ((b.region (c t) hbt).mpr ht.le))

lemma side_conormal_pos_smul_of_germ_inclusion {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hinc : ∀ᶠ q in 𝓝 p, q ∈ D → q ∈ E) :
    ∃ r : ℝ, 0 < r ∧ scalarDerivative S a.definingFunction p =
      r • scalarDerivative S b.definingFunction p := by
  exact conormal_pos_smul_of_halfspace_inclusion (V := TangentSpace S p)
    (scalarDerivative S b.definingFunction p) (scalarDerivative S a.definingFunction p)
    b.regular a.regular (side_conormal_nonneg_of_germ_inclusion hpint b a hinc)


/-- Positive values of an actual regular defining function belong to the
interior of its actual region. -/
lemma mem_interior_of_definingFunction_pos {D : Set M} {p q : M}
    (b : BoundarySideAt (S := S) D p) (hq : q ∈ b.neighborhood)
    (hpos : 0 < b.definingFunction q) : q ∈ interior D := by
  have hc : ContinuousAt b.definingFunction q :=
    ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp (b.smooth q hq)).1
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [b.isOpen.mem_nhds hq, hc.eventually (lt_mem_nhds hpos)] with x hx hfx
  exact (b.region x hx).mpr hfx.le

lemma side_conormal_nonpos_of_disjoint_interiors {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hdisj : Disjoint (interior D) (interior E))
    (v : TangentSpace S p) (hv : 0 < scalarDerivative S b.definingFunction p v) :
    scalarDerivative S a.definingFunction p v ≤ 0 := by
  obtain ⟨c, hc⟩ := exists_forward_curve p hpint v
  have hct : Tendsto c (𝓝[Ici 0] 0) (𝓝 p) := by
    simpa only [ContinuousWithinAt, hc.1.1, curveParameterSet] using hc.1.2.1
  have hct' : Tendsto c (𝓝[>] 0) (𝓝 p) := hct.mono_left
    (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hb0 : (b.definingFunction ∘ c) 0 = 0 := hc.1.1 ▸ b.vanishes
  have ha0 : (fun t => -(a.definingFunction ∘ c) t) 0 = 0 := by
    simp only [Function.comp_apply, hc.1.1, a.vanishes, neg_zero]
  have hbpos := eventually_pos_of_forward_derivative hb0
    (side_scalarDerivative_on_curve b v c hc) hv
  have hn : 0 ≤ -(scalarDerivative S a.definingFunction p v) := by
    apply nonneg_of_forward_derivative ha0 (side_scalarDerivative_on_curve a v c hc).neg
    filter_upwards [hbpos, hct'.eventually (b.isOpen.mem_nhds b.contains),
      hct'.eventually (a.isOpen.mem_nhds a.contains)] with t ht hbt hat
    apply neg_nonneg.mpr
    apply le_of_not_gt
    intro hpos
    exact Set.disjoint_left.mp hdisj
      (mem_interior_of_definingFunction_pos b hbt ht)
      (mem_interior_of_definingFunction_pos a hat hpos)
  exact neg_nonneg.mp hn

/-- The actual conormals of disjoint smooth local sides are opposite positive
multiples. This is derived from the occupied sets, not assumed as a premise. -/
lemma side_conormal_neg_smul_of_disjoint_interiors {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hdisj : Disjoint (interior D) (interior E)) :
    ∃ r : ℝ, 0 < r ∧ scalarDerivative S a.definingFunction p =
      -(r • scalarDerivative S b.definingFunction p) := by
  have hneg : -(scalarDerivative S a.definingFunction p) ≠ 0 := neg_ne_zero.mpr a.regular
  obtain ⟨r, hr, he⟩ := conormal_pos_smul_of_halfspace_inclusion (V := TangentSpace S p)
    (scalarDerivative S b.definingFunction p) (-(scalarDerivative S a.definingFunction p))
    b.regular hneg (fun v hv => neg_nonneg.mpr
      (side_conormal_nonpos_of_disjoint_interiors hpint b a hdisj v hv))
  exact ⟨r, hr, neg_eq_iff_eq_neg.mp he⟩

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Even local inclusion of two genuine smooth sides forces their inward
unit normals to agree at a common boundary point. -/
theorem boundaryNormal_eq_of_germ_inclusion (g : RiemannianMetric S)
    {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hinc : ∀ᶠ q in 𝓝 p, q ∈ D → q ∈ E) :
    boundaryNormal g a = boundaryNormal g b := by
  obtain ⟨r, hr, he⟩ := side_conormal_pos_smul_of_germ_inclusion hpint b a hinc
  exact boundaryNormal_eq_of_pos_smul g b a r hr he

/-- Actual opposite normals follow from the actual disjoint interiors.
No equality of defining functions or their differentials is an input. -/
theorem boundaryNormal_neg_of_disjoint_interiors (g : RiemannianMetric S)
    {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hdisj : Disjoint (interior D) (interior E)) :
    boundaryNormal g a = -boundaryNormal g b := by
  obtain ⟨r, hr, he⟩ := side_conormal_neg_smul_of_disjoint_interiors hpint b a hdisj
  unfold boundaryNormal
  rw [he, normalVector_neg, normalVector_pos_smul g p _ r hr]


/-- For two distinct original regions, the upstream decomposition already
supplies disjoint actual interiors. Their genuine local boundary sides
therefore have opposite inward normals. -/
theorem region_boundaryNormals_opposite (g : RiemannianMetric S)
    (D : RegionDecomposition S) {j k : Fin D.regionCount} (hjk : j ≠ k) {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) (P202Specs.SurfaceRegionsEuler.regionClosure D j) p)
    (a : BoundarySideAt (S := S) (P202Specs.SurfaceRegionsEuler.regionClosure D k) p) :
    boundaryNormal g a = -boundaryNormal g b := by
  apply boundaryNormal_neg_of_disjoint_interiors g hpint b a
  exact D.disjoint_interiors hjk

/-- The common curvature vector paired with the two actual region normals
cancels. This conclusion is independent of any surface orientation. -/
theorem inwardCurvature_cancel_of_disjoint_interiors (g : RiemannianMetric S)
    {D E : Set M} {p : M}
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hdisj : Disjoint (interior D) (interior E)) (V : TangentSpace S p) :
    inwardCurvature g p V (boundaryNormal g b) +
      inwardCurvature g p V (boundaryNormal g a) = 0 := by
  rw [boundaryNormal_neg_of_disjoint_interiors g hpint b a hdisj,
    inwardCurvature_neg_normal, add_neg_cancel]

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma tangentNorm_heq (g : RiemannianMetric S) {p q : M} (hp : p = q)
    {V : TangentSpace S p} {W : TangentSpace S q} (hV : HEq V W) :
    tangentNorm g p V = tangentNorm g q W := by
  subst q
  cases hV
  rfl

lemma rescale_vector_heq {p q : M} (hp : p = q)
    (V : TangentSpace S p) (W : TangentSpace S q) (a b k : ℝ)
    (hk : k ≠ 0) (hV : HEq (k • V) W) (hspeed : b = k * a) :
    HEq (a⁻¹ • V) (b⁻¹ • W) := by
  subst q
  have he : k • V = W := eq_of_heq hV
  subst W
  rw [hspeed, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hk, mul_one]

/-- Unsigned speeds transform by the absolute derivative of the actual
parameter transition, even for independently defined manifold-valued curves. -/
theorem regularArc_speed_transition {g : RiemannianMetric S}
    (c d : RegularArc g) (φ : ℝ → ℝ) (s a : ℝ)
    (hs : s ∈ Ioo c.left c.right) (ht : φ s ∈ Ioo d.left d.right)
    (hd : HasDerivAt φ a s) (heq : (d.curve ∘ φ) =ᶠ[𝓝 s] c.curve) :
    c.speed s = |a| * d.speed (φ s) := by
  have hn := tangentNorm_heq g heq.eq_of_nhds
    (regularArc_velocity_transition_heq c d φ s a hs ht hd heq)
  simpa only [P202.Geometry.SmoothMetrics.tangentNorm_smul, RegularArc.speed, Function.comp_apply] using hn.symm

/-- The actual vector D_T T is independent of an increasing regular
parameter transition. No comparison of curvature vectors is a hypothesis. -/
theorem regularArc_curvatureVector_reparam_pos {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hpos : ∀ x ∈ Ioo l r, 0 < deriv φ x)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x) :
    HEq (curvatureVector C g c.curve c.tangent c.speed s)
      (curvatureVector C g d.curve d.tangent d.speed (φ s)) := by
  have hgerm : ∀ x ∈ Ioo l r, (d.curve ∘ φ) =ᶠ[𝓝 x] c.curve := by
    intro x hx
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hcurve y hy
  obtain ⟨V, hV⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative
    g C d (φ s) (hmaps hs)
  have hcomp := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hV (hder s hs)
  have hT : ∀ᶠ x in 𝓝 s, HEq (d.tangent (φ x)) (c.tangent x) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact regularArc_tangent_transition_pos c d φ x (deriv φ x)
      (hsub hx) (hmaps hx) (hder x hx) (hpos x hx) (hgerm x hx)
  obtain ⟨W, hVW, hW⟩ := hasCovariantDerivativeAt_congr_curve C hcomp (hgerm s hs) hT
  have hspeed := regularArc_speed_transition c d φ s (deriv φ s)
    (hsub hs) (hmaps hs) (hder s hs) (hgerm s hs)
  rw [abs_of_pos (hpos s hs)] at hspeed
  unfold curvatureVector covariantDerivative
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ s) uniqueDiffWithinAt_univ hW,
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ (φ s)) uniqueDiffWithinAt_univ hV]
  exact (rescale_vector_heq (hcurve s hs) V W _ _ _ (ne_of_gt (hpos s hs)) hVW hspeed).symm

/-- Reversing the unit tangent and the direction of differentiation cancels
both signs: D_T T is unchanged under a decreasing regular transition. -/
theorem regularArc_curvatureVector_reparam_neg {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hneg : ∀ x ∈ Ioo l r, deriv φ x < 0)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x) :
    HEq (curvatureVector C g c.curve c.tangent c.speed s)
      (curvatureVector C g d.curve d.tangent d.speed (φ s)) := by
  have hgerm : ∀ x ∈ Ioo l r, (d.curve ∘ φ) =ᶠ[𝓝 x] c.curve := by
    intro x hx
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hcurve y hy
  obtain ⟨V, hV⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative
    g C d (φ s) (hmaps hs)
  have hcomp := P202.Geometry.CurveCovariantDerivative.ordinary_reparam C hV (hder s hs)
  have hcompneg := P202.Geometry.CurveCovariantDerivative.derivative_const_smul C hcomp (-1)
  simp only [neg_one_smul] at hcompneg
  have hT : ∀ᶠ x in 𝓝 s, HEq (-d.tangent (φ x)) (c.tangent x) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact regularArc_tangent_transition_neg c d φ x (deriv φ x)
      (hsub hx) (hmaps hx) (hder x hx) (hneg x hx) (hgerm x hx)
  obtain ⟨W, hVW, hW⟩ := hasCovariantDerivativeAt_congr_curve C hcompneg (hgerm s hs) hT
  have hspeed := regularArc_speed_transition c d φ s (deriv φ s)
    (hsub hs) (hmaps hs) (hder s hs) (hgerm s hs)
  rw [abs_of_neg (hneg s hs)] at hspeed
  have hVW' : HEq ((-deriv φ s) • V) W := by
    dsimp only [Function.comp_apply] at hVW
    rw [← neg_smul] at hVW
    exact hVW
  unfold curvatureVector covariantDerivative
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ s) uniqueDiffWithinAt_univ hW,
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
      (mem_univ (φ s)) uniqueDiffWithinAt_univ hV]
  exact (rescale_vector_heq (hcurve s hs) V W _ _ _ (neg_ne_zero.mpr (ne_of_lt (hneg s hs)))
    hVW' hspeed).symm

/-- An arbitrary injective differentiable transition between genuine arcs has
one sign, so either tangent direction gives the same curvature vector. -/
theorem regularArc_curvatureVector_reparam {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hi : InjOn φ (Ioo l r))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x) :
    HEq (curvatureVector C g c.curve c.tangent c.speed s)
      (curvatureVector C g d.curve d.tangent d.speed (φ s)) := by
  have hn (x : ℝ) (hx : x ∈ Ioo l r) : deriv φ x ≠ 0 := by
    have hspeed := regularArc_speed_transition c d φ x (deriv φ x)
      (hsub hx) (hmaps hx) (hder x hx) (by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact hcurve y hy)
    intro hz
    rw [hz, abs_zero, zero_mul] at hspeed
    exact (ne_of_gt (P202.Geometry.SurfaceBoundaryGeometry.unitTangent_unit g c x (hsub hx)).2)
      hspeed
  obtain hpos | hneg := injective_interval_derivative_sign (hs.1.trans hs.2)
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt) hi
    (fun x hx => (hder x hx).differentiableAt) hn
  · exact regularArc_curvatureVector_reparam_pos C c d φ hs hsub hmaps hder hpos hcurve
  · exact regularArc_curvatureVector_reparam_neg C c d φ hs hsub hmaps hder hneg hcurve

end P202.GlobalGaussBonnet.BoundaryDensities
namespace P202.GlobalGaussBonnet.BoundaryDensities
lemma arcPresentation_affine_mem_Ioo {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t ∈ Ioo (0 : ℝ) 1 := by
  have ha : 0 ≤ A.time k.castSucc := by
    rw [← A.first]
    exact A.strictMono.monotone (Fin.zero_le _)
  have hb : A.time k.succ ≤ 1 := by
    rw [← A.last]
    exact A.strictMono.monotone (Fin.le_last _)
  have hd : 0 < A.time k.succ - A.time k.castSucc :=
    sub_pos.mpr (A.strictMono k.castSucc_lt_succ)
  constructor <;> nlinarith [mul_pos hd ht.1, mul_pos hd (sub_pos.mpr ht.2)]

/-- Open arcs in every genuine regional presentation are embedded, including
when the two endpoints are the same point of the parameter circle. -/
lemma arcPresentation_open_injective {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count) :
    InjOn (A.arc k) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hparam : ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x : ℝ) :
      ParameterCircle) =
      ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * y : ℝ) : ParameterCircle) := by
    apply q.injective
    change realLift q.parametrization _ = realLift q.parametrization _
    rw [← A.agrees k x ⟨hx.1.le, hx.2.le⟩, ← A.agrees k y ⟨hy.1.le, hy.2.le⟩]
    exact hxy
  have hx' := arcPresentation_affine_mem_Ioo A k hx
  have hy' := arcPresentation_affine_mem_Ioo A k hy
  have he : A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * x =
      A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * y :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨hx'.1.le, by simpa only [zero_add] using hx'.2⟩
      ⟨hy'.1.le, by simpa only [zero_add] using hy'.2⟩).mp hparam
  have hd : 0 < A.time k.succ - A.time k.castSucc :=
    sub_pos.mpr (A.strictMono k.castSucc_lt_succ)
  nlinarith

lemma arcPresentation_cutParameters_finite {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count)
    {F : Set Plane} (hF : F.Finite) :
    (Ioo (0 : ℝ) 1 ∩ A.arc k ⁻¹' F).Finite := by
  exact Set.Finite.of_injOn (t := F) (fun t ht => ht.2)
    ((arcPresentation_open_injective A k).mono inter_subset_left) hF
end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Every point of every actual regional boundary arc is on the original
graph, in the original assigned coordinates. This includes inserted smooth
subdivision endpoints and both original model kinds. -/
theorem region_arc_on_graph (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ p ∈ P202Specs.SurfaceRegionsEuler.regionClosure D j ∩ D.graph.carrier,
      p ∈ (D.chart j).source ∧ coordinates (D.chart j) p = A.arc k t := by
  have hx : A.arc k t ∈ (D.region j).boundary := by
    change A.arc k t ∈ frontier (D.region j).domain
    rw [(D.region j).boundary_eq]
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    refine ⟨((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t : ℝ) :
      ParameterCircle), ?_⟩
    exact (A.agrees k t ht).symm
  rw [region_boundary_eq_coordinates_graph D j] at hx
  obtain ⟨p, hp, he⟩ := hx
  exact ⟨p, hp, D.closure_in_chart j hp.1, he⟩

/-- Cutting a genuine presentation arc at all original graph vertices adds
only finitely many parameter values. No endpoint regularity of the supplied
graph parametrizations is needed. -/
theorem region_arc_vertex_cutParameters_finite (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) :
    (Ioo (0 : ℝ) 1 ∩ A.arc k ⁻¹' (coordinates (D.chart j) '' range D.graph.vertex)).Finite := by
  exact arcPresentation_cutParameters_finite A k ((Set.finite_range _).image _)

end P202.GlobalGaussBonnet.BoundaryDensities


/-! DefiningFunctions: derived from original regional and metric data. -/
section DefiningFunctions
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical BigOperators ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The full chart formula for the actual defining differential. -/
theorem scalarDerivative_chart_function
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (F : Euclidean 2 → ℝ)
    (U : Set (Euclidean 2)) (hU : IsOpen U) (hpU : (e p).val ∈ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) (V : TangentSpace S p) :
    scalarDerivative S (fun q => F (e q).val) p V =
      fderiv ℝ F (e p).val (SmoothManifolds.coordinateDerivationEquiv S p e he hp V) := by
  have hsm : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val (fun q => F (e q).val) p := by
    apply SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
    exact ⟨U, hU, hpU, F, hF, Eventually.of_forall (fun _ => rfl)⟩
  have hrep : Germ.ofFun (fun q => F (e q).val) =
      (scalarGerm S (fun q => F (e q).val) p).val := by
    simp only [scalarGerm, dite_eq_left hsm]
  change V.val (scalarGerm S (fun q => F (e q).val) p) = _
  rw [SmoothManifolds.derivation_coordinate_formula S p e he hp V
    (scalarGerm S (fun q => F (e q).val) p) F ⟨⟨U, hU, hpU, hF⟩, hrep⟩]
  let E := SmoothManifolds.coordinateDerivationEquiv S p e he hp
  change (∑ i, E V i * fderiv ℝ F (e p).val (Pi.single i 1)) = _
  have hvec : E V = ∑ i : Fin 2, E V i • Pi.single i 1 := by
    ext i
    fin_cases i <;> simp
  conv_rhs => rw [hvec]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Chart smoothness and a regular coordinate defining function construct an
actual local side of the original set, with no supplied normal certificate. -/
def boundarySideOfChartFunction {D : Set M} {p : M}
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (N : Set M) (hN : IsOpen N) (hpN : p ∈ N) (hNe : N ⊆ e.source)
    (F : Euclidean 2 → ℝ) (U : Set (Euclidean 2)) (hU : IsOpen U)
    (hNU : ∀ q ∈ N, (e q).val ∈ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) (hzero : F (e p).val = 0)
    (hD : ∀ q ∈ N, q ∈ D ↔ 0 ≤ F (e q).val)
    (hreg : fderiv ℝ F (e p).val ≠ 0) : BoundarySideAt (S := S) D p where
  neighborhood := N
  isOpen := hN
  contains := hpN
  definingFunction := fun q => F (e q).val
  smooth := by
    intro q hq
    apply SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 he (hNe hq)
    exact ⟨U, hU, hNU q hq, F, hF, Eventually.of_forall (fun _ => rfl)⟩
  vanishes := hzero
  region := hD
  regular := by
    intro hz
    apply hreg
    ext v
    have hv := scalarDerivative_chart_function e he p (hNe hpN) F U hU (hNU p hpN)
      hF ((SmoothManifolds.coordinateDerivationEquiv S p e he (hNe hpN)).symm v)
    rw [hz, LinearMap.zero_apply, LinearEquiv.apply_symm_apply] at hv
    exact hv.symm

/-- A smooth graph description produces the actual regional side. The
nonvanishing differential is proved by testing the vertical coordinate. -/
def boundarySideOfCoordinateGraph {D : Set M} {p : M}
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (N : Set M) (hN : IsOpen N) (hpN : p ∈ N) (hNe : N ⊆ e.source)
    (height : ℝ → ℝ) (J : Set ℝ) (hJ : IsOpen J)
    (hNJ : ∀ q ∈ N, (e q).val 0 ∈ J)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) height J)
    (hp : (e p).val 1 = height ((e p).val 0))
    (hD : ∀ q ∈ N, q ∈ D ↔ height ((e q).val 0) ≤ (e q).val 1) :
    BoundarySideAt (S := S) D p := by
  let F : Euclidean 2 → ℝ := fun x => x 1 - height (x 0)
  let U : Set (Euclidean 2) := {x | x 0 ∈ J}
  have hU : IsOpen U := hJ.preimage (continuous_apply 0)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U := by
    exact (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1).contDiffOn.sub
      (hh.comp (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).contDiffOn (fun _ h => h))
  refine boundarySideOfChartFunction e he N hN hpN hNe F U hU hNJ hF
    (sub_eq_zero.mpr hp) (fun q hq => (hD q hq).trans sub_nonneg.symm) ?_
  have hheight : DifferentiableAt ℝ height ((e p).val 0) :=
    (hh.contDiffAt (hJ.mem_nhds (hNJ p hpN))).differentiableAt (by simp)
  have hder := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (e p).val).sub
    (hheight.hasFDerivAt.comp (e p).val (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (e p).val))
  intro hz
  have htest := congrArg (fun L : Euclidean 2 →L[ℝ] ℝ => L (Pi.single 1 1)) hz
  rw [show fderiv ℝ F (e p).val = _ from hder.fderiv] at htest
  simp at htest

/-- An inverse to a regular scalar coordinate retains all derivatives.
This upgrades the continuous boundary graph to a smooth graph away from joins. -/
theorem smooth_of_smooth_parameter {u v g : ℝ → ℝ} {q : ℝ}
    (hu : ContDiffAt ℝ ∞ u q) (hv : ContDiffAt ℝ ∞ v q)
    (hun : deriv u q ≠ 0) (hgraph : (fun t => g (u t)) =ᶠ[𝓝 q] v) :
    ContDiffAt ℝ ∞ g (u q) := by
  have hsu := hu.hasStrictDerivAt (by simp)
  let E := (hsu.hasStrictFDerivAt_equiv hun).toOpenPartialHomeomorph u
  have hq : q ∈ E.source := (hsu.hasStrictFDerivAt_equiv hun).mem_toOpenPartialHomeomorph_source
  have him : u q ∈ E.target := E.map_source hq
  have hleft : E.symm (u q) = q := E.left_inv hq
  have hdinv : ContDiffAt ℝ ∞ E.symm (u q) := by
    apply E.contDiffAt_symm_deriv hun him
    · change HasDerivAt u (deriv u q) (E.symm (u q))
      rw [hleft]
      exact hsu.hasDerivAt
    · change ContDiffAt ℝ ∞ u (E.symm (u q))
      rw [hleft]
      exact hu
  have htend : Tendsto E.symm (𝓝 (u q)) (𝓝 q) := by
    simpa only [hleft] using hdinv.continuousAt.tendsto
  have heq : g =ᶠ[𝓝 (u q)] (fun x => v (E.symm x)) := by
    filter_upwards [E.open_target.mem_nhds him, htend.eventually hgraph] with x hx hg
    have hright : u (E.symm x) = x := E.right_inv hx
    simpa only [hright] using hg
  have hdv : ContDiffAt ℝ ∞ v (E.symm (u q)) := hleft.symm ▸ hv
  exact (hdv.comp _ hdinv).congr_of_eventuallyEq heq

end P202.GlobalGaussBonnet.BoundaryDensities
end DefiningFunctions


/-! ActualRegionalSides: derived from original regional and metric data. -/
section ActualRegionalSides
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.ConnectionData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.BoundaryGraphDirections
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u

lemma closure_local_eq {X : Type u} [TopologicalSpace X]
    {A B N : Set X} (hN : IsOpen N) (h : A ∩ N = B ∩ N) :
    closure A ∩ N = closure B ∩ N := by
  have h' : N ∩ A = N ∩ B := by simpa only [inter_comm] using h
  apply Subset.antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    have hh := hN.inter_closure ⟨hx.2, hx.1⟩
    rw [h'] at hh
    exact closure_mono inter_subset_right hh
  · intro x hx
    refine ⟨?_, hx.2⟩
    have hh := hN.inter_closure ⟨hx.2, hx.1⟩
    rw [← h'] at hh
    exact closure_mono inter_subset_right hh

lemma closure_upper_halfspace :
    closure {x : Euclidean 2 | 0 < x 1} = {x | 0 ≤ x 1} := by
  change closure ((fun x : Euclidean 2 => x 1) ⁻¹' Ioi 0) =
    (fun x : Euclidean 2 => x 1) ⁻¹' Ici 0
  rw [← (isOpenMap_eval (1 : Fin 2)).preimage_closure_eq_closure_preimage
    (continuous_apply 1), closure_Ioi]

lemma closure_local_upper_side {A N : Set (Euclidean 2)}
    (H : Euclidean 2 ≃ₜ Euclidean 2) (hN : IsOpen N)
    (h : A ∩ N = (H ⁻¹' {x | 0 < x 1}) ∩ N) :
    closure A ∩ N = (H ⁻¹' {x | 0 ≤ x 1}) ∩ N := by
  rw [closure_local_eq hN h, ← H.preimage_closure, closure_upper_halfspace]

lemma closure_plane_upper_halfspace :
    closure {x : Plane | 0 < x 1} = {x | 0 ≤ x 1} := by
  let E : Plane ≃ₜ Euclidean 2 := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
  change closure (E ⁻¹' {x : Euclidean 2 | 0 < x 1}) =
    E ⁻¹' {x : Euclidean 2 | 0 ≤ x 1}
  rw [← E.preimage_closure, closure_upper_halfspace]

lemma closure_strict_epigraph (h : ℝ → ℝ) (hc : Continuous h) :
    closure {x : Plane | h (x 0) < x 1} = {x | h (x 0) ≤ x 1} := by
  let H : Plane ≃ₜ Plane := {
    toFun := fun x => !₂[x 0, x 1 - h (x 0)]
    invFun := fun x => !₂[x 0, x 1 + h (x 0)]
    left_inv := by intro x; ext i; fin_cases i <;> simp
    right_inv := by intro x; ext i; fin_cases i <;> simp
    continuous_toFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    continuous_invFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop }
  have hlt : {x : Plane | h (x 0) < x 1} = H ⁻¹' {x | 0 < x 1} := by
    ext x
    simp [H, sub_pos]
  have hle : {x : Plane | h (x 0) ≤ x 1} = H ⁻¹' {x | 0 ≤ x 1} := by
    ext x
    simp [H, sub_nonneg]
  rw [hlt, ← H.preimage_closure, closure_plane_upper_halfspace, ← hle]

/-- The actual occupied closed side follows from the actual open-domain graph,
by local closure, including points exactly on the graph. -/
theorem localDirectedBoundaryGraph_carrier {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O) :
    R.carrier ∩ O = (G.frame.map '' {z : Plane | G.height (z 0) ≤ z 1}) ∩ O := by
  have hcl := closure_local_eq hO G.domain_eq
  change closure R.domain ∩ O = _
  rw [hcl]
  have hc := G.frame.map.toHomeomorph.image_closure
    {z : Plane | G.height (z 0) < z 1}
  change G.frame.map '' closure {z : Plane | G.height (z 0) < z 1} =
    closure (G.frame.map '' {z : Plane | G.height (z 0) < z 1}) at hc
  rw [← hc, closure_strict_epigraph G.height G.continuous_height]

/-- A genuinely smooth regular parametrized graph has a smooth height on an
open coordinate neighborhood; this is stronger than smoothness at one point. -/
theorem smooth_graph_neighborhood {u v g : ℝ → ℝ} {q : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hq : q ∈ I)
    (hu : ContDiffOn ℝ ∞ u I) (hv : ContDiffOn ℝ ∞ v I)
    (hun : deriv u q ≠ 0) (hgraph : (fun t => g (u t)) =ᶠ[𝓝 q] v) :
    ∃ J : Set ℝ, IsOpen J ∧ u q ∈ J ∧ ContDiffOn ℝ ∞ g J := by
  have huq := hu.contDiffAt (hI.mem_nhds hq)
  have hsu := huq.hasStrictDerivAt (by simp)
  let E := (hsu.hasStrictFDerivAt_equiv hun).toOpenPartialHomeomorph u
  have hEq : q ∈ E.source :=
    (hsu.hasStrictFDerivAt_equiv hun).mem_toOpenPartialHomeomorph_source
  have hdu : ContinuousAt (deriv u) q :=
    (huq.derivWithin (m := 0) (by simp)).continuousAt
  have hnon : ∀ᶠ x in 𝓝 q, deriv u x ≠ 0 :=
    hdu.eventually (isOpen_compl_singleton.mem_nhds hun)
  have hall : ∀ᶠ x in 𝓝 q, x ∈ I ∧ deriv u x ≠ 0 ∧ g (u x) = v x := by
    filter_upwards [hI.mem_nhds hq, hnon, hgraph] with x hx hn hg
    exact ⟨hx, hn, hg⟩
  obtain ⟨W, hW, hWopen, hqW⟩ := eventually_nhds_iff.mp hall
  refine ⟨E '' (E.source ∩ W), E.isOpen_image_source_inter hWopen,
    ⟨q, ⟨hEq, hqW⟩, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  apply ContDiffAt.contDiffWithinAt
  apply smooth_of_smooth_parameter
    (hu.contDiffAt (hI.mem_nhds (hW x hx.2).1))
    (hv.contDiffAt (hI.mem_nhds (hW x hx.2).1)) (hW x hx.2).2.1
  filter_upwards [hWopen.mem_nhds hx.2] with z hz
  exact (hW z hz).2.2


private lemma graph_frame_vertical {e : Plane} (he : ‖e‖ = 1)
    (F : OrientedFrame e) (z : Plane) :
    inner ℝ (quarterTurn e) (F.map z) = z 1 := by
  have horth : inner ℝ (quarterTurn e) e = 0 := by
    simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  rw [F.formula, inner_add_right, inner_smul_right, inner_smul_right,
    horth, P202.PlanarRegionTopology.quarterTurn_inner,
    real_inner_self_eq_norm_sq, he]
  simp

/-- The height of the actual regional boundary graph is C∞ near every
original nonjoin parameter. No extra graph smoothness is assumed. -/
theorem localDirectedBoundaryGraph_height_smooth {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O)
    (ht : (t : ParameterCircle) ∉ (R.curve i).joins) :
    ∃ J : Set ℝ, IsOpen J ∧
      inner ℝ G.arc.axis (realLift (R.curve i).parametrization t) ∈ J ∧
      ContDiffOn ℝ ∞ G.height J := by
  let c := R.curve i
  let γ := realLift c.parametrization
  let I : Set ℝ := {q | (q : ParameterCircle) ∉ c.joins}
  have hI : IsOpen I :=
    c.joins.finite_toSet.isClosed.isOpen_compl.preimage (AddCircle.continuous_mk' 1)
  have hγ : ContDiffAt ℝ ∞ γ t := c.smooth_off_joins t ht
  have hleft : DifferentiableAt ℝ G.arc.leftExtension t :=
    (G.arc.left_smooth.contDiffAt (isOpen_Ioo.mem_nhds
      ⟨by linarith [G.arc.radius_pos, G.arc.radius_lt],
        by linarith [G.arc.radius_pos, G.arc.radius_lt]⟩)).differentiableAt (by simp)
  have hder := P202.PlanarRegionTopology.deriv_eq_of_eqOn_left G.arc.radius_pos
    hleft (hγ.differentiableAt (by simp)) G.arc.left_eq
  have hproj : inner ℝ G.arc.axis (deriv γ t) ≠ 0 := by
    have hp := G.arc.left_positive t ⟨by linarith [G.arc.radius_pos], le_rfl⟩
    rw [hder] at hp
    intro hz
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hu : ContDiffOn ℝ ∞ (fun q => inner ℝ G.arc.axis (γ q)) I := by
    intro q hq
    exact (contDiffAt_const.inner ℝ (c.smooth_off_joins q hq)).contDiffWithinAt
  have hv : ContDiffOn ℝ ∞ (fun q => inner ℝ (quarterTurn G.arc.axis) (γ q)) I := by
    intro q hq
    exact (contDiffAt_const.inner ℝ (c.smooth_off_joins q hq)).contDiffWithinAt
  have hun : deriv (fun q => inner ℝ G.arc.axis (γ q)) t ≠ 0 := by
    simpa only [deriv_inner_apply ℝ (differentiableAt_const G.arc.axis)
      (hγ.differentiableAt (by simp)), deriv_const, inner_zero_left,
      zero_add, add_zero] using hproj
  apply smooth_graph_neighborhood hI ht hu hv hun
  filter_upwards [Icc_mem_nhds
    (show t - G.arc.radius < t by linarith [G.arc.radius_pos])
    (show t < t + G.arc.radius by linarith [G.arc.radius_pos])] with q hq
  have hh := congrArg (fun z => inner ℝ (quarterTurn G.arc.axis) z) (G.arc_identity q hq)
  simpa only [graph_frame_vertical G.arc.unit_axis G.frame,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, arcProjection, γ, c] using hh.symm


/-- The frame of an actual directed boundary graph may have any axis. This
constructor uses its two scalar projections directly in the original chart. -/
def boundarySideOfPlaneGraph {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {D : Set M} {p : M}
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (N : Set M) (hN : IsOpen N) (hpN : p ∈ N) (hNe : N ⊆ e.source)
    (axis : Plane) (haxis : ‖axis‖ = 1)
    (height : ℝ → ℝ) (J : Set ℝ) (hJ : IsOpen J)
    (hNJ : ∀ q ∈ N, inner ℝ axis
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm (e q).val) ∈ J)
    (hh : ContDiffOn ℝ ∞ height J)
    (hp : inner ℝ (quarterTurn axis) ((EuclideanSpace.equiv (Fin 2) ℝ).symm (e p).val) =
      height (inner ℝ axis ((EuclideanSpace.equiv (Fin 2) ℝ).symm (e p).val)))
    (hD : ∀ q ∈ N, q ∈ D ↔
      height (inner ℝ axis ((EuclideanSpace.equiv (Fin 2) ℝ).symm (e q).val)) ≤
        inner ℝ (quarterTurn axis) ((EuclideanSpace.equiv (Fin 2) ℝ).symm (e q).val)) :
    BoundarySideAt (S := S) D p := by
  let E := EuclideanSpace.equiv (Fin 2) ℝ
  let u : Euclidean 2 →L[ℝ] ℝ := (innerSL ℝ axis).comp E.symm.toContinuousLinearMap
  let v : Euclidean 2 →L[ℝ] ℝ :=
    (innerSL ℝ (quarterTurn axis)).comp E.symm.toContinuousLinearMap
  let F : Euclidean 2 → ℝ := fun x => v x - height (u x)
  let U : Set (Euclidean 2) := u ⁻¹' J
  have hU : IsOpen U := hJ.preimage u.continuous
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U :=
    v.contDiff.contDiffOn.sub (hh.comp u.contDiff.contDiffOn (fun _ hx => hx))
  refine boundarySideOfChartFunction e he N hN hpN hNe F U hU hNJ hF
    (sub_eq_zero.mpr hp) (fun q hq => (hD q hq).trans sub_nonneg.symm) ?_
  have hheight : DifferentiableAt ℝ height (u (e p).val) :=
    (hh.contDiffAt (hJ.mem_nhds (hNJ p hpN))).differentiableAt (by simp)
  have hder := v.hasFDerivAt.sub (hheight.hasFDerivAt.comp (e p).val u.hasFDerivAt)
  have horth : inner ℝ axis (quarterTurn axis) = 0 := by
    simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hunit : inner ℝ (quarterTurn axis) (quarterTurn axis) = 1 := by
    rw [P202.PlanarRegionTopology.quarterTurn_inner, real_inner_self_eq_norm_sq, haxis]
    norm_num
  intro hz
  have htest := congrArg (fun L : Euclidean 2 →L[ℝ] ℝ => L (E (quarterTurn axis))) hz
  rw [show fderiv ℝ F (e p).val = _ from hder.fderiv] at htest
  have huval : u (E (quarterTurn axis)) = 0 := by
    change inner ℝ axis (E.symm (E (quarterTurn axis))) = 0
    rw [E.symm_apply_apply]
    exact horth
  have hvval : v (E (quarterTurn axis)) = 1 := by
    change inner ℝ (quarterTurn axis) (E.symm (E (quarterTurn axis))) = 1
    rw [E.symm_apply_apply]
    exact hunit
  change v (E (quarterTurn axis)) -
    fderiv ℝ height (u (e p).val) (u (E (quarterTurn axis))) = 0 at htest
  rw [huval, hvval, map_zero, sub_zero] at htest
  exact one_ne_zero htest


private lemma graph_frame_horizontal {e : Plane} (he : ‖e‖ = 1)
    (F : OrientedFrame e) (z : Plane) : inner ℝ e (F.map z) = z 0 := by
  have horth : inner ℝ e (quarterTurn e) = 0 := by
    simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  rw [F.formula, inner_add_right, inner_smul_right, inner_smul_right,
    horth, real_inner_self_eq_norm_sq, he]
  simp

private lemma graph_frame_epigraph {e : Plane} (he : ‖e‖ = 1)
    (F : OrientedFrame e) (height : ℝ → ℝ) (x : Plane) :
    x ∈ F.map '' {z : Plane | height (z 0) ≤ z 1} ↔
      height (inner ℝ e x) ≤ inner ℝ (quarterTurn e) x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change height (z 0) ≤ z 1 at hz
    simpa only [graph_frame_horizontal he F, graph_frame_vertical he F] using hz
  · intro hx
    refine ⟨F.map.symm x, ?_, F.map.apply_symm_apply x⟩
    have hu := graph_frame_horizontal he F (F.map.symm x)
    have hv := graph_frame_vertical he F (F.map.symm x)
    rw [F.map.apply_symm_apply] at hu hv
    change height _ ≤ _
    rw [← hu, ← hv]
    exact hx

open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
  P202Specs.SurfaceRegionsEuler

/-- The genuine graph's defining scalar, positive on the actual occupied side. -/
def graphDefiningFunction {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (x : Plane) : ℝ :=
  inner ℝ (quarterTurn G.arc.axis) x - G.height (inner ℝ G.arc.axis x)

/-- At a genuine nonjoin boundary point, the actual planar domain and the
actual regional chart construct a genuine side of the original component
closure. No side, conormal or metric-normal comparison is a premise. -/
theorem regionalBoundarySideAtOfDirectedGraph_withFunction
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S) (j : Fin D.regionCount)
    (s : Fin (D.region j).boundaryCount → ℝ)
    (i : Fin (D.region j).boundaryCount) (t : ℝ) (O : Set Plane)
    (G : LocalDirectedBoundaryGraph (D.region j) s i t O)
    (hO : IsOpen O) (htO : realLift ((D.region j).curve i).parametrization t ∈ O)
    (ht : (t : ParameterCircle) ∉ ((D.region j).curve i).joins)
    (p : M) (hp : p ∈ regionClosure D j)
    (hcoord : coordinates (D.chart j) p =
      realLift ((D.region j).curve i).parametrization t) :
    ∃ b : BoundarySideAt (S := S) (regionClosure D j) p,
      b.definingFunction = fun q => graphDefiningFunction G (coordinates (D.chart j) q) := by
  obtain ⟨J, hJ, htJ, hheight⟩ := localDirectedBoundaryGraph_height_smooth G ht
  let e := D.chart j
  let E := EuclideanSpace.equiv (Fin 2) ℝ
  let coord : M → Plane := fun q => E.symm (e q).val
  have hcoord_eq : coord = coordinates e := rfl
  let W : Set Plane := O ∩ {x | inner ℝ G.arc.axis x ∈ J}
  have hW : IsOpen W := hO.inter (hJ.preimage (by fun_prop))
  let N : Set M := e.source ∩ coord ⁻¹' W
  have hc : ContinuousOn coord e.source :=
    E.symm.continuous.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn e.continuousOn)
  have hN : IsOpen N := hc.isOpen_inter_preimage e.open_source hW
  have hpN : p ∈ N := by
    refine ⟨D.closure_in_chart j hp, ?_⟩
    change coordinates e p ∈ W
    rw [hcoord]
    exact ⟨htO, htJ⟩
  have hNE : N ⊆ e.source := inter_subset_left
  have hNJ : ∀ q ∈ N, inner ℝ G.arc.axis (coord q) ∈ J := fun _ hq => hq.2.2
  have hzero : inner ℝ (quarterTurn G.arc.axis) (coord p) =
      G.height (inner ℝ G.arc.axis (coord p)) := by
    have htarc := G.arc_identity t
      ⟨by linarith [G.arc.radius_pos], by linarith [G.arc.radius_pos]⟩
    have hh := congrArg (fun z => inner ℝ (quarterTurn G.arc.axis) z) htarc
    rw [graph_frame_vertical G.arc.unit_axis G.frame] at hh
    change inner ℝ (quarterTurn G.arc.axis)
      (realLift ((D.region j).curve i).parametrization t) =
      G.height (inner ℝ G.arc.axis
        (realLift ((D.region j).curve i).parametrization t)) at hh
    change inner ℝ (quarterTurn G.arc.axis) (coordinates e p) =
      G.height (inner ℝ G.arc.axis (coordinates e p))
    change inner ℝ (quarterTurn G.arc.axis) (coordinates (D.chart j) p) =
      G.height (inner ℝ G.arc.axis (coordinates (D.chart j) p))
    rw [hcoord]
    exact hh
  refine ⟨boundarySideOfPlaneGraph e (D.chart_mem j) N hN hpN hNE
    G.arc.axis G.arc.unit_axis G.height J hJ hNJ hheight hzero ?_, rfl⟩
  intro q hq
  have hmem : q ∈ regionClosure D j ↔ coord q ∈ (D.region j).carrier := by
    constructor
    · intro hqR
      rw [← D.closure_coordinates j]
      exact ⟨q, hqR, rfl⟩
    · intro hqR
      rw [← D.closure_coordinates j] at hqR
      obtain ⟨r, hr, heq⟩ := hqR
      have heqr : r = q := by
        apply e.injOn (D.closure_in_chart j hr) hq.1
        apply Subtype.ext
        exact E.symm.injective heq
      exact heqr ▸ hr
  have hcar := localDirectedBoundaryGraph_carrier G hO
  have hside : coord q ∈ (D.region j).carrier ↔
      coord q ∈ G.frame.map '' {z : Plane | G.height (z 0) ≤ z 1} := by
    constructor
    · intro hx
      have hh : coord q ∈ (D.region j).carrier ∩ O := ⟨hx, hq.2.1⟩
      rw [hcar] at hh
      exact hh.1
    · intro hx
      have hh : coord q ∈ (G.frame.map '' {z : Plane | G.height (z 0) ≤ z 1}) ∩ O :=
        ⟨hx, hq.2.1⟩
      rw [← hcar] at hh
      exact hh.1
  exact hmem.trans (hside.trans (graph_frame_epigraph G.arc.unit_axis G.frame G.height (coord q)))


/-- At a nonjoin, the occupied component closure has a genuine smooth side. -/
theorem regionalBoundarySideAtOfDirectedGraph
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S) (j : Fin D.regionCount)
    (s : Fin (D.region j).boundaryCount → ℝ)
    (i : Fin (D.region j).boundaryCount) (t : ℝ) (O : Set Plane)
    (G : LocalDirectedBoundaryGraph (D.region j) s i t O)
    (hO : IsOpen O) (htO : realLift ((D.region j).curve i).parametrization t ∈ O)
    (ht : (t : ParameterCircle) ∉ ((D.region j).curve i).joins)
    (p : M) (hp : p ∈ regionClosure D j)
    (hcoord : coordinates (D.chart j) p =
      realLift ((D.region j).curve i).parametrization t) :
    Nonempty (BoundarySideAt (S := S) (regionClosure D j) p) := by
  obtain ⟨b, _⟩ := regionalBoundarySideAtOfDirectedGraph_withFunction D j s i t O G hO htO ht p hp hcoord
  exact ⟨b⟩


/-- Genuine regional boundary sides are derived for every induced orientation
at every original nonjoin, in either original surface model kind. -/
theorem regionalBoundarySideAt_nonjoin
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S) (j : Fin D.regionCount)
    (s : Fin (D.region j).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region j) s)
    (i : Fin (D.region j).boundaryCount) (t : ℝ)
    (ht : (t : ParameterCircle) ∉ ((D.region j).curve i).joins)
    (p : M) (hp : p ∈ regionClosure D j)
    (hcoord : coordinates (D.chart j) p =
      realLift ((D.region j).curve i).parametrization t) :
    Nonempty (BoundarySideAt (S := S) (regionClosure D j) p) := by
  obtain ⟨A, hA⟩ := P202.BoundaryGraphDirections.twoDirectedProjectionArcs
    ((D.region j).curve i) (s i) t (hs i).1
  have hσ : s i ≠ 0 := by
    rcases (hs i).1 with h | h <;> rw [h] <;> norm_num
  obtain ⟨O, G, hO, htO, hGA⟩ := P202.BoundaryGraphDirections.localDirectedBoundaryGraph_of_arc
    (D.region j) s i t hσ (hs i).2 (A 0)
  exact regionalBoundarySideAtOfDirectedGraph D j s i t O G hO htO ht p hp hcoord

end P202.GlobalGaussBonnet.BoundaryDensities
end ActualRegionalSides


/-! CovariantTransport: derived from original regional and metric data. -/
section CovariantTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
open SmoothManifolds.BundleData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.LeviCivitaData
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}

lemma matchingChart_frame_coordinates
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet c)
    (hq : f p ∈ (tangentBundle W).baseSet d) (V : TangentSpace S p) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle W) d).basis
      ⟨f p, hq⟩).equivFun (L p V) =
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c).basis
      ⟨p, hp⟩).equivFun V := by
  rw [P202.Geometry.LeviCivita.trivializationFrame_coordinates,
    P202.Geometry.LeviCivita.trivializationFrame_coordinates]
  have hpc : p ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  have hpd : f p ∈ d.val.source := (tangentRealization W).baseSet d ▸ hq
  have he := differential_matching_coordinates f hf p (L p) (hL p)
    c.val d.val c.property d.property hpc hpd
    (by filter_upwards [c.val.open_source.mem_nhds hpc] with q hq
        exact hcoord q hq)
    (tangentStructure S).fiberCoordinates (tangentStructure W).fiberCoordinates V
  exact ((tangentRealization W).coordinates d (f p) hpd (L p V)).trans
    (he.trans ((tangentRealization S).coordinates c p hpc V).symm)

lemma matchingChart_pointDerivative_related_at
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (p : M) (hp : p ∈ c.val.source)
    (V : (q : M) → TangentSpace S q) (Z : (q : N) → TangentSpace W q)
    (hV : ∃ Y : Field S, ∀ᶠ q in 𝓝 p, Y.val q = V q)
    (hZ : ∃ Y : Field W, ∀ᶠ q in 𝓝 (f p), Y.val q = Z q)
    (hrel : ∀ᶠ q in 𝓝 p, L q (V q) = Z (f q))
    (v : TangentSpace S p) :
    L p (pointDerivative C V p v) = pointDerivative K Z (f p) (L p v) := by
  obtain ⟨X, X', hXp, hX⟩ := exists_matchingChart_related_fields f hf L hL c d hs hcoord p hp v
  obtain ⟨Y, hY⟩ := hV
  obtain ⟨Y', hY'⟩ := hZ
  have hYY : ∀ᶠ q in 𝓝 p, L q (Y.val q) = Y'.val (f q) := by
    filter_upwards [hY, (hf p).1.eventually hY', hrel] with q hq hq' hrelq
    rw [hq, hq']
    exact hrelq
  have hXp' : X'.val (f p) = L p v := by rw [← hX.self_of_nhds, hXp]
  have hCY : pointDerivative C V p = pointDerivative C Y.val p :=
    (P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle S) C Y.val V p
      ⟨Y, Eventually.of_forall (fun _ => rfl)⟩ hY).symm
  have hKZ : pointDerivative K Z (f p) = pointDerivative K Y'.val (f p) :=
    (P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle W) K Y'.val Z (f p)
      ⟨Y', Eventually.of_forall (fun _ => rfl)⟩ hY').symm
  have hCXY : pointDerivative C Y.val p (X.val p) = (C.cov X Y).val p :=
    P202.Geometry.ConnectionForms.pointDerivative_global (tangentBundle S) C Y p X
  have hKXY : pointDerivative K Y'.val (f p) (X'.val (f p)) =
      (K.cov X' Y').val (f p) :=
    P202.Geometry.ConnectionForms.pointDerivative_global (tangentBundle W) K Y' (f p) X'
  rw [← hXp', ← hXp, hCY, hKZ, hCXY, hKXY]
  exact matchingChart_connection_related_at f hf L hL g h hm c d hs hcoord C K hC hK
    X Y X' Y' p hp hX hYY


/-- The actual Levi-Civita matrices agree in matching coordinate frames,
including when the source chart is a half-space chart. -/
lemma matchingChart_connectionMatrix
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet c)
    (hq : f p ∈ (tangentBundle W).baseSet d) (v : TangentSpace S p) :
    connectionMatrix C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) c) ⟨p, hp⟩ v =
    connectionMatrix K (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle W) d) ⟨f p, hq⟩ (L p v) := by
  let bc := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let bd := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle W) d
  obtain ⟨Y, hY⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle S) bc ⟨p, hp⟩
  obtain ⟨Z, hZ⟩ := P202.Geometry.ConnectionForms.local_frame_representative
    (tangentBundle W) bd ⟨f p, hq⟩
  have hpc : p ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  have hpd : f p ∈ d.val.source := (tangentRealization W).baseSet d ▸ hq
  ext i j
  have hrel : ∀ᶠ q in 𝓝 p,
      L q (SmoothManifolds.SectionExtension.totalSection (bc.section_ j) q) =
      SmoothManifolds.SectionExtension.totalSection (bd.section_ j) (f q) := by
    filter_upwards [c.val.open_source.mem_nhds hpc] with q hcq
    have hqc : q ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hcq
    have hqd : f q ∈ (tangentBundle W).baseSet d :=
      (tangentRealization W).baseSet d ▸ hs q hcq
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hqc,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ (f q) hqd,
      P202.Geometry.LeviCivita.trivializationFrame_section,
      P202.Geometry.LeviCivita.trivializationFrame_section]
    exact differential_coordinateVector f hf L hL c d hs hcoord q hcq j
  have he := matchingChart_pointDerivative_related_at f hf L hL g h hm c d hs hcoord
    C K hC hK p hpc _ _ ⟨Y j, hY j⟩ ⟨Z j, hZ j⟩ hrel v
  change ((bc.basis ⟨p, hp⟩).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (bc.section_ j)) p v)) i =
    ((bd.basis ⟨f p, hq⟩).equivFun
    (pointDerivative K (SmoothManifolds.SectionExtension.totalSection (bd.section_ j))
      (f p) (L p v))) i
  rw [← he]
  exact (congrFun (matchingChart_frame_coordinates f hf L hL c d hs hcoord p hp hq _) i).symm

/-- Actual curve velocities commute with a genuine differential in matching
coordinates, with within derivatives allowed at parameter endpoints. -/
lemma matchingChart_velocity
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hp : γ t ∈ c.val.source) (v : TangentSpace S (γ t))
    (hv : HasVelocityWithinAt S γ J t v) :
    HasVelocityWithinAt W (f ∘ γ) J t (L (γ t) v) := by
  refine ⟨(hf (γ t)).1.comp_continuousWithinAt hv.1, d.val, d.property, hs _ hp, ?_⟩
  have hd := P202.Geometry.CurveCovariantDerivative.velocity_coordinates hv ht
    c.val c.property hp
  rw [← differential_matching_coordinates f hf (γ t) (L (γ t)) (hL (γ t))
    c.val d.val c.property d.property hp (hs _ hp)
    (by filter_upwards [c.val.open_source.mem_nhds hp] with q hq
        exact hcoord q hq)
    (tangentStructure S).fiberCoordinates (tangentStructure W).fiberCoordinates] at hd
  apply hd.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [hv.1.eventually (c.val.open_source.mem_nhds hp)] with s hsp
  exact (hcoord (γ s) hsp).symm

/-- Differentiation of a field along a curve commutes with a local isometry
in matching charts. The field need not extend to a vector field on the surface. -/
lemma matchingChart_covariantDerivativeWithin
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) (hp : γ t ∈ c.val.source)
    (X : (s : ℝ) → TangentSpace S (γ s)) (V : TangentSpace S (γ t))
    (hV : HasCovariantDerivativeWithinAt C γ X J t V) :
    HasCovariantDerivativeWithinAt K (f ∘ γ) (fun s => L (γ s) (X s)) J t
      (L (γ t) V) := by
  let bc := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let bd := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle W) d
  have hpc : γ t ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hpd : f (γ t) ∈ (tangentBundle W).baseSet d :=
    (tangentRealization W).baseSet d ▸ hs _ hp
  have hV0 := hV
  obtain ⟨v, hv, _⟩ := hV0
  obtain ⟨a, ha⟩ := P202.Geometry.CurveCovariantDerivative.exists_coefficients_deriv
    C ht hV bc hpc
  have hform := P202.Geometry.CurveCovariantDerivative.local_formula C ht hJ hV bc hpc hv ha
  have hcoef : coefficientsAlong bd (f ∘ γ) (fun s => L (γ s) (X s)) =ᶠ[𝓝[J] t]
      coefficientsAlong bc γ X := by
    filter_upwards [hv.1.eventually (c.val.open_source.mem_nhds hp)] with s hsp
    have hsc : γ s ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hsp
    have hsd : f (γ s) ∈ (tangentBundle W).baseSet d :=
      (tangentRealization W).baseSet d ▸ hs _ hsp
    rw [P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hsd,
      P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hsc]
    exact matchingChart_frame_coordinates f hf L hL c d hs hcoord (γ s) hsc hsd (X s)
  refine ⟨L (γ t) v, matchingChart_velocity f hf L hL c d hs hcoord ht hp v hv,
    _, _, bd, hpd, a, ha.congr_of_eventuallyEq_of_mem hcoef ht, ?_⟩
  rw [hform]
  apply (bd.basis ⟨f (γ t), hpd⟩).equivFun.injective
  rw [matchingChart_frame_coordinates f hf L hL c d hs hcoord (γ t) hpc hpd]
  have hmat : connectionMatrix C bc ⟨γ t, hpc⟩ v =
      connectionMatrix K bd ⟨f (γ t), hpd⟩ (L (γ t) v) :=
    matchingChart_connectionMatrix f hf L hL g h hm c d hs hcoord C K hC hK
      (γ t) hpc hpd v
  change (bc.basis ⟨γ t, hpc⟩).equivFun (frameDerivative C bc γ X t hpc v a) =
    (bd.basis ⟨f (γ t), hpd⟩).equivFun
      (frameDerivative K bd (f ∘ γ) (fun s => L (γ s) (X s)) t hpd (L (γ t) v) a)
  simp only [frameDerivative, Function.comp_apply, LinearEquiv.apply_symm_apply]
  rw [← hmat, hcoef.self_of_nhdsWithin ht]


/-- The chosen intrinsic within derivative satisfies the same naturality
identity once existence is known. -/
lemma matchingChart_covariantDerivativeWithin_eq
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) (hp : γ t ∈ c.val.source)
    (X : (s : ℝ) → TangentSpace S (γ s)) (V : TangentSpace S (γ t))
    (hV : HasCovariantDerivativeWithinAt C γ X J t V) :
    L (γ t) (covariantDerivativeWithin C γ X J t) =
      covariantDerivativeWithin K (f ∘ γ) (fun s => L (γ s) (X s)) J t := by
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C ht hJ hV,
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq K ht hJ
      (matchingChart_covariantDerivativeWithin f hf L hL g h hm c d hs hcoord
        C K hC hK ht hJ hp X V hV)]

end P202.GlobalGaussBonnet.BoundaryDensities

open P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 a M} {W : SmoothManifold 2 b N}

/-- A metric-preserving differential preserves the actual unsigned speed. -/
lemma tangentNorm_metricPreserving
    (f : M → N) (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L) (p : M) (v : TangentSpace S p) :
    tangentNorm h (f p) (L p v) = tangentNorm g p v := by
  unfold tangentNorm
  rw [hm]

/-- The normalized actual tangent is natural under a metric-preserving
map; no choice of orientation or traversal sign occurs. -/
lemma unitTangent_metricPreserving
    (f : M → N) (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (γ : ℝ → M) (v : (t : ℝ) → TangentSpace S (γ t)) (t : ℝ) :
    L (γ t) (unitTangent g γ v t) =
      unitTangent h (f ∘ γ) (fun s => L (γ s) (v s)) t := by
  simp only [unitTangent, Function.comp_apply, map_smul,
    tangentNorm_metricPreserving f L g h hm]

/-- The actual vector D_T T commutes with a metric-preserving map in
matching charts, also when a source chart meets the original smooth boundary. -/
lemma matchingChart_curvatureVector
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (γ : RegularArc g) {t : ℝ} (ht : t ∈ Ioo γ.left γ.right)
    (hp : γ.curve t ∈ c.val.source) :
    L (γ.curve t) (curvatureVector C g γ.curve γ.tangent γ.speed t) =
      curvatureVector K h (f ∘ γ.curve)
        (unitTangent h (f ∘ γ.curve) (fun s => L (γ.curve s) (γ.velocity s)))
        (fun s => tangentNorm h (f (γ.curve s)) (L (γ.curve s) (γ.velocity s))) t := by
  obtain ⟨V, hV⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative g C γ t ht
  have hn := matchingChart_covariantDerivativeWithin_eq f hf L hL g h hm c d hs hcoord
    C K hC hK (mem_univ t) uniqueDiffWithinAt_univ hp γ.tangent V hV
  have hT : (fun s => L (γ.curve s) (γ.tangent s)) =
      unitTangent h (f ∘ γ.curve) (fun s => L (γ.curve s) (γ.velocity s)) := by
    funext s
    exact unitTangent_metricPreserving f L g h hm γ.curve γ.velocity s
  simp only [curvatureVector, covariantDerivative, map_smul,
    tangentNorm_metricPreserving f L g h hm, hT] at hn ⊢
  rw [hn]
  rfl

/-- The full inward-curvature density is natural when the occupied defining
functions are genuine pullbacks. Both normals are computed from those actual
functions and the covariant derivatives are derived from the LC connections. -/
lemma matchingChart_regularArc_inwardDensity
    (f : M → N) (hf : IsSmoothMap S W f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace W (f p))
    (hL : ∀ p, IsDifferential S W f p (L p))
    (g : RiemannianMetric S) (h : RiemannianMetric W)
    (hm : IsMetricPreserving g h f L)
    (c : TangentIndex S) (d : TangentIndex W)
    (hs : ∀ p ∈ c.val.source, f p ∈ d.val.source)
    (hcoord : ∀ p ∈ c.val.source, (c.val p).val = (d.val (f p)).val)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (γ : RegularArc g) {t : ℝ} (ht : t ∈ Ioo γ.left γ.right)
    (hp : γ.curve t ∈ c.val.source)
    {D : Set M} {E : Set N}
    (B : BoundarySideAt (S := S) D (γ.curve t))
    (A : BoundarySideAt (S := W) E (f (γ.curve t)))
    (hside : B.definingFunction =ᶠ[𝓝 (γ.curve t)] A.definingFunction ∘ f) :
    inwardCurvature g (γ.curve t)
        (curvatureVector C g γ.curve γ.tangent γ.speed t) (boundaryNormal g B) * γ.speed t =
      inwardCurvature h (f (γ.curve t))
        (curvatureVector K h (f ∘ γ.curve)
          (unitTangent h (f ∘ γ.curve) (fun s => L (γ.curve s) (γ.velocity s)))
          (fun s => tangentNorm h (f (γ.curve s)) (L (γ.curve s) (γ.velocity s))) t)
        (boundaryNormal h A) *
          tangentNorm h (f (γ.curve t)) (L (γ.curve t) (γ.velocity t)) := by
  have hnormal := matchingChart_boundaryNormal g h f hf (γ.curve t) (L (γ.curve t))
    (hL (γ.curve t)) c.val d.val c.property d.property hp (hs _ hp)
    (by filter_upwards [c.val.open_source.mem_nhds hp] with q hq
        exact hcoord q hq) (hm (γ.curve t)) B A hside
  rw [← matchingChart_curvatureVector f hf L hL g h hm c d hs hcoord C K hC hK γ ht hp,
    ← hnormal]
  unfold inwardCurvature
  rw [hm, tangentNorm_metricPreserving f L g h hm]
  rfl

end P202.GlobalGaussBonnet.BoundaryDensities
end CovariantTransport


/-! The inward transverse sign determines the actual metric normal. -/
section TransverseNormal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical RealInnerProductSpace
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- A single actual inward transverse vector determines which metric normal
is inward. Its positivity is tested by the defining differential itself. -/
theorem boundaryNormal_eq_rotation_of_positive_transverse
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    {D : Set M} {p : M} (b : BoundarySideAt (S := S) D p)
    (T W : TangentSpace S p)
    (htan : scalarDerivative S b.definingFunction p T = 0)
    (hunit : pairing g p T T = 1)
    (htrans : 0 < scalarDerivative S b.definingFunction p W)
    (hpos : PositiveBoundaryOrientation o p T W) :
    boundaryNormal g b = rotation g o p T := by
  let ℓ := scalarDerivative S b.definingFunction p
  let N := boundaryNormal g b
  have hn : IsInwardUnitNormal g p ℓ N :=
    P202.Geometry.SurfaceBoundaryGeometry.normalVector_inward g p ℓ b.regular
  have hℓN : 0 < ℓ N := hn.2.2
  have hker : ℓ (W + (-(ℓ W / ℓ N)) • N) = 0 := by
    rw [map_add, map_smul]
    change ℓ W + (-(ℓ W / ℓ N)) * ℓ N = 0
    field_simp [ne_of_gt hℓN]
    ring
  have horth := hn.2.1 (W + (-(ℓ W / ℓ N)) • N) hker
  change pairing g p N (W + (-(ℓ W / ℓ N)) • N) = 0 at horth
  rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hn.1, mul_one] at horth
  have hNW : 0 < pairing g p N W := by
    have hh : 0 < ℓ W / ℓ N := div_pos htrans hℓN
    linarith
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let q := planeOrientation g o p
  have hNT : inner ℝ N T = 0 := hn.2.1 T htan
  have hNN : ‖N‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hn.1
  have hTW : 0 < q.areaForm T W :=
    (P202.Geometry.SurfaceBoundaryGeometry.orientation_bridge g p o T W).mp hpos
  have harea := q.inner_mul_areaForm_sub N T W
  rw [hNT, zero_mul, hNN, one_mul, q.areaForm_swap N T] at harea
  have hTN : 0 < q.areaForm T N := by
    have hNW' : 0 < inner ℝ N W := hNW
    nlinarith
  have hTNpos : PositiveBoundaryOrientation o p T N :=
    (P202.Geometry.SurfaceBoundaryGeometry.orientation_bridge g p o T N).mpr hTN
  exact (P202.Geometry.SurfaceBoundaryGeometry.boundary_rotation g o b T htan hunit hTNpos).1.symm

end P202.GlobalGaussBonnet.BoundaryDensities
end TransverseNormal


/-! Positive coordinate determinants give the actual tangent orientation. -/
section CoordinateOrientation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.SurfaceBoundaryData
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- A positive actual chart identifies the sign of the determinant of the
actual tangent coordinates with the source determinant-ray orientation. -/
theorem positiveBoundaryOrientation_of_coordinate_determinant
    (o : SmoothManifolds.OrientationData.Orientation S)
    (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (T W : TangentSpace S p)
    (hpos : SmoothManifolds.OrientationData.IsPositive (o.val p)
      (SmoothManifolds.OrientationData.coordinateVector K c hc ⟨p, hp⟩))
    (hdet : 0 <
      (K.equiv c hc p hp T) 0 * (K.equiv c hc p hp W) 1 -
        (K.equiv c hc p hp T) 1 * (K.equiv c hc p hp W) 0) :
    PositiveBoundaryOrientation o p T W := by
  let E := K.equiv c hc p hp
  let b : Module.Basis (Fin 2) ℝ (TangentSpace S p) :=
    (Pi.basisFun ℝ (Fin 2)).map E.symm
  have hb : b.det ![T, W] = E T 0 * E W 1 - E T 1 * E W 0 := by
    simp [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply, b, mul_comm]
  have hcoord : exteriorPower.ιMulti ℝ 2 b =
      SmoothManifolds.OrientationData.coordinateVector K c hc ⟨p, hp⟩ := rfl
  change SmoothManifolds.OrientationData.IsPositive (o.val p)
    (exteriorPower.ιMulti ℝ 2 ![T, W])
  rw [SmoothManifolds.MetricVolumeResults.wedge_basis_expansion b ![T, W], hcoord]
  apply SmoothManifolds.MetricVolumeResults.positive_smul hpos
  rw [hb]
  exact hdet

end P202.GlobalGaussBonnet.BoundaryDensities
end CoordinateOrientation

namespace P202.GlobalGaussBonnet.BoundaryDensities
open P202Specs.RegionalBoundaryDensities
open P202Specs.SurfaceRegionsEuler
open P202Specs.PlanarRegionTopology
universe u

lemma arcPresentation_joinParameters_finite {q : RegularJordanCurve}
    (A : P202Specs.PlaneTurning.ArcPresentation q) (k : Fin A.count) :
    (Ioo (0 : ℝ) 1 ∩ {t | ((A.time k.castSucc +
      (A.time k.succ - A.time k.castSucc) * t : ℝ) : ParameterCircle) ∈ q.joins}).Finite := by
  apply (arcPresentation_cutParameters_finite A k
    (q.joins.finite_toSet.image q.parametrization)).subset
  intro t ht
  exact ⟨ht.1, _, ht.2, (A.agrees k t (Ioo_subset_Icc_self ht.1)).symm⟩

theorem exceptionalParameters_finite :
    P202Specs.RegionalBoundaryDensities.Expected.exceptionalParameters_finite := by
  intro kind M _ S D j i A k
  rw [exceptionalParameters, inter_union_distrib_left]
  exact (arcPresentation_joinParameters_finite A k).union
    (region_arc_vertex_cutParameters_finite D j i A k)

/-- Literal coordinates determine the actual occupied point, without any
normal or curvature assumption and without constructing a sibling's arc. -/
lemma representsRegionalArc_point {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
    (D : RegionDecomposition S) (j : Fin D.regionCount)
    (i : Fin (D.region j).boundaryCount)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c.curve t ∈ regionClosure D j := by
  obtain ⟨p, hp, hps, hcoord⟩ := region_arc_on_graph D j i A k t ht
  have he : p = c.curve t := by
    apply (D.chart j).injOn hps (hc.2.2 t ht).1
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective
      (hcoord.trans (hc.2.2 t ht).2.symm)
  exact he ▸ hp.1

theorem regionalSide_exists : P202Specs.RegionalBoundaryDensities.Expected.regionalSide_exists := by
  intro kind M _ S g D j s hs i A k c hc t ht hn
  refine regionalBoundarySideAt_nonjoin D j s hs i
    (A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t) ?_ (c.curve t)
    (representsRegionalArc_point D j i A k c hc (Ioo_subset_Icc_self ht)) ?_
  · intro hj
    exact hn ⟨ht, Or.inl hj⟩
  · exact (hc.2.2 t (Ioo_subset_Icc_self ht)).2.trans
      (A.agrees k t (Ioo_subset_Icc_self ht))

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma curveDomain_punctured_neBot (side : CurveSide) :
    NeBot (𝓝[curveParameterSet side \ {0}] (0 : ℝ)) := by
  cases side with
  | twoSided =>
    change NeBot (𝓝[(univ : Set ℝ) \ {0}] 0)
    simpa only [sdiff_eq, univ_inter] using (inferInstance : NeBot (𝓝[≠] (0 : ℝ)))
  | forward =>
    change NeBot (𝓝[Ici (0 : ℝ) \ {0}] 0)
    rw [Ici_sdiff_left]
    infer_instance
  | backward =>
    change NeBot (𝓝[Iic (0 : ℝ) \ {0}] 0)
    rw [Iic_sdiff_right]
    infer_instance

lemma deriv_product_nonneg_of_sign_germ {f g : ℝ → ℝ} {a b : ℝ} {J : Set ℝ}
    [NeBot (𝓝[J \ {0}] (0 : ℝ))]
    (hf : HasDerivWithinAt f a J 0) (hg : HasDerivWithinAt g b J 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hsign : ∀ᶠ t in 𝓝[J] (0 : ℝ), (0 ≤ f t ↔ 0 ≤ g t)) : 0 ≤ a * b := by
  apply ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope.mp hf).mul
    (hasDerivWithinAt_iff_tendsto_slope.mp hg))
  have hs : ∀ᶠ t in 𝓝[J \ {0}] (0 : ℝ), (0 ≤ f t ↔ 0 ≤ g t) :=
    hsign.filter_mono (nhdsWithin_mono 0 sdiff_subset)
  filter_upwards [hs] with t ht
  simp only [slope_def_field, hf0, hg0, sub_zero]
  rw [← mul_div_mul_comm]
  apply div_nonneg _ (mul_self_nonneg t)
  by_cases h : 0 ≤ f t
  · exact mul_nonneg h (ht.mp h)
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h) (le_of_not_ge (mt ht.mpr h))

/-- Equal occupied germs determine equal metric inward normals, including
at original boundary points. The proof uses an available one-sided realizing
curve and the product of its slopes, rather than arbitrary forward directions. -/
theorem boundaryNormal_eq_of_same_germ (g : RiemannianMetric S)
    {D E : Set M} {p : M}
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p)
    (hsets : D =ᶠ[𝓝 p] E) : boundaryNormal g a = boundaryNormal g b := by
  have hprod (v : TangentSpace S p) :
      0 ≤ scalarDerivative S b.definingFunction p v *
        scalarDerivative S a.definingFunction p v := by
    obtain ⟨side, c, hc⟩ := SmoothManifolds.every_derivation_is_curve_velocity S p v
    haveI := curveDomain_punctured_neBot side
    have hd (F : M → ℝ)
        (hF : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
          S.smoothStructure.val F p) :
        HasDerivWithinAt (F ∘ c) (scalarDerivative S F p v) (curveParameterSet side) 0 := by
      apply hc.2 (scalarGerm S F p) F
      simp only [scalarGerm, dite_eq_left hF]
    have hct : Tendsto c (𝓝[curveParameterSet side] (0 : ℝ)) (𝓝 p) := by
      simpa only [ContinuousWithinAt, hc.1.1] using hc.1.2.1
    apply deriv_product_nonneg_of_sign_germ
      (hd b.definingFunction (b.smooth p b.contains))
      (hd a.definingFunction (a.smooth p a.contains))
      (by simp only [Function.comp_apply, hc.1.1, b.vanishes])
      (by simp only [Function.comp_apply, hc.1.1, a.vanishes])
    filter_upwards [hct.eventually (b.isOpen.mem_nhds b.contains),
      hct.eventually (a.isOpen.mem_nhds a.contains), hct.eventually hsets] with t hbt hat hset
    exact (b.region (c t) hbt).symm.trans ((iff_of_eq hset).trans (a.region (c t) hat))
  have hinc : ∀ v : TangentSpace S p,
      0 < scalarDerivative S b.definingFunction p v →
        0 ≤ scalarDerivative S a.definingFunction p v := by
    intro v hv
    nlinarith [hprod v]
  obtain ⟨r, hr, he⟩ := conormal_pos_smul_of_halfspace_inclusion (V := TangentSpace S p)
    (scalarDerivative S b.definingFunction p) (scalarDerivative S a.definingFunction p)
    b.regular a.regular hinc
  exact boundaryNormal_eq_of_pos_smul g b a r hr he

theorem inwardCurvature_eq_of_same_side (g : RiemannianMetric S)
    {D : Set M} {p q : M} (hp : p = q)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) D q)
    (V : TangentSpace S p) (W : TangentSpace S q) (hV : HEq V W) :
    inwardCurvature g p V (boundaryNormal g b) = inwardCurvature g q W (boundaryNormal g a) := by
  subst q
  have hVW : V = W := eq_of_heq hV
  rw [hVW, boundaryNormal_eq_of_same_germ g b a (Eventually.of_forall (fun _ => rfl))]

theorem regularArc_inwardDensity_reparam :
    P202Specs.RegionalBoundaryDensities.Expected.regularArc_inwardDensity_reparam := by
  intro kind M _ S g C c d φ l r s hs hsub hmaps hi hder hcurve D b a
  have he := inwardCurvature_eq_of_same_side g (hcurve s hs).symm b a _ _
    (regularArc_curvatureVector_reparam C c d φ hs hsub hmaps hi hder hcurve)
  have hspeed := regularArc_speed_transition c d φ s (deriv φ s)
    (hsub hs) (hmaps hs) (hder s hs) (by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      exact hcurve t ht)
  rw [he, hspeed]
  ring

end P202.GlobalGaussBonnet.BoundaryDensities
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma inwardCurvature_cancel_at_equal_point (g : RiemannianMetric S)
    {D E : Set M} {p q : M} (hp : p = q)
    (hpint : p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E q)
    (hdisj : Disjoint (interior D) (interior E))
    (V : TangentSpace S p) (W : TangentSpace S q) (hV : HEq V W) :
    inwardCurvature g p V (boundaryNormal g b) +
      inwardCurvature g q W (boundaryNormal g a) = 0 := by
  subst q
  have he : V = W := eq_of_heq hV
  subst W
  exact inwardCurvature_cancel_of_disjoint_interiors g hpint b a hdisj V

/-- Two genuine smooth sides of distinct occupied regions cancel at a
matched arc point. The curvature vectors and normals are derived from the
curves and defining functions, and both traversal directions are allowed. -/
theorem regularArc_inwardCurvature_cancel {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hi : InjOn φ (Ioo l r))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x)
    {D E : Set M}
    (b : BoundarySideAt (S := S) D (c.curve s))
    (a : BoundarySideAt (S := S) E (d.curve (φ s)))
    (hdisj : Disjoint (interior D) (interior E))
    (hpint : c.curve s ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    inwardCurvature g (c.curve s)
        (curvatureVector C g c.curve c.tangent c.speed s) (boundaryNormal g b) +
      inwardCurvature g (d.curve (φ s))
        (curvatureVector C g d.curve d.tangent d.speed (φ s)) (boundaryNormal g a) = 0 := by
  exact inwardCurvature_cancel_at_equal_point g (hcurve s hs).symm hpint b a hdisj _ _
    (regularArc_curvatureVector_reparam C c d φ hs hsub hmaps hi hder hcurve)

/-- The same cancellation holds for the actual unsigned arc-length densities,
with the absolute transition derivative supplied by genuine velocities. -/
theorem regularArc_inwardDensity_cancel {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ} (hs : s ∈ Ioo l r)
    (hsub : Ioo l r ⊆ Ioo c.left c.right)
    (hmaps : MapsTo φ (Ioo l r) (Ioo d.left d.right))
    (hi : InjOn φ (Ioo l r))
    (hder : ∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x)
    (hcurve : ∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x)
    {D E : Set M}
    (b : BoundarySideAt (S := S) D (c.curve s))
    (a : BoundarySideAt (S := S) E (d.curve (φ s)))
    (hdisj : Disjoint (interior D) (interior E))
    (hpint : c.curve s ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S) :
    inwardCurvature g (c.curve s)
        (curvatureVector C g c.curve c.tangent c.speed s) (boundaryNormal g b) * c.speed s +
      inwardCurvature g (d.curve (φ s))
        (curvatureVector C g d.curve d.tangent d.speed (φ s)) (boundaryNormal g a) *
          d.speed (φ s) * |deriv φ s| = 0 := by
  have hzero := regularArc_inwardCurvature_cancel C c d φ hs hsub hmaps hi hder hcurve b a hdisj hpint
  have hspeed := regularArc_speed_transition c d φ s (deriv φ s)
    (hsub hs) (hmaps hs) (hder s hs) (by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
      exact hcurve x hx)
  rw [hspeed]
  have hz := congrArg (fun z : ℝ => z * (|deriv φ s| * d.speed (φ s))) hzero
  convert hz using 1 <;> ring

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
open P202Specs.PlanarRegionTopology P202Specs.BoundaryGraphDirections
open P202.PlanarRegionTopology P202.BoundaryGraphDirections

/-- The actual directed graph, not a normal assumption, determines the
annihilated tangent and strictly positive induced left-normal conormal. -/
theorem localDirectedBoundaryGraph_conormal_sign {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O)
    (ht : (t : ParameterCircle) ∉ (R.curve i).joins) :
    DifferentiableAt ℝ (graphDefiningFunction G) (realLift (R.curve i).parametrization t) ∧
    fderiv ℝ (graphDefiningFunction G) (realLift (R.curve i).parametrization t)
      (deriv (realLift (R.curve i).parametrization) t) = 0 ∧
    0 < fderiv ℝ (graphDefiningFunction G) (realLift (R.curve i).parametrization t)
      (s i • quarterTurn (deriv (realLift (R.curve i).parametrization) t)) := by
  let γ := realLift (R.curve i).parametrization
  let Z := graphDefiningFunction G
  obtain ⟨J, hJ, htJ, hh⟩ := localDirectedBoundaryGraph_height_smooth G ht
  have hheight : DifferentiableAt ℝ G.height (inner ℝ G.arc.axis (γ t)) :=
    (hh.contDiffAt (hJ.mem_nhds htJ)).differentiableAt (by simp)
  have hd := (innerSL ℝ (quarterTurn G.arc.axis)).hasFDerivAt.sub
    (hheight.hasFDerivAt.comp (γ t) (innerSL ℝ G.arc.axis).hasFDerivAt)
  change HasFDerivAt Z _ (γ t) at hd
  have hZ : DifferentiableAt ℝ Z (γ t) := hd.differentiableAt
  have hzero : ∀ᶠ u in 𝓝 t, Z (γ u) = 0 := by
    filter_upwards [Icc_mem_nhds
      (show t - G.arc.radius < t by linarith [G.arc.radius_pos])
      (show t < t + G.arc.radius by linarith [G.arc.radius_pos])] with u hu
    have he := congrArg (fun x => inner ℝ (quarterTurn G.arc.axis) x) (G.arc_identity u hu)
    exact sub_eq_zero.mpr (by
      simpa only [graph_frame_vertical G.arc.unit_axis G.frame,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, arcProjection, γ] using he)
  have htan := defining_function_tangent_zero (R.curve i) t ht Z hZ hzero
  have hunit : fderiv ℝ Z (γ t) (quarterTurn G.arc.axis) = 1 := by
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply,
      P202.BoundaryGraphDirections.inner_self_quarterTurn,
      quarterTurn_inner, real_inner_self_eq_norm_sq, G.arc.unit_axis]
  have hγ := ((R.curve i).smooth_off_joins t ht).differentiableAt (by simp)
  have hleft : DifferentiableAt ℝ G.arc.leftExtension t :=
    (G.arc.left_smooth.contDiffAt (isOpen_Ioo.mem_nhds
      ⟨by linarith [G.arc.radius_pos, G.arc.radius_lt],
        by linarith [G.arc.radius_pos, G.arc.radius_lt]⟩)).differentiableAt (by simp)
  have hder := deriv_eq_of_eqOn_left G.arc.radius_pos hleft hγ G.arc.left_eq
  have hproj := G.arc.left_positive t ⟨by linarith [G.arc.radius_pos], le_rfl⟩
  rw [hder] at hproj
  have htrans : 0 < inner ℝ (quarterTurn G.arc.axis) (quarterTurn (s i • deriv γ t)) := by
    simpa only [quarterTurn_smul, inner_smul_right, quarterTurn_inner] using hproj
  refine ⟨hZ, htan, ?_⟩
  have htan' : fderiv ℝ Z (γ t) (s i • deriv γ t) = 0 := by rw [map_smul, htan, smul_zero]
  have hp := left_normal_covector_positive (fderiv ℝ Z (γ t))
    (s i • deriv γ t) (quarterTurn G.arc.axis) htrans htan' hunit
  simpa only [quarterTurn_smul] using hp

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The original presentation may be arbitrary. Its genuine inward normal
agrees with that of any occupied region containing a surface neighborhood. -/
theorem boundaryNormal_eq_presentationNormal_of_mem_nhds
    (g : RiemannianMetric S) (B : BoundaryPresentation g) (i : Fin B.count)
    {t : ℝ} (ht : t ∈ Ioo (B.arc i).left (B.arc i).right)
    {D : Set M} (b : BoundarySideAt (S := S) D ((B.arc i).curve t))
    (hD : D ∈ 𝓝 ((B.arc i).curve t)) :
    boundaryNormal g b = boundaryNormal g (B.side i t ht) := by
  apply boundaryNormal_eq_surfaceNormal_of_mem_nhds g _ b (B.side i t ht) hD
  rw [B.covers]
  exact mem_iUnion.mpr ⟨i, t, Ioo_subset_Icc_self ht, rfl⟩

end P202.GlobalGaussBonnet.BoundaryDensities


/-! Specialization to every original regional chart geometry and literal arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
  {D : RegionDecomposition S} {j : Fin D.regionCount}

def regionalInclusionEquiv (G : RegionalChartGeometry g D j) (p : G.neighborhood) :
    TangentSpace G.restriction p ≃ₗ[ℝ] TangentSpace S p.val :=
  ((tangentStructure G.restriction).fiberCoordinates.equiv G.restrictedChart
    G.restrictedChart_mem p (by rw [G.restrictedChart_source]; trivial)).trans
    ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j) p.val
      (G.source_subset p.property)).symm

theorem regionalInclusionEquiv_apply (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) (v : TangentSpace G.restriction p) :
    regionalInclusionEquiv G p v = G.inclusion.differential p v := by
  apply ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j) p.val
    (G.source_subset p.property)).injective
  rw [show (tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
      p.val (G.source_subset p.property) (G.inclusion.differential p v) =
      (tangentStructure G.restriction).fiberCoordinates.equiv G.restrictedChart
        G.restrictedChart_mem p (by rw [G.restrictedChart_source]; trivial) v from
    differential_matching_coordinates Subtype.val G.inclusion.smooth p
      (G.inclusion.differential p) (G.inclusion.isDifferential p)
      G.restrictedChart (D.chart j) G.restrictedChart_mem (D.chart_mem j)
      (by rw [G.restrictedChart_source]; trivial) (G.source_subset p.property)
      (Eventually.of_forall (fun q => congrArg Subtype.val (G.restrictedChart_eq q)))
      (tangentStructure G.restriction).fiberCoordinates
      (tangentStructure S).fiberCoordinates v]
  exact LinearEquiv.apply_symm_apply _ _

def regionalTangentEquiv (G : RegionalChartGeometry g D j) (p : G.neighborhood) :
    TangentSpace S p.val ≃ₗ[ℝ] TangentSpace G.ambientSurface (G.map p) :=
  ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j) p.val
    (G.source_subset p.property)).trans
    ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
      G.ambientChart_mem (G.map p) (by rw [G.ambientChart_source]; trivial)).symm

theorem regionalTangentEquiv_inclusion (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) (v : TangentSpace G.restriction p) :
    regionalTangentEquiv G p (G.inclusion.differential p v) = G.immersion.differential p v := by
  apply ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
    G.ambientChart_mem (G.map p) (by rw [G.ambientChart_source]; trivial)).injective
  have hi := congrArg
    ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j) p.val
      (G.source_subset p.property)) (regionalInclusionEquiv_apply G p v)
  have hj := differential_matching_coordinates G.map G.immersion.smooth p
    (G.immersion.differential p) (G.immersion.isDifferential p)
    G.restrictedChart G.ambientChart G.restrictedChart_mem G.ambientChart_mem
    (by rw [G.restrictedChart_source]; trivial)
    (by rw [G.ambientChart_source]; trivial)
    (Eventually.of_forall G.matching_coordinates)
    (tangentStructure G.restriction).fiberCoordinates
    (tangentStructure G.ambientSurface).fiberCoordinates v
  simp only [regionalInclusionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at hi
  simpa only [regionalTangentEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply] using hi.symm.trans hj.symm

theorem regionalTangentEquiv_pairing (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) (v w : TangentSpace S p.val) :
    pairing G.metric (G.map p) (regionalTangentEquiv G p v) (regionalTangentEquiv G p w) =
      pairing g p.val v w := by
  obtain ⟨v, rfl⟩ := (regionalInclusionEquiv G p).surjective v
  obtain ⟨w, rfl⟩ := (regionalInclusionEquiv G p).surjective w
  simp only [regionalInclusionEquiv_apply, regionalTangentEquiv_inclusion]
  exact G.metric_preserving p v w



theorem regionalTangentEquiv_coordinates (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) (v : TangentSpace S p.val) :
    (tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
      G.ambientChart_mem (G.map p) (by rw [G.ambientChart_source]; trivial)
        (regionalTangentEquiv G p v) =
      (tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j) p.val
        (G.source_subset p.property) v := by
  exact LinearEquiv.apply_symm_apply _ _

theorem regionalChartGeometry_coordinates (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) :
    coordinates (D.chart j) p.val = coordinates G.ambientChart (G.map p) := by
  exact congrArg (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ((congrArg Subtype.val (G.restrictedChart_eq p)).symm.trans (G.matching_coordinates p))

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
open P202Specs.BoundaryGraphDirections P202Specs.PlanarRegionTopology
open P202.BoundaryGraphDirections P202.PlanarRegionTopology
universe u

/-- The actual planar carrier defines a genuine side in every ambient chart.
The defining function is the literal graph function in that chart. -/
theorem ambientBoundarySideAtOfDirectedGraph_withFunction
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (Q : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O)
    (htO : realLift (R.curve i).parametrization t ∈ O)
    (ht : (t : ParameterCircle) ∉ (R.curve i).joins)
    (p : M) (hp : p ∈ c.source)
    (hcoord : coordinates c p = realLift (R.curve i).parametrization t) :
    ∃ b : BoundarySideAt (S := S) {q | coordinates c q ∈ R.carrier} p,
      b.definingFunction = fun q => graphDefiningFunction Q (coordinates c q) := by
  obtain ⟨J, hJ, htJ, hheight⟩ := localDirectedBoundaryGraph_height_smooth Q ht
  let E := EuclideanSpace.equiv (Fin 2) ℝ
  let coord : M → Plane := coordinates c
  let W : Set Plane := O ∩ {x | inner ℝ Q.arc.axis x ∈ J}
  have hW : IsOpen W := hO.inter (hJ.preimage (by fun_prop))
  let N : Set M := c.source ∩ coord ⁻¹' W
  have hcont : ContinuousOn coord c.source :=
    E.symm.continuous.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn c.continuousOn)
  have hN : IsOpen N := hcont.isOpen_inter_preimage c.open_source hW
  have hpN : p ∈ N := by
    refine ⟨hp, ?_⟩
    change coordinates c p ∈ W
    rw [hcoord]
    exact ⟨htO, htJ⟩
  have hNJ : ∀ q ∈ N, inner ℝ Q.arc.axis (coord q) ∈ J := fun _ hq => hq.2.2
  have hzero : inner ℝ (quarterTurn Q.arc.axis) (coord p) =
      Q.height (inner ℝ Q.arc.axis (coord p)) := by
    have hh := congrArg (fun z => inner ℝ (quarterTurn Q.arc.axis) z)
      (Q.arc_identity t ⟨by linarith [Q.arc.radius_pos], by linarith [Q.arc.radius_pos]⟩)
    rw [graph_frame_vertical Q.arc.unit_axis Q.frame] at hh
    change inner ℝ (quarterTurn Q.arc.axis)
      (realLift (R.curve i).parametrization t) =
      Q.height (inner ℝ Q.arc.axis (realLift (R.curve i).parametrization t)) at hh
    change inner ℝ (quarterTurn Q.arc.axis) (coordinates c p) =
      Q.height (inner ℝ Q.arc.axis (coordinates c p))
    rw [hcoord]
    exact hh
  have hside : ∀ q ∈ N, q ∈ {q | coordinates c q ∈ R.carrier} ↔
      Q.height (inner ℝ Q.arc.axis (coord q)) ≤ inner ℝ (quarterTurn Q.arc.axis) (coord q) := by
    intro q hq
    have hcar := localDirectedBoundaryGraph_carrier Q hO
    have he : coord q ∈ R.carrier ↔ coord q ∈ Q.frame.map '' {z : Plane | Q.height (z 0) ≤ z 1} := by
      constructor
      · intro hx
        have hh : coord q ∈ R.carrier ∩ O := ⟨hx, hq.2.1⟩
        rw [hcar] at hh
        exact hh.1
      · intro hx
        have hh : coord q ∈ (Q.frame.map '' {z : Plane | Q.height (z 0) ≤ z 1}) ∩ O := ⟨hx, hq.2.1⟩
        rw [← hcar] at hh
        exact hh.1
    exact he.trans (graph_frame_epigraph Q.arc.unit_axis Q.frame Q.height (coord q))
  refine ⟨boundarySideOfPlaneGraph c hc N hN hpN inter_subset_left
    Q.arc.axis Q.arc.unit_axis Q.height J hJ hNJ hheight hzero hside, rfl⟩

/-- The graph conormal is smooth on an open coordinate neighborhood. -/
theorem graphDefiningFunction_contDiffAt {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (Q : LocalDirectedBoundaryGraph R s i t O)
    (ht : (t : ParameterCircle) ∉ (R.curve i).joins) :
    ∃ U : Set Plane, IsOpen U ∧ realLift (R.curve i).parametrization t ∈ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (graphDefiningFunction Q) U := by
  obtain ⟨J, hJ, htJ, hh⟩ := localDirectedBoundaryGraph_height_smooth Q ht
  refine ⟨{x | inner ℝ Q.arc.axis x ∈ J}, hJ.preimage (by fun_prop), htJ, ?_⟩
  exact (innerSL ℝ (quarterTurn Q.arc.axis)).contDiff.contDiffOn.sub
    (hh.comp (innerSL ℝ Q.arc.axis).contDiff.contDiffOn (fun _ hx => hx))

/-- The literal plane chart formula for a scalar differential. -/
theorem scalarDerivative_plane_chart_function
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M}
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (F : Plane → ℝ)
    (U : Set Plane) (hU : IsOpen U) (hpU : coordinates c p ∈ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) (V : TangentSpace S p) :
    scalarDerivative S (fun q => F (coordinates c q)) p V =
      fderiv ℝ F (coordinates c p)
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          (SmoothManifolds.coordinateDerivationEquiv S p c hc hp V)) := by
  let E := EuclideanSpace.equiv (Fin 2) ℝ
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (F ∘ E.symm) (E.symm ⁻¹' U) :=
    hF.comp E.symm.contDiff.contDiffOn (fun _ hx => hx)
  have he := scalarDerivative_chart_function c hc p hp (F ∘ E.symm)
    (E.symm ⁻¹' U) (hU.preimage E.symm.continuous) hpU hcomp V
  have hd : DifferentiableAt ℝ F (E.symm (c p).val) :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  rw [fderiv_comp (c p).val hd E.symm.differentiableAt] at he
  simpa only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, E, coordinates, toPlane] using he


/-- In a positive chart, the actual occupied graph side has exactly the induced
signed rotation normal. The tangent is any positive multiple of the original
Jordan velocity; the defining function and its sign are derived from the graph. -/
theorem ambientDirectedGraph_boundaryNormal
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpositive : P202Specs.ChartRegionStokes.PositiveChart
      (P202.VolumeData.cotangentBundle S) o c hc)
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    (hs : IsInducedBoundaryOrientation R s)
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (Q : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O)
    (htO : realLift (R.curve i).parametrization t ∈ O)
    (ht : (t : ParameterCircle) ∉ (R.curve i).joins)
    (p : M) (hp : p ∈ c.source)
    (hcoord : coordinates c p = realLift (R.curve i).parametrization t)
    (V : TangentSpace S p) (a : ℝ) (ha : 0 < a)
    (hV : SmoothManifolds.coordinateDerivationEquiv S p c hc hp V =
      (EuclideanSpace.equiv (Fin 2) ℝ)
        (a • deriv (realLift (R.curve i).parametrization) t)) :
    ∃ b : BoundarySideAt (S := S) {q | coordinates c q ∈ R.carrier} p,
      b.definingFunction = (fun q => graphDefiningFunction Q (coordinates c q)) ∧
      boundaryNormal g b = s i • rotation g o p ((tangentNorm g p V)⁻¹ • V) := by
  obtain ⟨b, hb⟩ := ambientBoundarySideAtOfDirectedGraph_withFunction c hc Q hO htO ht p hp hcoord
  refine ⟨b, hb, ?_⟩
  let E := EuclideanSpace.equiv (Fin 2) ℝ
  let C := SmoothManifolds.coordinateDerivationEquiv S p c hc hp
  let K := (tangentStructure S).fiberCoordinates
  let z := deriv (realLift (R.curve i).parametrization) t
  have hCV : C V = E (a • z) := hV
  let n := tangentNorm g p V
  let T := s i • (n⁻¹ • V)
  let W := C.symm (E (s i • quarterTurn z))
  obtain ⟨U, hU, htU, hZ⟩ := graphDefiningFunction_contDiffAt Q ht
  obtain ⟨_, htanZ, htransZ⟩ := localDirectedBoundaryGraph_conormal_sign Q ht
  have hz : z ≠ 0 := by
    intro hz
    change 0 < fderiv ℝ (graphDefiningFunction Q)
      (realLift (R.curve i).parametrization t) (s i • quarterTurn z) at htransZ
    have hqzero : quarterTurn (0 : Plane) = 0 := by
      ext j
      fin_cases j <;> simp [quarterTurn]
    rw [hz, hqzero, smul_zero, map_zero] at htransZ
    exact (lt_irrefl 0) htransZ
  have hVne : V ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hV
    have hzero' : a • z = 0 := E.injective (by simpa only [map_zero] using hV.symm)
    exact hz ((smul_eq_zero.mp hzero').resolve_left (ne_of_gt ha))
  have hn : 0 < n := Real.sqrt_pos.mpr (g.positive p V hVne)
  have hss : s i * s i = 1 := by
    rcases (hs i).1 with h | h <;> rw [h] <;> norm_num
  have hder (X : TangentSpace S p) :
      scalarDerivative S b.definingFunction p X =
        fderiv ℝ (graphDefiningFunction Q) (realLift (R.curve i).parametrization t)
          (E.symm (C X)) := by
    rw [hb, scalarDerivative_plane_chart_function c hc p hp
      (graphDefiningFunction Q) U hU (by rw [hcoord]; exact htU) hZ X, hcoord]
  have htanZ' : fderiv ℝ (graphDefiningFunction Q)
      (realLift (R.curve i).parametrization t) z = 0 := htanZ
  have htan : scalarDerivative S b.definingFunction p T = 0 := by
    rw [hder]
    simp only [T, map_smul, hCV, E.symm_apply_apply, htanZ', smul_zero]
  have htrans : 0 < scalarDerivative S b.definingFunction p W := by
    rw [hder]
    simpa only [W, LinearEquiv.apply_symm_apply, E.symm_apply_apply] using htransZ
  have hunit0 : pairing g p (n⁻¹ • V) (n⁻¹ • V) = 1 := by
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      ← P202.Geometry.SmoothMetrics.tangentNorm_sq g p V]
    change n⁻¹ * (n⁻¹ * n ^ 2) = 1
    field_simp [ne_of_gt hn]
  have hunit : pairing g p T T = 1 := by
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hunit0, mul_one]
    exact hss
  have hKC (X : TangentSpace S p) : K.equiv c hc p hp X = C X :=
    SmoothManifolds.chartCoordinates_eq S p c hc hp (K.equiv c hc p hp)
      (K.isCoordinates c hc p hp) X
  have hTcoord : K.equiv c hc p hp T = E ((s i * n⁻¹ * a) • z) := by
    rw [hKC]
    simp only [T, map_smul, hCV]
    simp only [map_smul, smul_smul, mul_assoc]
  have hWcoord : K.equiv c hc p hp W = E (s i • quarterTurn z) := by
    rw [hKC]
    exact C.apply_symm_apply _
  have hzs : 0 < z 0 ^ 2 + z 1 ^ 2 := by
    by_contra h
    have h0 : z 0 = 0 := by nlinarith [sq_nonneg (z 1)]
    have h1 : z 1 = 0 := by nlinarith [sq_nonneg (z 0)]
    apply hz
    ext j
    fin_cases j <;> simp_all
  have hpos : PositiveBoundaryOrientation o p T W := by
    apply positiveBoundaryOrientation_of_coordinate_determinant o K c hc p hp T W
      (hpositive ⟨p, hp⟩)
    rw [hTcoord, hWcoord]
    change 0 < ((s i * n⁻¹ * a) * z 0) * (s i * z 0) -
      ((s i * n⁻¹ * a) * z 1) * (s i * (-z 1))
    have he : ((s i * n⁻¹ * a) * z 0) * (s i * z 0) -
        ((s i * n⁻¹ * a) * z 1) * (s i * (-z 1)) =
        (s i * s i) * (n⁻¹ * a) * (z 0 ^ 2 + z 1 ^ 2) := by ring
    rw [he, hss, one_mul]
    exact mul_pos (mul_pos (inv_pos.mpr hn) ha) hzs
  have he := boundaryNormal_eq_rotation_of_positive_transverse g o b T W htan hunit htrans hpos
  simpa only [T, map_smul] using he

end P202.GlobalGaussBonnet.BoundaryDensities

namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
  {D : RegionDecomposition S} {j : Fin D.regionCount}

theorem regionalTangentEquiv_scalarDerivative (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) (F : Plane → ℝ) (U : Set Plane) (hU : IsOpen U)
    (hpU : coordinates (D.chart j) p.val ∈ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (v : TangentSpace S p.val) :
    scalarDerivative G.ambientSurface (fun q => F (coordinates G.ambientChart q))
        (G.map p) (regionalTangentEquiv G p v) =
      scalarDerivative S (fun q => F (coordinates (D.chart j) q)) p.val v := by
  have hq : G.map p ∈ G.ambientChart.source := by rw [G.ambientChart_source]; trivial
  rw [scalarDerivative_plane_chart_function G.ambientChart G.ambientChart_mem
      (G.map p) hq F U hU (by rwa [← regionalChartGeometry_coordinates G p]) hF,
    scalarDerivative_plane_chart_function (D.chart j) (D.chart_mem j) p.val
      (G.source_subset p.property) F U hU hpU hF]
  rw [← SmoothManifolds.chartCoordinates_eq G.ambientSurface (G.map p)
      G.ambientChart G.ambientChart_mem hq
      ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
        G.ambientChart_mem (G.map p) hq)
      ((tangentStructure G.ambientSurface).fiberCoordinates.isCoordinates
        G.ambientChart G.ambientChart_mem (G.map p) hq),
    ← SmoothManifolds.chartCoordinates_eq S p.val (D.chart j) (D.chart_mem j)
      (G.source_subset p.property)
      ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
        p.val (G.source_subset p.property))
      ((tangentStructure S).fiberCoordinates.isCoordinates
        (D.chart j) (D.chart_mem j) p.val (G.source_subset p.property)),
    regionalTangentEquiv_coordinates, regionalChartGeometry_coordinates]

theorem regionalTangentEquiv_boundaryNormal (G : RegionalChartGeometry g D j)
    (p : G.neighborhood) {B : Set M} {A : Set (ULift.{u} G.ambientDomain)}
    (b : BoundarySideAt (S := S) B p.val)
    (a : BoundarySideAt (S := G.ambientSurface) A (G.map p))
    (F : Plane → ℝ) (U : Set Plane) (hU : IsOpen U)
    (hpU : coordinates (D.chart j) p.val ∈ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hb : b.definingFunction = fun q => F (coordinates (D.chart j) q))
    (ha : a.definingFunction = fun q => F (coordinates G.ambientChart q)) :
    regionalTangentEquiv G p (boundaryNormal g b) = boundaryNormal G.metric a := by
  apply normalVector_metricPreserving g G.metric p.val (G.map p)
    (regionalTangentEquiv G p).toLinearMap (regionalTangentEquiv G p).surjective
    (regionalTangentEquiv_pairing G p) _ _ b.regular
  intro v
  rw [hb, ha]
  exact regionalTangentEquiv_scalarDerivative G p F U hU hpU hF v

end P202.GlobalGaussBonnet.BoundaryDensities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology Classical BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.DifferentialData SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
open SmoothManifolds.BundleData SmoothManifolds.FrameData
open P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.LeviCivitaData
open P202.SurfaceBoundaryData P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.SurfaceRegionsEuler
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
lemma regional_connectionMatrix {g : RiemannianMetric S}
    {D : RegionDecomposition S} {j : Fin D.regionCount}
    (G : RegionalChartGeometry g D j)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (p : G.neighborhood) (v : TangentSpace G.restriction p)
    (hp : p.val ∈ (tangentBundle S).baseSet ⟨D.chart j, D.chart_mem j⟩)
    (hq : G.map p ∈ (tangentBundle G.ambientSurface).baseSet
      ⟨G.ambientChart, G.ambientChart_mem⟩) :
    connectionMatrix C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) ⟨D.chart j, D.chart_mem j⟩) ⟨p.val, hp⟩
      (G.inclusion.differential p v) =
    connectionMatrix G.connection (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle G.ambientSurface) ⟨G.ambientChart, G.ambientChart_mem⟩)
      ⟨G.map p, hq⟩ (G.immersion.differential p v) := by
  let gR := P202.Geometry.SmoothMetrics.pullbackMetric g Subtype.val G.inclusion
  obtain ⟨CR, hCR, _⟩ := P202.Geometry.LeviCivita.exists_unique gR
  have hpr : p ∈ (tangentBundle G.restriction).baseSet
      ⟨G.restrictedChart, G.restrictedChart_mem⟩ := by
    rw [(tangentRealization G.restriction).baseSet]
    rw [G.restrictedChart_source]
    trivial
  have hi := matchingChart_connectionMatrix Subtype.val G.inclusion.smooth G.inclusion.differential
    G.inclusion.isDifferential gR g (fun _ _ _ => rfl)
    ⟨G.restrictedChart, G.restrictedChart_mem⟩ ⟨D.chart j, D.chart_mem j⟩
    (fun q _ => G.source_subset q.property)
    (fun q _ => congrArg Subtype.val (G.restrictedChart_eq q))
    CR C hCR hC p hpr hp v
  have hj := matchingChart_connectionMatrix G.map G.immersion.smooth G.immersion.differential
    G.immersion.isDifferential gR G.metric G.metric_preserving
    ⟨G.restrictedChart, G.restrictedChart_mem⟩ ⟨G.ambientChart, G.ambientChart_mem⟩
    (fun q _ => by rw [G.ambientChart_source]; trivial)
    (fun q _ => G.matching_coordinates q)
    CR G.connection hCR G.connection_LC p hpr hq v
  exact hi.symm.trans hj

end P202.GlobalGaussBonnet.BoundaryDensities
namespace P202.GlobalGaussBonnet.BoundaryDensities
universe u
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {W : SmoothManifold n b N}
lemma covariantDerivative_of_matching_coefficients
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle W))
    {U : Set M} {hU : IsOpen U} (bc : LocalFrame (tangentBundle S) U hU)
    {V : Set N} {hV : IsOpen V} (bd : LocalFrame (tangentBundle W) V hV)
    (γ : ℝ → M) (δ : ℝ → N)
    (X : (s : ℝ) → TangentSpace S (γ s))
    (Y : (s : ℝ) → TangentSpace W (δ s)) (t : ℝ)
    (hp : γ t ∈ U) (hq : δ t ∈ V)
    (L : TangentSpace S (γ t) →ₗ[ℝ] TangentSpace W (δ t))
    (hframe : ∀ Z, (bd.basis ⟨δ t, hq⟩).equivFun (L Z) =
      (bc.basis ⟨γ t, hp⟩).equivFun Z)
    (v : TangentSpace S (γ t)) (w : TangentSpace W (δ t))
    (hv : HasVelocityWithinAt S γ univ t v)
    (hw : HasVelocityWithinAt W δ univ t w)
    (hmat : connectionMatrix C bc ⟨γ t, hp⟩ v =
      connectionMatrix K bd ⟨δ t, hq⟩ w)
    (hcoef : coefficientsAlong bd δ Y =ᶠ[𝓝 t] coefficientsAlong bc γ X)
    (Z : TangentSpace S (γ t)) (hZ : HasCovariantDerivativeAt C γ X t Z) :
    L (covariantDerivative C γ X t) = covariantDerivative K δ Y t := by
  obtain ⟨z', hz⟩ := P202.Geometry.CurveCovariantDerivative.exists_coefficients_deriv
    C (mem_univ t) hZ bc hp
  have hform := P202.Geometry.CurveCovariantDerivative.local_formula C (mem_univ t)
    uniqueDiffWithinAt_univ hZ bc hp hv hz
  have hz' : HasDerivWithinAt (coefficientsAlong bd δ Y) z' univ t := by
    exact hz.congr_of_eventuallyEq_of_mem (by simpa only [nhdsWithin_univ] using hcoef) (mem_univ t)
  have htarg : HasCovariantDerivativeAt K δ Y t (L Z) := by
    refine ⟨w, hw, V, hV, bd, hq, z', hz', ?_⟩
    apply (bd.basis ⟨δ t, hq⟩).equivFun.injective
    rw [hframe, hform]
    simp only [frameDerivative, LinearEquiv.apply_symm_apply]
    rw [hmat, hcoef.self_of_nhds]
  change L (covariantDerivativeWithin C γ X univ t) = covariantDerivativeWithin K δ Y univ t
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ t)
      uniqueDiffWithinAt_univ hZ,
    P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq K (mem_univ t)
      uniqueDiffWithinAt_univ htarg]
end P202.GlobalGaussBonnet.BoundaryDensities
namespace P202.GlobalGaussBonnet.BoundaryDensities
open P202Specs.RegionalBoundaryDensities P202Specs.PlanarRegionTopology
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
  {D : RegionDecomposition S} {j : Fin D.regionCount}
  {i : Fin (D.region j).boundaryCount}
lemma regionalArcPoint_eq (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    G.map ⟨c.curve t, G.closure_subset (representsRegionalArc_point D j i A k c hc ht)⟩ =
      P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t := by
  let p : G.neighborhood :=
    ⟨c.curve t, G.closure_subset (representsRegionalArc_point D j i A k c hc ht)⟩
  have he : G.ambientChart (G.map p) =
      P202Specs.ChartRegionStokes.modelPoint (A.arc k t) := by
    apply Subtype.ext
    have h := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) (hc.2.2 t ht).2
    change (G.ambientChart (G.map p)).val = _
    rw [← G.matching_coordinates p, G.restrictedChart_eq p]
    exact h
  change G.map p = G.ambientChart.symm _
  rw [← he, G.ambientChart.left_inv (by rw [G.ambientChart_source]; trivial)]

def regionalArcTangentEquiv (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    TangentSpace S (c.curve t) ≃ₗ[ℝ]
      TangentSpace G.ambientSurface (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t) :=
  ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
    (c.curve t) (hc.2.2 t ht).1).trans
    ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
      G.ambientChart_mem (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
      (by rw [G.ambientChart_source]; trivial)).symm

lemma regionalArcTangentEquiv_coordinates (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (v : TangentSpace S (c.curve t)) :
    (tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
      G.ambientChart_mem (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
      (by rw [G.ambientChart_source]; trivial) (regionalArcTangentEquiv G A k c hc t ht v) =
    (tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
      (c.curve t) (hc.2.2 t ht).1 v := by
  exact LinearEquiv.apply_symm_apply _ _

lemma regionalArcTangentEquiv_pairing (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (v w : TangentSpace S (c.curve t)) :
    pairing G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
      (regionalArcTangentEquiv G A k c hc t ht v)
      (regionalArcTangentEquiv G A k c hc t ht w) = pairing g (c.curve t) v w := by
  let p : G.neighborhood :=
    ⟨c.curve t, G.closure_subset (representsRegionalArc_point D j i A k c hc ht)⟩
  have he := regionalArcPoint_eq G A k c hc t ht
  let F (q : ULift.{u} G.ambientDomain) : ℝ :=
    let E := ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
      (c.curve t) (hc.2.2 t ht).1).trans
      ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
        G.ambientChart_mem q (by rw [G.ambientChart_source]; trivial)).symm
    pairing G.metric q (E v) (E w)
  have h := regionalTangentEquiv_pairing G p v w
  change F (G.map p) = _ at h
  change F (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t) = _
  exact (congrArg F he).symm.trans h

lemma representsRegionalArc_velocity_coordinates
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
      (c.curve t) (hc.2.2 t (Ioo_subset_Icc_self ht)).1 (c.velocity t) =
      EuclideanSpace.equiv (Fin 2) ℝ (P202Specs.PlaneTurning.velocity A k t) := by
  have hct : t ∈ Ioo c.left c.right := by rw [hc.1, hc.2.1]; exact ht
  have hv := P202.Geometry.CurveCovariantDerivative.velocity_coordinates
    (P202.Geometry.CurveCovariantDerivative.ordinary_velocity_iff.mpr (c.hasVelocity t hct))
    (mem_univ t) (D.chart j) (D.chart_mem j) (hc.2.2 t (Ioo_subset_Icc_self ht)).1
  have hA := (P202.MetricBoundaryTurning.arc_contDiffAt A k (Ioo_subset_Icc_self ht)).differentiableAt
    (by simp)
  have hd := (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t hA.hasDerivAt
  have he : (fun s => ((D.chart j) (c.curve s)).val) =ᶠ[𝓝 t]
      (fun s => EuclideanSpace.equiv (Fin 2) ℝ (A.arc k s)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact congrArg (EuclideanSpace.equiv (Fin 2) ℝ)
      (hc.2.2 s (Ioo_subset_Icc_self hs)).2
  rw [hasDerivWithinAt_univ] at hv
  exact hv.unique (hd.congr_of_eventuallyEq he)

lemma regionalArcTangentEquiv_velocity (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht) (c.velocity t) =
      P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k t := by
  let hx := P202.GlobalGaussBonnet.regionalChartGeometry_carrier_subset G
    (frontier_subset_closure (by
      rw [(D.region j).boundary_eq]
      exact mem_iUnion.mpr ⟨i, P202.MetricBoundaryTurning.arc_mem_trace A k (Ioo_subset_Icc_self ht)⟩))
  apply ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
    G.ambientChart_mem (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
    (by rw [G.ambientChart_source]; trivial)).injective
  rw [regionalArcTangentEquiv_coordinates G A k c hc t (Ioo_subset_Icc_self ht),
    representsRegionalArc_velocity_coordinates A k c hc t ht]
  symm
  have hx' : P202Specs.ChartRegionStokes.modelPoint (A.arc k t) ∈ G.ambientChart.target := hx
  rw [P202Specs.LocalGaussBonnet.arcVelocity, P202Specs.LocalGaussBonnet.chartVector, dite_eq_left hx']
  exact LinearEquiv.apply_symm_apply _ _

lemma regionalArc_speed (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    P202Specs.LocalGaussBonnet.arcSpeed G.metric G.ambientChart G.ambientChart_mem A k t =
      c.speed t := by
  rw [P202Specs.LocalGaussBonnet.arcSpeed, ← regionalArcTangentEquiv_velocity G A k c hc t ht]
  change tangentNorm G.metric _ _ = tangentNorm g _ _
  unfold tangentNorm
  rw [regionalArcTangentEquiv_pairing]

end P202.GlobalGaussBonnet.BoundaryDensities
namespace P202.GlobalGaussBonnet.BoundaryDensities
open P202Specs.RegionalBoundaryDensities P202Specs.PlanarRegionTopology
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
  {D : RegionDecomposition S} {j : Fin D.regionCount}
  {i : Fin (D.region j).boundaryCount}
lemma regionalArcTangentEquiv_frame_coordinates (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : c.curve t ∈ (tangentBundle S).baseSet ⟨D.chart j, D.chart_mem j⟩)
    (hq : P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t ∈
      (tangentBundle G.ambientSurface).baseSet ⟨G.ambientChart, G.ambientChart_mem⟩)
    (v : TangentSpace S (c.curve t)) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle G.ambientSurface)
      ⟨G.ambientChart, G.ambientChart_mem⟩).basis
        ⟨P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t, hq⟩).equivFun
          (regionalArcTangentEquiv G A k c hc t ht v) =
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S)
      ⟨D.chart j, D.chart_mem j⟩).basis ⟨c.curve t, hp⟩).equivFun v := by
  refine (P202.Geometry.LeviCivita.trivializationFrame_coordinates
    ⟨G.ambientChart, G.ambientChart_mem⟩
    ⟨P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t, hq⟩
    (regionalArcTangentEquiv G A k c hc t ht v)).trans ?_
  refine ((tangentRealization G.ambientSurface).coordinates
      ⟨G.ambientChart, G.ambientChart_mem⟩ _
      (by rw [G.ambientChart_source]; trivial) _).trans ?_
  refine (regionalArcTangentEquiv_coordinates G A k c hc t ht v).trans ?_
  exact ((tangentRealization S).coordinates ⟨D.chart j, D.chart_mem j⟩ _
      (hc.2.2 t ht).1 v).symm.trans
    (P202.Geometry.LeviCivita.trivializationFrame_coordinates
      ⟨D.chart j, D.chart_mem j⟩ ⟨c.curve t, hp⟩ v).symm

lemma regionalArcTangentEquiv_tangent (G : RegionalChartGeometry g D j)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht) (c.tangent t) =
      unitTangent G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
        (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k) t := by
  change regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht)
      ((c.speed t)⁻¹ • c.velocity t) =
    (P202Specs.LocalGaussBonnet.arcSpeed G.metric G.ambientChart G.ambientChart_mem A k t)⁻¹ • _
  rw [map_smul, regionalArc_speed G A k c hc t ht,
    regionalArcTangentEquiv_velocity G A k c hc t ht]

lemma regionalArc_connectionMatrix (G : RegionalChartGeometry g D j)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : c.curve t ∈ (tangentBundle S).baseSet ⟨D.chart j, D.chart_mem j⟩)
    (hq : P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t ∈
      (tangentBundle G.ambientSurface).baseSet ⟨G.ambientChart, G.ambientChart_mem⟩)
    (v : TangentSpace S (c.curve t)) :
    connectionMatrix C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) ⟨D.chart j, D.chart_mem j⟩) ⟨c.curve t, hp⟩ v =
    connectionMatrix G.connection (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle G.ambientSurface) ⟨G.ambientChart, G.ambientChart_mem⟩)
      ⟨P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t, hq⟩
      (regionalArcTangentEquiv G A k c hc t ht v) := by
  let p : G.neighborhood :=
    ⟨c.curve t, G.closure_subset (representsRegionalArc_point D j i A k c hc ht)⟩
  have he := regionalArcPoint_eq G A k c hc t ht
  have hqm : G.map p ∈ (tangentBundle G.ambientSurface).baseSet
      ⟨G.ambientChart, G.ambientChart_mem⟩ := by
    rw [(tangentRealization G.ambientSurface).baseSet, G.ambientChart_source]
    trivial
  have h := regional_connectionMatrix G C hC p ((regionalInclusionEquiv G p).symm v) hp hqm
  rw [← regionalInclusionEquiv_apply, LinearEquiv.apply_symm_apply] at h
  have hv : G.immersion.differential p ((regionalInclusionEquiv G p).symm v) =
      regionalTangentEquiv G p v := by
    rw [← regionalTangentEquiv_inclusion, ← regionalInclusionEquiv_apply,
      LinearEquiv.apply_symm_apply]
  rw [hv] at h
  let F (q : ULift.{u} G.ambientDomain) : Matrix (Fin 2) (Fin 2) ℝ :=
    let E := ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
      (c.curve t) (hc.2.2 t ht).1).trans
      ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
        G.ambientChart_mem q (by rw [G.ambientChart_source]; trivial)).symm
    connectionMatrix G.connection (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle G.ambientSurface) ⟨G.ambientChart, G.ambientChart_mem⟩)
      ⟨q, (by rw [(tangentRealization G.ambientSurface).baseSet, G.ambientChart_source]; trivial)⟩ (E v)
  change _ = F (G.map p) at h
  change _ = F (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
  exact h.trans (congrArg F he)

lemma regionalArcTangentEquiv_covariantDerivative (G : RegionalChartGeometry g D j)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht)
      (covariantDerivative C c.curve c.tangent t) =
    covariantDerivative G.connection (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
      (unitTangent G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
        (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k)) t := by
  let bc := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S)
    ⟨D.chart j, D.chart_mem j⟩
  let bd := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle G.ambientSurface)
    ⟨G.ambientChart, G.ambientChart_mem⟩
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      c.curve s ∈ (tangentBundle S).baseSet ⟨D.chart j, D.chart_mem j⟩ :=
    (tangentRealization S).baseSet _ ▸ (hc.2.2 s hs).1
  have hq (s : ℝ) : P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k s ∈
      (tangentBundle G.ambientSurface).baseSet ⟨G.ambientChart, G.ambientChart_mem⟩ := by
    rw [(tangentRealization G.ambientSurface).baseSet, G.ambientChart_source]
    trivial
  have htrace : ((D.region j).curve i).trace ⊆ P202Specs.ChartRegionStokes.chartTarget G.ambientChart := by
    intro x hx
    exact P202.GlobalGaussBonnet.regionalChartGeometry_carrier_subset G
      (frontier_subset_closure (by rw [(D.region j).boundary_eq]; exact mem_iUnion.mpr ⟨i, hx⟩))
  have hct : t ∈ Ioo c.left c.right := by rw [hc.1, hc.2.1]; exact ht
  obtain ⟨Z, hZ⟩ := P202.Geometry.SurfaceBoundaryGeometry.regularArc_derivative g C c t hct
  refine covariantDerivative_of_matching_coefficients C G.connection bc bd c.curve
    (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k) c.tangent
    (unitTangent G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
      (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k)) t
    (hp t (Ioo_subset_Icc_self ht)) (hq t)
    (regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht)).toLinearMap
    (regionalArcTangentEquiv_frame_coordinates G A k c hc t (Ioo_subset_Icc_self ht)
      (hp t (Ioo_subset_Icc_self ht)) (hq t))
    (c.velocity t) (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k t)
    (P202.Geometry.CurveCovariantDerivative.ordinary_velocity_iff.mpr (c.hasVelocity t hct))
    (P202.MetricBoundaryTurning.arc_hasVelocity G.ambientChart G.ambientChart_mem htrace A k
      (Ioo_subset_Icc_self ht)) ?_ ?_ Z hZ
  · rw [← regionalArcTangentEquiv_velocity G A k c hc t ht]
    exact regionalArc_connectionMatrix G C hC A k c hc t (Ioo_subset_Icc_self ht)
      (hp t (Ioo_subset_Icc_self ht)) (hq t) (c.velocity t)
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    calc
      _ = (bd.basis ⟨P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k s, hq s⟩).equivFun
          (unitTangent G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
            (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k) s) :=
        P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem bd _ _ s (hq s)
      _ = (bd.basis ⟨P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k s, hq s⟩).equivFun
          (regionalArcTangentEquiv G A k c hc s (Ioo_subset_Icc_self hs) (c.tangent s)) :=
        congrArg _ (regionalArcTangentEquiv_tangent G A k c hc s hs).symm
      _ = (bc.basis ⟨c.curve s, hp s (Ioo_subset_Icc_self hs)⟩).equivFun (c.tangent s) :=
        regionalArcTangentEquiv_frame_coordinates G A k c hc s (Ioo_subset_Icc_self hs)
          (hp s (Ioo_subset_Icc_self hs)) (hq s) (c.tangent s)
      _ = _ := (P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem bc _ _ s
        (hp s (Ioo_subset_Icc_self hs))).symm

lemma regionalArcTangentEquiv_curvatureVector (G : RegionalChartGeometry g D j)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (A : P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (k : Fin A.count) (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht)
      (curvatureVector C g c.curve c.tangent c.speed t) =
    curvatureVector G.connection G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
      (unitTangent G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
        (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k))
      (P202Specs.LocalGaussBonnet.arcSpeed G.metric G.ambientChart G.ambientChart_mem A k) t := by
  unfold curvatureVector
  rw [map_smul, regionalArcTangentEquiv_covariantDerivative G C hC A k c hc t ht,
    regionalArc_speed G A k c hc t ht]
end P202.GlobalGaussBonnet.BoundaryDensities

/-! The literal regional density follows from normal and covariant transport. -/
namespace P202.GlobalGaussBonnet.BoundaryDensities
open P202Specs.RegionalBoundaryDensities P202Specs.PlaneTurning
open P202Specs.PlanarRegionTopology P202Specs.BoundaryGraphDirections
open P202.PlanarRegionTopology P202.BoundaryGraphDirections
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
  {D : RegionDecomposition S} {j : Fin D.regionCount}
  {i : Fin (D.region j).boundaryCount}

lemma arcPresentation_velocity_of_nonjoin
    {q : RegularJordanCurve} (A : ArcPresentation q) (k : Fin A.count)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hn : ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t : ℝ) :
      ParameterCircle) ∉ q.joins) :
    velocity A k t = (A.time k.succ - A.time k.castSucc) •
      deriv (realLift q.parametrization)
        (A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t) := by
  let d := A.time k.succ - A.time k.castSucc
  let a := A.time k.castSucc
  let γ := realLift q.parametrization
  have hγ : DifferentiableAt ℝ γ (a + d * t) :=
    (q.smooth_off_joins (a + d * t) hn).differentiableAt (by simp)
  have hφ : HasDerivAt (fun x : ℝ => a + d * x) d t := by
    convert! (hasDerivAt_id t).const_mul d |>.const_add a using 1 <;> simp
  have hd : HasDerivAt (fun x => γ (a + d * x)) (d • deriv γ (a + d * t)) t := by
    convert! hγ.hasDerivAt.scomp t hφ using 1
  have he : A.arc k =ᶠ[𝓝 t] (fun x => γ (a + d * x)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact A.agrees k x (Ioo_subset_Icc_self hx)
  exact (hd.congr_of_eventuallyEq he).deriv

lemma regionalArcTangentEquiv_boundaryNormal
    (G : RegionalChartGeometry g D j) (s : Fin (D.region j).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region j) s)
    (A : ArcPresentation ((D.region j).curve i)) (k : Fin A.count)
    (c : RegularArc g) (hc : RepresentsRegionalArc D j i A k c)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hn : t ∉ exceptionalParameters D j i A k)
    (b : BoundarySideAt (S := S) (regionClosure D j) (c.curve t)) :
    regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht) (boundaryNormal g b) =
      s i • rotation G.metric G.orientation
        (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
        (unitTangent G.metric (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k)
          (P202Specs.LocalGaussBonnet.arcVelocity G.ambientChart G.ambientChart_mem A k) t) := by
  let τ := A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t
  have hτ : (τ : ParameterCircle) ∉ ((D.region j).curve i).joins := by
    intro h
    exact hn ⟨ht, Or.inl h⟩
  have hpR := representsRegionalArc_point D j i A k c hc (Ioo_subset_Icc_self ht)
  let p : G.neighborhood := ⟨c.curve t, G.closure_subset hpR⟩
  have hcoord : coordinates (D.chart j) p.val =
      realLift ((D.region j).curve i).parametrization τ :=
    (hc.2.2 t (Ioo_subset_Icc_self ht)).2.trans (A.agrees k t (Ioo_subset_Icc_self ht))
  obtain ⟨B, hB⟩ := twoDirectedProjectionArcs ((D.region j).curve i) (s i) τ (hs i).1
  have hσ : s i ≠ 0 := by
    rcases (hs i).1 with h | h <;> rw [h] <;> norm_num
  obtain ⟨O, Q, hO, hτO, hQB⟩ := localDirectedBoundaryGraph_of_arc
    (D.region j) s i τ hσ (hs i).2 (B 0)
  obtain ⟨b0, hb0⟩ := regionalBoundarySideAtOfDirectedGraph_withFunction
    D j s i τ O Q hO hτO hτ (c.curve t) hpR hcoord
  have hq : G.map p ∈ G.ambientChart.source := by rw [G.ambientChart_source]; trivial
  have hqcoord : coordinates G.ambientChart (G.map p) =
      realLift ((D.region j).curve i).parametrization τ :=
    (regionalChartGeometry_coordinates G p).symm.trans hcoord
  have hV : SmoothManifolds.coordinateDerivationEquiv G.ambientSurface (G.map p)
      G.ambientChart G.ambientChart_mem hq (regionalTangentEquiv G p (c.velocity t)) =
      (EuclideanSpace.equiv (Fin 2) ℝ)
        ((A.time k.succ - A.time k.castSucc) •
          deriv (realLift ((D.region j).curve i).parametrization) τ) := by
    rw [← SmoothManifolds.chartCoordinates_eq G.ambientSurface (G.map p)
      G.ambientChart G.ambientChart_mem hq
      ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
        G.ambientChart_mem (G.map p) hq)
      ((tangentStructure G.ambientSurface).fiberCoordinates.isCoordinates G.ambientChart
        G.ambientChart_mem (G.map p) hq)]
    rw [regionalTangentEquiv_coordinates,
      representsRegionalArc_velocity_coordinates A k c hc t ht,
      arcPresentation_velocity_of_nonjoin A k ht hτ]
  obtain ⟨a, ha, hna⟩ := ambientDirectedGraph_boundaryNormal G.metric G.orientation
    G.ambientChart G.ambientChart_mem G.orientation_positive hs Q hO hτO hτ
    (G.map p) hq hqcoord (regionalTangentEquiv G p (c.velocity t))
    (A.time k.succ - A.time k.castSucc)
    (sub_pos.mpr (A.strictMono k.castSucc_lt_succ)) hV
  obtain ⟨U, hU, hτU, hF⟩ := graphDefiningFunction_contDiffAt Q hτ
  have hnormal := regionalTangentEquiv_boundaryNormal G p b0 a
    (graphDefiningFunction Q) U hU (by rw [hcoord]; exact hτU) hF hb0 ha
  have hsame : boundaryNormal g b = boundaryNormal g b0 :=
    boundaryNormal_eq_of_same_germ g b0 b (Eventually.of_forall (fun _ => rfl))
  have hn0 : regionalTangentEquiv G p (boundaryNormal g b) =
      s i • rotation G.metric G.orientation (G.map p)
        ((tangentNorm G.metric (G.map p) (regionalTangentEquiv G p (c.velocity t)))⁻¹ •
          regionalTangentEquiv G p (c.velocity t)) := by
    rw [hsame, hnormal, hna]
  let E : (q : ULift.{u} G.ambientDomain) → TangentSpace S (c.curve t) ≃ₗ[ℝ]
      TangentSpace G.ambientSurface q := fun q =>
    ((tangentStructure S).fiberCoordinates.equiv (D.chart j) (D.chart_mem j)
      (c.curve t) (hc.2.2 t (Ioo_subset_Icc_self ht)).1).trans
      ((tangentStructure G.ambientSurface).fiberCoordinates.equiv G.ambientChart
        G.ambientChart_mem q (by rw [G.ambientChart_source]; trivial)).symm
  let F : ULift.{u} G.ambientDomain → Prop := fun q =>
    E q (boundaryNormal g b) = s i • rotation G.metric G.orientation q
      ((tangentNorm G.metric q (E q (c.velocity t)))⁻¹ • E q (c.velocity t))
  change F (G.map p) at hn0
  have hn1 : F (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t) :=
    (congrArg F (regionalArcPoint_eq G A k c hc t (Ioo_subset_Icc_self ht))).mp hn0
  change regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht) (boundaryNormal g b) =
      s i • rotation G.metric G.orientation
        (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
        ((tangentNorm G.metric
          (P202Specs.LocalGaussBonnet.surfaceArc G.ambientChart A k t)
          (regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht) (c.velocity t)))⁻¹ •
          regionalArcTangentEquiv G A k c hc t (Ioo_subset_Icc_self ht) (c.velocity t)) at hn1
  simpa only [regionalArcTangentEquiv_velocity G A k c hc t ht, unitTangent] using hn1

theorem regional_density_eq : P202Specs.RegionalBoundaryDensities.Expected.regional_density_eq := by
  intro kind M _ S g C hC D j G s hs i A k c hc t ht hn b
  have hnormal := regionalArcTangentEquiv_boundaryNormal G s hs A k c hc t ht hn b
  have hcurv := regionalArcTangentEquiv_curvatureVector G C hC A k c hc t ht
  have hpair := regionalArcTangentEquiv_pairing G A k c hc t (Ioo_subset_Icc_self ht)
    (curvatureVector C g c.curve c.tangent c.speed t) (boundaryNormal g b)
  rw [hcurv, hnormal] at hpair
  simp only [pairing, LinearMap.BilinForm.smul_right] at hpair
  unfold P202Specs.LocalGaussBonnet.geodesicIntegrand signedCurveCurvature signedCurvature inwardCurvature
  rw [regionalArc_speed G A k c hc t ht]
  change s i * (pairing G.metric _ _ _ * c.speed t) = _
  calc
    _ = (s i * pairing G.metric _ _ _) * c.speed t := by ring
    _ = _ := congrArg (fun z : ℝ => z * c.speed t) hpair

end P202.GlobalGaussBonnet.BoundaryDensities
