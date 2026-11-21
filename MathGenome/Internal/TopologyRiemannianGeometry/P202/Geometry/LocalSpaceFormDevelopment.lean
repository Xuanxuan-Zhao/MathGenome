import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalSpaceFormDevelopment
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteExponentialMinimizers
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConstantCurvaturePolar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricGeodesicCompleteness
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.BracketFromFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.OrientedTopDegree
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Local development and uniqueness of local-isometry germs, paper.tex 4589–4607.

The development theorem applies to every supplied source normal chart. The
accepted model polar-domain charts therefore give all model normal balls.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace P202.Geometry.LocalSpaceFormDevelopment
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
  P202.ExponentialJacobiData P202.CurvatureData P202.ConstantCurvaturePolarData
  P202.CompletenessData P202.CompleteExponentialData P202.LocalDevelopmentData
open Set Filter
open scoped _root_.Topology
universe u

/-- The model warping function is positive before its first positive zero. -/
theorem s_pos_below_radius {k r t : ℝ} (hr : BelowModelRadius k r)
    (ht : 0 < t) (htr : t < r) : 0 < s k t := by
  unfold s
  by_cases hk : 0 < k
  · rw [ite_eq_left hk]
    have hs := Real.sqrt_pos.mpr hk
    apply div_pos _ hs
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hs ht)
    simpa only [mul_comm] using (lt_div_iff₀ hs).mp (lt_trans htr (hr.2 hk))
  · rw [ite_eq_right hk]
    split_ifs with hz
    · exact ht
    · have hs : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr (by
        have : k < 0 := lt_of_le_of_ne (le_of_not_gt hk) hz
        linarith)
      exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hs ht)) hs

variable {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
  {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}

/-- Completeness supplies the entire target exponential domain. -/
theorem full_target_exponential [ConnectedSpace M] (h : RiemannianMetric T)
    (D : Connection (tangentBundle T)) (hD : IsLeviCivita h D)
    (hc : LengthMetricComplete h) (G : CurveFamily (Phase T))
    (hG : IsMaximalFamily T D G) (y : M) : FullExponentialAt G y := by
  intro v
  change 1 ∈ (G.interval ⟨y, v⟩).carrier
  rw [MetricGeodesicCompleteness.metric_complete_geodesically_complete T h D hD hc
    _ _ _ (hG ⟨y, v⟩)]
  exact mem_univ _

/-- The fiber differential at zero is the canonical tangent identification,
including the propositionally equal endpoint fiber. -/
theorem fiberDifferential_zero (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (x : X)
    (w : TangentSpace S x) :
    fiberDifferential S F x 0 w =
      castTangent S (ExponentialNormalCoordinates.zero_section S C F hF x).2.symm w := by
  let e := (selectedChart S x).val
  have he := (selectedChart S x).property.1
  have hx := (selectedChart S x).property.2
  have hz := ExponentialNormalCoordinates.zero_section S C F hF x
  have hze : fiberExponential F x 0 ∈ e.source := by rwa [hz.2]
  let E := (tangentStructure S).fiberCoordinates.equiv e he x hx
  let K := (tangentStructure S).fiberCoordinates.equiv e he (fiberExponential F x 0) hze
  apply K.injective
  have hd := ExponentialJacobi.differential_coordinates S C F hF x 0 hz.1 e e he he hx hze w
  change K (fiberDifferential S F x 0 w) = _ at hd
  rw [show E 0 = 0 from map_zero E] at hd
  have hder := ExponentialNormalCoordinates.derivative_zero S C F hF x e he hx
  rw [hder.fderiv] at hd
  change K (fiberDifferential S F x 0 w) = E w at hd
  exact hd.trans (ExponentialJacobi.coordinates_cast hz.2.symm e he hx hze w).symm

/-- The full tensor equality at zero follows from the true derivative there. -/
theorem fiber_metric_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (x : X) (w z : TangentSpace S x) :
    pairing g (fiberExponential F x 0)
      (fiberDifferential S F x 0 w) (fiberDifferential S F x 0 z) = pairing g x w z := by
  rw [fiberDifferential_zero C F hF, fiberDifferential_zero C F hF]
  exact ConstantCurvaturePolar.pairing_cast g _ w z

/-- Decompose an arbitrary vector into its radial and angular polar inputs.
The angular input is divided by the radial coordinate because the polar
exponential differential contains t*w. -/
theorem radial_decomposition (g : RiemannianMetric S) (x : X)
    (v : TangentSpace S x) (hv : v ≠ 0) :
    let t := tangentNorm g x v
    let e := t⁻¹ • v
    0 < t ∧ pairing g x e e = 1 ∧ t • e = v ∧
    ∀ w : TangentSpace S x,
      let a := pairing g x w e
      let z := t⁻¹ • (w + (-a) • e)
      pairing g x z e = 0 ∧ a • e + t • z = w := by
  dsimp only
  let t := tangentNorm g x v
  let e := t⁻¹ • v
  have ht : 0 < t := lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g x v)
    (Ne.symm ((SmoothMetrics.tangentNorm_eq_zero_iff g x v).not.mpr hv))
  have he : pairing g x e e = 1 := by
    dsimp only [e]
    simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [← SmoothMetrics.tangentNorm_sq g x v]
    change t⁻¹ * (t⁻¹ * t ^ 2) = 1
    field_simp [ne_of_gt ht]
  have hte : t • e = v := by simp [e, smul_smul, ne_of_gt ht]
  refine ⟨ht, he, hte, ?_⟩
  intro w
  change pairing g x (t⁻¹ • (w + (-pairing g x w e) • e)) e = 0 ∧
    pairing g x w e • e + t • (t⁻¹ • (w + (-pairing g x w e) • e)) = w
  constructor
  · simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left, he,
      mul_one, add_neg_cancel, mul_zero]
  · simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
    rw [add_left_comm, ← add_smul, add_neg_cancel, zero_smul, add_zero]

/-- The two exponential pullback tensors coincide for every vector, including
zero and singular points. No injectivity of either exponential is used. -/
theorem exponential_metric_comparison
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hk : ConstantSectional g R k) (hl : ConstantSectional h Q k)
    (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T))
    (hF : IsMaximalFamily S C F) (hG : IsMaximalFamily T D G)
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hA : ∀ v w, pairing h y (A v) (A w) = pairing g x v w)
    (v : TangentSpace S x)
    (hv : (⟨x, v⟩ : Phase S) ∈ exponentialDomain F)
    (hAv : (⟨y, A v⟩ : Phase T) ∈ exponentialDomain G)
    (w z : TangentSpace S x) :
    pairing h (fiberExponential G y (A v))
      (fiberDifferential T G y (A v) (A w)) (fiberDifferential T G y (A v) (A z)) =
    pairing g (fiberExponential F x v)
      (fiberDifferential S F x v w) (fiberDifferential S F x v z) := by
  by_cases hv0 : v = 0
  · subst v
    rw [A.map_zero, fiber_metric_zero g C F hF, fiber_metric_zero h D G hG, hA]
  · let t := tangentNorm g x v
    let e := t⁻¹ • v
    obtain ⟨ht, he, hte, hdecomp⟩ := radial_decomposition g x v hv0
    change 0 < t at ht
    change pairing g x e e = 1 at he
    change t • e = v at hte
    let a := pairing g x w e
    let b := pairing g x z e
    let W := t⁻¹ • (w + (-a) • e)
    let Z := t⁻¹ • (z + (-b) • e)
    have hW : pairing g x W e = 0 := (hdecomp w).1
    have hZ : pairing g x Z e = 0 := (hdecomp z).1
    have hw : a • e + t • W = w := (hdecomp w).2
    have hz : b • e + t • Z = z := (hdecomp z).2
    have hv' : (⟨x, t • e⟩ : Phase S) ∈ exponentialDomain F := by rwa [hte]
    have hAv' : (⟨y, t • A e⟩ : Phase T) ∈ exponentialDomain G := by
      rw [← map_smul, hte]
      exact hAv
    have hAe : pairing h y (A e) (A e) = 1 := (hA e e).trans he
    have hAW : pairing h y (A W) (A e) = 0 := (hA W e).trans hW
    have hAZ : pairing h y (A Z) (A e) = 0 := (hA Z e).trans hZ
    have hs := ConstantCurvaturePolar.polar_metric S g C hC R hR k hk F hF x t e
      (ne_of_gt ht) he hv' a b W Z hW hZ
    have htgt := ConstantCurvaturePolar.polar_metric T h D hD Q hQ k hl G hG y t (A e)
      (ne_of_gt ht) hAe hAv' a b (A W) (A Z) hAW hAZ
    unfold polarDifferential at hs htgt
    rw [hte, hw, hz] at hs
    rw [← map_smul, hte, ← map_smul, ← map_smul, ← map_add, hw,
      ← map_smul, ← map_smul, ← map_add, hz, hA] at htgt
    exact htgt.trans hs.symm

/-- The actual fiber differential in arbitrary linear source coordinates.
This follows by differentiating straight fiber curves and uniqueness of their
coordinate velocities; the basis need not be a tangent atlas trivialization. -/
theorem fiberDifferential_basis (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (x : X)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n)
    (v w : TangentSpace S x) (hv : (⟨x, v⟩ : Phase S) ∈ exponentialDomain F)
    (d : ModelChart n .euclidean X) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F x v ∈ d.source) :
    (tangentStructure S).fiberCoordinates.equiv d hd (fiberExponential F x v) hq
      (fiberDifferential S F x v w) =
    fderiv ℝ (fun a : Euclidean n => (d (fiberExponential F x (E.symm a))).val)
      (E v) (E w) := by
  let H := fun a : Euclidean n => (d (fiberExponential F x (E.symm a))).val
  have hcd := ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF x E d hd
    (E v) (by simpa only [LinearEquiv.symm_apply_apply] using hv)
    (by simpa only [LinearEquiv.symm_apply_apply] using hq)
  have hline : HasDerivAt (fun t : ℝ => E v + t • E w) (E w) 0 := by
    simpa only [one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (E w)).const_add (E v)
  have hdH := (hcd.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp)
  have hdH' : HasDerivAt (fun t : ℝ => (d (fiberExponential F x (v + t • w))).val)
      (fderiv ℝ H (E v) (E w)) 0 := by
    simpa only [Function.comp_def, map_add, map_smul, LinearEquiv.symm_apply_apply] using hdH
  have hvel := ExponentialJacobi.fiber_ray_velocity C F hF x v w hv
  have h0 : fiberExponential F x v = fiberExponential F x (v + (0 : ℝ) • w) := by simp
  have hq0 : fiberExponential F x (v + (0 : ℝ) • w) ∈ d.source := by simpa using hq
  have hray := CurveCovariantDerivative.velocity_coordinates hvel (mem_univ 0) d hd hq0
  rw [ExponentialJacobi.coordinates_cast h0 d hd hq hq0] at hray
  have hray' : HasDerivAt (fun t : ℝ => (d (fiberExponential F x (v + t • w))).val)
      ((tangentStructure S).fiberCoordinates.equiv d hd (fiberExponential F x v) hq
        (fiberDifferential S F x v w)) 0 := by
    simpa only [hasDerivWithinAt_univ] using hray
  exact hray'.unique hdH'

/-- On a normal chart, the exponential differential is precisely the inverse
of the actual chart tangent coordinates. -/
theorem normal_chart_fiberDifferential
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (x : X)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g x E)
    (r : ℝ) (d : ModelChart n .euclidean X) (hd : IsNormalChart g F x E r d)
    (v w : TangentSpace S x) (hv : tangentNorm g x v < r) :
    ∃ hq : fiberExponential F x v ∈ d.source,
      (tangentStructure S).fiberCoordinates.equiv d hd.2.1 (fiberExponential F x v) hq
        (fiberDifferential S F x v w) = E w := by
  let B : Set (Euclidean n) := {a | tangentNorm g x (E.symm a) < r}
  have hB : IsOpen B :=
    (ExponentialNormalCoordinates.orthonormal_norm_continuous g x E hE).isOpen_preimage _ isOpen_Iio
  have hvin : E v ∈ B := by simpa only [B, mem_ofPred_eq, LinearEquiv.symm_apply_apply] using hv
  have heq (a : Euclidean n) (ha : a ∈ B) :
      (d (fiberExponential F x (E.symm a))).val = a := by
    let z : ModelSpace n .euclidean := ⟨a, by simp [modelSet]⟩
    have hzt : z ∈ d.target := by rw [hd.2.2.2.2.1]; exact ha
    rw [(hd.2.2.2.2.2 z ha).2, d.right_inv hzt]
  have hdom : (⟨x, v⟩ : Phase S) ∈ exponentialDomain F := by
    simpa only [LinearEquiv.symm_apply_apply] using
      (hd.2.2.2.2.2 ⟨E v, by simp [modelSet]⟩ hvin).1
  have hq : fiberExponential F x v ∈ d.source := by
    have hzt : (⟨E v, by simp [modelSet]⟩ : ModelSpace n .euclidean) ∈ d.target := by
      rw [hd.2.2.2.2.1]; exact hvin
    have hh := d.map_target hzt
    rwa [← (hd.2.2.2.2.2 ⟨E v, by simp [modelSet]⟩ hvin).2, LinearEquiv.symm_apply_apply] at hh
  refine ⟨hq, ?_⟩
  rw [fiberDifferential_basis C F hF x E v w hdom d hd.2.1 hq]
  have hgerm : (fun a : Euclidean n => (d (fiberExponential F x (E.symm a))).val)
      =ᶠ[𝓝 (E v)] id := by
    filter_upwards [hB.mem_nhds hvin] with a ha
    exact heq a ha
  rw [hgerm.fderiv_eq]
  simp

/-- Local coordinate computation of a differential. Only a smooth germ is
needed; no smoothness is imposed on the representative away from the point. -/
theorem local_differential_coordinates (f : X → M) (p : X)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L)
    (e : ModelChart n .euclidean X) (d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hfp : f p ∈ d.source)
    (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
    (hV : IsOpen V) (hpV : (e p).val ∈ V) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (hrep : (fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d (f q)).val))
    (v : TangentSpace S p) :
    (tangentStructure T).fiberCoordinates.equiv d hd (f p) hfp (L v) =
      fderiv ℝ H (e p).val ((tangentStructure S).fiberCoordinates.equiv e he p hp v) := by
  let B := (tangentStructure S).fiberCoordinates.equiv e he p hp
  have hdiff := (hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hexp : B v = ∑ i, (B v) i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  ext j
  let k := SmoothManifolds.germOfChart S p e he hp (fun a => H a j)
    ⟨V, hV, hpV, (contDiffOn_pi.mp hH) j⟩
  have hk : Germ.ofFun ((fun q => (d q).val j) ∘ f) = k.val :=
    Germ.coe_eq.mpr ((hrep.fun_comp (fun a => a j)).symm)
  rw [SmoothManifolds.LieBrackets.coordinates_eval d hd (f p) hfp,
    hL v (SmoothManifolds.coordinateGerm T (f p) d hd hfp j) k _ rfl hk,
    SmoothManifolds.derivation_coordinate_formula S p e he hp v k (fun a => H a j)
      ⟨⟨V, hV, hpV, (contDiffOn_pi.mp hH) j⟩, rfl⟩]
  calc
    _ = fderiv ℝ (fun a => H a j) (e p).val (∑ i, (B v) i • Pi.single i (1 : ℝ)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [← SmoothManifolds.LieBrackets.coordinates_eval e he p hp]
    _ = _ := by rw [← hexp, fderiv_apply hdiff j]; rfl

/-- The inverse function theorem for a smooth germ with an invertible
intrinsic differential. The chosen inverse is smooth near the image point. -/
theorem inverse_germ_of_bijective_differential (f : X → M) (p : X)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L) (hbij : Function.Bijective L) :
    ∃ j : M → X,
      ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val j (f p) ∧
      j (f p) = p ∧ (j ∘ f) =ᶠ[𝓝 p] id ∧ (f ∘ j) =ᶠ[𝓝 (f p)] id := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨V, hV, hpV, H, hH, hrep⟩ := hf.2 e he d hd hp hfp
  let B := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let K := (tangentStructure T).fiberCoordinates.equiv d hd (f p) hfp
  let J := fderiv ℝ H (e p).val
  have hJK (v : TangentSpace S p) : K (L v) = J (B v) :=
    local_differential_coordinates f p L hL e d he hd hp hfp V H hV hpV hH hrep v
  have hJbij : Function.Bijective J := by
    constructor
    · intro a b hab
      have hh : L (B.symm a) = L (B.symm b) := K.injective (by
        simpa only [hJK, LinearEquiv.apply_symm_apply] using hab)
      exact B.symm.injective (hbij.1 hh)
    · intro b
      obtain ⟨v, hv⟩ := hbij.2 (K.symm b)
      refine ⟨B v, ?_⟩
      rw [← hJK, hv, LinearEquiv.apply_symm_apply]
  obtain ⟨a, hpa, haH, hainv⟩ := SmoothManifolds.InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) H V hV hH (e p).val hpV J
    ((hH.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)).hasFDerivAt hJbij
  let e₀ := SmoothManifolds.InteriorInverse.ambientChart e
  let d₀ := SmoothManifolds.InteriorInverse.ambientChart d
  let b := (e₀.trans a).trans d₀.symm
  have hpe₀ : p ∈ e₀.source := by
    change p ∈ e.source ∧ (e p).val ∈ interior (modelSet n .euclidean)
    exact ⟨hp, by simp [modelSet]⟩
  have hfpd₀ : f p ∈ d₀.source := by
    change f p ∈ d.source ∧ (d (f p)).val ∈ interior (modelSet n .euclidean)
    exact ⟨hfp, by simp [modelSet]⟩
  have hap : a (e₀ p) = d₀ (f p) := by
    change a (e p).val = (d (f p)).val
    rw [haH]
    exact hrep.eq_of_nhds
  have hpb : p ∈ b.source := by
    refine ⟨⟨hpe₀, hpa⟩, ?_⟩
    change a (e₀ p) ∈ d₀.target
    rw [hap]
    exact d₀.map_source hfpd₀
  have hbp : b p = f p := by
    change d₀.symm (a (e₀ p)) = f p
    rw [hap, d₀.left_inv hfpd₀]
  have hfpb : f p ∈ b.target := hbp ▸ b.map_source hpb
  have hbf : (b : X → M) =ᶠ[𝓝 p] f := by
    filter_upwards [hrep, hf.1.preimage_mem_nhds (d₀.open_source.mem_nhds hfpd₀)] with q hq hqd
    change d₀.symm (a (e₀ q)) = f q
    have haq : a (e₀ q) = d₀ (f q) := by change a (e q).val = _; rw [haH]; exact hq
    rw [haq, d₀.left_inv hqd]
  have hcoords (q : M) (hq : q ∈ b.target) :
      (e (b.symm q)).val = a.symm (d q).val := by
    change e₀ (e₀.symm (a.symm (d₀ q))) = a.symm (d₀ q)
    exact e₀.right_inv hq.2.2
  have hinvs : ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val b.symm (f p) := by
    apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      T.smoothStructure.property.1 S.smoothStructure.property.1 b.symm (f p)).mpr
    refine ⟨b.symm.continuousAt hfpb, d, hd, e, he, hfp, (b.map_target hfpb).1.1.1, ?_⟩
    refine ⟨a.target, a.open_target, hfpb.2.1, a.symm, hainv, ?_⟩
    filter_upwards [b.open_target.mem_nhds hfpb] with q hq
    exact (hcoords q hq).symm
  refine ⟨b.symm, hinvs, ?_, ?_, ?_⟩
  · rw [← hbp, b.left_inv hpb]
  · filter_upwards [hbf, b.open_source.mem_nhds hpb] with q hq hqb
    change b.symm (f q) = q
    rw [← hq, b.left_inv hqb]
  · have hbcont : ContinuousAt b.symm (f p) := b.symm.continuousAt hfpb
    have hbi : b.symm (f p) = p := by rw [← hbp, b.left_inv hpb]
    have htend : Tendsto b.symm (𝓝 (f p)) (𝓝 p) := by
      simpa only [hbi] using hbcont.tendsto
    have hcomp := hbf.comp_tendsto htend
    filter_upwards [hcomp, b.open_target.mem_nhds hfpb] with q hq hqb
    change f (b.symm q) = q
    change b (b.symm q) = f (b.symm q) at hq
    exact hq.symm.trans (b.right_inv hqb)

/-- Completeness is used only to guarantee the domain. Smoothness then follows
from the existing smooth exponential, on the entire parameter vector space. -/
theorem exponential_basis_continuous (D : Connection (tangentBundle T))
    (G : CurveFamily (Phase T)) (hG : IsMaximalFamily T D G) (y : M)
    (B : TangentSpace T y ≃ₗ[ℝ] Euclidean n) (hfull : FullExponentialAt G y) :
    Continuous (fun a : Euclidean n => fiberExponential G y (B.symm a)) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (ExponentialNormalCoordinates.exponential_smooth D G hG _ (hfull _)).1.comp
    (f := fun b : Euclidean n => (⟨y, B.symm b⟩ : Phase T))
    (ExponentialNormalCoordinates.fiberInclusion_continuous_basis y B).continuousAt

/-- The development is smooth at every point of the source chart, including
its center. No positive radial coordinate is used in this assertion. -/
theorem development_smooth (D : Connection (tangentBundle T))
    (G : CurveFamily (Phase T)) (hG : IsMaximalFamily T D G)
    (y : M) (hfull : FullExponentialAt G y)
    (x : X) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean X) (hd : d ∈ S.smoothStructure.val)
    (p : X) (hp : p ∈ d.source) :
    ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val
      (development G x y A E d) p := by
  let B : TangentSpace T y ≃ₗ[ℝ] Euclidean n := A.symm.trans E
  let f := development G x y A E d
  have hfc := exponential_basis_continuous D G hG y B hfull
  have hf : ContinuousAt f p := hfc.continuousAt.comp
    (continuous_subtype_val.continuousAt.comp (d.continuousAt hp))
  obtain ⟨e, he, hfe⟩ := T.smoothStructure.property.1.1 (f p)
  let V : Set (Euclidean n) := {a | fiberExponential G y (B.symm a) ∈ e.source}
  have hV : IsOpen V := e.open_source.preimage hfc
  have hpV : (d p).val ∈ V := hfe
  have hH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun a : Euclidean n => (e (fiberExponential G y (B.symm a))).val) V := by
    intro a ha
    exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis D G hG y B
      e he a (hfull _) ha).contDiffWithinAt
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 T.smoothStructure.property.1 f p).mpr
  exact ⟨hf, d, hd, e, he, hp, hfe, V, hV, hpV, _, hH, Eventually.of_forall (fun _ => rfl)⟩

/-- The differential of the exponential composition is its literal chain rule
formula in the original tangent spaces. -/
theorem development_differential (D : Connection (tangentBundle T))
    (G : CurveFamily (Phase T)) (hG : IsMaximalFamily T D G)
    (y : M) (hfull : FullExponentialAt G y)
    (x : X) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean X) (hd : d ∈ S.smoothStructure.val)
    (p : X) (hp : p ∈ d.source) :
    IsDifferential S T (development G x y A E d) p
      ((fiberDifferential T G y (A (E.symm (d p).val))).comp
        (A.toLinearMap.comp (E.symm.toLinearMap.comp
          ((tangentStructure S).fiberCoordinates.equiv d hd p hp).toLinearMap))) := by
  let f := development G x y A E d
  let B : TangentSpace T y ≃ₗ[ℝ] Euclidean n := A.symm.trans E
  let K := (tangentStructure S).fiberCoordinates.equiv d hd p hp
  obtain ⟨L, hL, _⟩ := SmoothManifolds.BracketFromFlow.differentialAt_exists S T f p
    (development_smooth D G hG y hfull x A E d hd p hp)
  obtain ⟨e, he, hfe⟩ := T.smoothStructure.property.1.1 (f p)
  let J := (tangentStructure T).fiberCoordinates.equiv e he (f p) hfe
  have hfc := exponential_basis_continuous D G hG y B hfull
  let V : Set (Euclidean n) := {a | fiberExponential G y (B.symm a) ∈ e.source}
  have hV : IsOpen V := e.open_source.preimage hfc
  have hpV : (d p).val ∈ V := hfe
  have hH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun a : Euclidean n => (e (fiberExponential G y (B.symm a))).val) V := by
    intro a ha
    exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis D G hG y B
      e he a (hfull _) ha).contDiffWithinAt
  have hformula (w : TangentSpace S p) : L w =
      fiberDifferential T G y (A (E.symm (d p).val)) (A (E.symm (K w))) := by
    apply J.injective
    have hh := local_differential_coordinates f p L hL d e hd he hp hfe
      V _ hV hpV hH (Eventually.of_forall (fun _ => rfl)) w
    have hg := fiberDifferential_basis D G hG y B (A (E.symm (d p).val))
      (A (E.symm (K w))) (hfull _) e he hfe
    have hBp : B (A (E.symm (d p).val)) = (d p).val := by simp [B]
    have hBw : B (A (E.symm (K w))) = K w := by simp [B]
    rw [hBp, hBw] at hg
    exact hh.trans hg.symm
  have hLeq : L = (fiberDifferential T G y (A (E.symm (d p).val))).comp
      (A.toLinearMap.comp (E.symm.toLinearMap.comp K.toLinearMap)) :=
    LinearMap.ext hformula
  rw [← hLeq]
  exact hL

/-- In equal finite dimensions a linear map preserving positive definite
bilinear forms is bijective. -/
theorem metric_linearMap_bijective {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ V) (H : LinearMap.BilinForm ℝ W)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) (L : V →ₗ[ℝ] W)
    (hm : ∀ v w, H (L v) (L w) = B v w)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W) : Function.Bijective L := by
  have hinj : Function.Injective L := by
    intro v w hvw
    apply sub_eq_zero.mp
    by_contra hne
    have hp := hpos (v - w) hne
    have hh := hm (v - w) (v - w)
    rw [L.map_sub, hvw, sub_self] at hh
    simp only [map_zero] at hh
    exact (ne_of_gt hp) hh.symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- The local development argument for a supplied normal chart. In fact no
radius bound is needed once the source chart is known to be normal. -/
theorem development_on_normal_chart
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (R : CurvatureTensor S) (Q : CurvatureTensor T)
    (hR : RepresentsCurvature C R) (hQ : RepresentsCurvature D Q)
    (k : ℝ) (hk : ConstantSectional g R k) (hl : ConstantSectional h Q k)
    (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T))
    (hF : IsMaximalFamily S C F) (hG : IsMaximalFamily T D G)
    (x : X) (y : M) (hfull : FullExponentialAt G y)
    (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hA : ∀ v w, pairing h y (A v) (A w) = pairing g x v w)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g x E)
    (r : ℝ) (d : ModelChart n .euclidean X) (hd : IsNormalChart g F x E r d) :
    IsLocalIsometryOn g h (development G x y A E d) d.source ∧
    HasCenterData (development G x y A E d) x y A := by
  let f := development G x y A E d
  let K (p : X) (hp : p ∈ d.source) :=
    (tangentStructure S).fiberCoordinates.equiv d hd.2.1 p hp
  let L (p : X) (hp : p ∈ d.source) : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p) :=
    (fiberDifferential T G y (A (E.symm (d p).val))).comp
      (A.toLinearMap.comp (E.symm.toLinearMap.comp (K p hp).toLinearMap))
  have hL (p : X) (hp : p ∈ d.source) : IsDifferential S T f p (L p hp) :=
    development_differential D G hG y hfull x A E d hd.2.1 p hp
  have hmetric (p : X) (hp : p ∈ d.source) (w z : TangentSpace S p) :
      pairing h (f p) (L p hp w) (L p hp z) = pairing g p w z := by
    let v := E.symm (d p).val
    have hv : tangentNorm g x v < r := by
      have hh := d.map_source hp
      rw [hd.2.2.2.2.1] at hh
      exact hh
    have hexp : fiberExponential F x v = p := (hd.2.2.2.2.2 (d p) hv).2.trans (d.left_inv hp)
    have hdom : (⟨x, v⟩ : Phase S) ∈ exponentialDomain F := (hd.2.2.2.2.2 (d p) hv).1
    have hinv (a : TangentSpace S p) : HEq
        (fiberDifferential S F x v (E.symm (K p hp a))) a := by
      obtain ⟨hq, hcoord⟩ := normal_chart_fiberDifferential g C F hF x E hE r d hd v
        (E.symm (K p hp a)) hv
      have hh : fiberDifferential S F x v (E.symm (K p hp a)) =
          castTangent S hexp.symm a := by
        apply ((tangentStructure S).fiberCoordinates.equiv d hd.2.1 _ hq).injective
        rw [hcoord, LinearEquiv.apply_symm_apply,
          ExponentialJacobi.coordinates_cast hexp.symm d hd.2.1 hp hq]
      rw [hh]
      exact ExponentialJacobi.castTangent_heq (S := S) hexp.symm a
    have hm := exponential_metric_comparison g h C D hC hD R Q hR hQ k hk hl F G hF hG
      x y A hA v hdom (hfull _) (E.symm (K p hp w)) (E.symm (K p hp z))
    exact hm.trans (ConstantCurvaturePolar.pairing_heq g hexp (hinv w) (hinv z))
  constructor
  · refine ⟨d.open_source, ?_⟩
    intro p hp
    have hs := development_smooth D G hG y hfull x A E d hd.2.1 p hp
    letI := (SmoothManifolds.tangent_dimension S p).1
    letI := (SmoothManifolds.tangent_dimension T (f p)).1
    have hdim : Module.finrank ℝ (TangentSpace S p) = Module.finrank ℝ (TangentSpace T (f p)) :=
      (SmoothManifolds.tangent_dimension S p).2.trans (SmoothManifolds.tangent_dimension T (f p)).2.symm
    have hbij : Function.Bijective (L p hp) := by
      apply metric_linearMap_bijective (V := TangentSpace S p) (W := TangentSpace T (f p))
        (pairing g p) (pairing h (f p))
        (g.positive p) (L p hp) (hmetric p hp)
      exact hdim
    exact ⟨hs, inverse_germ_of_bijective_differential f p hs (L p hp) (hL p hp) hbij,
      L p hp, hL p hp, hmetric p hp⟩
  · have hfx : f x = y := by
      change fiberExponential G y (A (E.symm (d x).val)) = y
      rw [hd.2.2.2.1, map_zero, map_zero]
      exact (ExponentialNormalCoordinates.zero_section T D G hG y).2
    refine ⟨hfx, ?_⟩
    have hval (w : TangentSpace S x) : HEq (L x hd.2.2.1 w) (A w) := by
      change HEq (fiberDifferential T G y (A (E.symm (d x).val))
        (A (E.symm ((tangentStructure S).fiberCoordinates.equiv d hd.2.1 x hd.2.2.1 w)))) (A w)
      rw [ExponentialNormalCoordinates.normal_chart_coordinates C F hF g x E r d hd,
        LinearEquiv.symm_apply_apply]
      have hz : A (E.symm (d x).val) = 0 := by
        rw [hd.2.2.2.1, E.symm.map_zero, A.map_zero]
      have hh : HEq
          (fiberDifferential T G y (A (E.symm (d x).val)) (A w))
          (fiberDifferential T G y 0 (A w)) := by rw [hz]
      exact hh.trans ((heq_of_eq (fiberDifferential_zero D G hG y (A w))).trans
        (ExponentialJacobi.castTangent_heq (S := T) _ (A w)))
    have heq : L x hd.2.2.1 = (castTangent T hfx).symm.toLinearMap.comp A.toLinearMap := by
      apply LinearMap.ext
      intro w
      have hcast : HEq ((castTangent T hfx).symm (A w)) (A w) := by
        have hh := ExponentialJacobi.castTangent_heq (S := T) hfx ((castTangent T hfx).symm (A w))
        simpa only [LinearEquiv.apply_symm_apply] using hh.symm
      exact eq_of_heq ((hval w).trans hcast.symm)
    rw [← heq]
    exact hL x hd.2.2.1


/-- The center value and a metric linear isometry are extracted from an actual
local isometry. No prescribed exponential-intertwining data are assumed. -/
theorem center_data_exists (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : X → M) (U : Set X) (hf : IsLocalIsometryOn g h f U)
    (x : X) (hx : x ∈ U) :
    ∃ A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T (f x),
      (∀ v w, pairing h (f x) (A v) (A w) = pairing g x v w) ∧
      HasCenterData f x (f x) A := by
  obtain ⟨L, hL, hm⟩ := (hf.2 x hx).2.2
  letI := (SmoothManifolds.tangent_dimension S x).1
  letI := (SmoothManifolds.tangent_dimension T (f x)).1
  have hdim : Module.finrank ℝ (TangentSpace S x) = Module.finrank ℝ (TangentSpace T (f x)) :=
    (SmoothManifolds.tangent_dimension S x).2.trans (SmoothManifolds.tangent_dimension T (f x)).2.symm
  have hbij : Function.Bijective L := by
    apply metric_linearMap_bijective (V := TangentSpace S x) (W := TangentSpace T (f x))
      (pairing g x) (pairing h (f x)) (g.positive x) L hm
    exact hdim
  let A := LinearEquiv.ofBijective L hbij
  refine ⟨A, hm, rfl, ?_⟩
  change IsDifferential S T f x L
  exact hL

/-- Logical assembly of the extension step from germ uniqueness. This is an
ordinary reduction lemma, not a conditional target: its uniqueness premise is
an outstanding obligation and is not among the frozen upstream premises. -/
theorem germ_extension_of_uniqueness
    (huniq : P202Specs.Geometry.LocalSpaceFormDevelopment.germUniquenessType.{u}) :
    P202Specs.Geometry.LocalSpaceFormDevelopment.germExtensionType.{u} := by
  intro n hn X M _ _ _ S T g h C D hC hD R Q hR hQ k hk hl hc F G hF hG
    x f U hf hx E hE r d hr hd
  obtain ⟨A, hA, hcenter⟩ := center_data_exists g h f U hf x hx
  have hdev := development_on_normal_chart g h C D hC hD R Q hR hQ k hk hl F G hF hG
    x (f x) (full_target_exponential h D hD hc G hG (f x)) A hA E hE r d hd
  refine ⟨A, hA, hcenter, hdev.1, ?_⟩
  exact huniq S T g h f (development G x (f x) A E d) U d.source hf hdev.1
    x hx hd.2.2.1 (f x) A hcenter hdev.2

end P202.Geometry.LocalSpaceFormDevelopment


/-! Restriction to a genuine open submanifold for the germ argument. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.LocalSpaceFormDevelopment.Localization
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.LocalDevelopmentData
open Set Filter
open scoped _root_.Topology
universe u
open private scalar_comp_at from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

theorem differential_comp_at {n m l : ℕ} {X M N : Type u}
    [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
    (R : SmoothManifold n .euclidean X) (S : SmoothManifold m .euclidean M)
    (T : SmoothManifold l .euclidean N) (i : X → M) (f : M → N) (p : X)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f (i p))
    (L : TangentSpace R p →ₗ[ℝ] TangentSpace S (i p))
    (K : TangentSpace S (i p) →ₗ[ℝ] TangentSpace T (f (i p)))
    (hL : IsDifferential R S i p L) (hK : IsDifferential S T f (i p) K) :
    IsDifferential R T (f ∘ i) p (K.comp L) := by
  intro v h k r hr hk
  obtain ⟨s, hs, he⟩ := (SmoothManifolds.mem_smoothGermAlgebra_iff T (f (i p)) h.val).mp h.property
  have hrs : s =ᶠ[𝓝 (f (i p))] r := Germ.coe_eq.mp (he.symm.trans hr.symm)
  have hrsm := hs.congr hrs
  let j : SmoothGerm S (i p) := ⟨Germ.ofFun (r ∘ f),
    Algebra.subset_adjoin ⟨r ∘ f, scalar_comp_at hf hrsm, rfl⟩⟩
  exact (hK (L v) h j r hr rfl).trans (hL v j k (r ∘ f) rfl hk)


theorem smoothAt_codRestrict_open {n m : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold m .euclidean M)
    (U : Set M) (hU : IsOpen U) (R : SmoothManifold m .euclidean U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas T.smoothStructure.val U hU))
    (f : X → U) (p : X)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val
      (fun q => (f q).val) p) :
    ManifoldSmoothAt S.smoothStructure.val R.smoothStructure.val f p := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hfc⟩ := T.smoothStructure.property.1.1 (f p).val
  let d := c.subtypeRestr (s := ⟨U, hU⟩) ⟨f p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _ T.smoothStructure.property.1 U hU)
      ⟨⟨f p⟩, c, hc, rfl⟩
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 R.smoothStructure.property.1 f p).mpr
  refine ⟨tendsto_subtype_rng.mpr hf.1, e, he, d, hd, hp, ?_, ?_⟩
  · simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hfc
  · exact hf.2 e he c hc hp hfc

theorem local_diffeomorphism_restrict_open {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (U : Set X) (hU : IsOpen U) (R : SmoothManifold n .euclidean U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U hU))
    (hi : IsSmoothMap R S Subtype.val) (f : X → M)
    (hf : ∀ p ∈ U, ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p ∧
      ∃ j : M → X,
        ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val j (f p) ∧
        j (f p) = p ∧ (j ∘ f) =ᶠ[𝓝 p] id ∧ (f ∘ j) =ᶠ[𝓝 (f p)] id) :
    SmoothManifolds.TensorData.IsLocalDiffeomorphism R T (f ∘ Subtype.val) := by
  classical
  refine ⟨fun p => SmoothManifolds.manifoldContDiffAt_comp
    S.smoothStructure.property.1.1 (hi p) (hf p.val p.property).1, ?_⟩
  intro p
  obtain ⟨j, hj, hjp, hjf, hfj⟩ := (hf p.val p.property).2
  let k : M → U := fun q => if hq : j q ∈ U then ⟨j q, hq⟩ else p
  have hmem : ∀ᶠ q in 𝓝 (f p.val), j q ∈ U := by
    apply hj.1.preimage_mem_nhds
    rw [hjp]
    exact hU.mem_nhds p.property
  have hkj : (fun q => (k q).val) =ᶠ[𝓝 (f p.val)] j := by
    filter_upwards [hmem] with q hq
    simp only [k, dite_eq_left hq]
  have hks : ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val
      (fun q => (k q).val) (f p.val) :=
    SmoothManifolds.manifoldContDiffAt_congr hj hkj.symm
  refine ⟨k, smoothAt_codRestrict_open T S U hU R hR k (f p.val) hks, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact hkj.self_of_nhds.trans hjp
  · filter_upwards [hjf.comp_tendsto continuousAt_subtype_val,
      hkj.comp_tendsto ((hf p.val p.property).1.1.comp continuousAt_subtype_val)] with q hq hkq
    apply Subtype.ext
    exact hkq.trans hq
  · filter_upwards [hkj, hfj] with q hkq hq
    change f (k q).val = q
    rw [hkq]
    exact hq

theorem map_restrict_isometry {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (U : Set X) (hU : IsOpen U) (R : SmoothManifold n .euclidean U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U hU))
    (hi : IsSmoothMap R S Subtype.val)
    (E : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (gR : RiemannianMetric R)
    (hgR : ∀ p v w, pairing gR p v w = pairing g p.val (E p v) (E p w))
    (f : X → M) (hf : IsLocalIsometryOn g h f U) :
    IsLocalIsometry gR h (f ∘ Subtype.val) := by
  classical
  have hld := local_diffeomorphism_restrict_open S T U hU R hR hi f
    (fun p hp => ⟨(hf.2 p hp).1, (hf.2 p hp).2.1⟩)
  refine ⟨hld, ?_⟩
  choose L hL hm using fun p : U => (hf.2 p.val p.property).2.2
  refine ⟨fun p => (L p).comp (E p).toLinearMap, ?_, ?_⟩
  · intro p
    exact differential_comp_at R S T Subtype.val f p (hf.2 p.val p.property).1
      (E p).toLinearMap (L p) (hE p) (hL p)
  · intro p v w
    exact (hm p (E p v) (E p w)).trans (hgR p v w).symm

theorem open_metric_localization {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (U : Set X) (hU : IsOpen U) :
    ∃ (R : SmoothManifold n .euclidean U)
      (E : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
      (gR : RiemannianMetric R),
      (∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap) ∧
      (∀ p v w, pairing gR p v w = pairing g p.val (E p v) (E p w)) ∧
      ∀ f : X → M, IsLocalIsometryOn g h f U → IsLocalIsometry gR h (f ∘ Subtype.val) := by
  classical
  obtain ⟨R, _, hR, hi⟩ := SmoothManifolds.exists_openSubset_smoothManifold S U hU
  choose E hE using SmoothManifolds.OrientedTopDegreeResults.LocalTransport.open_inclusion_differential_equiv
    S U hU R hR hi
  let i : SmoothImmersion R S Subtype.val := ⟨hi, fun p => (E p).toLinearMap, hE,
    fun p => (E p).injective⟩
  obtain ⟨gR, hgR⟩ := P202.Geometry.SmoothMetrics.pullback_metric R S Subtype.val i g
  refine ⟨R, E, gR, hE, hgR, ?_⟩
  exact map_restrict_isometry S T g h U hU R hR hi E hE gR hgR

theorem center_data_restrict {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (U : Set X) (R : SmoothManifold n .euclidean U)
    (E : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (f : X → M) (p : U) (y : M)
    (A : TangentSpace S p.val ≃ₗ[ℝ] TangentSpace T y)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p.val)
    (hc : HasCenterData f p.val y A) :
    HasCenterData (f ∘ Subtype.val) p y ((E p).trans A) := by
  obtain ⟨e, he⟩ := hc
  refine ⟨e, ?_⟩
  exact differential_comp_at R S T Subtype.val f p hf (E p).toLinearMap
    ((P202.ExponentialJacobiData.castTangent T e).symm.toLinearMap.comp A.toLinearMap)
    (hE p) he

/-- Uniqueness on globally defined smooth local isometries. This proposition
has the same germ conclusion as the independent target, with global map hypotheses. -/
def GlobalGermUniqueness : Prop :=
  ∀ {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f₁ f₂ : X → M),
    IsLocalIsometry g h f₁ → IsLocalIsometry g h f₂ →
    ∀ (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y),
    HasCenterData f₁ x y A → HasCenterData f₂ x y A → f₁ =ᶠ[𝓝 x] f₂

theorem germ_uniqueness_of_global (hglobal : GlobalGermUniqueness.{u}) :
    P202Specs.Geometry.LocalSpaceFormDevelopment.germUniquenessType.{u} := by
  intro n X M _ _ S T g h f₁ f₂ U₁ U₂ hf₁ hf₂ x hx₁ hx₂ y A hc₁ hc₂
  let U := U₁ ∩ U₂
  have hU : IsOpen U := hf₁.1.inter hf₂.1
  have h₁ : IsLocalIsometryOn g h f₁ U := ⟨hU, fun p hp => hf₁.2 p hp.1⟩
  have h₂ : IsLocalIsometryOn g h f₂ U := ⟨hU, fun p hp => hf₂.2 p hp.2⟩
  obtain ⟨R, E, gR, hE, _hgR, hrestrict⟩ := open_metric_localization S T g h U hU
  let p : U := ⟨x, hx₁, hx₂⟩
  have hp₁ := center_data_restrict S T U R E hE f₁ p y A (hf₁.2 x hx₁).1 hc₁
  have hp₂ := center_data_restrict S T U R E hE f₂ p y A (hf₂.2 x hx₂).1 hc₂
  have heq := hglobal R T gR h (f₁ ∘ Subtype.val) (f₂ ∘ Subtype.val)
    (hrestrict f₁ h₁) (hrestrict f₂ h₂) p y ((E p).trans A) hp₁ hp₂
  rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq p]
  exact heq

end P202.Geometry.LocalSpaceFormDevelopment.Localization


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.LocalSpaceFormDevelopment
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData
open Set Filter
open scoped _root_.Topology
universe u
variable {n m : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
  {S : SmoothManifold n .euclidean X} {T : SmoothManifold m .euclidean M}

theorem tangent_derivative_congr (C : Connection (tangentBundle S))
    {c : ℝ → X} {V W : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    {D : TangentSpace S (c t)} (h : HasCovariantDerivativeAt C c V t D)
    (he : ∀ᶠ s in 𝓝 t, V s = W s) : HasCovariantDerivativeAt C c W t D := by
  obtain ⟨v, hv, U, hU, b, hp, a, ha, hD⟩ := h
  have hc : coefficientsAlong b c V =ᶠ[𝓝 t] coefficientsAlong b c W := by
    filter_upwards [he] with s hs
    simp only [coefficientsAlong, hs]
  refine ⟨v, hv, U, hU, b, hp, a, ?_, ?_⟩
  · exact ha.congr_of_eventuallyEq (by simpa only [nhdsWithin_univ] using hc.symm)
      (by simp only [coefficientsAlong, he.self_of_nhds])
  · rw [hD]
    unfold frameDerivative
    rw [hc.self_of_nhds]

theorem tangent_derivative_zero (C : Connection (tangentBundle S))
    {c : ℝ → X} {t : ℝ} {v : TangentSpace S (c t)}
    (hv : HasVelocityWithinAt S c univ t v) :
    HasCovariantDerivativeAt C c (fun _ => 0) t 0 := by
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame
    (tangentBundle S) (c t)
  refine ⟨v, hv, U, hU, b, hp, 0, ?_, ?_⟩
  · have he : coefficientsAlong b c (fun _ => 0) = fun _ => 0 := by
      funext s
      simp [coefficientsAlong]
    rw [he]
    exact hasDerivWithinAt_const t univ 0
  · simp [frameDerivative, coefficientsAlong]

theorem tangent_derivative_finset_sum {α : Type} (s : Finset α)
    (C : Connection (tangentBundle S)) {c : ℝ → X} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityWithinAt S c univ t v)
    (V : α → (s : ℝ) → TangentSpace S (c s))
    (D : α → TangentSpace S (c t))
    (h : ∀ i ∈ s, HasCovariantDerivativeAt C c (V i) t (D i)) :
    HasCovariantDerivativeAt C c (fun a => ∑ i ∈ s, V i a) t (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tangent_derivative_zero C hv
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using CurveCovariantDerivative.derivative_add C
      (mem_univ t) (uniqueDiffWithinAt_univ) (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Naturality for one smooth section evaluated on a curve. -/
theorem localIsometry_derivative_section
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (f : X → M) (hi : IsLocalIsometry g h f) (hf : IsSmoothMap S T f)
    (Y : Field S) {c : ℝ → X} {t : ℝ} {v : TangentSpace S (c t)}
    (hv : HasVelocityWithinAt S c univ t v) :
    HasCovariantDerivativeAt K (f ∘ c)
      (fun s => SmoothManifolds.differential S T f hf (c s) (Y.val (c s))) t
      (SmoothManifolds.differential S T f hf (c t)
        (pointDerivative C Y.val (c t) v)) := by
  let L := SmoothManifolds.differential S T f hf
  have hL := SmoothManifolds.differential_spec S T f hf
  obtain ⟨hlocal, A, hA, hmA⟩ := hi
  have hAL : A = L := by
    funext p
    exact (SmoothManifolds.differential_exists S T f hf p).unique (hA p) (hL p)
  have hm : IsMetricPreserving g h f L := hAL ▸ hmA
  obtain ⟨X, hXv⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) v
  obtain ⟨X', hX'⟩ := LeviCivita.exists_related_germ f hlocal L hL X (c t)
  obtain ⟨Y', hY'⟩ := LeviCivita.exists_related_germ f hlocal L hL Y (c t)
  have hfv := GaussLemma.velocity_smooth_postcomposition f hf (mem_univ t) hv
  have hv' : HasVelocityWithinAt T (f ∘ c) univ t (X'.val ((f ∘ c) t)) := by
    simpa only [Function.comp_apply, ← hX'.self_of_nhds, hXv] using hfv
  have hd := CurveCovariantDerivative.derivative_section_field K Y' X' (mem_univ t) hv'
  have he := LeviCivita.connection_related_at TorsionAndMetric.torsion_apply
    f hlocal L hL g h hm C K hC hK X Y X' Y' (c t) hX' hY'
  rw [← ConnectionForms.pointDerivative_global (tangentBundle S) C Y (c t) X, hXv] at he
  simp only [Function.comp_apply] at hd
  rw [← he] at hd
  apply tangent_derivative_congr K hd
  have hvc : ContinuousAt c t := by simpa only [continuousWithinAt_univ] using hv.1
  filter_upwards [hvc.eventually hY'] with s hs
  exact hs.symm

/-- The intrinsic differential of a local isometry commutes with covariant
 differentiation along every differentiable field on a curve. -/
theorem localIsometry_covariant_derivative
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (f : X → M) (hi : IsLocalIsometry g h f) (hf : IsSmoothMap S T f)
    {c : ℝ → X} {W : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    {D : TangentSpace S (c t)} (hD : HasCovariantDerivativeAt C c W t D) :
    HasCovariantDerivativeAt K (f ∘ c)
      (fun s => SmoothManifolds.differential S T f hf (c s) (W s)) t
      (SmoothManifolds.differential S T f hf (c t) D) := by
  classical
  let L := SmoothManifolds.differential S T f hf
  obtain ⟨v, hv, U, hU, b, hp, a', ha', hDeq⟩ := hD
  let a := coefficientsAlong b c W
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b ⟨c t, hp⟩
  let d (j : Fin n) := pointDerivative C (e j).val (c t) v
  let Z (j : Fin n) (s : ℝ) := a s j • (e j).val (c s)
  let Dz (j : Fin n) := a' j • (e j).val (c t) + a t j • d j
  have hz (j : Fin n) : HasCovariantDerivativeAt C c (Z j) t (Dz j) := by
    exact CurveCovariantDerivative.derivative_smul C
      (CurveCovariantDerivative.derivative_section C (e j) (mem_univ t) hv)
      (hasDerivWithinAt_pi.mp ha' j)
  have hsum := tangent_derivative_finset_sum Finset.univ C hv Z Dz (fun j _ => hz j)
  have hvc : ContinuousAt c t := by simpa only [continuousWithinAt_univ] using hv.1
  have hrep : ∀ᶠ s in 𝓝 t, (∑ j, Z j s) = W s := by
    filter_upwards [hvc.eventually (hU.mem_nhds hp),
      hvc.eventually (Filter.eventually_all.mpr he)] with s hs hes
    have hev (j : Fin n) : (e j).val (c s) = b.basis ⟨c s, hs⟩ j := by
      simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ (c s) hs,
        b.basis_eq] using hes j
    simp only [Z, a, CurveCovariantDerivative.coefficientsAlong_of_mem b c W s hs, hev]
    exact (b.basis ⟨c s, hs⟩).sum_equivFun (W s)
  have hDsum : (∑ j, Dz j) = D := by
    exact CurveCovariantDerivative.covariantDerivative_unique C (mem_univ t)
      uniqueDiffWithinAt_univ (tangent_derivative_congr C hsum hrep)
      ⟨v, hv, U, hU, b, hp, a', ha', hDeq⟩
  have hvf := GaussLemma.velocity_smooth_postcomposition f hf (mem_univ t) hv
  have hz' (j : Fin n) :
      HasCovariantDerivativeAt K (f ∘ c) (fun s => L (c s) (Z j s)) t (L (c t) (Dz j)) := by
    have hsec := localIsometry_derivative_section g h C K hC hK f hi hf (e j) hv
    have hh := CurveCovariantDerivative.derivative_smul K hsec
      (hasDerivWithinAt_pi.mp ha' j)
    simpa only [Z, Dz, d, map_smul, map_add, L] using hh
  have hsum' := tangent_derivative_finset_sum Finset.univ K hvf
    (fun j s => L (c s) (Z j s)) (fun j => L (c t) (Dz j)) (fun j _ => hz' j)
  have hrep' : ∀ᶠ s in 𝓝 t, (∑ j, L (c s) (Z j s)) = L (c s) (W s) := by
    filter_upwards [hrep] with s hs
    rw [← map_sum, hs]
  have hEq : (∑ j, L (c t) (Dz j)) = L (c t) D := by rw [← map_sum, hDsum]
  rw [hEq] at hsum'
  exact tangent_derivative_congr K hsum' hrep'

/-- Global local isometries preserve actual intrinsic geodesics. -/
theorem localIsometry_geodesic
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hK : IsLeviCivita h K)
    (f : X → M) (hi : IsLocalIsometry g h f) (hf : IsSmoothMap S T f)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) :
    IsGeodesicOn T K I.carrier
      (fun t => ⟨f (q t).1, SmoothManifolds.differential S T f hf (q t).1 (q t).2⟩) := by
  intro t ht
  obtain ⟨hv, ha⟩ := hq t ht
  refine ⟨GaussLemma.velocity_smooth_postcomposition f hf (mem_univ t) hv, ?_⟩
  simpa only [Function.comp_def, map_zero] using localIsometry_covariant_derivative g h C K hC hK f hi hf ha

end P202.Geometry.LocalSpaceFormDevelopment


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace P202.Geometry.LocalSpaceFormDevelopment
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
  P202.ExponentialJacobiData P202.LocalDevelopmentData
open Set Filter
open scoped _root_.Topology
universe u
variable {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
  {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}

theorem center_phase_eq (f : X → M) (hf : IsSmoothMap S T f)
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hc : HasCenterData f x y A) (v : TangentSpace S x) :
    (⟨f x, SmoothManifolds.differential S T f hf x v⟩ : Phase T) = ⟨y, A v⟩ := by
  obtain ⟨e, hd⟩ := hc
  cases e
  have heq : SmoothManifolds.differential S T f hf x = A.toLinearMap := by
    apply (SmoothManifolds.differential_exists S T f hf x).unique
    · exact SmoothManifolds.differential_spec S T f hf x
    · simpa [castTangent] using hd
  rw [heq]
  rfl

theorem global_germ_uniqueness_of_geodesic_preservation
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T))
    (hC : IsLeviCivita g C) (hD : IsLeviCivita h D)
    (hpres : ∀ (f : X → M) (_hf : IsLocalIsometry g h f)
      (hs : IsSmoothMap S T f) (I : D13Unified.OpenTimeInterval)
      (q : ℝ → Phase S), IsGeodesicOn S C I.carrier q →
      IsGeodesicOn T D I.carrier (fun t =>
        ⟨f (q t).1, SmoothManifolds.differential S T f hs (q t).1 (q t).2⟩))
    (f₁ f₂ : X → M) (hf₁ : IsLocalIsometry g h f₁)
    (hf₂ : IsLocalIsometry g h f₂)
    (hs₁ : IsSmoothMap S T f₁) (hs₂ : IsSmoothMap S T f₂)
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hc₁ : HasCenterData f₁ x y A) (hc₂ : HasCenterData f₂ x y A) :
    f₁ =ᶠ[𝓝 x] f₂ := by
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_exists S g x
  obtain ⟨r, d, hd⟩ := ExponentialNormalCoordinates.normal_chart_exists S g C hC F hF x E hE
  have hexp (v : TangentSpace S x)
      (hv : (⟨x, v⟩ : Phase S) ∈ exponentialDomain F) :
      f₁ (fiberExponential F x v) = f₂ (fiberExponential F x v) := by
    let w : Phase S := ⟨x, v⟩
    let q₁ : ℝ → Phase T := fun t =>
      ⟨f₁ (F.curve w t).1,
        SmoothManifolds.differential S T f₁ hs₁ (F.curve w t).1 (F.curve w t).2⟩
    let q₂ : ℝ → Phase T := fun t =>
      ⟨f₂ (F.curve w t).1,
        SmoothManifolds.differential S T f₂ hs₂ (F.curve w t).1 (F.curve w t).2⟩
    have hq₁ : IsGeodesicOn T D (F.interval w).carrier q₁ :=
      hpres f₁ hf₁ hs₁ (F.interval w) (F.curve w) (hF w).2.2.1
    have hq₂ : IsGeodesicOn T D (F.interval w).carrier q₂ :=
      hpres f₂ hf₂ hs₂ (F.interval w) (F.curve w) (hF w).2.2.1
    have heq₀ : q₁ 0 = q₂ 0 := by
      change (fun z : Phase S =>
        (⟨f₁ z.1, SmoothManifolds.differential S T f₁ hs₁ z.1 z.2⟩ : Phase T))
        (F.curve w 0) = (fun z : Phase S =>
        (⟨f₂ z.1, SmoothManifolds.differential S T f₂ hs₂ z.1 z.2⟩ : Phase T))
        (F.curve w 0)
      rw [(hF w).2.1]
      exact (center_phase_eq f₁ hs₁ x y A hc₁ v).trans
        (center_phase_eq f₂ hs₂ x y A hc₂ v).symm
    have heq := GeodesicIVP.overlap_unique T D (F.interval w) (F.interval w)
      q₁ q₂ hq₁ hq₂ 0 ⟨(hF w).1, (hF w).1⟩ heq₀
    exact congrArg Sigma.fst (heq ⟨hv, hv⟩)
  filter_upwards [d.open_source.mem_nhds hd.2.2.1] with p hp
  have hm : tangentNorm g x (E.symm (d p).val) < r := by
    have hmem := d.map_source hp
    rwa [hd.2.2.2.2.1] at hmem
  have hnormal := hd.2.2.2.2.2 (d p) hm
  have hpoint : fiberExponential F x (E.symm (d p).val) = p :=
    hnormal.2.trans (d.left_inv hp)
  simpa only [hpoint] using hexp (E.symm (d p).val) hnormal.1


/-- Globally defined local isometries with the same center data have equal germs. -/
theorem global_germ_uniqueness
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f₁ f₂ : X → M) (hf₁ : IsLocalIsometry g h f₁)
    (hf₂ : IsLocalIsometry g h f₂)
    (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (hc₁ : HasCenterData f₁ x y A) (hc₂ : HasCenterData f₂ x y A) :
    f₁ =ᶠ[𝓝 x] f₂ := by
  obtain ⟨C, hC, _⟩ := LeviCivita.exists_unique g
  obtain ⟨D, hD, _⟩ := LeviCivita.exists_unique h
  exact global_germ_uniqueness_of_geodesic_preservation g h C D hC hD
    (fun f hf hs I q hq => localIsometry_geodesic g h C D hC hD f hf hs I q hq)
    f₁ f₂ hf₁ hf₂ hf₁.1.1 hf₂.1.1 x y A hc₁ hc₂


end P202.Geometry.LocalSpaceFormDevelopment


namespace P202.Geometry.LocalSpaceFormDevelopment
universe u

/-- The exponential formula is a smooth local isometry on each normal ball. -/
theorem development : P202Specs.Geometry.LocalSpaceFormDevelopment.developmentType.{u} := by
  intro n _ X M _ _ _ S T g h C D hC hD R Q hR hQ k hk hl hc F G hF hG x y A hA E hE r d _ hd
  exact development_on_normal_chart g h C D hC hD R Q hR hQ k hk hl F G hF hG x y
    (full_target_exponential h D hD hc G hG y) A hA E hE r d hd

/-- The center value and differential determine a local-isometry germ. -/
theorem germ_uniqueness : P202Specs.Geometry.LocalSpaceFormDevelopment.germUniquenessType.{u} := by
  apply Localization.germ_uniqueness_of_global
  intro n X M _ _ S T g h f₁ f₂ hf₁ hf₂ x y A hc₁ hc₂
  exact global_germ_uniqueness g h f₁ f₂ hf₁ hf₂ x y A hc₁ hc₂

/-- Every local-isometry germ extends over each prescribed normal ball. -/
theorem germ_extension : P202Specs.Geometry.LocalSpaceFormDevelopment.germExtensionType.{u} := by
  exact germ_extension_of_uniqueness germ_uniqueness

end P202.Geometry.LocalSpaceFormDevelopment
