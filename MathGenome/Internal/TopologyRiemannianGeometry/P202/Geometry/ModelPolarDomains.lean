import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ModelPolarDomains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HyperbolicHalfSpace
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConstantCurvaturePolar
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.StandardCoverings
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.SpaceFormData P202.ModelPolarData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData
open P202Specs.Geometry.ModelPolarDomains

/-- The earlier construction supplies all three actual models and the
intrinsic hyperboloid/half-space bridge. -/
theorem models_exist : modelsExistType := HyperbolicHalfSpace.models

/-- Universal maximality identifies every chosen maximal family with the
explicit all-time affine geodesics, including zero initial velocity. -/
theorem euclidean_formula : euclideanFormulaType := by
  intro n G hG F hF p v
  obtain ⟨q, hq, hformula⟩ := hG.2.2.2.2 p v
  have hm := (hF ⟨p, v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
    hq.1 hq.2.1 hq.2.2.1
  refine ⟨hm.1 (by trivial), ?_⟩
  exact (congrArg Sigma.fst (hm.2 (by trivial))).trans (hformula 1).1

/-- An attained minimizing velocity must be the unique affine displacement.
This uses Hopf–Rinow, which is independent of Killing–Hopf. -/
theorem euclidean_distance : euclideanDistanceType := by
  intro n G hG F hF p v
  let : ConnectedSpace (E n) := hG.1
  obtain ⟨w, hw, hdist⟩ := CompleteExponentialMinimizers.attaining_vectors
    G.metric G.connection G.leviCivita F hF p
    (fun w => (euclidean_formula n G hG F hF p w).1) (fiberExponential F p v)
  have heq := (euclidean_formula n G hG F hF p w).2.symm.trans
    (hw.trans (euclidean_formula n G hG F hF p v).2)
  have hwv : w = v := (G.coordinates p).injective (by
    simpa only [line, one_smul] using add_left_cancel heq)
  simpa only [hwv] using hdist.symm

/-- The all-speed spherical formula is the same intrinsic exponential,
independently of the selection of maximal representatives. -/
theorem spherical_formula : sphericalFormulaType := by
  intro n a A B hB F hF p v
  obtain ⟨q, hq, hformula⟩ := hB.2.2.2.2.1 p v
  have hm := (hF ⟨p, v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
    hq.1 hq.2.1 hq.2.2.1
  refine ⟨hm.1 (by trivial), ?_⟩
  exact (congrArg (fun z : Phase B.manifold => z.1.val) (hm.2 (by trivial))).trans
    (hformula 1).1

/-- All unit directions reach the actual ambient antipode at the prescribed
cut time. The exponential/scaled-geodesic bridge is the upstream radial identity. -/
theorem spherical_cut_time : sphericalCutTimeType := by
  intro n a ha A B hB F hF p v hv
  obtain ⟨q, hq, hformula⟩ := hB.2.2.2.2.2 p v hv
  have hm := (hF ⟨p, v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
    hq.1 hq.2.1 hq.2.2.1
  have ht : Real.pi * a ∈ (F.interval ⟨p, v⟩).carrier := hm.1 (by trivial)
  obtain ⟨hdomain, heq⟩ := ExponentialNormalCoordinates.radial_identity
    B.manifold B.connection F hF p v (Real.pi * a) ht
  refine ⟨hdomain, ?_⟩
  rw [heq]
  have hphase := congrArg (fun z : Phase B.manifold => z.1.val) (hm.2 (x := Real.pi * a) (by trivial))
  rw [hphase, (hformula (Real.pi * a)).1]
  simp [greatCircle, mul_div_cancel_right₀ _ (ne_of_gt ha)]

/-- The specific orthogonal map needed for spherical homogeneity. Its
restriction is connected to the intrinsic smooth metric below. -/
theorem sphere_orthogonal_transitive {n : ℕ} {a : ℝ} (p q : Sphere n a) :
    ∃ U : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1), U p.val = q.val := by
  refine ⟨Submodule.reflection (ℝ ∙ (p.val - q.val))ᗮ, ?_⟩
  apply Submodule.reflection_sub
  have hp : ‖p.val‖ = a := by simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  have hq : ‖q.val‖ = a := by simpa only [Metric.mem_sphere, dist_zero_right] using q.property
  exact hp.trans hq.symm

section NormalDistance
open P202.CurveData P202.DistanceData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n .euclidean M}

/-- A normal chart supplies global radial distance equality below its radius.
The comparison is against every piecewise-C1 competitor in the manifold. -/
theorem normal_chart_distance (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (R : ℝ) (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R) :
    modelDistance g p (fiberExponential F p v) = tangentNorm g p v := by
  let r := (tangentNorm g p v + R) / 2
  have hn := SmoothMetrics.tangentNorm_nonneg g p v
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hvr : tangentNorm g p v < r := by dsimp [r]; linarith
  obtain ⟨γ, h0, h1, hrad, hcurve, hgeo, hlen⟩ :=
    NormalMinimality.radial_segment_exists S g C hC F hF p E R d hd v hv
  apply le_antisymm
  · have h := CompleteExponentialMinimizers.lengthDistance_le_length g γ
    simpa only [h0, h1, hlen] using h
  · apply le_csInf
    · exact ⟨length g γ, 0, 1, γ, h0, h1, rfl⟩
    · intro L hL
      obtain ⟨a, b, η, hη0, hη1, rfl⟩ := hL
      exact (NormalMinimality.global_comparison S g C hC F hF p E r R d hr hrR hd
        v hvr η hη0 hη1).1
end NormalDistance

end P202.Geometry.ModelPolarDomains

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.SpaceFormData P202.ModelPolarData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
open Set Filter
open scoped _root_.Topology

 theorem euclidean_contDiff_smooth {n m : ℕ} (A : EuclideanModel n)
    (B : EuclideanModel m) (f : E n → E m) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsSmoothMap A.manifold B.manifold f := by
  let c : ModelChart n .euclidean (E n) :=
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).toOpenPartialHomeomorph.trans
      (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph
  let d : ModelChart m .euclidean (E m) :=
    (PiLp.homeomorph 2 (fun _ : Fin m => ℝ)).toOpenPartialHomeomorph.trans
      (Homeomorph.Set.univ (Euclidean m)).symm.toOpenPartialHomeomorph
  have hc : c ∈ A.manifold.smoothStructure.val := by
    rw [A.standard]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.transportAtlas_isContDiffAtlas _ _ _
        (SmoothManifolds.StandardCoverings.euclideanAtlas_isContDiffAtlas n))
      ⟨_, rfl, rfl⟩
  have hd : d ∈ B.manifold.smoothStructure.val := by
    rw [B.standard]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.transportAtlas_isContDiffAtlas _ _ _
        (SmoothManifolds.StandardCoverings.euclideanAtlas_isContDiffAtlas m))
      ⟨_, rfl, rfl⟩
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let K := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)
  intro p
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart _ _ _
    A.manifold.smoothStructure.property.1 B.manifold.smoothStructure.property.1 f p).mpr
  refine ⟨hf.continuous.continuousAt, c, hc, d, hd, ?_, ?_, ?_⟩
  · change p ∈ Set.univ ∩ _
    exact ⟨mem_univ _, mem_univ _⟩
  · change f p ∈ Set.univ ∩ _
    exact ⟨mem_univ _, mem_univ _⟩
  · refine ⟨univ, isOpen_univ, mem_univ _, fun x => K (f (L.symm x)), ?_, ?_⟩
    · exact (K.contDiff.comp (hf.comp L.symm.contDiff)).contDiffOn
    · exact Eventually.of_forall (fun y => by
        change K (f (L.symm (L y))) = K (f y)
        rw [L.symm_apply_apply])

theorem euclidean_differential_coordinates {n m : ℕ} (A : EuclideanModel n)
    (B : EuclideanModel m) (f : E n → E m) (hf : IsSmoothMap A.manifold B.manifold f)
    (p : E n) (L : TangentSpace A.manifold p →ₗ[ℝ] TangentSpace B.manifold (f p))
    (hL : SmoothManifolds.DifferentialData.IsDifferential A.manifold B.manifold f p L)
    (D : E n →L[ℝ] E m) (hD : HasFDerivAt f D p)
    (v : TangentSpace A.manifold p) :
    B.coordinates (f p) (L v) = D (A.coordinates p v) := by
  let c : ℝ → E n := fun t => p + t • A.coordinates p v
  have h0 : c 0 = p := by simp [c]
  let w : TangentSpace A.manifold (c 0) := h0.symm ▸ v
  have htransport (x y : E n) (h : x = y) (v : TangentSpace A.manifold x) :
      A.coordinates y (h ▸ v) = A.coordinates x v := by subst y; rfl
  have hw : A.coordinates (c 0) w = A.coordinates p v := htransport p (c 0) h0.symm v
  have hc : HasDerivAt c (A.coordinates (c 0) w) 0 := by
    rw [hw]
    change HasDerivAt (fun t : ℝ => p + t • A.coordinates p v) _ 0
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const (A.coordinates p v)).const_add p
  have hv : P202.CurveConnectionData.HasVelocityWithinAt A.manifold c univ 0 w :=
    (A.velocity c 0 w).mpr hc
  have hv' : P202.CurveData.HasVelocityAt A.manifold c 0 w := by
    simpa only [P202.CurveConnectionData.HasVelocityWithinAt, P202.CurveData.HasVelocityAt,
      continuousWithinAt_univ, hasDerivWithinAt_univ] using hv
  have htransportL (x y : E n) (h : x = y)
      (LL : TangentSpace A.manifold x →ₗ[ℝ] TangentSpace B.manifold (f x))
      (hLL : SmoothManifolds.DifferentialData.IsDifferential A.manifold B.manifold f x LL) :
      SmoothManifolds.DifferentialData.IsDifferential A.manifold B.manifold f y (h ▸ LL) := by
    subst y; exact hLL
  have hL' : SmoothManifolds.DifferentialData.IsDifferential A.manifold B.manifold
      f (c 0) (h0.symm ▸ L) := htransportL p (c 0) h0.symm L hL
  have hpost := PiecewiseCurves.HasVelocityAt.postcomp hf hv' (h0.symm ▸ L) hL'
  have ht : HasDerivAt (f ∘ c)
      (B.coordinates (f (c 0)) ((h0.symm ▸ L) w)) 0 := by
    apply (B.velocity (f ∘ c) 0 _).mp
    obtain ⟨hcont, e, he, hp, hd⟩ := hpost
    exact ⟨hcont.continuousWithinAt, e, he, hp, hd.hasDerivWithinAt⟩
  have hD' : HasFDerivAt f D (c 0) := by rwa [h0]
  have heq := ht.unique (hD'.comp_hasDerivAt 0 hc)
  have htransportOut (x y : E n) (h : x = y)
      (LL : TangentSpace A.manifold x →ₗ[ℝ] TangentSpace B.manifold (f x))
      (vv : TangentSpace A.manifold x) :
      B.coordinates (f y) ((h ▸ LL) (h ▸ vv)) = B.coordinates (f x) (LL vv) := by
    subst y; rfl
  rw [hw] at heq
  exact (htransportOut p (c 0) h0.symm L v).symm.trans heq


theorem euclidean_translations {n : ℕ} (G : EuclideanModel n) : EuclideanTranslations G := by
  intro p q
  let s := q - p
  let e : E n ≃ E n := Equiv.addRight s
  have hf : IsSmoothMap G.manifold G.manifold e :=
    euclidean_contDiff_smooth G G e (contDiff_id.add contDiff_const)
  have hg : IsSmoothMap G.manifold G.manifold e.symm :=
    euclidean_contDiff_smooth G G e.symm (contDiff_id.sub contDiff_const)
  let d : Diffeomorph G.manifold.smoothStructure.val G.manifold.smoothStructure.val :=
    ⟨e, hf, hg⟩
  refine ⟨d, fun _ => rfl, ?_, ?_⟩
  · change p + (q - p) = q
    abel
  · let L := fun x => SmoothManifolds.differential G.manifold G.manifold e hf x
    have hL := fun x => SmoothManifolds.differential_spec G.manifold G.manifold e hf x
    refine ⟨L, hL, ?_⟩
    intro x v w
    have hD : HasFDerivAt e (ContinuousLinearMap.id ℝ (E n)) x := by
      change HasFDerivAt (fun y : E n => y + s) _ x
      simpa only [id_eq] using (hasFDerivAt_id x).add_const s
    have hc := fun z => euclidean_differential_coordinates G G e hf x (L x) (hL x)
      (ContinuousLinearMap.id ℝ (E n)) hD z
    rw [G.metric_standard, G.metric_standard, hc v, hc w]
    rfl


theorem euclidean_centered_chart {n : ℕ} (G : EuclideanModel n) (p : E n) :
    ∃ (E : TangentSpace G.manifold p ≃ₗ[ℝ] Euclidean n)
      (c : ModelChart n .euclidean (P202.SpaceFormData.E n)),
      IsOrthonormalCoordinates G.metric p E ∧ c ∈ G.manifold.smoothStructure.val ∧
      c.source = univ ∧ c.target = univ ∧ (c p).val = 0 ∧
      (∀ v : TangentSpace G.manifold p,
        c.symm ⟨E v, by simp [modelSet]⟩ = line p (G.coordinates p v) 1) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let E' := (G.coordinates p).trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
  let c : ModelChart n .euclidean (E n) :=
    (((Homeomorph.addRight (-p)).trans (PiLp.homeomorph 2 (fun _ : Fin n => ℝ))).trans
      (Homeomorph.Set.univ (Euclidean n)).symm).toOpenPartialHomeomorph
  have hc : c ∈ G.manifold.smoothStructure.val := by
    rw [G.standard]
    intro d hd
    obtain ⟨d, hd, rfl⟩ := hd
    have hd0 : d = (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph := hd
    subst d
    apply SmoothManifolds.contDiffCompatible_of_germs
    · intro x hx hx'
      refine ⟨univ, isOpen_univ, mem_univ _, fun y => y + L p,
        (contDiff_id.add contDiff_const).contDiffOn, ?_⟩
      apply Eventually.of_forall
      intro y
      change L (y + -p) + L p = L y
      rw [map_add, map_neg]
      abel
    · intro x hx hx'
      refine ⟨univ, isOpen_univ, mem_univ _, fun y => y - L p,
        (contDiff_id.sub contDiff_const).contDiffOn, ?_⟩
      apply Eventually.of_forall
      intro y
      change L y - L p = L (y + -p)
      rw [map_add, map_neg]
      rfl
  refine ⟨E', c, ?_, hc, rfl, rfl, ?_, ?_⟩
  · intro i j
    rw [G.metric_standard]
    simp only [E', LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change inner ℝ (WithLp.toLp 2 (Pi.single i (1 : ℝ) : Euclidean n)) (WithLp.toLp 2 (Pi.single j (1 : ℝ) : Euclidean n)) = _
    simp [PiLp.inner_apply, Pi.single_apply]
  · change L (p + -p) = 0
    simp
  · intro v
    change L.symm (L (G.coordinates p v)) - -p = p + 1 • G.coordinates p v
    rw [L.symm_apply_apply, one_smul]
    abel


section ChartRestriction
universe u
variable {k : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold k .euclidean M}

theorem normal_chart_restriction (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean k) (hE : IsOrthonormalCoordinates g p E)
    (c : ModelChart k .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hp : p ∈ c.source) (hc0 : (c p).val = 0)
    (r : ℝ) (hr : 0 < r)
    (hball : {x : ModelSpace k .euclidean | tangentNorm g p (E.symm x.val) < r} ⊆ c.target)
    (hexp : ∀ x : ModelSpace k .euclidean, x ∈ c.target →
      (⟨p, E.symm x.val⟩ : Phase S) ∈ exponentialDomain F ∧
      fiberExponential F p (E.symm x.val) = c.symm x) :
    ∃ d : ModelChart k .euclidean M,
      IsNormalChart g F p E r d ∧
      d.source = {q | q ∈ c.source ∧ tangentNorm g p (E.symm (c q).val) < r} := by
  let B : Set (ModelSpace k .euclidean) := {x | tangentNorm g p (E.symm x.val) < r}
  have hB : IsOpen B :=
    ((ExponentialNormalCoordinates.orthonormal_norm_continuous g p E hE).comp
      continuous_subtype_val).isOpen_preimage _ isOpen_Iio
  let d := (c.symm.restrOpen B hB).symm
  have hd : d ∈ S.smoothStructure.val := by
    have hm : d ∈ maximalExtension (⊤ : ℕ∞) S.smoothStructure.val := by
      intro e he
      apply SmoothManifolds.contDiffCompatible_of_germs
      · intro x hx hxe
        exact SmoothManifolds.chartContDiffAt_of_compatible
          (S.smoothStructure.property.1.2 c hc e he) hx.1 hxe
      · intro x hxe hx
        exact SmoothManifolds.chartContDiffAt_of_compatible
          (S.smoothStructure.property.1.2 e he c hc) hxe hx.1
    have heq := S.smoothStructure.property.2
      (maximalExtension (⊤ : ℕ∞) S.smoothStructure.val)
      (SmoothManifolds.maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
      (SmoothManifolds.subset_maximalExtension S.smoothStructure.property.1)
    rwa [heq] at hm
  have hpt : p ∈ d.source := by
    refine ⟨hp, ?_⟩
    change tangentNorm g p (E.symm (c p).val) < r
    simpa only [hc0, map_zero, SmoothMetrics.tangentNorm_zero] using hr
  refine ⟨d, ⟨hr, hd, hpt, hc0, ?_, ?_⟩, rfl⟩
  · change c.target ∩ B = B
    exact inter_eq_right.mpr hball
  · intro x hx
    exact hexp x (hball hx)
end ChartRestriction

end P202.Geometry.ModelPolarDomains


set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.ModelPolarData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.ExponentialData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n .euclidean M}

/-- The fiber norm in orthonormal coordinates is smooth away from zero. -/
theorem orthonormal_norm_smooth (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Euclidean n => tangentNorm g p (E.symm y))
      {y | y ≠ 0} := by
  simp_rw [ExponentialNormalCoordinates.orthonormal_norm_formula g p E hE]
  apply ContDiffOn.sqrt
  · apply ContDiff.contDiffOn
    fun_prop
  · intro y hy hzero
    have hnorm : tangentNorm g p (E.symm y) = 0 := by
      rw [ExponentialNormalCoordinates.orthonormal_norm_formula g p E hE, hzero, Real.sqrt_zero]
    exact hy (by simpa using congrArg E ((SmoothMetrics.tangentNorm_eq_zero_iff g p _).mp hnorm))

/-- A Cartesian exponential chart gives the full polar equivalence and its
smooth coordinate maps, for any positive interval of radial parameters. -/
theorem polar_diffeomorphism_of_chart (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (c : ModelChart n .euclidean M)
    (J : Set ℝ) (hE : IsOrthonormalCoordinates g p E)
    (hp : p ∈ c.source) (hc0 : (c p).val = 0)
    (hJ : ∀ t ∈ J, 0 < t)
    (hct : ∀ y : Euclidean n, y ≠ 0 →
      ((⟨y, by simp [modelSet]⟩ : ModelSpace n .euclidean) ∈ c.target ↔
        tangentNorm g p (E.symm y) ∈ J))
    (hexp : ∀ x : ModelSpace n .euclidean, x ∈ c.target →
      fiberExponential F p (E.symm x.val) = c.symm x) :
    HasPolarDiffeomorphism g F p E c J := by
  classical
  let N : Euclidean n → ℝ := fun y => tangentNorm g p (E.symm y)
  have hN0 (y : Euclidean n) : N y = 0 ↔ y = 0 := by
    dsimp [N]
    rw [SmoothMetrics.tangentNorm_eq_zero_iff]
    exact E.symm.map_eq_zero_iff
  have hNpos (y : Euclidean n) (hy : y ≠ 0) : 0 < N y :=
    lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p _) (Ne.symm (mt (hN0 y).mp hy))
  have hNsmul (t : ℝ) (y : Euclidean n) : N (t • y) = |t| * N y := by
    simp only [N, map_smul, SmoothMetrics.tangentNorm_smul]
  have hzN (z : ↥(polarParameters g p E J)) : N (z.val.1 • z.val.2) = z.val.1 := by
    rw [hNsmul, abs_of_pos (hJ _ z.property.1)]
    change z.val.1 * tangentNorm g p (E.symm z.val.2) = z.val.1
    rw [z.property.2, mul_one]
  have hzNe (z : ↥(polarParameters g p E J)) : z.val.1 • z.val.2 ≠ 0 := by
    intro h
    have := hzN z
    rw [h, (hN0 0).mpr rfl] at this
    exact (ne_of_gt (hJ _ z.property.1)) this.symm
  have hzT (z : ↥(polarParameters g p E J)) :
      (⟨z.val.1 • z.val.2, by simp [modelSet]⟩ : ModelSpace n .euclidean) ∈ c.target := by
    apply (hct _ (hzNe z)).mpr
    change N (z.val.1 • z.val.2) ∈ J
    rw [hzN]
    exact z.property.1
  have hqNe (q : {q : M | q ∈ c.source ∧ q ≠ p}) : (c q.val).val ≠ 0 := by
    intro h
    apply q.property.2
    apply c.injOn q.property.1 hp
    exact Subtype.ext (h.trans hc0.symm)
  have hqJ (q : {q : M | q ∈ c.source ∧ q ≠ p}) : N (c q.val).val ∈ J :=
    (hct _ (hqNe q)).mp (c.map_source q.property.1)
  have hqUnit (q : {q : M | q ∈ c.source ∧ q ≠ p}) :
      N ((N (c q.val).val)⁻¹ • (c q.val).val) = 1 := by
    rw [hNsmul, abs_inv, abs_of_pos (hNpos _ (hqNe q)), inv_mul_cancel₀ (ne_of_gt (hNpos _ (hqNe q)))]
  let e : ↥(polarParameters g p E J) ≃ {q : M | q ∈ c.source ∧ q ≠ p} :=
    { toFun := fun z => ⟨c.symm ⟨z.val.1 • z.val.2, by simp [modelSet]⟩,
        c.map_target (hzT z), by
          intro h
          have hx := c.right_inv (hzT z)
          rw [h] at hx
          exact hzNe z ((congrArg Subtype.val hx).symm.trans hc0)⟩
      invFun := fun q => ⟨(N (c q.val).val, (N (c q.val).val)⁻¹ • (c q.val).val),
        hqJ q, hqUnit q⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change (N (c (c.symm _)).val, (N (c (c.symm _)).val)⁻¹ • (c (c.symm _)).val) = z.val
        rw [c.right_inv (hzT z)]
        simp only [hzN]
        apply Prod.ext
        · rfl
        · change z.val.1⁻¹ • (z.val.1 • z.val.2) = z.val.2
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (hJ _ z.property.1)), one_smul]
      right_inv := by
        intro q
        apply Subtype.ext
        change c.symm ⟨N (c q.val).val • ((N (c q.val).val)⁻¹ • (c q.val).val), _⟩ = q.val
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hNpos _ (hqNe q))), one_smul]
        exact c.left_inv q.property.1 }
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (hexp _ (hzT z)).symm
  · intro q
    rfl
  · have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × Euclidean n => z.1 • z.2) (polarParameters g p E J) :=
      (contDiff_fst.smul contDiff_snd).contDiffOn
    apply hsm.congr
    intro z hz
    let z' : ↥(polarParameters g p E J) := ⟨z, hz⟩
    change (c (fiberExponential F p (E.symm (z'.val.1 • z'.val.2)))).val = z'.val.1 • z'.val.2
    rw [hexp _ (hzT z'), c.right_inv (hzT z')]
  · have hn := orthonormal_norm_smooth g p E hE
    exact hn.prodMk ((hn.inv (fun y hy => ne_of_gt (hNpos y hy))).smul contDiffOn_id)

end P202.Geometry.ModelPolarDomains

namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData P202.SpaceFormData P202.ModelPolarData P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData P202.ExponentialData P202Specs.Geometry.ModelPolarDomains
theorem euclidean_geometry : euclideanType := by
  intro n hn G hG
  refine ⟨?_, euclidean_translations G⟩
  intro F hF p
  obtain ⟨E, c, hE, hc, hsource, htarget, hc0, hcformula⟩ := euclidean_centered_chart G p
  have hv (v : TangentSpace G.manifold p) :
      (⟨p, v⟩ : Phase G.manifold) ∈ exponentialDomain F ∧
      fiberExponential F p v = c.symm ⟨E v, by simp [modelSet]⟩ ∧
      modelDistance G.metric p (fiberExponential F p v) = tangentNorm G.metric p v :=
    ⟨(euclidean_formula n G hG F hF p v).1,
      (euclidean_formula n G hG F hF p v).2.trans (hcformula v).symm,
      euclidean_distance n G hG F hF p v⟩
  have hp : p ∈ c.source := by rw [hsource]; trivial
  have hexp (x : ModelSpace n .euclidean) (_hx : x ∈ c.target) :
      (⟨p, E.symm x.val⟩ : Phase G.manifold) ∈ exponentialDomain F ∧
      fiberExponential F p (E.symm x.val) = c.symm x := by
    simpa only [LinearEquiv.apply_symm_apply] using
      And.intro (hv (E.symm x.val)).1 (hv (E.symm x.val)).2.1
  refine ⟨E, c, hE, hc, hsource, htarget, hc0, hv, ?_, ?_⟩
  · apply polar_diffeomorphism_of_chart G.metric F p E c (Set.Ioi 0) hE hp hc0
    · exact fun t ht => ht
    · intro y hy
      rw [htarget]
      simp only [Set.mem_univ, Set.mem_Ioi, true_iff]
      apply lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg G.metric p _)
      intro hz
      apply hy
      have hz' := (SmoothMetrics.tangentNorm_eq_zero_iff G.metric p _).mp hz.symm
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg E hz'
    · intro x hx
      exact (hexp x hx).2
  · intro r hr
    obtain ⟨d, hd, hds⟩ := normal_chart_restriction G.metric F p E hE c hc hp hc0 r hr
      (by rw [htarget]; exact Set.subset_univ _) hexp
    refine ⟨d, hd, ?_⟩
    rw [hds]
    ext q
    have hq : q ∈ c.source := by rw [hsource]; trivial
    have hqexp : fiberExponential F p (E.symm (c q).val) = q :=
      (hexp (c q) (c.map_source hq)).2.trans (c.left_inv hq)
    have hdist := euclidean_distance n G hG F hF p (E.symm (c q).val)
    rw [hqexp] at hdist
    simp only [Set.mem_setOf_eq, hq, true_and, hdist]
end P202.Geometry.ModelPolarDomains

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.SpaceFormData P202.ModelPolarData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
open Set

/-- Restrict an orthogonal map to the literal round sphere. -/
def sphereOrthogonalEquiv {n : ℕ} {a : ℝ}
    (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1)) : Sphere n a ≃ Sphere n a where
  toFun p := ⟨U p.val, by simpa only [mem_sphere_zero_iff_norm, U.norm_map] using p.property⟩
  invFun q := ⟨U.symm q.val, by simpa only [mem_sphere_zero_iff_norm, U.symm.norm_map] using q.property⟩
  left_inv p := Subtype.ext (U.symm_apply_apply p.val)
  right_inv q := Subtype.ext (U.apply_symm_apply q.val)

@[simp] theorem sphereOrthogonalEquiv_val {n : ℕ} {a : ℝ}
    (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1)) (p : Sphere n a) :
    (sphereOrthogonalEquiv U p).val = U p.val := rfl

theorem continuous_sphereOrthogonalEquiv {n : ℕ} {a : ℝ}
    (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1)) : Continuous (sphereOrthogonalEquiv (a := a) U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _

theorem spherical_inclusion_immersion {n : ℕ} {a : ℝ} {A : EuclideanModel (n+1)}
    (B : SphericalModel n a A) : SmoothManifolds.MapClassData.IsImmersion B.manifold A.manifold Subtype.val := by
  intro p
  exact (SmoothManifolds.MapClasses.smooth_tangent_invariants B.manifold A.manifold
    Subtype.val B.inclusion.smooth p (B.inclusion.differential p)
    (B.inclusion.isDifferential p)).2.1.mpr (B.inclusion.injective p)

theorem sphereOrthogonalEquiv_smooth {n : ℕ} {a : ℝ} {A : EuclideanModel (n+1)}
    (B : SphericalModel n a A) (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1))
    (hU : IsSmoothMap A.manifold A.manifold U) :
    IsSmoothMap B.manifold B.manifold (sphereOrthogonalEquiv (a := a) U) := by
  apply SmoothManifolds.TransversePreimage.smooth_factor_of_immersion
    B.manifold B.manifold A.manifold Subtype.val B.inclusion.smooth
    (spherical_inclusion_immersion B) (sphereOrthogonalEquiv U)
    (continuous_sphereOrthogonalEquiv U)
  exact SmoothManifolds.manifoldContDiff_comp ⊤ _ _ _
    A.manifold.smoothStructure.property.1.1 _ _ B.inclusion.smooth hU

open P202.CurveData P202.CurveConnectionData

theorem sphere_velocity_ambient {n : ℕ} {a : ℝ} {A : EuclideanModel (n+1)}
    (B : SphericalModel n a A) {c : ℝ → Sphere n a} {t : ℝ}
    {v : TangentSpace B.manifold (c t)}
    (hv : HasVelocityWithinAt B.manifold c univ t v) :
    HasDerivAt (fun s => (c s).val) (B.ambientVector (c t) v) t := by
  have hv' : HasVelocityAt B.manifold c t v := by
    simpa only [HasVelocityWithinAt, HasVelocityAt,
      continuousWithinAt_univ, hasDerivWithinAt_univ] using hv
  have hi := PiecewiseCurves.HasVelocityAt.postcomp B.inclusion.smooth hv'
    (B.inclusion.differential (c t)) (B.inclusion.isDifferential (c t))
  have hi' : HasVelocityWithinAt A.manifold (Subtype.val ∘ c) univ t
      (B.inclusion.differential (c t) v) := by
    simpa only [HasVelocityWithinAt, HasVelocityAt,
      continuousWithinAt_univ, hasDerivWithinAt_univ] using hi
  exact (A.velocity (Subtype.val ∘ c) t (B.inclusion.differential (c t) v)).mp hi'

theorem sphereOrthogonal_differential {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A)
    (hB : B.Conclusion) (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1))
    (hf : IsSmoothMap B.manifold B.manifold (sphereOrthogonalEquiv (a := a) U))
    (p : Sphere n a) (v : TangentSpace B.manifold p) :
    B.ambientVector (sphereOrthogonalEquiv U p)
      (SmoothManifolds.differential B.manifold B.manifold (sphereOrthogonalEquiv U) hf p v) =
      U (B.ambientVector p v) := by
  obtain ⟨q, hq, _hformula⟩ := hB.2.2.2.2.1 p v
  have hv : HasVelocityWithinAt B.manifold (fun t => (q t).1) univ 0 (q 0).2 :=
    (hq.2.2.1 0 (by trivial)).1
  have hv' : HasVelocityAt B.manifold (fun t => (q t).1) 0 (q 0).2 := by
    simpa only [HasVelocityWithinAt, HasVelocityAt,
      continuousWithinAt_univ, hasDerivWithinAt_univ] using hv
  have hV' := PiecewiseCurves.HasVelocityAt.postcomp hf hv'
    (SmoothManifolds.differential B.manifold B.manifold (sphereOrthogonalEquiv U) hf (q 0).1)
    (SmoothManifolds.differential_spec _ _ _ hf (q 0).1)
  have hV : HasVelocityWithinAt B.manifold
      (sphereOrthogonalEquiv U ∘ fun t => (q t).1) univ 0
      (SmoothManifolds.differential B.manifold B.manifold (sphereOrthogonalEquiv U) hf (q 0).1 (q 0).2) := by
    simpa only [HasVelocityWithinAt, HasVelocityAt,
      continuousWithinAt_univ, hasDerivWithinAt_univ] using hV'
  have hd₁ := sphere_velocity_ambient B hV
  have hd₂ := U.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt 0 (sphere_velocity_ambient B hv)
  have heq : B.ambientVector (sphereOrthogonalEquiv U (q 0).1)
      (SmoothManifolds.differential B.manifold B.manifold (sphereOrthogonalEquiv U) hf (q 0).1 (q 0).2) =
      U (B.ambientVector (q 0).1 (q 0).2) := hd₁.unique hd₂
  have hq0 : q 0 = ⟨p, v⟩ := hq.2.1
  exact Eq.mp (congrArg (fun z : Phase B.manifold =>
    B.ambientVector (sphereOrthogonalEquiv U z.1)
      (SmoothManifolds.differential B.manifold B.manifold (sphereOrthogonalEquiv U) hf z.1 z.2) =
      U (B.ambientVector z.1 z.2)) hq0) heq

def sphereOrthogonalDiffeomorph {n : ℕ} {a : ℝ} {A : EuclideanModel (n+1)}
    (B : SphericalModel n a A) (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1))
    (hU : IsSmoothMap A.manifold A.manifold U)
    (hUi : IsSmoothMap A.manifold A.manifold U.symm) :
    Diffeomorph B.manifold.smoothStructure.val B.manifold.smoothStructure.val where
  toEquiv := sphereOrthogonalEquiv U
  contDiff_toFun := sphereOrthogonalEquiv_smooth B U hU
  contDiff_invFun := sphereOrthogonalEquiv_smooth B U.symm hUi

theorem sphereOrthogonal_isometry {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A)
    (hB : B.Conclusion) (U : E (n+1) ≃ₗᵢ[ℝ] E (n+1))
    (hU : IsSmoothMap A.manifold A.manifold U)
    (hUi : IsSmoothMap A.manifold A.manifold U.symm) :
    IsSmoothIsometry B.metric (sphereOrthogonalDiffeomorph B U hU hUi) := by
  dsimp only [IsSmoothIsometry, sphereOrthogonalDiffeomorph]
  let hf := sphereOrthogonalEquiv_smooth B U hU
  refine ⟨SmoothManifolds.differential B.manifold B.manifold (sphereOrthogonalEquiv U) hf,
    SmoothManifolds.differential_spec _ _ _ hf, ?_⟩
  intro p v w
  change pairing B.metric (sphereOrthogonalEquiv U p) _ _ = pairing B.metric p v w
  rw [← B.induced (sphereOrthogonalEquiv U p), ← B.induced p v w,
    A.metric_standard, A.metric_standard]
  change inner ℝ (B.ambientVector _ _) (B.ambientVector _ _) =
    inner ℝ (B.ambientVector p v) (B.ambientVector p w)
  exact (congrArg₂ (inner ℝ) (sphereOrthogonal_differential B hB U hf p v)
    (sphereOrthogonal_differential B hB U hf p w)).trans
    (U.inner_map_map (B.ambientVector p v) (B.ambientVector p w))

end P202.Geometry.ModelPolarDomains

namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData P202.SpaceFormData P202.ModelPolarData P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
theorem spherical_homogeneity {n : ℕ} {a : ℝ} {A : EuclideanModel (n+1)}
    (B : SphericalModel n a A) (hB : B.Conclusion) : SphericalHomogeneity B := by
  intro p q
  obtain ⟨U, hUp⟩ := sphere_orthogonal_transitive p q
  let hU := euclidean_contDiff_smooth A A U U.toContinuousLinearEquiv.contDiff
  let hUi := euclidean_contDiff_smooth A A U.symm U.symm.toContinuousLinearEquiv.contDiff
  refine ⟨U, hUp, sphereOrthogonalDiffeomorph B U hU hUi, fun x => rfl, ?_,
    sphereOrthogonal_isometry B hB U hU hUi⟩
  exact Subtype.ext hUp

end P202.Geometry.ModelPolarDomains

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.SpaceFormData P202.ModelPolarData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData
open Set


open P202.Geometry.EuclideanSphericalModels
theorem spherical_unit_exponential {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) (v : TangentSpace B.manifold p) (hv : tangentNorm B.metric p v = 1)
    (t : ℝ) :
    (fiberExponential F p (t • v)).val = greatCircle a p.val (B.ambientVector p v) t := by
  obtain ⟨q, hq, hformula⟩ := hB.2.2.2.2.2 p v hv
  have hm := (hF ⟨p, v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
    hq.1 hq.2.1 hq.2.2.1
  obtain ⟨_, heq⟩ := ExponentialNormalCoordinates.radial_identity
    B.manifold B.connection F hF p v t (hm.1 (by trivial))
  rw [heq]
  exact (congrArg (fun z : Phase B.manifold => z.1.val)
    (hm.2 (x := t) (by trivial))).trans (hformula t).1

theorem sphereCurve_inner {n : ℕ} {a : ℝ} (p v : E (n+1))
    (hp : ‖p‖ = a) (hv : inner ℝ p v = 0) :
    inner ℝ p (sphereCurve a p v 1) = a ^ 2 * Real.cos (‖v‖ / a) := by
  by_cases hzero : v = 0
  · simp [sphereCurve, hzero, real_inner_self_eq_norm_sq, hp]
  · simp only [sphereCurve, if_neg hzero, greatCircle, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hp, hv, mul_zero,
      add_zero, mul_one]
    ring

theorem spherical_exponential_inner {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) (v : TangentSpace B.manifold p) :
    inner ℝ p.val (fiberExponential F p v).val =
      a ^ 2 * Real.cos (tangentNorm B.metric p v / a) := by
  rw [(spherical_formula B hB F hF p v).2, spherical_model_norm]
  apply sphereCurve_inner _ _ (mem_sphere_zero_iff_norm.mp p.property)
  exact spherical_model_tangent B p v

theorem spherical_radial_distance {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) (v : TangentSpace B.manifold p)
    (hv : tangentNorm B.metric p v ≤ Real.pi * a) :
    modelDistance B.metric p (fiberExponential F p v) = tangentNorm B.metric p v := by
  letI : ConnectedSpace (Sphere n a) := hB.1
  have hfull : P202.CompleteExponentialData.FullExponentialAt F p :=
    fun w => (spherical_formula B hB F hF p w).1
  obtain ⟨w, hw, hd⟩ := CompleteExponentialMinimizers.attaining_vectors
    B.metric B.connection B.leviCivita F hF p hfull (fiberExponential F p v)
  have hwv : tangentNorm B.metric p w ≤ tangentNorm B.metric p v := by
    rw [hd]
    exact CompleteExponentialMinimizers.distance_exponential_le_norm
      B.metric B.connection B.leviCivita F hF p hfull v
  have heq : a ^ 2 * Real.cos (tangentNorm B.metric p w / a) =
      a ^ 2 * Real.cos (tangentNorm B.metric p v / a) := by
    rw [← spherical_exponential_inner B hB F hF p w,
      ← spherical_exponential_inner B hB F hF p v, hw]
  have hc := mul_left_cancel₀ (pow_ne_zero 2 ha.ne') heq
  have hangle := Real.injOn_cos
    (show tangentNorm B.metric p w / a ∈ Icc 0 Real.pi from
      ⟨div_nonneg (SmoothMetrics.tangentNorm_nonneg _ _ _) ha.le,
        (div_le_iff₀ ha).mpr (hwv.trans hv)⟩)
    (show tangentNorm B.metric p v / a ∈ Icc 0 Real.pi from
      ⟨div_nonneg (SmoothMetrics.tangentNorm_nonneg _ _ _) ha.le,
        (div_le_iff₀ ha).mpr hv⟩) hc
  have hnorm : tangentNorm B.metric p w = tangentNorm B.metric p v :=
    (div_left_inj' ha.ne').mp hangle
  exact hd.symm.trans hnorm

theorem spherical_minimizer_norm_bound {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) (w : TangentSpace B.manifold p)
    (hd : tangentNorm B.metric p w = modelDistance B.metric p (fiberExponential F p w)) :
    tangentNorm B.metric p w ≤ Real.pi * a := by
  by_contra hn
  have hlarge : Real.pi * a < tangentNorm B.metric p w := lt_of_not_ge hn
  let r := tangentNorm B.metric p w
  have hpa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hr : 0 < r := hpa.trans hlarge
  let u := r⁻¹ • w
  have hu : tangentNorm B.metric p u = 1 := by
    rw [SmoothMetrics.tangentNorm_smul]
    simp [r, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hw : r • u = w := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hperiod : greatCircle a p.val (B.ambientVector p u) (r - 2 * Real.pi * a) =
      greatCircle a p.val (B.ambientVector p u) r := by
    have hangle : (r - 2 * Real.pi * a) / a = r / a - 2 * Real.pi := by
      field_simp
    simp only [greatCircle, hangle, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
  have hexp : fiberExponential F p ((r - 2 * Real.pi * a) • u) =
      fiberExponential F p w := by
    apply Subtype.ext
    rw [spherical_unit_exponential B hB F hF p u hu, hperiod,
      ← spherical_unit_exponential B hB F hF p u hu, hw]
  have hfull : P202.CompleteExponentialData.FullExponentialAt F p :=
    fun z => (spherical_formula B hB F hF p z).1
  have hle := CompleteExponentialMinimizers.distance_exponential_le_norm
    B.metric B.connection B.leviCivita F hF p hfull ((r - 2 * Real.pi * a) • u)
  change modelDistance B.metric p (fiberExponential F p ((r - 2 * Real.pi * a) • u)) ≤
    tangentNorm B.metric p ((r - 2 * Real.pi * a) • u) at hle
  rw [hexp, ← hd, SmoothMetrics.tangentNorm_smul, hu, mul_one] at hle
  have hshort : |r - 2 * Real.pi * a| < r := by
    apply abs_lt.mpr
    constructor <;> dsimp [r] at * <;> linarith
  exact (not_lt_of_ge hle) hshort

theorem spherical_distance_arccos {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p q : Sphere n a) :
    modelDistance B.metric p q = a * Real.arccos (inner ℝ p.val q.val / a ^ 2) := by
  letI : ConnectedSpace (Sphere n a) := hB.1
  have hfull : P202.CompleteExponentialData.FullExponentialAt F p :=
    fun w => (spherical_formula B hB F hF p w).1
  obtain ⟨w, hw, hd⟩ := CompleteExponentialMinimizers.attaining_vectors
    B.metric B.connection B.leviCivita F hF p hfull q
  have hbound := spherical_minimizer_norm_bound ha B hB F hF p w (by rw [hw]; exact hd)
  have hangle : inner ℝ p.val q.val / a ^ 2 = Real.cos (tangentNorm B.metric p w / a) := by
    rw [← hw, spherical_exponential_inner B hB F hF p w]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 ha.ne')
  rw [hangle, Real.arccos_cos
    (div_nonneg (SmoothMetrics.tangentNorm_nonneg _ _ _) ha.le)
    ((div_le_iff₀ ha).mpr hbound)]
  change P202.CompleteExponentialData.lengthDistance B.metric p q = _
  rw [← hd]
  field_simp

theorem spherical_antipode_distance {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p q : Sphere n a) (hq : q.val = -p.val) :
    modelDistance B.metric p q = Real.pi * a := by
  rw [spherical_distance_arccos ha B hB F hF p q, hq]
  have hp : ‖p.val‖ = a := mem_sphere_zero_iff_norm.mp p.property
  have hratio : inner ℝ p.val (-p.val) / a ^ 2 = -1 := by
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hp]
    field_simp
  rw [hratio, Real.arccos_neg_one, mul_comm]

end P202.Geometry.ModelPolarDomains

namespace P202.Geometry.ModelPolarDomains
open scoped BigOperators
namespace MetricTransport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData P202.MetricData
open Filter
open private scalar_comp_at rebased_differential_exists from
  MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
universe u
variable {n m l : ℕ} {M N Q : Type u}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
  {S : SmoothManifold n .euclidean M} {T : SmoothManifold m .euclidean N}
  {U : SmoothManifold l .euclidean Q}

structure MetricDiffeomorph (g : RiemannianMetric S) (h : RiemannianMetric T) where
  diffeomorph : Diffeomorph S.smoothStructure.val T.smoothStructure.val
  linear : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (diffeomorph.toEquiv p)
  linear_spec : ∀ p, IsDifferential S T diffeomorph.toEquiv p (linear p)
  preserves : IsMetricPreserving g h diffeomorph.toEquiv linear

namespace MetricDiffeomorph
variable {g : RiemannianMetric S} {h : RiemannianMetric T} {j : RiemannianMetric U}

def trans (d : MetricDiffeomorph g h) (e : MetricDiffeomorph h j) : MetricDiffeomorph g j where
  diffeomorph :=
    { toEquiv := d.diffeomorph.toEquiv.trans e.diffeomorph.toEquiv
      contDiff_toFun := fun p => SmoothManifolds.manifoldContDiffAt_comp
        T.smoothStructure.property.1.1 (d.diffeomorph.contDiff_toFun p)
          (e.diffeomorph.contDiff_toFun (d.diffeomorph.toEquiv p))
      contDiff_invFun := fun p => SmoothManifolds.manifoldContDiffAt_comp
        T.smoothStructure.property.1.1 (e.diffeomorph.contDiff_invFun p)
          (d.diffeomorph.contDiff_invFun (e.diffeomorph.toEquiv.symm p)) }
  linear p := (e.linear (d.diffeomorph.toEquiv p)).comp (d.linear p)
  linear_spec p := SmoothManifolds.differential_comp S T U
    d.diffeomorph.toEquiv e.diffeomorph.toEquiv d.diffeomorph.contDiff_toFun
      e.diffeomorph.contDiff_toFun p (d.linear p) (e.linear (d.diffeomorph.toEquiv p))
      (d.linear_spec p) (e.linear_spec (d.diffeomorph.toEquiv p))
  preserves p v w := (e.preserves (d.diffeomorph.toEquiv p) (d.linear p v) (d.linear p w)).trans
    (d.preserves p v w)

lemma rebased_preserves (d : MetricDiffeomorph g h) (p : M) (q : N)
    (hpq : d.diffeomorph.toEquiv p = q)
    (J : TangentSpace S p →ₗ[ℝ] TangentSpace T q)
    (hJ : ∀ (v : TangentSpace S p) (a : SmoothGerm T q) (b : SmoothGerm S p)
      (r : N → ℝ), Germ.ofFun r = a.val → Germ.ofFun (r ∘ d.diffeomorph.toEquiv) = b.val →
      (J v).val a = v.val b) (v w : TangentSpace S p) :
    pairing h q (J v) (J w) = pairing g p v w := by
  subst q
  have he := (SmoothManifolds.differential_exists S T d.diffeomorph.toEquiv
    d.diffeomorph.contDiff_toFun p).unique (d.linear_spec p) hJ
  rw [← he]
  exact d.preserves p v w

def symm (d : MetricDiffeomorph g h) : MetricDiffeomorph h g := by
  let f := d.diffeomorph.toEquiv
  let fi := f.symm
  let hf := d.diffeomorph.contDiff_toFun
  let hfi := d.diffeomorph.contDiff_invFun
  let K := SmoothManifolds.differential T S fi hfi
  have hK := SmoothManifolds.differential_spec T S fi hfi
  refine ⟨⟨fi, hfi, hf⟩, K, hK, ?_⟩
  intro p v w
  obtain ⟨J, hJ⟩ := rebased_differential_exists (@SmoothManifolds.mem_smoothGermAlgebra_iff.{u})
    S T f hf (fi p) p (f.apply_symm_apply p)
  have hJK (v : TangentSpace T p) : J (K p v) = v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    obtain ⟨r, hr, hra⟩ := (SmoothManifolds.mem_smoothGermAlgebra_iff T p a.val).mp a.property
    have hr' : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
        T.smoothStructure.val r (f (fi p)) := by
      simpa only [fi, f.apply_symm_apply] using hr
    let b : SmoothGerm S (fi p) := ⟨Germ.ofFun (r ∘ f),
      Algebra.subset_adjoin ⟨r ∘ f, scalar_comp_at (hf (fi p)) hr', rfl⟩⟩
    have hcomp : Germ.ofFun ((r ∘ f) ∘ fi) = a.val := by
      rw [show (r ∘ f) ∘ fi = r from funext (fun x => congrArg r (f.apply_symm_apply x))]
      exact hra.symm
    exact (hJ (K p v) a b r hra.symm rfl).trans (hK p v b a (r ∘ f) rfl hcomp)
  have hpair := rebased_preserves d (fi p) p (f.apply_symm_apply p) J hJ (K p v) (K p w)
  rw [hJK v, hJK w] at hpair
  exact hpair.symm

end MetricDiffeomorph
lemma homogeneous_transfer {g : RiemannianMetric S} {h : RiemannianMetric T}
    (d : MetricDiffeomorph g h) (hg : P202.ModelPolarData.IsHomogeneous g) :
    P202.ModelPolarData.IsHomogeneous h := by
  intro p q
  obtain ⟨e, he, L, hL, hmetric⟩ := hg (d.diffeomorph.toEquiv.symm p) (d.diffeomorph.toEquiv.symm q)
  let eM : MetricDiffeomorph g g := ⟨e, L, hL, hmetric⟩
  let t := (d.symm.trans eM).trans d
  refine ⟨t.diffeomorph, ?_, t.linear, t.linear_spec, t.preserves⟩
  change d.diffeomorph.toEquiv (e.toEquiv (d.diffeomorph.toEquiv.symm p)) = q
  rw [he, d.diffeomorph.toEquiv.apply_symm_apply]

end MetricTransport
namespace HalfSpaceAction
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData P202.MetricData P202.ConnectionData
  P202.HalfSpaceData P202.HyperboloidData P202.ModelPolarData
open Set

def affineEquiv {m : ℕ} (b : Spatial m) (k : ℝ) (hk : 0 < k) :
    P202.HalfSpaceData.HalfSpace m ≃ P202.HalfSpaceData.HalfSpace m where
  toFun x := ⟨(b + k • x.val.1, k * x.val.2), mul_pos hk x.property⟩
  invFun x := ⟨(-k⁻¹ • b + k⁻¹ • x.val.1, k⁻¹ * x.val.2), mul_pos (inv_pos.mpr hk) x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change -k⁻¹ * b i + k⁻¹ * (b i + k * x.val.1 i) = x.val.1 i
      field_simp [ne_of_gt hk]
      <;> ring
    · change k⁻¹ * (k * x.val.2) = x.val.2
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk), one_mul]
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change b i + k * (-k⁻¹ * b i + k⁻¹ * x.val.1 i) = x.val.1 i
      field_simp [ne_of_gt hk]
      <;> ring
    · change k * (k⁻¹ * x.val.2) = x.val.2
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hk), one_mul]

lemma affine_smooth {m : ℕ} {a : ℝ} (H : HalfSpaceModel m a)
    (c : ModelChart (m + 1) .euclidean (P202.HalfSpaceData.HalfSpace m))
    (hc : c ∈ H.manifold.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = Fin.snoc p.val.1 p.val.2)
    (b : Spatial m) (k : ℝ) (hk : 0 < k) :
    IsSmoothMap H.manifold H.manifold (affineEquiv b k hk) := by
  intro p
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart _ _ _
    H.manifold.smoothStructure.property.1 H.manifold.smoothStructure.property.1 _ p).mpr
  have hcont : Continuous (affineEquiv b k hk : P202.HalfSpaceData.HalfSpace m → P202.HalfSpaceData.HalfSpace m) := by
    apply Continuous.subtype_mk
    fun_prop
  refine ⟨hcont.continuousAt, c, hc, c, hc, hs ▸ mem_univ _, hs ▸ mem_univ _, ?_⟩
  refine ⟨univ, isOpen_univ, mem_univ _,
    (fun x : Spatial (m + 1) => Fin.snoc (fun i => b i + k * x i.castSucc) (k * x (Fin.last m))),
    ?_, ?_⟩
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop
  · apply Filter.Eventually.of_forall
    intro x
    dsimp only
    rw [hproj, hproj]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rfl

def affineDiffeomorph {m : ℕ} {a : ℝ} (H : HalfSpaceModel m a)
    (c : ModelChart (m + 1) .euclidean (P202.HalfSpaceData.HalfSpace m))
    (hc : c ∈ H.manifold.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = Fin.snoc p.val.1 p.val.2)
    (b : Spatial m) (k : ℝ) (hk : 0 < k) :
    Diffeomorph H.manifold.smoothStructure.val H.manifold.smoothStructure.val where
  toEquiv := affineEquiv b k hk
  contDiff_toFun := affine_smooth H c hc hs hproj b k hk
  contDiff_invFun := by
    exact affine_smooth H c hc hs hproj (-k⁻¹ • b) k⁻¹ (inv_pos.mpr hk)


lemma coordinate_scalar_smooth {m : ℕ} {a : ℝ} (H : HalfSpaceModel m a)
    (c : ModelChart (m + 1) .euclidean (P202.HalfSpaceData.HalfSpace m))
    (hc : c ∈ H.manifold.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = Fin.snoc p.val.1 p.val.2)
    (i : Fin (m+1)) (p : P202.HalfSpaceData.HalfSpace m) :
    SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      H.manifold.smoothStructure.val (fun x : P202.HalfSpaceData.HalfSpace m => (Fin.snoc x.val.1 x.val.2 : Spatial (m+1)) i) p := by
  apply SmoothManifolds.scalarContDiffAt_of_chart H.manifold.smoothStructure.property.1 hc
    (hs ▸ mem_univ _)
  refine ⟨univ, isOpen_univ, mem_univ _, (fun x : Spatial (m+1) => x i),
    (contDiff_apply ℝ (fun _ : Fin (m+1) => ℝ) i).contDiffOn, ?_⟩
  exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [hproj])

lemma affine_coordinates_differential {m : ℕ} {a : ℝ} (H : HalfSpaceModel m a)
    (c : ModelChart (m + 1) .euclidean (P202.HalfSpaceData.HalfSpace m))
    (hc : c ∈ H.manifold.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = Fin.snoc p.val.1 p.val.2)
    (b : Spatial m) (k : ℝ) (hk : 0 < k)
    (p : P202.HalfSpaceData.HalfSpace m) (v : TangentSpace H.manifold p) :
    H.coordinates (affineEquiv b k hk p)
      (SmoothManifolds.differential H.manifold H.manifold (affineEquiv b k hk)
        (affine_smooth H c hc hs hproj b k hk) p v) = k • H.coordinates p v := by
  let hf := affine_smooth H c hc hs hproj b k hk
  rw [H.coordinates_standard, H.coordinates_standard]
  apply Prod.ext
  · funext i
    change scalarDerivative H.manifold (fun x => x.val.1 i) _ _ =
      k * scalarDerivative H.manifold (fun x => x.val.1 i) p v
    rw [← P202.Geometry.PullbackConnections.scalar_chain_local (affineEquiv b k hk) hf
      (fun x => x.val.1 i) p
      (by simpa only [Fin.snoc_castSucc] using coordinate_scalar_smooth H c hc hs hproj i.castSucc _) v]
    rw [P202.Geometry.HyperboloidModel.scalarDerivative_chart H.manifold c hc p (hs ▸ mem_univ _)
      _ (fun x => b i + k * x i.castSucc) (by fun_prop)
      (fun x => by rw [hproj]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; try rfl)]
    rw [P202.Geometry.HyperboloidModel.scalarDerivative_chart H.manifold c hc p (hs ▸ mem_univ _)
      _ (fun x => x i.castSucc) (by fun_prop)
      (fun x => by rw [hproj]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; try rfl)]
    rw [(((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (m+1) => ℝ) i.castSucc
      (c p).val).const_mul k).const_add (b i)).fderiv,
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (m+1) => ℝ) i.castSucc (c p).val).fderiv]
    rfl
  · change scalarDerivative H.manifold (fun x => x.val.2) _ _ =
      k * scalarDerivative H.manifold (fun x => x.val.2) p v
    rw [← P202.Geometry.PullbackConnections.scalar_chain_local (affineEquiv b k hk) hf
      (fun x => x.val.2) p
      (by simpa only [Fin.snoc_last] using coordinate_scalar_smooth H c hc hs hproj (Fin.last m) _) v]
    rw [P202.Geometry.HyperboloidModel.scalarDerivative_chart H.manifold c hc p (hs ▸ mem_univ _)
      _ (fun x => k * x (Fin.last m)) (by fun_prop)
      (fun x => by rw [hproj]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; try rfl)]
    rw [P202.Geometry.HyperboloidModel.scalarDerivative_chart H.manifold c hc p (hs ▸ mem_univ _)
      _ (fun x => x (Fin.last m)) (by fun_prop)
      (fun x => by rw [hproj]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; try rfl)]
    rw [((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (m+1) => ℝ) (Fin.last m)
      (c p).val).const_mul k).fderiv,
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (m+1) => ℝ) (Fin.last m) (c p).val).fderiv]
    rfl

lemma halfMetric_scale {m : ℕ} (a : ℝ) (x : P202.HalfSpaceData.HalfSpace m)
    (b : Spatial m) (k : ℝ) (hk : 0 < k) (v w : Coordinates m) :
    halfMetric a (affineEquiv b k hk x).val (k • v) (k • w) =
      halfMetric a x.val v w := by
  have hz : x.val.2 ≠ 0 := ne_of_gt x.property
  have hsp : spatialDot (k • v.1) (k • w.1) = k^2 * spatialDot v.1 w.1 := by
    simp only [spatialDot, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ i, k * v.1 i * (k * w.1 i) = k^2 * (v.1 i * w.1 i) by intro i; ring]
    rw [Finset.mul_sum]
  change a^2 / (k * x.val.2)^2 *
    (spatialDot (k • v.1) (k • w.1) + (k * v.2) * (k * w.2)) = _
  rw [hsp]
  unfold halfMetric
  field_simp [ne_of_gt hk, hz]
  <;> ring

lemma affine_isometry {m : ℕ} {a : ℝ} (H : HalfSpaceModel m a)
    (c : ModelChart (m + 1) .euclidean (P202.HalfSpaceData.HalfSpace m))
    (hc : c ∈ H.manifold.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = Fin.snoc p.val.1 p.val.2)
    (b : Spatial m) (k : ℝ) (hk : 0 < k) :
    IsSmoothIsometry H.metric (affineDiffeomorph H c hc hs hproj b k hk) := by
  let hf := affine_smooth H c hc hs hproj b k hk
  let L := SmoothManifolds.differential H.manifold H.manifold (affineEquiv b k hk) hf
  refine ⟨L, SmoothManifolds.differential_spec H.manifold H.manifold (affineEquiv b k hk) hf, ?_⟩
  intro p v w
  exact (H.metric_standard (affineEquiv b k hk p) (L p v) (L p w)).trans
    ((congrArg₂ (halfMetric a (affineEquiv b k hk p).val)
      (affine_coordinates_differential H c hc hs hproj b k hk p v)
      (affine_coordinates_differential H c hc hs hproj b k hk p w)).trans
      ((halfMetric_scale a p b k hk (H.coordinates p v) (H.coordinates p w)).trans
        (H.metric_standard p v w).symm))

theorem halfSpace_homogeneity : P202Specs.Geometry.ModelPolarDomains.halfSpaceHomogeneityType := by
  intro m _hm a _ha H p q
  obtain ⟨c, hc, hs, _ht, hproj⟩ := H.standard_chart
  let k : ℝ := q.val.2 / p.val.2
  have hk : 0 < k := div_pos q.property p.property
  let b : Spatial m := q.val.1 - k • p.val.1
  refine ⟨b, k, hk, affineDiffeomorph H c hc hs hproj b k hk, fun _ => rfl, ?_,
    affine_isometry H c hc hs hproj b k hk⟩
  apply Subtype.ext
  apply Prod.ext
  · change q.val.1 - k • p.val.1 + k • p.val.1 = q.val.1
    exact sub_add_cancel _ _
  · change q.val.2 / p.val.2 * p.val.2 = q.val.2
    exact div_mul_cancel₀ _ (ne_of_gt p.property)

end HalfSpaceAction

open SmoothManifolds.AtlasData P202.ModelPolarData P202.MetricData

theorem halfSpace_homogeneity : P202Specs.Geometry.ModelPolarDomains.halfSpaceHomogeneityType :=
  HalfSpaceAction.halfSpace_homogeneity

lemma hyperbolic_homogeneous {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a))
    (g : RiemannianMetric S) (hchart : HasProjectionChart S)
    (hg : P202.HyperboloidData.IsInduced g) : IsHomogeneous g := by
  cases n with
  | zero => omega
  | succ m =>
    have hm : 1 ≤ m := by omega
    obtain ⟨H, d, _hforward, _hinverse, L, hL, hmetric⟩ :=
      P202.Geometry.HyperbolicHalfSpace.intrinsicHalfSpaceIsometry ha S g hchart hg
    apply MetricTransport.homogeneous_transfer
      (⟨d, L, hL, hmetric⟩ : MetricTransport.MetricDiffeomorph H.metric g)
    intro p q
    obtain ⟨b, k, hk, e, _he, hpq, hiso⟩ := halfSpace_homogeneity m hm a ha H p q
    exact ⟨e, hpq, hiso⟩


end P202.Geometry.ModelPolarDomains

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ModelPolarData P202.MetricData P202.ConnectionData P202.GeodesicData P202.ExponentialData
open Set Filter
open scoped _root_.Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n .euclidean M}

/-- A logarithm agreeing with a normal chart is smooth at the center. -/
theorem normal_chart_log_smooth (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (r : ℝ) (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E r d)
    (l : M → Euclidean n) (hl : ∀ q ∈ d.source, l q = (d q).val) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val l p := by
  have heq : (fun q : M => (d q).val) =ᶠ[𝓝 p] l := by
    filter_upwards [d.open_source.mem_nhds hd.2.2.1] with q hq
    exact (hl q hq).symm
  refine ⟨(continuous_subtype_val.continuousAt.comp (d.continuousAt hd.2.2.1)).congr heq, ?_⟩
  intro c hc hp
  exact SmoothManifolds.LocalCoordinateExtension.congr
    (SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 c hc d hd.2.1) hp hd.2.2.1) heq

/-- A bijective exponential with a smooth logarithm is a genuine global
chart in the original maximal smooth atlas. -/
theorem exponential_global_chart (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (hfull : ∀ v : TangentSpace S p, (⟨p,v⟩ : Phase S) ∈ exponentialDomain F)
    (e : Euclidean n ≃ M)
    (he : ∀ x, e x = fiberExponential F p (E.symm x))
    (hlog : ∀ q, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      S.smoothStructure.val e.symm q) :
    ∃ c : ModelChart n .euclidean M, c ∈ S.smoothStructure.val ∧
      c.source = univ ∧ c.target = univ ∧ (c p).val = 0 ∧
      ∀ v : TangentSpace S p,
        fiberExponential F p v = c.symm ⟨E v, by simp [modelSet]⟩ := by
  let h : Euclidean n ≃ₜ M :=
    { toEquiv := e
      continuous_toFun := continuous_iff_continuousAt.mpr (by
        intro x
        have hc := (ExponentialNormalCoordinates.exponential_smooth C F hF _ (hfull (E.symm x))).1.comp
          (f := fun y : Euclidean n => (⟨p, E.symm y⟩ : Phase S))
          (ExponentialNormalCoordinates.fiberInclusion_continuous_basis p E).continuousAt
        exact hc.congr (Eventually.of_forall (fun y => (he y).symm)))
      continuous_invFun := continuous_iff_continuousAt.mpr (fun q => (hlog q).1) }
  let c := ExponentialNormalCoordinates.parametrizationChart h.toOpenPartialHomeomorph
  have hc : c ∈ S.smoothStructure.val := by
    apply ExponentialNormalCoordinates.parametrizationChart_mem
    · intro x hx d hd hxd
      have hqd : fiberExponential F p (E.symm x) ∈ d.source := by rwa [← he x]
      have hh := ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF p E d hd x
        (hfull _) hqd
      exact hh.congr_of_eventuallyEq (Eventually.of_forall (fun y => congrArg (fun q => (d q).val) (he y)))
    · intro q hq
      exact hlog q
  refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
  · rw [ExponentialNormalCoordinates.parametrizationChart_source]
    rfl
  · rw [ExponentialNormalCoordinates.parametrizationChart_target]
    ext x
    simp
  · change e.symm p = 0
    apply e.injective
    rw [e.apply_symm_apply, he, map_zero]
    exact (ExponentialNormalCoordinates.zero_section_at C F hF p).2.symm
  · intro v
    change fiberExponential F p v = e (E v)
    rw [he, E.symm_apply_apply]

end P202.Geometry.ModelPolarDomains


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.ModelPolarData P202.HyperboloidData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
open Set
variable {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hS : HasProjectionChart S) (hg : IsInduced g) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)

include ha g C hS hg hC F hF

/-- Every chosen maximal family in an induced hyperboloid model has full
exponential domain, by its explicit all-velocity geodesics. -/
theorem hyperbolic_exponential_domain (p : Hyperboloid n a) (v : TangentSpace S p) :
    (⟨p,v⟩ : Phase S) ∈ exponentialDomain F := by
  obtain ⟨c, hc, hs, ht, hproj⟩ := hS
  have hcoord := HyperboloidModel.hyperboloid_coordinateAcceleration ha S c hc hs hproj g hg C hC
  obtain ⟨q, hq0, hq⟩ :=
    HyperboloidModel.global_geodesic_exists_of_coordinateAcceleration ha S c hc hs hproj g hg C hcoord ⟨p,v⟩
  exact ((hF ⟨p,v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q (by trivial) hq0 hq).1 (by trivial)

/-- The actual intrinsic exponential agrees with the source's unit-speed
Lorentz formula, at every center and every real time. -/
theorem hyperbolic_unit_formula (p : Hyperboloid n a) (v : TangentSpace S p)
    (hv : tangentNorm g p v = 1) (t : ℝ) :
    (⟨p,t • v⟩ : Phase S) ∈ exponentialDomain F ∧
    (fiberExponential F p (t • v)).val = unitCurve a p.val (ambientDifferential S p v) t := by
  obtain ⟨c, hc, hs, ht, hproj⟩ := hS
  have hcoord := HyperboloidModel.hyperboloid_coordinateAcceleration ha S c hc hs hproj g hg C hC
  have hvv : pairing g p v v = 1 := by
    have := SmoothMetrics.tangentNorm_sq g p v
    rw [hv, one_pow] at this
    exact this.symm
  obtain ⟨q, hq0, hq, huniq, hformula⟩ :=
    HyperboloidModel.unit_global_geodesic ha S c hc hs hproj g hg C hcoord p v hvv
  have hm := (hF ⟨p,v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q (by trivial) hq0 hq
  obtain ⟨hd, heq⟩ := ExponentialNormalCoordinates.radial_identity S C F hF p v t (hm.1 (by trivial))
  refine ⟨hd, ?_⟩
  rw [heq]
  exact (congrArg (fun z : Phase S => z.1.val) (hm.2 (x := t) (by trivial))).trans (hformula t).1

/-- An all-speed formula, including the zero vector, convenient for injectivity. -/
theorem hyperbolic_radial_formula (p : Hyperboloid n a) (v : TangentSpace S p) :
    (fiberExponential F p v).val =
      unitCurve a p.val (ambientDifferential S p ((tangentNorm g p v)⁻¹ • v)) (tangentNorm g p v) := by
  by_cases hv : v = 0
  · subst v
    simp only [SmoothMetrics.tangentNorm_zero, inv_zero, zero_smul]
    simp only [unitCurve, zero_div, Real.cosh_zero, Real.sinh_zero, mul_zero, zero_smul, one_smul, add_zero]
    exact congrArg Subtype.val (ExponentialNormalCoordinates.zero_section S C F hF p).2
  · have hr : 0 < tangentNorm g p v := lt_of_le_of_ne
      (SmoothMetrics.tangentNorm_nonneg g p v)
      (Ne.symm (mt (SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp hv))
    have hu : tangentNorm g p ((tangentNorm g p v)⁻¹ • v) = 1 := by
      rw [SmoothMetrics.tangentNorm_smul, abs_inv, abs_of_pos hr, inv_mul_cancel₀ (ne_of_gt hr)]
    have heq := (hyperbolic_unit_formula ha S g C hS hg hC F hF p _ hu (tangentNorm g p v)).2
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul] using heq

/-- Pairing the exponential with its center recovers the radial speed. -/
theorem hyperbolic_radial_inner (p : Hyperboloid n a) (v : TangentSpace S p) :
    lorentz p.val (fiberExponential F p v).val =
      -(a ^ 2) * Real.cosh (tangentNorm g p v / a) := by
  have hSource := hS
  obtain ⟨c, hc, hs, ht, hproj⟩ := hS
  have htangent := HyperboloidModel.tangent_identification n a ha S c hc hs hproj p
  have htan : lorentz p.val (ambientDifferential S p ((tangentNorm g p v)⁻¹ • v)) = 0 := by
    have hmem : ambientDifferential S p ((tangentNorm g p v)⁻¹ • v) ∈ tangentPlane p.val := by
      rw [← htangent.2]
      exact ⟨_, rfl⟩
    exact hmem
  have hadd (x y : Ambient n) : lorentz p.val (x + y) = lorentz p.val x + lorentz p.val y :=
    HyperboloidModel.lorentz_add_right p.val x y
  have hsmul (b : ℝ) (x : Ambient n) : lorentz p.val (b • x) = b * lorentz p.val x :=
    HyperboloidModel.lorentz_smul_right b p.val x
  rw [hyperbolic_radial_formula ha S g C hSource hg hC F hF p v, unitCurve,
    hadd, hsmul, hsmul, htan, p.property.1]
  ring

/-- The explicit hyperbolic exponential is injective at every center. -/
theorem hyperbolic_exponential_injective (p : Hyperboloid n a) :
    Function.Injective (fiberExponential F p) := by
  intro v w heq
  have hinner := congrArg (fun q : Hyperboloid n a => lorentz p.val q.val) heq
  rw [hyperbolic_radial_inner ha S g C hS hg hC F hF p v,
    hyperbolic_radial_inner ha S g C hS hg hC F hF p w] at hinner
  have hcosh := mul_left_cancel₀ (neg_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt ha))) hinner
  have hnorm : tangentNorm g p v = tangentNorm g p w := by
    have hdiv := Real.cosh_strictMonoOn.injOn
      (div_nonneg (SmoothMetrics.tangentNorm_nonneg g p v) ha.le)
      (div_nonneg (SmoothMetrics.tangentNorm_nonneg g p w) ha.le) hcosh
    exact (div_left_inj' (ne_of_gt ha)).mp hdiv
  by_cases hv : v = 0
  · subst v
    have hw := (SmoothMetrics.tangentNorm_eq_zero_iff g p w).mp (by
      simpa only [SmoothMetrics.tangentNorm_zero] using hnorm.symm)
    exact hw.symm
  · have hr : 0 < tangentNorm g p v := lt_of_le_of_ne
      (SmoothMetrics.tangentNorm_nonneg g p v)
      (Ne.symm (mt (SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp hv))
    have hc : a * Real.sinh (tangentNorm g p v / a) ≠ 0 :=
      ne_of_gt (mul_pos ha (Real.sinh_pos_iff.mpr (div_pos hr ha)))
    have heq' := congrArg Subtype.val heq
    rw [hyperbolic_radial_formula ha S g C hS hg hC F hF p v,
      hyperbolic_radial_formula ha S g C hS hg hC F hF p w, ← hnorm] at heq'
    have hD := add_left_cancel heq'
    change (a * Real.sinh (tangentNorm g p v / a)) •
        ambientDifferential S p ((tangentNorm g p v)⁻¹ • v) =
      (a * Real.sinh (tangentNorm g p v / a)) •
        ambientDifferential S p ((tangentNorm g p v)⁻¹ • w) at hD
    have hD' := (smul_right_inj hc).mp hD
    obtain ⟨c, hcm, hs, ht, hproj⟩ := hS
    have hscaled := (HyperboloidModel.tangent_identification n a ha S c hcm hs hproj p).1 hD'
    exact (smul_right_inj (inv_ne_zero (ne_of_gt hr))).mp hscaled

/-- The source's intrinsic distance equals hyperbolic radial length. The
attained minimizing velocity equals the given velocity by injectivity. -/
theorem hyperbolic_distance (p : Hyperboloid n a) (v : TangentSpace S p) :
    modelDistance g p (fiberExponential F p v) = tangentNorm g p v := by
  letI : ConnectedSpace (Hyperboloid n a) := (HyperboloidModel.topology n a ha).1
  obtain ⟨w, hw, hdist⟩ := CompleteExponentialMinimizers.attaining_vectors g C hC F hF p
    (hyperbolic_exponential_domain ha S g C hS hg hC F hF p) (fiberExponential F p v)
  have hwv := hyperbolic_exponential_injective ha S g C hS hg hC F hF p hw
  simpa only [hwv] using hdist.symm


def hyperbolicRadius (p q : Hyperboloid n a) : ℝ :=
  a * Real.arcosh (-lorentz p.val q.val / a^2)

lemma hyperbolicRadius_exponential (p : Hyperboloid n a) (v : TangentSpace S p) :
    hyperbolicRadius p (fiberExponential F p v) = tangentNorm g p v := by
  have hinner : -lorentz p.val (fiberExponential F p v).val / a^2 =
      Real.cosh (tangentNorm g p v / a) := by
    rw [hyperbolic_radial_inner ha S g C hS hg hC F hF p v]
    field_simp
  unfold hyperbolicRadius
  rw [hinner, Real.arcosh_cosh (div_nonneg (SmoothMetrics.tangentNorm_nonneg g p v) ha.le)]
  exact mul_div_cancel₀ _ (ne_of_gt ha)

def hyperbolicLog (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (p : Hyperboloid n a) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (q : Hyperboloid n a) : Euclidean n :=
  E (((tangentStructure S).fiberCoordinates.equiv c hc p (hs ▸ mem_univ p)).symm
    ((hyperbolicRadius p q / (a * Real.sinh (hyperbolicRadius p q / a))) •
      (q.val.1 - Real.cosh (hyperbolicRadius p q / a) • p.val.1)))

lemma hyperbolicLog_exponential (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (p : Hyperboloid n a) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (v : TangentSpace S p) :
    hyperbolicLog S c hc hs p E (fiberExponential F p v) = E v := by
  unfold hyperbolicLog
  rw [hyperbolicRadius_exponential ha S g C hS hg hC F hF p v]
  by_cases hv : v = 0
  · subst v
    simp only [SmoothMetrics.tangentNorm_zero, zero_div, Real.sinh_zero, mul_zero,
      div_zero, zero_smul, map_zero]
  · have hr : 0 < tangentNorm g p v := lt_of_le_of_ne
      (SmoothMetrics.tangentNorm_nonneg g p v)
      (Ne.symm (mt (SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp hv))
    have hdenom : a * Real.sinh (tangentNorm g p v / a) ≠ 0 :=
      ne_of_gt (mul_pos ha (Real.sinh_pos_iff.mpr (div_pos hr ha)))
    let K := (tangentStructure S).fiberCoordinates.equiv c hc p (hs ▸ mem_univ p)
    have hspatial : (fiberExponential F p v).val.1 =
        Real.cosh (tangentNorm g p v / a) • p.val.1 +
        (a * Real.sinh (tangentNorm g p v / a)) • K ((tangentNorm g p v)⁻¹ • v) := by
      have h := congrArg Prod.fst (hyperbolic_radial_formula ha S g C hS hg hC F hF p v)
      rw [HyperboloidModel.ambientDifferential_formula ha S c hc hs hproj] at h
      exact h
    rw [hspatial, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hdenom]
    change E (K.symm ((tangentNorm g p v) • K ((tangentNorm g p v)⁻¹ • v))) = E v
    rw [map_smul, K.symm_apply_apply, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]

lemma hyperbolic_exponential_log (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (p : Hyperboloid n a) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (q : Hyperboloid n a) :
    fiberExponential F p (E.symm (hyperbolicLog S c hc hs p E q)) = q := by
  letI : ConnectedSpace (Hyperboloid n a) := (HyperboloidModel.topology n a ha).1
  obtain ⟨v, hv, _hdist⟩ := CompleteExponentialMinimizers.attaining_vectors g C hC F hF p
    (hyperbolic_exponential_domain ha S g C hS hg hC F hF p) q
  rw [← hv, hyperbolicLog_exponential ha S g C hS hg hC F hF c hc hs hproj p E v,
    E.symm_apply_apply]


lemma hyperbolicLog_smooth_off_pole (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (p : Hyperboloid n a) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (q : Hyperboloid n a) (hqp : q ≠ p) :
    SmoothManifolds.MapData.ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      S.smoothStructure.val (hyperbolicLog S c hc hs p E) q := by
  let A : Spatial n → ℝ := fun x => -lorentz p.val (graphPoint a x) / a^2
  let R : Spatial n → ℝ := fun x => a * Real.arcosh (A x)
  let K := (tangentStructure S).fiberCoordinates.equiv c hc p (hs ▸ mem_univ p)
  let B := K.symm.trans E
  let G : Spatial n → Spatial n := fun x => B
    ((R x / (a * Real.sinh (R x / a))) • (x - Real.cosh (R x / a) • p.val.1))
  let U : Set (Spatial n) := {x | 1 < A x}
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    have hdot : ContDiff ℝ (⊤ : ℕ∞) (fun x : Spatial n => spatialDot p.val.1 x) := by
      unfold spatialDot
      fun_prop
    have ht := (HyperboloidModel.graph_smooth n a ha).snd
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Spatial n => -(spatialDot p.val.1 x - p.val.2 * (graphPoint a x).2) / a^2)
    exact (hdot.sub (contDiff_const.mul ht)).neg.div_const _
  have hU : IsOpen U := isOpen_lt continuous_const hA.continuous
  have hqU : (c q).val ∈ U := by
    letI : ConnectedSpace (Hyperboloid n a) := (HyperboloidModel.topology n a ha).1
    obtain ⟨v, hv, _hdist⟩ := CompleteExponentialMinimizers.attaining_vectors g C hC F hF p
      (hyperbolic_exponential_domain ha S g C hS hg hC F hF p) q
    have hv0 : v ≠ 0 := by
      intro hv0
      subst v
      have hz := (ExponentialNormalCoordinates.zero_section S C F hF p).2
      exact hqp (hv.symm.trans hz)
    have hr : 0 < tangentNorm g p v := lt_of_le_of_ne
      (SmoothMetrics.tangentNorm_nonneg g p v)
      (Ne.symm (mt (SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp hv0))
    change 1 < A (c q).val
    dsimp only [A]
    have hpgraph : graphPoint a q.val.1 = q.val := HyperboloidModel.graphPoint_projection q
    rw [hproj, hpgraph, ← hv,
      hyperbolic_radial_inner ha S g C hS hg hC F hF p v]
    have hn : a^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
    have hsimp : -(-(a^2) * Real.cosh (tangentNorm g p v / a)) / a^2 =
        Real.cosh (tangentNorm g p v / a) := by field_simp
    rw [hsimp]
    exact Real.one_lt_cosh.mpr (ne_of_gt (div_pos hr ha))
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) R U :=
    contDiffOn_const.mul (Real.contDiffOn_arcosh.comp hA.contDiffOn (fun x hx => hx))
  have hdenom : ∀ x ∈ U, a * Real.sinh (R x / a) ≠ 0 := by
    intro x hx
    have hRa : R x / a = Real.arcosh (A x) := by
      dsimp only [R]
      exact mul_div_cancel_left₀ _ (ne_of_gt ha)
    rw [hRa]
    exact ne_of_gt (mul_pos ha (Real.sinh_pos_iff.mpr (Real.arcosh_pos hx)))
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G U := by
    have hden : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => a * Real.sinh (R x / a)) U :=
      contDiffOn_const.mul (Real.contDiff_sinh.comp_contDiffOn (hR.div_const a))
    have hcosh : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Real.cosh (R x / a)) U :=
      Real.contDiff_cosh.comp_contDiffOn (hR.div_const a)
    exact B.toContinuousLinearEquiv.contDiff.contDiffOn.comp
      ((hR.div hden hdenom).smul (contDiffOn_id.sub (hcosh.smul contDiffOn_const)))
      (Set.mapsTo_univ _ _)
  have hrepr : ∀ z, G (c z).val = hyperbolicLog S c hc hs p E z := by
    intro z
    dsimp only [G, B, LinearEquiv.trans_apply, R, A, hyperbolicLog, hyperbolicRadius]
    have hpgraph : graphPoint a z.val.1 = z.val := HyperboloidModel.graphPoint_projection z
    rw [hproj, hpgraph]
  have hcont : ContinuousAt (hyperbolicLog S c hc hs p E) q := by
    have hcoordcont : ContinuousAt (fun z : Hyperboloid n a => (c z).val) q :=
      continuous_subtype_val.continuousAt.comp (c.continuousAt (hs ▸ mem_univ q))
    have h : ContinuousAt (fun z : Hyperboloid n a => G (c z).val) q :=
      (hG.continuousOn.continuousAt (hU.mem_nhds hqU)).comp
        (f := fun z : Hyperboloid n a => (c z).val) hcoordcont
    exact h.congr (Filter.Eventually.of_forall hrepr)
  have hext : SmoothManifolds.LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z : Hyperboloid n a => (c z).val) (hyperbolicLog S c hc hs p E) q :=
    ⟨U, hU, hqU, G, hG, Filter.Eventually.of_forall hrepr⟩
  refine ⟨hcont, ?_⟩
  intro d hd hqd
  exact SmoothManifolds.LocalCoordinateExtension.comp hext
    (SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 d hd c hc) hqd (hs ▸ mem_univ q))

end P202.Geometry.ModelPolarDomains

namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData P202.ModelPolarData P202.HyperboloidData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
open Set Filter
open scoped _root_.Topology
/-- The explicit logarithm, with the local normal chart at the pole,
provides the global smooth Cartesian exponential chart. -/
theorem hyperbolic_global_chart {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hS : HasProjectionChart S) (hg : IsInduced g) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : Hyperboloid n a) :
    ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (c : ModelChart n .euclidean (Hyperboloid n a)),
      IsOrthonormalCoordinates g p E ∧ c ∈ S.smoothStructure.val ∧
      c.source = univ ∧ c.target = univ ∧ (c p).val = 0 ∧
      ∀ v : TangentSpace S p,
        fiberExponential F p v = c.symm ⟨E v, by simp [modelSet]⟩ := by
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g p
  have hSource := hS
  obtain ⟨c₀, hc₀, hs₀, ht₀, hproj₀⟩ := hS
  let l := hyperbolicLog S c₀ hc₀ hs₀ p E
  let e : Euclidean n ≃ Hyperboloid n a :=
    { toFun := fun x => fiberExponential F p (E.symm x)
      invFun := l
      left_inv := fun x => by
        simpa only [LinearEquiv.apply_symm_apply] using
          hyperbolicLog_exponential ha S g C hSource hg hC F hF c₀ hc₀ hs₀ hproj₀ p E (E.symm x)
      right_inv := hyperbolic_exponential_log ha S g C hSource hg hC F hF c₀ hc₀ hs₀ hproj₀ p E }
  have hlog : ∀ q, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val e.symm q := by
    intro q
    change ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val l q
    by_cases hq : q = p
    · subst q
      obtain ⟨R, d, hd⟩ := ExponentialNormalCoordinates.normal_chart_exists S g C hC F hF p E hE
      apply normal_chart_log_smooth g F p E R d hd l
      intro q hq
      have hqt : tangentNorm g p (E.symm (d q).val) < R := by
        have h := d.map_source hq
        rwa [hd.2.2.2.2.1] at h
      have heq : fiberExponential F p (E.symm (d q).val) = q :=
        (hd.2.2.2.2.2 (d q) hqt).2.trans (d.left_inv hq)
      have h := hyperbolicLog_exponential ha S g C hSource hg hC F hF c₀ hc₀ hs₀ hproj₀ p E
        (E.symm (d q).val)
      rw [heq, E.apply_symm_apply] at h
      exact h
    · exact hyperbolicLog_smooth_off_pole ha S g C hSource hg hC F hF c₀ hc₀ hs₀ hproj₀ p E q hq
  obtain ⟨c, hc, hs, ht, hc0, hformula⟩ := exponential_global_chart C F hF p E
    (hyperbolic_exponential_domain ha S g C hSource hg hC F hF p) e (fun _ => rfl) hlog
  exact ⟨E, c, hE, hc, hs, ht, hc0, hformula⟩

/-- Global normal geometry, intrinsic radial distances and uniform metric
normal balls of the hyperboloid, together with its transitive isometries. -/
theorem hyperbolic_geometry : P202Specs.Geometry.ModelPolarDomains.hyperbolicType := by
  intro n hn a ha S g C hS hg hC
  refine ⟨?_, hyperbolic_homogeneous hn ha S g hS hg, ?_⟩
  · intro F hF p
    obtain ⟨E, c, hE, hc, hsource, htarget, hc0, hcformula⟩ :=
      hyperbolic_global_chart ha S g C hS hg hC F hF p
    have hv (v : TangentSpace S p) :
        (⟨p, v⟩ : Phase S) ∈ exponentialDomain F ∧
        fiberExponential F p v = c.symm ⟨E v, by simp [modelSet]⟩ ∧
        modelDistance g p (fiberExponential F p v) = tangentNorm g p v :=
      ⟨hyperbolic_exponential_domain ha S g C hS hg hC F hF p v,
        hcformula v, hyperbolic_distance ha S g C hS hg hC F hF p v⟩
    have hp : p ∈ c.source := by rw [hsource]; trivial
    have hexp (x : ModelSpace n .euclidean) (_hx : x ∈ c.target) :
        (⟨p, E.symm x.val⟩ : Phase S) ∈ exponentialDomain F ∧
        fiberExponential F p (E.symm x.val) = c.symm x := by
      simpa only [LinearEquiv.apply_symm_apply] using
        And.intro (hv (E.symm x.val)).1 (hv (E.symm x.val)).2.1
    refine ⟨E, c, hE, hc, hsource, htarget, hc0, hv, ?_, ?_⟩
    · apply polar_diffeomorphism_of_chart g F p E c (Ioi 0) hE hp hc0
      · exact fun t ht => ht
      · intro y hy
        rw [htarget]
        simp only [mem_univ, mem_Ioi, true_iff]
        apply lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p _)
        intro hz
        apply hy
        have hz' := (SmoothMetrics.tangentNorm_eq_zero_iff g p _).mp hz.symm
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg E hz'
      · intro x hx
        exact (hexp x hx).2
    · intro r hr
      obtain ⟨d, hd, hds⟩ := normal_chart_restriction g F p E hE c hc hp hc0 r hr
        (by rw [htarget]; exact subset_univ _) hexp
      refine ⟨d, hd, ?_⟩
      rw [hds]
      ext q
      have hq : q ∈ c.source := by rw [hsource]; trivial
      have hqexp : fiberExponential F p (E.symm (c q).val) = q :=
        (hexp (c q) (c.map_source hq)).2.trans (c.left_inv hq)
      have hdist := hyperbolic_distance ha S g C hS hg hC F hF p (E.symm (c q).val)
      rw [hqexp] at hdist
      simp only [mem_ofPred_eq, hq, true_and, hdist]
  · intro F hF p v hv t
    exact hyperbolic_unit_formula ha S g C hS hg hC F hF p v hv t

end P202.Geometry.ModelPolarDomains

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData Set Filter
open scoped _root_.Topology
universe u

/-- A Euclidean parametrization with nonsingular coordinate differential has
an actual smooth local inverse in the original maximal smooth structure. -/
theorem local_smooth_parametrization {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (f : Euclidean n → M)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hf : ∀ x ∈ U, ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (f y)).val) x)
    (x : Euclidean n) (hx : x ∈ U)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hxe : f x ∈ e.source)
    (L : Euclidean n →L[ℝ] Euclidean n)
    (hL : HasFDerivAt (fun y => (e (f y)).val) L x) (hbij : Function.Bijective L) :
    ∃ h : OpenPartialHomeomorph (Euclidean n) M,
      x ∈ h.source ∧ h.source ⊆ U ∧ EqOn h f h.source ∧
      (∀ y ∈ h.target, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
        S.smoothStructure.val h.symm y) := by
  let V := U ∩ f ⁻¹' e.source
  have hV : IsOpen V := hfc.isOpen_inter_preimage hU e.open_source
  have hxV : x ∈ V := ⟨hx, hxe⟩
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (e (f y)).val) V :=
    fun y hy => (hf y hy.1 e he hy.2).contDiffWithinAt
  obtain ⟨j, hjx, hjf, hji⟩ := SmoothManifolds.InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) (fun y => (e (f y)).val) V hV hcd x hxV L hL hbij
  let b := SmoothManifolds.InteriorInverse.ambientChart e
  have hxb : f x ∈ b.source := by
    refine ⟨hxe, ?_⟩
    change (e (f x)).val ∈ interior (modelSet n .euclidean)
    simp [modelSet]
  have hjfx : j x = b (f x) := congrFun hjf x
  let h := (j.restrOpen V hV).trans b.symm
  have hx' : x ∈ h.source := by
    refine ⟨⟨hjx, hxV⟩, ?_⟩
    change j x ∈ b.target
    rw [hjfx]
    exact b.map_source hxb
  have hsource (z : Euclidean n) (hz : z ∈ h.source) : z ∈ V := hz.1.2
  have heq : EqOn h f h.source := by
    intro z hz
    change b.symm (j z) = f z
    rw [hjf]
    apply b.left_inv
    refine ⟨(hsource z hz).2, ?_⟩
    change (e (f z)).val ∈ interior (modelSet n .euclidean)
    simp [modelSet]
  refine ⟨h, hx', fun z hz => (hsource z hz).1, heq, ?_⟩
  intro y hy
  have hye : y ∈ e.source := hy.1.1
  have hyj : (e y).val ∈ j.target := hy.2.1
  refine ⟨h.symm.continuousAt hy, ?_⟩
  intro d hd hyd
  have ht := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 d hd e he) hyd hye
  have hi : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val) h.symm y :=
    ⟨j.target, j.open_target, hyj, j.symm, hji, Eventually.of_forall (fun _ => rfl)⟩
  exact SmoothManifolds.LocalCoordinateExtension.comp hi ht

/-- A smooth injective Euclidean parametrization with nonsingular coordinate
Jacobians defines one global chart on its entire open image. -/
theorem injective_smooth_parametrization {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (f : Euclidean n → M)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hinj : InjOn f U)
    (hf : ∀ x ∈ U, ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (f y)).val) x)
    (hder : ∀ x ∈ U, ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
      ∃ L : Euclidean n →L[ℝ] Euclidean n,
        HasFDerivAt (fun y => (d (f y)).val) L x ∧ Function.Bijective L) :
    ∃ h : OpenPartialHomeomorph (Euclidean n) M,
      h.source = U ∧ h.target = f '' U ∧ (h : Euclidean n → M) = f ∧
      ExponentialNormalCoordinates.parametrizationChart h ∈ S.smoothStructure.val := by
  classical
  let e : PartialEquiv (Euclidean n) M := hinj.toPartialEquiv f U
  have es : e.source = U := rfl
  have et : e.target = f '' U := rfl
  have ef : (e : Euclidean n → M) = f := rfl
  have hlocal (y : M) (hy : y ∈ e.target) :
      ∃ j : OpenPartialHomeomorph (Euclidean n) M,
        y ∈ j.target ∧ j.target ⊆ e.target ∧
        EqOn e.symm j.symm j.target ∧
        (∀ z ∈ j.target, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
          S.smoothStructure.val j.symm z) := by
    let x := e.symm y
    have hx : x ∈ U := e.map_target hy
    obtain ⟨d, hd, hyd⟩ := S.smoothStructure.property.1.1 (f x)
    obtain ⟨L, hL, hbij⟩ := hder x hx d hd hyd
    obtain ⟨j, hxj, hjU, hjf, hjg⟩ :=
      local_smooth_parametrization S f U hU hfc hf x hx d hd hyd L hL hbij
    have hxy : f x = y := e.right_inv hy
    have hyj : y ∈ j.target := by
      rw [← hxy, ← hjf hxj]
      exact j.map_source hxj
    have hjtarget (z : M) (hz : z ∈ j.target) : z ∈ e.target := by
      rw [et]
      exact ⟨j.symm z, hjU (j.map_target hz), (hjf (j.map_target hz)).symm.trans (j.right_inv hz)⟩
    refine ⟨j, hyj, hjtarget, ?_, hjg⟩
    intro z hz
    have hpre : j.symm z ∈ e.source := hjU (j.map_target hz)
    have hright : e (j.symm z) = z :=
      (hjf (j.map_target hz)).symm.trans (j.right_inv hz)
    have hleft := e.left_inv hpre
    rwa [hright] at hleft
  have ht : IsOpen e.target := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨j, hyj, hjt, -, -⟩ := hlocal y hy
    exact mem_of_superset (j.open_target.mem_nhds hyj) hjt
  have hgi (y : M) (hy : y ∈ e.target) :
      ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val e.symm y := by
    obtain ⟨j, hyj, hjt, heq, hjg⟩ := hlocal y hy
    have hevent : e.symm =ᶠ[𝓝 y] j.symm :=
      Filter.eventuallyEq_of_mem (j.open_target.mem_nhds hyj) heq
    refine ⟨(j.symm.continuousAt hyj).congr hevent.symm, ?_⟩
    intro d hd hyd
    obtain ⟨V, hV, hv, H, hH, hrep⟩ := (hjg y hyj).2 d hd hyd
    exact ⟨V, hV, hv, H, hH, hrep.trans hevent.symm⟩
  let h : OpenPartialHomeomorph (Euclidean n) M := {
    toPartialEquiv := e
    open_source := hU
    open_target := ht
    continuousOn_toFun := hfc
    continuousOn_invFun := fun y hy => (hgi y hy).1.continuousWithinAt }
  refine ⟨h, rfl, rfl, rfl, ?_⟩
  apply ExponentialNormalCoordinates.parametrizationChart_mem h
  · intro x hx d hd hxd
    exact hf x hx d hd hxd
  · exact hgi

end P202.Geometry.ModelPolarDomains
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData P202.ModelPolarData P202.SpaceFormData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.ExponentialData
open P202.Geometry.EuclideanSphericalModels Set Filter
theorem spherical_exponential_injOn {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) :
    Set.InjOn (fiberExponential F p)
      {v : TangentSpace B.manifold p | tangentNorm B.metric p v < Real.pi * a} := by
  intro v hv w hw heq
  have hnorm : tangentNorm B.metric p v = tangentNorm B.metric p w := by
    rw [← spherical_radial_distance ha B hB F hF p v hv.le,
      ← spherical_radial_distance ha B hB F hF p w hw.le, heq]
  by_cases hz : v = 0
  · subst v
    have hzw : w = 0 := (SmoothMetrics.tangentNorm_eq_zero_iff B.metric p w).mp
      (hnorm.symm.trans (SmoothMetrics.tangentNorm_zero B.metric p))
    exact hzw.symm
  have hnv : 0 < tangentNorm B.metric p v :=
    lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg _ _ _) (by
      intro h; exact hz ((SmoothMetrics.tangentNorm_eq_zero_iff _ _ _).mp h.symm))
  have hangle0 : 0 < tangentNorm B.metric p v / a := div_pos hnv ha
  have hanglepi : tangentNorm B.metric p v / a < Real.pi :=
    (div_lt_iff₀ ha).mpr hv
  have hsin : a * Real.sin (tangentNorm B.metric p v / a) ≠ 0 :=
    mul_ne_zero ha.ne' (Real.sin_pos_of_pos_of_lt_pi hangle0 hanglepi).ne'
  have hv0 : B.ambientVector p v ≠ 0 := by
    intro h; have h' := spherical_model_norm B p v; rw [h, norm_zero] at h'; linarith
  have hw0 : B.ambientVector p w ≠ 0 := by
    intro h; have h' := spherical_model_norm B p w; rw [h, norm_zero] at h'; linarith
  have hformula := congrArg Subtype.val heq
  rw [(spherical_formula B hB F hF p v).2, (spherical_formula B hB F hF p w).2] at hformula
  simp only [sphereCurve, ite_eq_right hv0, ite_eq_right hw0, greatCircle, mul_one,
    ← spherical_model_norm B p v, ← spherical_model_norm B p w, ← hnorm] at hformula
  have hscaled := add_left_cancel hformula
  have hunit := congrArg (fun x : E (n+1) =>
    (a * Real.sin (tangentNorm B.metric p v / a))⁻¹ • x) hscaled
  simp only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hsin, one_mul] at hunit
  have hamb := congrArg (fun x : E (n+1) => tangentNorm B.metric p v • x) hunit
  simp only [smul_smul, mul_inv_cancel₀ hnv.ne', one_smul] at hamb
  exact B.inclusion.injective p ((A.coordinates p.val).injective hamb)

theorem spherical_exponential_boundary {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) (v : TangentSpace B.manifold p)
    (hv : tangentNorm B.metric p v = Real.pi * a) :
    (fiberExponential F p v).val = -p.val := by
  have hnorm : ‖B.ambientVector p v‖ = Real.pi * a := (spherical_model_norm B p v).symm.trans hv
  have hv0 : B.ambientVector p v ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm
    exact (mul_pos Real.pi_pos ha).ne' hnorm.symm
  rw [(spherical_formula B hB F hF p v).2]
  simp [sphereCurve, hv0, greatCircle, hnorm, mul_div_cancel_right₀ _ ha.ne']

theorem spherical_exponential_surjOn {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) :
    Set.SurjOn (fiberExponential F p)
      {v : TangentSpace B.manifold p | tangentNorm B.metric p v < Real.pi * a}
      {q : Sphere n a | q.val ≠ -p.val} := by
  intro q hq
  letI : ConnectedSpace (Sphere n a) := hB.1
  have hfull : P202.CompleteExponentialData.FullExponentialAt F p :=
    fun w => (spherical_formula B hB F hF p w).1
  obtain ⟨w, hw, hd⟩ := CompleteExponentialMinimizers.attaining_vectors
    B.metric B.connection B.leviCivita F hF p hfull q
  have hbound := spherical_minimizer_norm_bound ha B hB F hF p w (by rw [hw]; exact hd)
  refine ⟨w, ?_, hw⟩
  apply lt_of_le_of_ne hbound
  intro heq
  apply hq
  rw [← hw]
  exact spherical_exponential_boundary ha B hB F hF p w heq

theorem spherical_exponential_mapsTo {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) :
    Set.MapsTo (fiberExponential F p)
      {v : TangentSpace B.manifold p | tangentNorm B.metric p v < Real.pi * a}
      {q : Sphere n a | q.val ≠ -p.val} := by
  intro v hv heq
  have hin := spherical_exponential_inner B hB F hF p v
  rw [heq, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp p.property] at hin
  have hcos : Real.cos (tangentNorm B.metric p v / a) = -1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ha.ne')
    rw [← hin]
    ring
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi
    (div_nonneg (SmoothMetrics.tangentNorm_nonneg _ _ _) ha.le)
    le_rfl ((div_lt_iff₀ ha).mpr hv)
  rw [Real.cos_pi, hcos] at hcoslt
  exact lt_irrefl _ hcoslt

end P202.Geometry.ModelPolarDomains

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.ExponentialData
  P202.ExponentialJacobiData P202.ConstantCurvaturePolarData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n .euclidean M}

theorem fiberDifferential_injective_of_polar_metric (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (r k : ℝ) (u : TangentSpace S p)
    (hr : r ≠ 0) (hu : pairing g p u u = 1) (hs : s k r ≠ 0)
    (hmetric : ∀ (a b : ℝ) (w z : TangentSpace S p),
      pairing g p w u = 0 → pairing g p z u = 0 →
      pairing g (fiberExponential F p (r • u))
        (polarDifferential F p r u a w) (polarDifferential F p r u b z) =
        a * b + s k r ^ 2 * pairing g p w z) :
    Function.Injective (fiberDifferential S F p (r • u)) := by
  intro v w hvw
  let δ := v + (-1 : ℝ) • w
  have hδ : fiberDifferential S F p (r • u) δ = 0 := by
    apply (selectedCoordinates S (fiberExponential F p (r • u))).injective
    simp only [δ, map_add, map_smul, hvw, map_zero]
    module
  let a := pairing g p δ u
  let z := r⁻¹ • (δ - a • u)
  have hz : pairing g p z u = 0 := by
    simp only [z, pairing, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.sub_left]
    change r⁻¹ * (pairing g p δ u - a * pairing g p u u) = 0
    rw [hu, mul_one]
    simp [a]
  have hsplit : a • u + r • z = δ := by
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    module
  have hpzero : polarDifferential F p r u a z = 0 := by
    change fiberDifferential S F p (r • u) (a • u + r • z) = 0
    rw [hsplit, hδ]
  have heq := hmetric a a z z hz hz
  rw [hpzero, SmoothMetrics.pairing_self_zero] at heq
  have hznn := SmoothMetrics.pairing_self_nonneg g p z
  have hss : 0 < s k r ^ 2 := sq_pos_of_ne_zero hs
  have ha : a = 0 := by nlinarith [sq_nonneg a]
  have hzz : pairing g p z z = 0 := by nlinarith
  have hz0 : z = 0 := by
    by_contra h
    exact (ne_of_gt (g.positive p z h)) hzz
  have hδ0 : δ = 0 := by rw [← hsplit, ha, hz0, zero_smul, smul_zero, add_zero]
  apply (selectedCoordinates S p).injective
  have hh := congrArg (selectedCoordinates S p) hδ0
  simp only [δ, map_add, map_smul, map_zero] at hh
  exact add_neg_eq_zero.mp (by simpa only [neg_one_smul] using hh)

theorem fiberDifferential_coordinates_basis
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (x : Euclidean n) (hx : (⟨p, E.symm x⟩ : Phase S) ∈ exponentialDomain F)
    (hxd : fiberExponential F p (E.symm x) ∈ d.source) (y : Euclidean n) :
    (tangentStructure S).fiberCoordinates.equiv d hd _ hxd
      (fiberDifferential S F p (E.symm x) (E.symm y)) =
      fderiv ℝ (fun z : Euclidean n => (d (fiberExponential F p (E.symm z))).val) x y := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E0 := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let A := (E.symm.trans E0).toContinuousLinearEquiv
  have hA (z : Euclidean n) : E0.symm (A z) = E.symm z := E0.symm_apply_apply _
  have hx0 : (⟨p, E0.symm (A x)⟩ : Phase S) ∈ exponentialDomain F := by rwa [hA]
  have hxd0 : fiberExponential F p (E0.symm (A x)) ∈ d.source := by rwa [hA]
  have hcd := ExponentialNormalCoordinates.fiberExponential_contDiffAt C F hF
    p e he hp d hd (A x) hx0 hxd0
  have hchain := (hcd.differentiableAt (by simp)).hasFDerivAt.comp x A.hasFDerivAt
  change HasFDerivAt
    (fun z : Euclidean n => (d (fiberExponential F p (E0.symm (A z)))).val) _ x at hchain
  have hchain' : HasFDerivAt
      (fun z : Euclidean n => (d (fiberExponential F p (E.symm z))).val)
      ((fderiv ℝ (fun z : Euclidean n => (d (fiberExponential F p (E0.symm z))).val)
        (A x)).comp A.toContinuousLinearMap) x := by
    simpa only [Function.comp_def, hA] using hchain
  rw [hchain'.fderiv]
  have h := ExponentialJacobi.differential_coordinates S C F hF p (E.symm x) hx
    e d he hd hp hxd (E.symm y)
  change _ = fderiv ℝ (fun z : Euclidean n => (d (fiberExponential F p (E0.symm z))).val)
    (E0 (E.symm x)) (E0 (E.symm y))
  exact h

 theorem fiberExponential_jacobian_bijective_of_fiberDifferential
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (x : Euclidean n) (hx : (⟨p, E.symm x⟩ : Phase S) ∈ exponentialDomain F)
    (hxd : fiberExponential F p (E.symm x) ∈ d.source)
    (hinj : Function.Injective (fiberDifferential S F p (E.symm x))) :
    Function.Bijective (fderiv ℝ
      (fun z : Euclidean n => (d (fiberExponential F p (E.symm z))).val) x) := by
  have hDinj : Function.Injective (fderiv ℝ
      (fun z : Euclidean n => (d (fiberExponential F p (E.symm z))).val) x) := by
    intro a b hab
    apply E.symm.injective
    apply hinj
    apply ((tangentStructure S).fiberCoordinates.equiv d hd _ hxd).injective
    rw [fiberDifferential_coordinates_basis C F hF p E d hd x hx hxd a,
      fiberDifferential_coordinates_basis C F hF p E d hd x hx hxd b]
    exact hab
  exact ⟨hDinj, LinearMap.surjective_of_injective hDinj⟩
theorem spherical_s_nonzero {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hrR : r < Real.pi * a) : s ((a ^ 2)⁻¹) r ≠ 0 := by
  have hk : 0 < (a ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos ha)
  rw [s, ite_eq_left hk, Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  apply div_ne_zero
  · have hs : 0 < Real.sin (r / a) :=
      Real.sin_pos_of_pos_of_lt_pi (div_pos hr ha) ((div_lt_iff₀ ha).mpr hrR)
    simpa only [div_eq_mul_inv, mul_comm] using hs.ne'
  · exact inv_ne_zero ha.ne'

open P202.SpaceFormData

theorem spherical_exponential_jacobian {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (F : CurveFamily (Phase B.manifold)) (hF : IsMaximalFamily B.manifold B.connection F)
    (p : Sphere n a) (E : TangentSpace B.manifold p ≃ₗ[ℝ] Euclidean n)
    (x : Euclidean n) (hx : tangentNorm B.metric p (E.symm x) < Real.pi * a)
    (d : ModelChart n .euclidean (Sphere n a)) (hd : d ∈ B.manifold.smoothStructure.val)
    (hxd : fiberExponential F p (E.symm x) ∈ d.source) :
    ∃ L : Euclidean n →L[ℝ] Euclidean n,
      HasFDerivAt (fun y : Euclidean n => (d (fiberExponential F p (E.symm y))).val) L x ∧
      Function.Bijective L := by
  have hfull (v : TangentSpace B.manifold p) :
      (⟨p, v⟩ : Phase B.manifold) ∈ exponentialDomain F := by
    obtain ⟨q, hq, hformula⟩ := hB.2.2.2.2.1 p v
    exact ((hF ⟨p, v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
      hq.1 hq.2.1 hq.2.2.1).1 (by trivial)
  by_cases hx0 : x = 0
  · subst x
    have hp : p ∈ d.source := by
      simpa only [map_zero, (ExponentialNormalCoordinates.zero_section_at B.connection F hF p).2] using hxd
    let K := (tangentStructure B.manifold).fiberCoordinates.equiv d hd p hp
    let L := (E.symm.trans K).toContinuousLinearEquiv
    refine ⟨L.toContinuousLinearMap, ?_, L.bijective⟩
    exact ExponentialNormalCoordinates.fiberExponential_derivative_basis B.connection F hF p E d hd hp
  · let r := tangentNorm B.metric p (E.symm x)
    have hr : 0 < r :=
      lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg _ _ _) (by
        intro hz
        apply hx0
        have hv := (SmoothMetrics.tangentNorm_eq_zero_iff B.metric p _).mp hz.symm
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg E hv)
    let u := r⁻¹ • E.symm x
    have huNorm : tangentNorm B.metric p u = 1 := by
      rw [SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      exact inv_mul_cancel₀ hr.ne'
    have hu : pairing B.metric p u u = 1 := by
      rw [← SmoothMetrics.tangentNorm_sq, huNorm, one_pow]
    have hru : r • u = E.symm x := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    obtain ⟨R, hR, hk⟩ := hB.2.2.2.1
    have hmetric := ConstantCurvaturePolar.polar_metric B.manifold B.metric B.connection
      B.leviCivita R hR ((a ^ 2)⁻¹) hk F hF p r u hr.ne' hu (by rw [hru]; exact hfull _)
    have hinj := fiberDifferential_injective_of_polar_metric B.metric F p r ((a ^ 2)⁻¹)
      u hr.ne' hu (spherical_s_nonzero ha hr hx) hmetric
    rw [hru] at hinj
    let f := fun y : Euclidean n => (d (fiberExponential F p (E.symm y))).val
    refine ⟨fderiv ℝ f x, ?_, ?_⟩
    · exact (ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis B.connection F hF
        p E d hd x (hfull _) hxd).differentiableAt (by simp) |>.hasFDerivAt
    · exact fiberExponential_jacobian_bijective_of_fiberDifferential B.connection F hF p E d hd
        x (hfull _) hxd hinj
end P202.Geometry.ModelPolarDomains
namespace P202.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData P202.ModelPolarData P202.SpaceFormData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.ExponentialData
open Set Filter
theorem spherical_normal_geometry_of_nonsingular {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (hder : ∀ (F : CurveFamily (Phase B.manifold)),
      IsMaximalFamily B.manifold B.connection F → ∀ (p : Sphere n a)
      (E : TangentSpace B.manifold p ≃ₗ[ℝ] Euclidean n),
      IsOrthonormalCoordinates B.metric p E → ∀ x : Euclidean n,
      tangentNorm B.metric p (E.symm x) < Real.pi * a →
      ∀ d ∈ B.manifold.smoothStructure.val,
      fiberExponential F p (E.symm x) ∈ d.source →
      ∃ L : Euclidean n →L[ℝ] Euclidean n,
        HasFDerivAt (fun y => (d (fiberExponential F p (E.symm y))).val) L x ∧
        Function.Bijective L) : SphericalNormalGeometry B := by
  intro F hF p
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist B.metric p
  let f : Euclidean n → Sphere n a := fun x => fiberExponential F p (E.symm x)
  let U : Set (Euclidean n) := {x | tangentNorm B.metric p (E.symm x) < Real.pi * a}
  have hU : IsOpen U :=
    (ExponentialNormalCoordinates.orthonormal_norm_continuous B.metric p E hE).isOpen_preimage _ isOpen_Iio
  have hfull : ∀ v : TangentSpace B.manifold p, (⟨p, v⟩ : Phase B.manifold) ∈ exponentialDomain F :=
    fun v => (spherical_formula B hB F hF p v).1
  have hfc : ContinuousOn f U := by
    intro x hx
    exact ((ExponentialNormalCoordinates.exponential_smooth B.connection F hF _ (hfull (E.symm x))).1.comp
      (f := fun y : Euclidean n => (⟨p, E.symm y⟩ : Phase B.manifold))
      (ExponentialNormalCoordinates.fiberInclusion_continuous_basis p E).continuousAt).continuousWithinAt
  have hinj : InjOn f U := by
    intro x hx y hy hxy
    exact E.symm.injective (spherical_exponential_injOn ha B hB F hF p hx hy hxy)
  have hf : ∀ x ∈ U, ∀ d ∈ B.manifold.smoothStructure.val, f x ∈ d.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (f y)).val) x := by
    intro x hx d hd hxd
    exact ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis B.connection F hF p E d hd x
      (hfull (E.symm x)) hxd
  obtain ⟨h, hs, ht, hh, hc⟩ := injective_smooth_parametrization B.manifold f U hU hfc hinj hf
    (fun x hx d hd hxd => hder F hF p E hE x hx d hd hxd)
  let c := ExponentialNormalCoordinates.parametrizationChart h
  have hc' : c ∈ B.manifold.smoothStructure.val := hc
  have hcs : c.source = {q : Sphere n a | q.val ≠ -p.val} := by
    rw [show c.source = h.target from ExponentialNormalCoordinates.parametrizationChart_source h, ht]
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact spherical_exponential_mapsTo ha B hB F hF p hx
    · intro hq
      obtain ⟨v, hv, heq⟩ := spherical_exponential_surjOn ha B hB F hF p hq
      refine ⟨E v, ?_, ?_⟩
      · change tangentNorm B.metric p v < Real.pi * a at hv
        change tangentNorm B.metric p (E.symm (E v)) < Real.pi * a
        simpa only [LinearEquiv.symm_apply_apply] using hv
      · simpa only [f, LinearEquiv.symm_apply_apply] using heq
  have hct : c.target = {x : ModelSpace n .euclidean | tangentNorm B.metric p (E.symm x.val) < Real.pi * a} := by
    rw [show c.target = {x | x.val ∈ h.source} from ExponentialNormalCoordinates.parametrizationChart_target h, hs]
    rfl
  have h0 : (0 : Euclidean n) ∈ h.source := by
    rw [hs]
    simp only [U, mem_ofPred_eq, map_zero, SmoothMetrics.tangentNorm_zero]
    exact mul_pos Real.pi_pos ha
  have h0p : h 0 = p := by
    rw [hh]
    simpa only [f, map_zero] using (ExponentialNormalCoordinates.zero_section_at B.connection F hF p).2
  have hp : p ∈ c.source := by
    rw [show c.source = h.target from ExponentialNormalCoordinates.parametrizationChart_source h]
    rw [← h0p]
    exact h.map_source h0
  have hc0 : (c p).val = 0 := by
    change h.symm p = 0
    rw [← h0p]
    exact h.left_inv h0
  have hexp (x : ModelSpace n .euclidean) (_hx : x ∈ c.target) :
      (⟨p, E.symm x.val⟩ : Phase B.manifold) ∈ exponentialDomain F ∧
      fiberExponential F p (E.symm x.val) = c.symm x := by
    refine ⟨hfull _, ?_⟩
    change f x.val = h x.val
    exact congrFun hh.symm x.val
  have hnormal : IsNormalChart B.metric F p E (Real.pi * a) c :=
    ⟨mul_pos Real.pi_pos ha, hc', hp, hc0, hct, fun x hx => hexp x (by rwa [hct])⟩
  refine ⟨E, c, hE, hnormal, hcs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact spherical_formula B hB F hF p v
  · intro v hv
    exact spherical_radial_distance ha B hB F hF p v hv
  · intro v hv
    apply spherical_exponential_boundary ha B hB F hF p
    rw [SmoothMetrics.tangentNorm_smul, hv, mul_one, abs_of_pos (mul_pos Real.pi_pos ha)]
  · exact spherical_distance_arccos ha B hB F hF p
  · exact spherical_antipode_distance ha B hB F hF p
  · apply polar_diffeomorphism_of_chart B.metric F p E c (Ioo 0 (Real.pi * a)) hE hp hc0
    · intro t ht
      exact ht.1
    · intro y hy
      rw [hct]
      change tangentNorm B.metric p (E.symm y) < Real.pi * a ↔ _
      have hy' : E.symm y ≠ 0 := by
        intro heq
        apply hy
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg E heq
      have hn : 0 < tangentNorm B.metric p (E.symm y) :=
        lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg _ _ _)
          (Ne.symm (mt (SmoothMetrics.tangentNorm_eq_zero_iff _ _ _).mp hy'))
      exact ⟨fun h => ⟨hn, h⟩, fun h => h.2⟩
    · intro x hx
      exact (hexp x hx).2
  · have hlogdist (q : Sphere n a) (hq : q ∈ c.source) :
        tangentNorm B.metric p (E.symm (c q).val) = modelDistance B.metric p q := by
      have hqt := c.map_source hq
      have hn : tangentNorm B.metric p (E.symm (c q).val) < Real.pi * a := by rwa [hct] at hqt
      have heq := (hexp (c q) hqt).2.trans (c.left_inv hq)
      have hdist := spherical_radial_distance ha B hB F hF p (E.symm (c q).val) hn.le
      rw [heq] at hdist
      exact hdist.symm
    intro r hr hrR
    obtain ⟨d, hd, hds⟩ := normal_chart_restriction B.metric F p E hE c hc' hp hc0 r hr
      (fun x hx => by rw [hct]; exact hx.trans hrR) hexp
    refine ⟨d, hd, hds.trans ?_⟩
    ext q
    constructor
    · rintro ⟨hqc, hqnorm⟩
      rwa [hlogdist q hqc] at hqnorm
    · intro hqdist
      change modelDistance B.metric p q < r at hqdist
      have hqc : q ∈ c.source := by
        rw [hcs]
        intro heq
        have hanti := spherical_antipode_distance ha B hB F hF p q heq
        rw [hanti] at hqdist
        linarith
      exact ⟨hqc, by rwa [hlogdist q hqc]⟩

 theorem spherical_normal_geometry {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A) (hB : B.Conclusion) :
    SphericalNormalGeometry B := by
  apply spherical_normal_geometry_of_nonsingular ha B hB
  intro F hF p E _hE x hx d hd hxd
  exact spherical_exponential_jacobian ha B hB F hF p E x hx d hd hxd

 theorem spherical_geometry : P202Specs.Geometry.ModelPolarDomains.sphericalType := by
  intro n _hn a ha A B hB
  exact ⟨spherical_normal_geometry ha B hB, spherical_homogeneity B hB⟩
end P202.Geometry.ModelPolarDomains

namespace P202.Geometry.ModelPolarDomains

/-- The complete model polar-domain, radial-distance and homogeneity stage,
proved from the original model constructions without classification. -/
theorem model_polar_domains : P202Specs.Geometry.ModelPolarDomains.modelPolarDomainsType :=
  ⟨models_exist, euclidean_formula, euclidean_distance, spherical_formula,
    spherical_cut_time, euclidean_geometry, spherical_geometry, hyperbolic_geometry,
    halfSpace_homogeneity⟩

end P202.Geometry.ModelPolarDomains
