import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.EuclideanSphericalModels
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.BasicFundamentalGroups
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HopfRinow
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussWeingarten
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussCodazziRicci
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.StandardCoverings
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.EuclideanSphericalModels
open P202.SpaceFormData
open P202Specs.Geometry.EuclideanSphericalModels

/-- Rescaling is a homeomorphism on the literal radius-a sphere. -/
def radiusHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Sphere n a ≃ₜ P202Specs.Topology.BasicFundamentalGroups.Sphere n where
  toFun p := ⟨a⁻¹ • p.val, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos ha, mem_sphere_zero_iff_norm.mp p.property]
    exact inv_mul_cancel₀ ha.ne'⟩
  invFun q := ⟨a • q.val, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, mem_sphere_zero_iff_norm.mp q.property, mul_one]⟩
  left_inv p := by ext; simp [smul_smul, ha.ne']
  right_inv q := by ext; simp [smul_smul, ha.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem radius_bridge : radiusBridgeType := by
  intro n a ha
  exact ⟨radiusHomeomorph n a ha, fun _ => rfl, fun _ => rfl⟩

theorem model_topology : topologyType := by
  intro n hn a ha
  have hs := P202.Topology.spheresSimplyConnected n hn
  let := hs.2
  let : SimplyConnectedSpace (Sphere n a) :=
    (radiusHomeomorph n a ha).toHomotopyEquiv.simplyConnectedSpace
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

/-- Expanding the ambient norm of a linear combination of orthogonal vectors. -/
theorem norm_combination_sq {n : ℕ} (p u : E n) (hpu : inner ℝ p u = 0)
    (c d : ℝ) : ‖c • p + d • u‖ ^ 2 = c ^ 2 * ‖p‖ ^ 2 + d ^ 2 * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have hup : inner ℝ u p = 0 := by rw [real_inner_comm]; exact hpu
  simp only [inner_add_left, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right, hpu, hup,
    real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_zero, zero_add, add_zero]

theorem line_formula : lineType := by
  intro n p v
  refine ⟨by simp [line], ?_, fun t => hasDerivAt_const t v⟩
  intro t
  change HasDerivAt (fun s : ℝ => p + s • v) v t
  simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add p

theorem greatCircle_derivative {n : ℕ} (a : ℝ) (ha : a ≠ 0) (p u : E n) (t : ℝ) :
    HasDerivAt (greatCircle a p u) (greatCircleVelocity a p u t) t := by
  have hd : HasDerivAt (fun s : ℝ => s / a) (1 / a) t :=
    (hasDerivAt_id t).div_const a
  change HasDerivAt (fun s => Real.cos (s / a) • p + (a * Real.sin (s / a)) • u) _ t
  convert ((hd.cos.smul_const p).add ((hd.sin.const_mul a).smul_const u)) using 1
  simp only [greatCircleVelocity]
  congr 1 <;> congr 1 <;> field_simp

theorem greatCircle_second_derivative {n : ℕ} (a : ℝ) (ha : a ≠ 0)
    (p u : E n) (t : ℝ) :
    HasDerivAt (greatCircleVelocity a p u) (-(a⁻¹ ^ 2) • greatCircle a p u t) t := by
  have hd : HasDerivAt (fun s : ℝ => s / a) (1 / a) t :=
    (hasDerivAt_id t).div_const a
  change HasDerivAt (fun s => (-(Real.sin (s / a)) / a) • p + Real.cos (s / a) • u) _ t
  convert (((hd.sin.neg.div_const a).smul_const p).add (hd.cos.smul_const u)) using 1
  simp only [greatCircle, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp


theorem greatCircle_formula : greatCircleType := by
  intro n a ha p u hp hpu hu
  refine ⟨by simp [greatCircle], by simp [greatCircleVelocity], fun t => ?_⟩
  have hc := Real.cos_sq_add_sin_sq (t / a)
  have hn : ‖greatCircle a p u t‖ ^ 2 = a ^ 2 := by
    rw [greatCircle, norm_combination_sq p u hpu, hp, hu]
    nlinarith
  have hv : ‖greatCircleVelocity a p u t‖ ^ 2 = 1 ^ 2 := by
    rw [greatCircleVelocity, norm_combination_sq p u hpu, hp, hu]
    field_simp
    nlinarith
  exact ⟨(sq_eq_sq₀ (norm_nonneg _) ha.le).mp hn,
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hv,
    greatCircle_derivative a ha.ne' p u t,
    greatCircle_second_derivative a ha.ne' p u t⟩

theorem sphereCurve_formula : arbitraryVelocityType := by
  intro n a ha p v hp hpv
  by_cases hv : v = 0
  · subst v
    have heq : sphereCurve a p 0 = fun _ : ℝ => p := by
      funext s; simp [sphereCurve]
    have hveq : sphereCurveVelocity a p 0 = fun _ : ℝ => (0 : E n) := by
      funext s; simp [sphereCurveVelocity]
    simpa only [heq, hveq, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_div, neg_zero, zero_smul] using
      (show p = p ∧ (0 : E n) = 0 ∧ ∀ t : ℝ,
        ‖p‖ = a ∧ ‖(0 : E n)‖ = ‖(0 : E n)‖ ∧
        HasDerivAt (fun _ : ℝ => p) 0 t ∧
        HasDerivAt (fun _ : ℝ => (0 : E n)) 0 t from
        ⟨rfl, rfl, fun t => ⟨hp, rfl, hasDerivAt_const t p,
          hasDerivAt_const t (0 : E n)⟩⟩)
  · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hn : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
      exact inv_mul_cancel₀ hvn
    have ho : inner ℝ p (‖v‖⁻¹ • v) = 0 := by
      rw [real_inner_smul_right, hpv, mul_zero]
    have hg := greatCircle_formula n a ha p (‖v‖⁻¹ • v) hp ho hn
    have heq : sphereCurve a p v = fun t => greatCircle a p (‖v‖⁻¹ • v) (‖v‖ * t) := by
      funext s; simp [sphereCurve, hv]
    have hveq : sphereCurveVelocity a p v =
        fun t => ‖v‖ • greatCircleVelocity a p (‖v‖⁻¹ • v) (‖v‖ * t) := by
      funext s; simp [sphereCurveVelocity, hv]
    rw [heq, hveq]
    refine ⟨by simpa using hg.1, ?_, fun t => ?_⟩
    · simpa [smul_smul, hvn] using congrArg (fun w : E n => ‖v‖ • w) hg.2.1
    · obtain ⟨hmem, hspeed, hd, hdd⟩ := hg.2.2 (‖v‖ * t)
      have hscale : HasDerivAt (fun s : ℝ => ‖v‖ * s) ‖v‖ t := by
        simpa using (hasDerivAt_id t).const_mul ‖v‖
      refine ⟨hmem, ?_, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v), hspeed, mul_one]
      · change HasDerivAt (fun s => greatCircle a p (‖v‖⁻¹ • v) (‖v‖ * s)) _ t
        exact hd.scomp t hscale
      · change HasDerivAt (fun s => ‖v‖ • greatCircleVelocity a p (‖v‖⁻¹ • v) (‖v‖ * s)) _ t
        have h := (hdd.scomp t hscale).const_smul ‖v‖
        apply h.congr_deriv
        simp only [smul_smul]
        congr 1
        field_simp

/-- The metric norm in a standard Euclidean realization is the actual
Euclidean norm of its intrinsic tangent coordinates. -/
theorem euclidean_model_norm {n : ℕ} (G : EuclideanModel n) (p : E n)
    (v : SmoothManifolds.TangentData.TangentSpace G.manifold p) :
    P202.MetricData.tangentNorm G.metric p v = ‖G.coordinates p v‖ := by
  unfold P202.MetricData.tangentNorm
  rw [G.metric_standard, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- This equality uses the induced metric and the actual immersion differential. -/
theorem spherical_model_pairing {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a)
    (v w : SmoothManifolds.TangentData.TangentSpace B.manifold p) :
    P202.MetricData.pairing B.metric p v w =
      inner ℝ (B.ambientVector p v) (B.ambientVector p w) := by
  rw [← B.induced p v w, A.metric_standard]
  rfl

theorem spherical_model_norm {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a)
    (v : SmoothManifolds.TangentData.TangentSpace B.manifold p) :
    P202.MetricData.tangentNorm B.metric p v = ‖B.ambientVector p v‖ := by
  unfold P202.MetricData.tangentNorm
  rw [spherical_model_pairing, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem spherical_model_tangent {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a)
    (v : SmoothManifolds.TangentData.TangentSpace B.manifold p) :
    inner ℝ p.val (B.ambientVector p v) = 0 :=
  (B.tangent_range p _).mp ⟨v, rfl⟩

/-- Global solutions for every initial phase force each actual maximal domain
to be all real times. In particular this requires the zero-velocity solutions. -/
theorem geodesicallyComplete_of_global_solutions {n : ℕ} {M : Type}
    [TopologicalSpace M] (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M)
    (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
    (h : ∀ w : P202.GeodesicData.Phase S, ∃ q : ℝ → P202.GeodesicData.Phase S,
      q 0 = w ∧ P202.GeodesicData.IsGeodesicOn S C Set.univ q) :
    P202.HopfRinowData.GeodesicallyComplete S C := by
  intro w I q hq
  obtain ⟨r, hr0, hr⟩ := h w
  have hi := (hq.2.2.2 D13Unified.OpenTimeInterval.whole r (by trivial) hr0 hr).1
  exact Set.Subset.antisymm (Set.subset_univ _) hi


section EuclideanConstruction
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData P202.MetricData P202.ConnectionData
  P202.CurveConnectionData
open Set Filter
open scoped _root_.Topology

/-- The ordinary global chart, now on the actual inner-product space. -/
def euclideanChart (n : ℕ) : ModelChart n .euclidean (E n) :=
  (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).toOpenPartialHomeomorph.trans
    (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph

theorem euclideanAtlas_smooth (n : ℕ) : IsContDiffAtlas (⊤ : ℕ∞)
    (transportAtlas (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm
      (SmoothManifolds.StandardCoveringData.euclideanAtlas n)) :=
  SmoothManifolds.transportAtlas_isContDiffAtlas _ _ _
    (SmoothManifolds.StandardCoverings.euclideanAtlas_isContDiffAtlas n)

/-- The maximal atlas generated by the single standard chart. -/
def euclideanManifold (n : ℕ) : SmoothManifold n .euclidean (E n) where
  topologicalManifold := ⟨inferInstance, inferInstance, _, (euclideanAtlas_smooth n).1⟩
  smoothStructure := ⟨_, SmoothManifolds.maximalExtension_isMaximal (euclideanAtlas_smooth n)⟩

theorem euclideanChart_mem (n : ℕ) :
    euclideanChart n ∈ (euclideanManifold n).smoothStructure.val :=
  SmoothManifolds.subset_maximalExtension (euclideanAtlas_smooth n) ⟨_, rfl, rfl⟩

@[simp] theorem euclideanChart_source (n : ℕ) : (euclideanChart n).source = univ := by
  ext p
  simp [euclideanChart]

@[simp] theorem euclideanChart_value (n : ℕ) (p : E n) :
    ((euclideanChart n) p).val = WithLp.ofLp p := rfl

/-- Coordinates of the original derivation fiber, in the global chart. -/
def euclideanCoordinates (n : ℕ) (p : E n) :
    TangentSpace (euclideanManifold n) p ≃ₗ[ℝ] E n :=
  ((tangentStructure (euclideanManifold n)).fiberCoordinates.equiv
    (euclideanChart n) (euclideanChart_mem n) p (by simp)).trans
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

theorem euclidean_velocity (n : ℕ) (c : ℝ → E n) (t : ℝ)
    (v : TangentSpace (euclideanManifold n) (c t)) :
    HasVelocityWithinAt (euclideanManifold n) c univ t v ↔
      HasDerivAt c (euclideanCoordinates n (c t) v) t := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
  constructor
  · intro hv
    have hd := CurveCovariantDerivative.velocity_coordinates hv (mem_univ t)
      (euclideanChart n) (euclideanChart_mem n) (by simp)
    rw [hasDerivWithinAt_univ] at hd
    have h := L.symm.hasFDerivAt.comp_hasDerivAt t hd
    simpa [L, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def, euclideanChart_value, euclideanCoordinates] using h
  · intro hd
    refine ⟨hd.continuousAt.continuousWithinAt,
      euclideanChart n, euclideanChart_mem n, by simp, ?_⟩
    have h := L.hasFDerivAt.comp_hasDerivAt t hd
    simpa [L, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def, euclideanChart_value, euclideanCoordinates] using h.hasDerivWithinAt (s := Set.univ)

/-- The global tangent chart has the whole space as its base domain. -/
def euclideanTangentIndex (n : ℕ) : TangentIndex (euclideanManifold n) :=
  ⟨euclideanChart n, euclideanChart_mem n⟩

theorem euclideanTangentIndex_mem (n : ℕ) (p : E n) :
    p ∈ (tangentBundle (euclideanManifold n)).baseSet (euclideanTangentIndex n) := by
  rw [(tangentRealization (euclideanManifold n)).baseSet]
  simp [euclideanTangentIndex]

/-- The standard inner product, pulled back to the actual derivation fibers.
The smoothness of all Gram coefficients follows from the verified smooth
transition maps of the intrinsic tangent bundle. -/
def euclideanMetric (n : ℕ) : RiemannianMetric (euclideanManifold n) where
  form := SmoothManifolds.BundleMetrics.localForm
    (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n)
  symmetric := SmoothManifolds.BundleMetrics.localForm_symmetric _ _
  positive p v hv := SmoothManifolds.BundleMetrics.localForm_positive _ _ p
    (euclideanTangentIndex_mem n p) v hv
  smooth i j k p hp := SmoothManifolds.BundleMetrics.localForm_gram_smoothAt _
    i (euclideanTangentIndex n) j k p hp (euclideanTangentIndex_mem n p)

theorem euclideanMetric_standard (n : ℕ) (p : E n)
    (v w : TangentSpace (euclideanManifold n) p) :
    pairing (euclideanMetric n) p v w =
      inner ℝ (euclideanCoordinates n p v) (euclideanCoordinates n p w) := by
  simp only [pairing, euclideanMetric, SmoothManifolds.BundleMetrics.localForm_apply]
  simp_rw [SmoothManifolds.BundleMetrics.coordinateMap_of_mem _ _ p
    (euclideanTangentIndex_mem n p)]
  rw [(tangentRealization (euclideanManifold n)).coordinates (euclideanTangentIndex n) p (by change p ∈ (euclideanChart n).source; simp),
    (tangentRealization (euclideanManifold n)).coordinates (euclideanTangentIndex n) p (by change p ∈ (euclideanChart n).source; simp)]
  change (∑ k : Fin n,
      ((tangentStructure (euclideanManifold n)).fiberCoordinates.equiv
        (euclideanChart n) (euclideanChart_mem n) p (by simp) v) k *
      ((tangentStructure (euclideanManifold n)).fiberCoordinates.equiv
        (euclideanChart n) (euclideanChart_mem n) p (by simp) w) k) = _
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  rfl



/-- Existence of the standard Euclidean metric and its intrinsic LC connection.
No flatness or geodesic conclusion is assumed in this construction. -/
def euclideanConnection (n : ℕ) : Connection (tangentBundle (euclideanManifold n)) :=
  Classical.choose (LeviCivita.exists_unique (euclideanMetric n))

def euclideanModel (n : ℕ) : EuclideanModel n where
  manifold := euclideanManifold n
  standard := rfl
  coordinates := euclideanCoordinates n
  velocity := euclidean_velocity n
  metric := euclideanMetric n
  metric_standard := euclideanMetric_standard n
  connection := euclideanConnection n
  leviCivita := (Classical.choose_spec (LeviCivita.exists_unique (euclideanMetric n))).1

open P202.LeviCivitaData P202.GeodesicData

theorem scalarDerivative_const {n : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (r : ℝ) (p : M)
    (v : TangentSpace S p) : scalarDerivative S (fun _ => r) p v = 0 := by
  have hs := SmoothManifolds.scalarContDiff_const (⊤ : ℕ∞) S.smoothStructure.val r p
  have hg : scalarGerm S (fun _ => r) p = algebraMap ℝ (SmoothGerm S p) r := by
    apply Subtype.ext
    simp only [scalarGerm, dite_eq_left hs]
    rfl
  change v.val (scalarGerm S (fun _ => r) p) = 0
  rw [hg]
  exact SmoothManifolds.derivation_kills_constants _ v r

 theorem euclideanMetric_matrix (n : ℕ) (p : E n) (i j : Fin n) :
    metricMatrix (euclideanMetric n) (euclideanTangentIndex n) p i j =
      if i = j then 1 else 0 := by
  classical
  have hp := euclideanTangentIndex_mem n p
  change SmoothManifolds.BundleMetrics.localForm (tangentBundle (euclideanManifold n))
    (euclideanTangentIndex n) p (coordinateVector (euclideanTangentIndex n) i p)
      (coordinateVector (euclideanTangentIndex n) j p) = _
  simp only [SmoothManifolds.BundleMetrics.localForm_apply,
    SmoothManifolds.BundleMetrics.coordinateMap_of_mem _ _ p hp,
    coordinateVector]
  change (∑ k : Fin n,
      ((tangentBundle (euclideanManifold n)).fiberCoordinates (euclideanTangentIndex n) p hp
        (((tangentBundle (euclideanManifold n)).trivialization (euclideanTangentIndex n)).symm p (Pi.single i 1))) k *
      ((tangentBundle (euclideanManifold n)).fiberCoordinates (euclideanTangentIndex n) p hp
        (((tangentBundle (euclideanManifold n)).trivialization (euclideanTangentIndex n)).symm p (Pi.single j 1))) k) = _
  simp only [← SmoothVectorBundle.fiberCoordinates_symm_apply _ _ p hp,
    LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply, eq_comm]

theorem euclidean_christoffel_zero (n : ℕ)
    (p : (tangentBundle (euclideanManifold n)).baseSet (euclideanTangentIndex n))
    (k i j : Fin n) :
    christoffel (euclideanConnection n) (euclideanTangentIndex n) p k i j = 0 := by
  rw [LeviCivita.christoffel_formula (euclideanMetric n) (euclideanConnection n)
    (euclideanModel n).leviCivita]
  simp_rw [euclideanMetric_matrix, scalarDerivative_const]
  simp

theorem euclidean_coordinateAcceleration_zero (n : ℕ)
    (p : (tangentBundle (euclideanManifold n)).baseSet (euclideanTangentIndex n))
    (v : Euclidean n) :
    coordinateAcceleration (euclideanManifold n) (euclideanConnection n)
      (euclideanTangentIndex n) p v = 0 := by
  ext k
  simp [coordinateAcceleration, euclidean_christoffel_zero]


open P202.CurvatureData P202.TorsionMetricData

def globalFrameOfUniv {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (h : U = univ) :
    LocalFrame (tangentBundle S) univ isOpen_univ := by
  subst U
  exact b

theorem globalFrameOfUniv_connectionForm {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {U : Set M} {hU : IsOpen U}
    (C : Connection (tangentBundle S)) (b : LocalFrame (tangentBundle S) U hU)
    (h : U = univ) (p : M) (hp : p ∈ U) (i j : Fin n) (v : TangentSpace S p) :
    connectionForm C (globalFrameOfUniv b h) ⟨p, mem_univ p⟩ i j v =
      connectionForm C b ⟨p, hp⟩ i j v := by
  subst U
  rfl

theorem global_connectionForm_eq_frameMatrix {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    (b : LocalFrame (tangentBundle S) univ isOpen_univ)
    (X : Field S) (p : M) (i j : Fin n) :
    connectionForm C b ⟨p, mem_univ p⟩ i j (X.val p) = frameMatrix C b X p i j := by
  have he : SmoothManifolds.SectionExtension.totalSection (b.section_ j) =
      (frameMember b j).val := by
    funext q
    simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q (mem_univ q)]
    rfl
  change (b.basis ⟨p, mem_univ p⟩).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p (X.val p)) i = _
  rw [he, ConnectionForms.pointDerivative_global]
  rfl

theorem euclidean_connectionForm_zero (n : ℕ)
    (p : (tangentBundle (euclideanManifold n)).baseSet (euclideanTangentIndex n))
    (k j : Fin n) (v : TangentSpace (euclideanManifold n) p.val) :
    connectionForm (euclideanConnection n)
      (SmoothManifolds.ConstantRankBundles.trivializationFrame
        (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n)) p k j v = 0 := by
  conv_lhs => rw [← LeviCivita.coordinate_expansion (euclideanTangentIndex n) p.val p.property v]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  change _ * christoffel (euclideanConnection n) (euclideanTangentIndex n) p k i j = 0
  rw [euclidean_christoffel_zero, mul_zero]

def euclideanGlobalFrame (n : ℕ) :
    LocalFrame (tangentBundle (euclideanManifold n)) univ isOpen_univ :=
  globalFrameOfUniv
    (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n))
    (Set.eq_univ_iff_forall.mpr (euclideanTangentIndex_mem n))

theorem euclidean_covariant_coefficient (n : ℕ)
    (X Y : Field (euclideanManifold n)) (i : Fin n) :
    frameCoefficient (euclideanGlobalFrame n) ((euclideanConnection n).cov X Y) i =
      act (euclideanManifold n) X (frameCoefficient (euclideanGlobalFrame n) Y i) := by
  apply Subtype.ext
  funext p
  rw [ConnectionForms.global_frame_formula (tangentBundle (euclideanManifold n))
    (euclideanConnection n) (euclideanGlobalFrame n) X Y p i]
  suffices ∀ j : Fin n,
      frameMatrix (euclideanConnection n) (euclideanGlobalFrame n) X p i j = 0 by
    simp [this]
  intro j
  rw [← global_connectionForm_eq_frameMatrix]
  unfold euclideanGlobalFrame
  rw [globalFrameOfUniv_connectionForm _ _ _ p (euclideanTangentIndex_mem n p)]
  exact euclidean_connectionForm_zero n ⟨p, euclideanTangentIndex_mem n p⟩ i j (X.val p)


theorem curvature_zero_of_parallel_frame {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    (b : LocalFrame (tangentBundle S) univ isOpen_univ)
    (h : ∀ (X Y : Field S) (i : Fin n),
      frameCoefficient b (C.cov X Y) i = act S X (frameCoefficient b Y i))
    (X Y Z : Field S) : curvature C X Y Z = 0 := by
  apply ConnectionForms.section_ext
  intro p
  apply (b.basis ⟨p, mem_univ p⟩).equivFun.injective
  ext i
  have hb := TorsionAndMetric.bracket_act X Y (frameCoefficient b Z i) p
  rw [ConnectionForms.scalarDerivative_global] at hb
  have hc (U V : Field S) :
      (b.basis ⟨p, mem_univ p⟩).equivFun ((C.cov U V).val p) i =
      (act S U (frameCoefficient b V i)).val p :=
    congrArg (fun f : GlobalSmooth S => f.val p) (h U V i)
  simp only [curvature, ConnectionForms.section_add_apply, ConnectionForms.section_smul_apply,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_zero, Pi.zero_apply,
    ConnectionForms.section_zero_apply]
  rw [hc, hc, hc, h Y Z i, h X Z i, hb]
  ring

theorem euclidean_curvature_zero (n : ℕ) (X Y Z : Field (euclideanManifold n)) :
    curvature (euclideanConnection n) X Y Z = 0 :=
  curvature_zero_of_parallel_frame (euclideanConnection n) (euclideanGlobalFrame n)
    (euclidean_covariant_coefficient n) X Y Z

theorem euclidean_chartVelocity (n : ℕ) (q : ℝ → Phase (euclideanManifold n)) (t : ℝ) :
    chartVelocity (euclideanManifold n) (euclideanTangentIndex n) q t =
      WithLp.ofLp (euclideanCoordinates n (q t).1 (q t).2) := by
  rw [chartVelocity, CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _
      (euclideanTangentIndex_mem n (q t).1), GeodesicIVP.trivializationFrame_equivFun]
  change (((tangentBundle (euclideanManifold n)).trivialization
    (euclideanTangentIndex n)) ⟨(q t).1, (q t).2⟩).2 = _
  rw [(tangentRealization (euclideanManifold n)).coordinates _ _ (by simp [euclideanTangentIndex])]
  rfl

/-- A phase specified by its point and standard ambient tangent coordinates. -/
def euclideanPhase (n : ℕ) (p w : E n) : Phase (euclideanManifold n) :=
  ⟨p, (euclideanCoordinates n p).symm w⟩

/-- The lifted line in the actual tangent fibers, for every speed. -/
def euclideanLinePhase (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) (t : ℝ) :
    Phase (euclideanManifold n) :=
  euclideanPhase n (line p (euclideanCoordinates n p v) t) (euclideanCoordinates n p v)

theorem euclideanLinePhase_initial (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) : euclideanLinePhase n p v 0 = ⟨p, v⟩ := by
  rw [euclideanLinePhase, (line_formula n p (euclideanCoordinates n p v)).1]
  simp [euclideanPhase]

theorem euclideanLinePhase_chartVelocity (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) :
    chartVelocity (euclideanManifold n) (euclideanTangentIndex n) (euclideanLinePhase n p v) =
      fun _ => WithLp.ofLp (euclideanCoordinates n p v) := by
  funext t
  rw [euclidean_chartVelocity]
  exact congrArg WithLp.ofLp ((euclideanCoordinates n _).apply_symm_apply _)

theorem euclideanLinePhase_geodesic (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) :
    IsGeodesicOn (euclideanManifold n) (euclideanConnection n) univ
      (euclideanLinePhase n p v) := by
  intro t ht
  have hd := (line_formula n p (euclideanCoordinates n p v)).2.1 t
  apply GeodesicIVP.coordinate_equation_implies_geodesic_at
    (euclideanConnection n) (euclideanLinePhase n p v) t (euclideanTangentIndex n)
    (euclideanTangentIndex_mem _ _)
  · exact hd.continuousAt
  · rw [euclideanLinePhase_chartVelocity]
    change HasDerivAt (fun s => WithLp.ofLp (line p (euclideanCoordinates n p v) s))
      (WithLp.ofLp (euclideanCoordinates n p v)) t
    have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt.comp_hasDerivAt t hd
    simpa [PiLp.coe_continuousLinearEquiv, Function.comp_def] using h
  · rw [euclidean_coordinateAcceleration_zero, euclideanLinePhase_chartVelocity]
    exact hasDerivAt_const t (WithLp.ofLp (euclideanCoordinates n p v))

theorem euclideanLinePhase_maximal (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) :
    IsMaximalThrough (euclideanManifold n) (euclideanConnection n) ⟨p, v⟩
      D13Unified.OpenTimeInterval.whole (euclideanLinePhase n p v) := by
  refine ⟨by trivial, euclideanLinePhase_initial n p v,
    euclideanLinePhase_geodesic n p v, ?_⟩
  intro J r hJ hr0 hr
  refine ⟨subset_univ _, ?_⟩
  have hu := GeodesicIVP.overlap_unique (euclideanManifold n) (euclideanConnection n)
    D13Unified.OpenTimeInterval.whole J (euclideanLinePhase n p v) r
    (euclideanLinePhase_geodesic n p v) hr 0 ⟨by trivial, hJ⟩
    ((euclideanLinePhase_initial n p v).trans hr0.symm)
  intro t ht
  exact hu ⟨by trivial, ht⟩

theorem euclidean_geodesicallyComplete (n : ℕ) :
    P202.HopfRinowData.GeodesicallyComplete (euclideanManifold n)
      (euclideanConnection n) := by
  apply geodesicallyComplete_of_global_solutions
  intro w
  exact ⟨euclideanLinePhase n w.1 w.2, euclideanLinePhase_initial n w.1 w.2,
    euclideanLinePhase_geodesic n w.1 w.2⟩

theorem euclidean_lengthMetricComplete (n : ℕ) :
    P202.CompletenessData.LengthMetricComplete (euclideanMetric n) :=
  HopfRinow.complete_of_geodesicallyComplete (euclideanMetric n) (euclideanConnection n)
    (euclideanModel n).leviCivita (euclidean_geodesicallyComplete n)

/-- The actual curvature tensor of the constant Euclidean metric. -/
def euclideanCurvatureTensor (n : ℕ) : CurvatureTensor (euclideanManifold n) where
  val _ := 0
  smooth X Y Z := by
    exact (0 : Field (euclideanManifold n)).property

theorem euclideanCurvatureTensor_represents (n : ℕ) :
    RepresentsCurvature (euclideanConnection n) (euclideanCurvatureTensor n) := by
  intro X Y Z p
  rw [euclidean_curvature_zero]
  rfl

theorem euclidean_sectionalCurvature_zero (n : ℕ) (p : E n)
    (X Y : TangentSpace (euclideanManifold n) p) (h : LinearIndependent ℝ ![X, Y]) :
    sectionalCurvature (euclideanMetric n) (euclideanCurvatureTensor n) p X Y h = 0 := by
  simp [sectionalCurvature, curvatureForm, euclideanCurvatureTensor, pairing]

theorem euclidean_conclusion (n : ℕ) : (euclideanModel n).Conclusion := by
  refine ⟨inferInstance, inferInstance, euclidean_lengthMetricComplete n,
    ⟨euclideanCurvatureTensor n, euclideanCurvatureTensor_represents n,
      euclidean_sectionalCurvature_zero n⟩, ?_⟩
  intro p v
  refine ⟨euclideanLinePhase n p v, euclideanLinePhase_maximal n p v, fun t => ?_⟩
  refine ⟨rfl, ?_, ?_⟩
  · exact (euclideanCoordinates n _).apply_symm_apply _
  · change tangentNorm (euclideanMetric n) (line p (euclideanCoordinates n p v) t)
      ((euclideanCoordinates n _).symm (euclideanCoordinates n p v)) = ‖euclideanCoordinates n p v‖
    unfold tangentNorm
    rw [euclideanMetric_standard]
    simp only [LinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
theorem euclidean_frameCoordinates (n : ℕ)
    (p : (tangentBundle (euclideanManifold n)).baseSet (euclideanTangentIndex n))
    (v : TangentSpace (euclideanManifold n) p.val) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n)).basis p).equivFun v =
      WithLp.ofLp (euclideanCoordinates n p.val v) := by
  rw [LeviCivita.trivializationFrame_coordinates]
  change (((tangentBundle (euclideanManifold n)).trivialization
    (euclideanTangentIndex n)) ⟨p.val, v⟩).2 = _
  rw [(tangentRealization (euclideanManifold n)).coordinates _ _ (by
    change p.val ∈ (euclideanChart n).source; simp)]
  rfl

theorem euclidean_coefficientsAlong (n : ℕ) (c : ℝ → E n)
    (V : (s : ℝ) → TangentSpace (euclideanManifold n) (c s)) :
    coefficientsAlong (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n)) c V =
      fun t => WithLp.ofLp (euclideanCoordinates n (c t) (V t)) := by
  funext t
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ (euclideanTangentIndex_mem n (c t))]
  exact euclidean_frameCoordinates n ⟨c t, euclideanTangentIndex_mem n (c t)⟩ (V t)

theorem euclidean_connectionMatrix_zero (n : ℕ)
    (p : (tangentBundle (euclideanManifold n)).baseSet (euclideanTangentIndex n))
    (v : TangentSpace (euclideanManifold n) p.val) :
    connectionMatrix (euclideanConnection n)
      (SmoothManifolds.ConstantRankBundles.trivializationFrame
        (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n)) p v = 0 := by
  ext i j
  exact euclidean_connectionForm_zero n p i j v

/-- Intrinsic covariant differentiation of arbitrary differentiable fields
along a Euclidean curve equals ordinary differentiation of their ambient
coordinates. No extension of the field or extra C² hypothesis is used. -/
theorem euclidean_covariantDerivative_iff (n : ℕ) (c : ℝ → E n)
    (V : (s : ℝ) → TangentSpace (euclideanManifold n) (c s)) (t : ℝ)
    (W D : TangentSpace (euclideanManifold n) (c t))
    (hW : HasVelocityWithinAt (euclideanManifold n) c univ t W) :
    HasCovariantDerivativeAt (euclideanConnection n) c V t D ↔
      HasDerivAt (fun s => euclideanCoordinates n (c s) (V s))
        (euclideanCoordinates n (c t) D) t := by
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame
    (tangentBundle (euclideanManifold n)) (euclideanTangentIndex n)
  have hp := euclideanTangentIndex_mem n (c t)
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  constructor
  · intro hD
    obtain ⟨v', hv'⟩ := CurveCovariantDerivative.exists_coefficients_deriv
      (euclideanConnection n) (mem_univ t) hD b hp
    have he := CurveCovariantDerivative.local_formula (euclideanConnection n)
      (mem_univ t) uniqueDiffWithinAt_univ hD b hp hW hv'
    have hcoords := congrArg (b.basis ⟨c t, hp⟩).equivFun he
    have hvD : v' = WithLp.ofLp (euclideanCoordinates n (c t) D) := by
      rw [← euclidean_frameCoordinates n ⟨c t, hp⟩ D]
      simpa only [b, frameDerivative, euclidean_connectionMatrix_zero, Matrix.zero_mulVec,
        add_zero, LinearEquiv.apply_symm_apply] using hcoords.symm
    rw [hasDerivWithinAt_univ, hvD] at hv'
    have h := L.symm.hasFDerivAt.comp_hasDerivAt t hv'
    simpa [b, euclidean_coefficientsAlong, L, PiLp.coe_symm_continuousLinearEquiv,
      Function.comp_def] using h
  · intro hd
    have h := L.hasFDerivAt.comp_hasDerivAt t hd
    have hcoeff : HasDerivAt (coefficientsAlong b c V)
        (WithLp.ofLp (euclideanCoordinates n (c t) D)) t := by
      simpa [b, euclidean_coefficientsAlong, L, PiLp.coe_continuousLinearEquiv,
        Function.comp_def] using h
    refine ⟨W, hW, _, _, b, hp,
      WithLp.ofLp (euclideanCoordinates n (c t) D), hcoeff.hasDerivWithinAt, ?_⟩
    apply (b.basis ⟨c t, hp⟩).equivFun.injective
    simp only [b, frameDerivative, euclidean_connectionMatrix_zero, Matrix.zero_mulVec,
      add_zero, LinearEquiv.apply_symm_apply]
    exact euclidean_frameCoordinates n ⟨c t, hp⟩ D

theorem globalFrameOfUniv_equivFun {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (h : U = univ)
    (p : M) (hp : p ∈ U) (v : TangentSpace S p) :
    ((globalFrameOfUniv b h).basis ⟨p, mem_univ p⟩).equivFun v =
      (b.basis ⟨p, hp⟩).equivFun v := by
  subst U
  rfl

theorem euclideanGlobalFrame_coordinates (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) :
    ((euclideanGlobalFrame n).basis ⟨p, mem_univ p⟩).equivFun v =
      WithLp.ofLp (euclideanCoordinates n p v) := by
  unfold euclideanGlobalFrame
  rw [globalFrameOfUniv_equivFun _ _ p (euclideanTangentIndex_mem n p)]
  exact euclidean_frameCoordinates n ⟨p, euclideanTangentIndex_mem n p⟩ v

open SmoothManifolds.DifferentialData

theorem scalarDerivative_chart {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (v : TangentSpace S p) (i : Fin n) :
    scalarDerivative S (fun q => (e q).val i) p v =
      ((tangentStructure S).fiberCoordinates.equiv e he p hp v) i := by
  have hs := SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
    (show ∃ U : Set (Euclidean n), IsOpen U ∧ (e p).val ∈ U ∧
      ∃ F : Euclidean n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        (fun y => F (e y).val) =ᶠ[𝓝 p] (fun q => (e q).val i) from
      ⟨univ, isOpen_univ, mem_univ _, fun y => y i,
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn, Eventually.of_forall (fun _ => rfl)⟩)
  obtain ⟨coords, hcoords, heval⟩ :=
    (tangentStructure S).fiberCoordinates.isCoordinates e he p hp
  have hg : scalarGerm S (fun q => (e q).val i) p = coords i := by
    apply Subtype.ext
    simp only [scalarGerm, dite_eq_left hs]
    exact (hcoords i).symm
  change v.val (scalarGerm S (fun q => (e q).val i) p) = _
  rw [hg]
  exact (heval v i).symm

-- Inside EuclideanConstruction. Requires scalarDerivative_chart and euclideanGlobalFrame_coordinates.
def euclideanScalarCoordinate (n : ℕ) (i : Fin n) : GlobalSmooth (euclideanManifold n) := by
  refine ⟨fun p => (euclideanChart n p).val i,
    (SmoothManifolds.mem_globalSmoothAlgebra_iff _ _).mpr ?_⟩
  intro p
  apply SmoothManifolds.scalarContDiffAt_of_chart (euclideanManifold n).smoothStructure.property.1
    (euclideanChart_mem n) (by simp : p ∈ (euclideanChart n).source)
  exact ⟨univ, isOpen_univ, mem_univ _, fun y => y i,
    (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn, Eventually.of_forall (fun _ => rfl)⟩

@[simp] theorem euclideanScalarCoordinate_value (n : ℕ) (i : Fin n) (p : E n) :
    (euclideanScalarCoordinate n i).val p = (WithLp.ofLp p) i := rfl

/-- The smooth position vector field on ordinary Euclidean space. -/
def euclideanEuler (n : ℕ) : Field (euclideanManifold n) :=
  ∑ i, mulSection (euclideanScalarCoordinate n i) (frameMember (euclideanGlobalFrame n) i)

theorem euclideanEuler_frameCoefficient (n : ℕ) (i : Fin n) :
    frameCoefficient (euclideanGlobalFrame n) (euclideanEuler n) i =
      euclideanScalarCoordinate n i := by
  apply Subtype.ext
  funext p
  change ((euclideanGlobalFrame n).basis ⟨p, mem_univ p⟩).equivFun ((euclideanEuler n).val p) i = _
  simp only [euclideanEuler, Submodule.coe_sum, Finset.sum_apply, ConnectionForms.mulSection_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ConnectionForms.frameMember_apply, ← (euclideanGlobalFrame n).basis_eq,
    Module.Basis.equivFun_self]
  simp

theorem euclideanEuler_coordinates (n : ℕ) (p : E n) :
    euclideanCoordinates n p ((euclideanEuler n).val p) = p := by
  apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective
  change WithLp.ofLp (euclideanCoordinates n p ((euclideanEuler n).val p)) = WithLp.ofLp p
  rw [← euclideanGlobalFrame_coordinates]
  ext i
  exact congrArg (fun f : GlobalSmooth (euclideanManifold n) => f.val p)
    (euclideanEuler_frameCoefficient n i)

theorem euclideanEuler_covariant (n : ℕ) (X : Field (euclideanManifold n)) (p : E n) :
    euclideanCoordinates n p (((euclideanConnection n).cov X (euclideanEuler n)).val p) =
      euclideanCoordinates n p (X.val p) := by
  apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective
  change WithLp.ofLp (euclideanCoordinates n p _) = WithLp.ofLp (euclideanCoordinates n p _)
  rw [← euclideanGlobalFrame_coordinates]
  ext i
  change (frameCoefficient (euclideanGlobalFrame n)
    ((euclideanConnection n).cov X (euclideanEuler n)) i).val p = _
  rw [euclidean_covariant_coefficient, euclideanEuler_frameCoefficient,
    ← ConnectionForms.scalarDerivative_global]
  exact scalarDerivative_chart (euclideanManifold n) (euclideanChart n) (euclideanChart_mem n)
    p (by simp) (X.val p) i

theorem euclideanEuler_pointDerivative (n : ℕ) (p : E n)
    (v : TangentSpace (euclideanManifold n) p) :
    euclideanCoordinates n p
      (pointDerivative (euclideanConnection n) (euclideanEuler n).val p v) =
      euclideanCoordinates n p v := by
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective
    (tangentBundle (euclideanManifold n)) p v
  rw [← hX, ConnectionForms.pointDerivative_global]
  exact euclideanEuler_covariant n X p

/-- The position section and its differentiated pullback identity, for every
smooth map into Euclidean space and every actual pullback connection. -/
theorem euclidean_position_pullback_exists {m n : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold m .euclidean M) (F : M → E n)
    (hF : IsSmoothMap S (euclideanManifold n) F)
    (P : PullbackBundle (tangentBundle (euclideanManifold n)) S F) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle),
      P202.PullbackData.IsPullback (tangentBundle (euclideanManifold n)) (euclideanConnection n)
        F hF P D →
      ∃ R : Section P.space.bundle,
        (∀ p, euclideanCoordinates n (F p) (R.val p) = F p) ∧
        ∀ (X : Field S) (p : M),
          euclideanCoordinates n (F p) ((D.cov X R).val p) =
            euclideanCoordinates n (F p)
              (SmoothManifolds.differential S (euclideanManifold n) F hF p (X.val p)) := by
  letI := P.space.topology
  intro D hD
  let R := PullbackConnections.pullSection (tangentBundle (euclideanManifold n))
    F hF P (euclideanEuler n)
  refine ⟨R, fun p => euclideanEuler_coordinates n (F p), ?_⟩
  intro X p
  rw [hD X (euclideanEuler n) R (fun _ => rfl) p]
  exact euclideanEuler_pointDerivative n (F p) _


/-- The preceding construction in exactly the spherical-model interface. -/
theorem spherical_position_pullback_exists {n : ℕ} {a : ℝ}
    (B : SphericalModel n a (euclideanModel (n + 1)))
    (P : PullbackBundle (tangentBundle (euclideanModel (n + 1)).manifold) B.manifold Subtype.val) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle),
      P202.PullbackData.IsPullback (tangentBundle (euclideanModel (n + 1)).manifold)
        (euclideanModel (n + 1)).connection Subtype.val B.inclusion.smooth P D →
      ∃ R : Section P.space.bundle,
        (∀ p, (euclideanModel (n + 1)).coordinates p.val (R.val p) = p.val) ∧
        ∀ (X : Field B.manifold) p,
          (euclideanModel (n + 1)).coordinates p.val ((D.cov X R).val p) =
            B.ambientVector p (X.val p) := by
  letI := P.space.topology
  intro D hD
  obtain ⟨R, hR, hDR⟩ :=
    euclidean_position_pullback_exists B.manifold Subtype.val B.inclusion.smooth P D hD
  refine ⟨R, hR, ?_⟩
  intro X p
  have hi : B.inclusion.differential p = SmoothManifolds.differential B.manifold
      (euclideanManifold (n + 1)) Subtype.val B.inclusion.smooth p :=
    (SmoothManifolds.differential_exists _ _ _ B.inclusion.smooth p).unique
      (B.inclusion.isDifferential p) (SmoothManifolds.differential_spec _ _ _ B.inclusion.smooth p)
  change euclideanCoordinates (n + 1) p.val ((D.cov X R).val p) =
    euclideanCoordinates (n + 1) p.val (B.inclusion.differential p (X.val p))
  rw [hi]
  exact hDR X p

end EuclideanConstruction


section SphereConstruction
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.SphereTorusData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData P202.MetricData
open Set Filter
open scoped _root_.Topology

def unitSquareHomeomorph (n : ℕ) : P202.SpaceFormData.Sphere n 1 ≃ₜ SmoothManifolds.SphereTorusData.Sphere n where
  toFun p := ⟨WithLp.ofLp p.val, by
    have h := EuclideanSpace.real_norm_sq_eq p.val
    rw [mem_sphere_zero_iff_norm.mp p.property] at h
    simpa [squareSum] using h.symm⟩
  invFun p := ⟨WithLp.toLp 2 p.val, by
    rw [mem_sphere_zero_iff_norm]
    have h := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 p.val)
    change ‖WithLp.toLp 2 p.val‖ ^ 2 = squareSum p.val at h
    rw [p.property] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 p.val)]⟩
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.homeomorph 2 (fun _ : Fin (n+1) => ℝ)).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (PiLp.homeomorph 2 (fun _ : Fin (n+1) => ℝ)).symm.continuous.comp continuous_subtype_val

def sphereSquareHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) :
    P202.SpaceFormData.Sphere n a ≃ₜ SmoothManifolds.SphereTorusData.Sphere n :=
  (radiusHomeomorph n a ha).trans (unitSquareHomeomorph n)

def sphereAtlas (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Set (ModelChart n .euclidean (P202.SpaceFormData.Sphere n a)) :=
  transportAtlas (sphereSquareHomeomorph n a ha).symm (hemisphereAtlas n)

theorem sphereAtlas_smooth (n : ℕ) (a : ℝ) (ha : 0 < a) :
    IsContDiffAtlas (⊤ : ℕ∞) (sphereAtlas n a ha) :=
  SmoothManifolds.transportAtlas_isContDiffAtlas _ _ _ (SmoothManifolds.SphereTorus.hemisphereAtlas_isContDiffAtlas n)

def sphereManifold (n : ℕ) (a : ℝ) (ha : 0 < a) :
    SmoothManifold n .euclidean (P202.SpaceFormData.Sphere n a) where
  topologicalManifold := ⟨inferInstance, inferInstance, _, (sphereAtlas_smooth n a ha).1⟩
  smoothStructure := ⟨_, SmoothManifolds.maximalExtension_isMaximal (sphereAtlas_smooth n a ha)⟩

open SmoothManifolds.TangentData SmoothManifolds.DifferentialData

def omitCLM {n : ℕ} (i : Fin (n+1)) : Euclidean (n+1) →L[ℝ] Euclidean n :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (i.succAbove j))

def hemisphereParam {n : ℕ} (i : Fin (n+1)) (s : Bool) : Euclidean n → E (n+1) :=
  fun y => WithLp.toLp 2 (insertRoot i s y)

theorem hemisphereParam_smooth {n : ℕ} (i : Fin (n+1)) (s : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (hemisphereParam i s) {y | squareSum y < 1} := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)).symm.contDiff.comp_contDiffOn
    (SmoothManifolds.SphereTorus.contDiffOn_insertRoot i s)

theorem hemisphereParam_differentiable {n : ℕ} (i : Fin (n+1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) :
    DifferentiableAt ℝ (hemisphereParam i s) y :=
  ((hemisphereParam_smooth i s).contDiffAt
    ((isOpen_lt (SmoothManifolds.SphereTorus.continuous_squareSum n) continuous_const).mem_nhds hy)).differentiableAt (by simp)

theorem hemisphereParam_norm_sq {n : ℕ} (i : Fin (n+1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) :
    ‖hemisphereParam i s y‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact SmoothManifolds.SphereTorus.squareSum_insertRoot i s y hy

theorem hemisphereParam_fderiv_injective {n : ℕ} (i : Fin (n+1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) :
    Function.Injective (fderiv ℝ (hemisphereParam i s) y) := by
  let C := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)
  let L := (omitCLM i).comp C.toContinuousLinearMap
  have hleft : L ∘ hemisphereParam i s = id := by
    funext z
    exact SmoothManifolds.SphereTorus.omit_insertRoot i s z
  have hd := L.hasFDerivAt.comp y (hemisphereParam_differentiable i s y hy).hasFDerivAt
  rw [hleft] at hd
  have heq := hd.unique (hasFDerivAt_id y)
  intro v w h
  have hh := congrArg L h
  have hv := congrArg (fun K : Euclidean n →L[ℝ] Euclidean n => K v) heq
  have hw := congrArg (fun K : Euclidean n →L[ℝ] Euclidean n => K w) heq
  exact hv.symm.trans (hh.trans hw)

theorem hemisphereParam_fderiv_orthogonal {n : ℕ} (i : Fin (n+1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) (v : Euclidean n) :
    inner ℝ (hemisphereParam i s y) (fderiv ℝ (hemisphereParam i s) y v) = 0 := by
  have hd := (hasStrictFDerivAt_norm_sq (hemisphereParam i s y)).hasFDerivAt.comp y
    (hemisphereParam_differentiable i s y hy).hasFDerivAt
  have heq : (fun z => ‖hemisphereParam i s z‖ ^ 2) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_lt (SmoothManifolds.SphereTorus.continuous_squareSum n) continuous_const).mem_nhds hy] with z hz
    exact hemisphereParam_norm_sq i s z hz
  have hc := hd.congr_of_eventuallyEq heq.symm
  have hz := congrArg (fun K : Euclidean n →L[ℝ] ℝ => K v)
    (hc.unique (hasFDerivAt_const (1 : ℝ) y))
  have hz' : 2 * inner ℝ (hemisphereParam i s y)
      (fderiv ℝ (hemisphereParam i s) y v) = 0 := by
    simpa using hz
  linarith


theorem hemisphereParam_fderiv_range {n : ℕ} (i : Fin (n+1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) (w : E (n+1)) :
    (∃ v, fderiv ℝ (hemisphereParam i s) y v = w) ↔
      inner ℝ (hemisphereParam i s y) w = 0 := by
  let D := (fderiv ℝ (hemisphereParam i s) y).toLinearMap
  let f : Module.Dual ℝ (E (n+1)) := (innerSL ℝ (hemisphereParam i s y)).toLinearMap
  have hle : LinearMap.range D ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    exact hemisphereParam_fderiv_orthogonal i s y hy v
  have hfn : f ≠ 0 := by
    intro hf
    have h := congrArg (fun g : Module.Dual ℝ (E (n+1)) => g (hemisphereParam i s y)) hf
    change inner ℝ (hemisphereParam i s y) (hemisphereParam i s y) = 0 at h
    rw [real_inner_self_eq_norm_sq, hemisphereParam_norm_sq i s y hy] at h
    norm_num at h
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hfn
  have hdim : Module.finrank ℝ (LinearMap.range D) = n := by
    rw [LinearMap.finrank_range_of_inj (hemisphereParam_fderiv_injective i s y hy)]
    simp
  have heq : LinearMap.range D = LinearMap.ker f := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [hdim]
    have hk' : Module.finrank ℝ (LinearMap.ker f) + 1 = n + 1 := by simpa using hk
    omega
  change w ∈ LinearMap.range D ↔ w ∈ LinearMap.ker f
  rw [heq]


def sphereChart {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (n+1)) (s : Bool) :
    ModelChart n .euclidean (P202.SpaceFormData.Sphere n a) :=
  (sphereSquareHomeomorph n a ha).toOpenPartialHomeomorph.trans
    (SmoothManifolds.SphereTorus.hemisphereChart i s)

theorem sphereChart_mem {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (n+1)) (s : Bool) :
    sphereChart ha i s ∈ (sphereManifold n a ha).smoothStructure.val :=
  SmoothManifolds.subset_maximalExtension (sphereAtlas_smooth n a ha)
    ⟨_, ⟨i, s, SmoothManifolds.SphereTorus.hemisphereChart_spec i s⟩, rfl⟩

theorem sphereChart_source {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (n+1)) (s : Bool)
    (p : P202.SpaceFormData.Sphere n a) :
    p ∈ (sphereChart ha i s).source ↔ sphereSquareHomeomorph n a ha p ∈ hemisphere i s := by
  exact SmoothManifolds.mem_transportedChart_source (sphereSquareHomeomorph n a ha).symm _ p

theorem sphereChart_param {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (n+1)) (s : Bool)
    (p : P202.SpaceFormData.Sphere n a) (hp : p ∈ (sphereChart ha i s).source) :
    a • insertRoot i s ((sphereChart ha i s p).val) = WithLp.ofLp p.val := by
  change a • insertRoot i s (omitCoordinate i (sphereSquareHomeomorph n a ha p).val) = _
  rw [SmoothManifolds.SphereTorus.insertRoot_omit i s _ ((sphereChart_source ha i s p).mp hp)]
  change a • (a⁻¹ • WithLp.ofLp p.val) = _
  simp [smul_smul, ha.ne']

theorem sphere_inclusion_smooth (n : ℕ) (a : ℝ) (ha : 0 < a) :
    IsSmoothMap (sphereManifold n a ha) (euclideanManifold (n+1)) Subtype.val := by
  apply (SmoothManifolds.manifoldContDiff_maximalExtension_iff _ _ _
    (sphereAtlas_smooth n a ha) (euclideanAtlas_smooth (n+1)) Subtype.val).mpr
  intro p
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart _ _ _
    (sphereAtlas_smooth n a ha) (euclideanAtlas_smooth (n+1)) Subtype.val p).mpr
  obtain ⟨i, s, hp⟩ := SmoothManifolds.SphereTorus.hemisphere_cover n (sphereSquareHomeomorph n a ha p)
  have hpc : p ∈ (sphereChart ha i s).source := (sphereChart_source ha i s p).mpr hp
  refine ⟨continuous_subtype_val.continuousAt, sphereChart ha i s,
    ⟨_, ⟨i, s, SmoothManifolds.SphereTorus.hemisphereChart_spec i s⟩, rfl⟩,
    euclideanChart (n+1), ⟨_, rfl, rfl⟩, hpc, ?_, ?_⟩
  · change p.val ∈ Set.univ ∧ _
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  · refine ⟨{y | squareSum y < 1},
      isOpen_lt (SmoothManifolds.SphereTorus.continuous_squareSum n) continuous_const,
      ?_, fun y => a • insertRoot i s y, ?_, ?_⟩
    · exact SmoothManifolds.SphereTorus.hemisphere_omit_mem i s _ hp
    · exact (contDiffOn_const (c := a)).smul (SmoothManifolds.SphereTorus.contDiffOn_insertRoot i s)
    · filter_upwards [(sphereChart ha i s).open_source.mem_nhds hpc] with q hq
      exact sphereChart_param ha i s q hq


def sphereParam {n : ℕ} (a : ℝ) (i : Fin (n+1)) (s : Bool) : Euclidean n → E (n+1) :=
  fun y => a • hemisphereParam i s y

theorem sphereParam_fderiv {n : ℕ} (a : ℝ) (i : Fin (n+1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) :
    fderiv ℝ (sphereParam a i s) y = a • fderiv ℝ (hemisphereParam i s) y :=
  ((hemisphereParam_differentiable i s y hy).hasFDerivAt.const_smul a).fderiv

theorem sphereParam_fderiv_injective {n : ℕ} {a : ℝ} (ha : 0 < a)
    (i : Fin (n+1)) (s : Bool) (y : Euclidean n) (hy : squareSum y < 1) :
    Function.Injective (fderiv ℝ (sphereParam a i s) y) := by
  rw [sphereParam_fderiv a i s y hy]
  intro v w h
  apply hemisphereParam_fderiv_injective i s y hy
  have h' := congrArg (fun z : E (n+1) => a⁻¹ • z) h
  simpa [smul_smul, ha.ne'] using h'

theorem sphereParam_fderiv_range {n : ℕ} {a : ℝ} (ha : 0 < a)
    (i : Fin (n+1)) (s : Bool) (y : Euclidean n) (hy : squareSum y < 1) (w : E (n+1)) :
    (∃ v, fderiv ℝ (sphereParam a i s) y v = w) ↔
      inner ℝ (sphereParam a i s y) w = 0 := by
  rw [sphereParam_fderiv a i s y hy]
  constructor
  · rintro ⟨v, rfl⟩
    simp [sphereParam, real_inner_smul_left, real_inner_smul_right,
      hemisphereParam_fderiv_orthogonal i s y hy v]
  · intro hw
    have hz : inner ℝ (hemisphereParam i s y) (a⁻¹ • w) = 0 := by
      simp only [sphereParam, real_inner_smul_left] at hw
      have h : inner ℝ (hemisphereParam i s y) w = 0 := (mul_eq_zero.mp hw).resolve_left ha.ne'
      simp [real_inner_smul_right, h]
    obtain ⟨v, hv⟩ := (hemisphereParam_fderiv_range i s y hy (a⁻¹ • w)).mpr hz
    refine ⟨v, ?_⟩
    change a • fderiv ℝ (hemisphereParam i s) y v = w
    rw [hv]
    simp [smul_smul, ha.ne']


open P202.MetricData

def sphereCoordinates {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (n+1)) (s : Bool)
    (p : P202.SpaceFormData.Sphere n a) (hp : p ∈ (sphereChart ha i s).source) :
    TangentSpace (sphereManifold n a ha) p ≃ₗ[ℝ] Euclidean n :=
  (tangentStructure (sphereManifold n a ha)).fiberCoordinates.equiv
    (sphereChart ha i s) (sphereChart_mem ha i s) p hp

def sphereDifferential (n : ℕ) (a : ℝ) (ha : 0 < a) (p : P202.SpaceFormData.Sphere n a) :
    TangentSpace (sphereManifold n a ha) p →ₗ[ℝ] TangentSpace (euclideanManifold (n+1)) p.val :=
  SmoothManifolds.differential (sphereManifold n a ha) (euclideanManifold (n+1))
    Subtype.val (sphere_inclusion_smooth n a ha) p

theorem sphereDifferential_spec (n : ℕ) (a : ℝ) (ha : 0 < a) (p : P202.SpaceFormData.Sphere n a) :
    IsDifferential (sphereManifold n a ha) (euclideanManifold (n+1)) Subtype.val p
      (sphereDifferential n a ha p) :=
  SmoothManifolds.differential_spec _ _ _ _ p

theorem sphereChart_param_ambient {n : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin (n+1)) (s : Bool)
    (p : P202.SpaceFormData.Sphere n a) (hp : p ∈ (sphereChart ha i s).source) :
    sphereParam a i s (sphereChart ha i s p).val = p.val := by
  have h := congrArg (WithLp.toLp 2) (sphereChart_param ha i s p hp)
  exact h

theorem sphereDifferential_coordinates {n : ℕ} {a : ℝ} (ha : 0 < a)
    (i : Fin (n+1)) (s : Bool) (p : P202.SpaceFormData.Sphere n a)
    (hp : p ∈ (sphereChart ha i s).source)
    (v : TangentSpace (sphereManifold n a ha) p) :
    euclideanCoordinates (n+1) p.val (sphereDifferential n a ha p v) =
      fderiv ℝ (sphereParam a i s) (sphereChart ha i s p).val (sphereCoordinates ha i s p hp v) := by
  let S := sphereManifold n a ha
  let T := euclideanManifold (n+1)
  let c := sphereChart ha i s
  let d := euclideanChart (n+1)
  let y := (c p).val
  let K := sphereCoordinates ha i s p hp
  let F := (tangentStructure T).fiberCoordinates.equiv d (euclideanChart_mem (n+1)) p.val
    (by change p.val ∈ univ ∧ _; exact ⟨mem_univ _, mem_univ _⟩)
  let H : Euclidean n → Euclidean (n+1) := fun z => a • insertRoot i s z
  let C := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)
  have hy : squareSum y < 1 := SmoothManifolds.SphereTorus.hemisphere_omit_mem i s _
    ((sphereChart_source ha i s p).mp hp)
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H {z | squareSum z < 1} :=
    (contDiffOn_const (c := a)).smul (SmoothManifolds.SphereTorus.contDiffOn_insertRoot i s)
  have hU : IsOpen {z : Euclidean n | squareSum z < 1} :=
    isOpen_lt (SmoothManifolds.SphereTorus.continuous_squareSum n) continuous_const
  have hdiff := (hH.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hrep : (fun q => H (c q).val) =ᶠ[𝓝 p] (fun q => (d q.val).val) := by
    filter_upwards [c.open_source.mem_nhds hp] with q hq
    exact sphereChart_param ha i s q hq
  have hJ := SmoothManifolds.differential_jacobian S T Subtype.val
    (sphere_inclusion_smooth n a ha) p (sphereDifferential n a ha p)
    (sphereDifferential_spec n a ha p) c d (sphereChart_mem ha i s) (euclideanChart_mem (n+1))
    hp (by change p.val ∈ univ ∧ _; exact ⟨mem_univ _, mem_univ _⟩) K F
    ((tangentStructure S).fiberCoordinates.isCoordinates c (sphereChart_mem ha i s) p hp)
    ((tangentStructure T).fiberCoordinates.isCoordinates d (euclideanChart_mem (n+1)) p.val _)
    _ H hU hy hH hrep v
  have hD : fderiv ℝ (sphereParam a i s) y = C.symm.toContinuousLinearMap.comp (fderiv ℝ H y) :=
    (C.symm.hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv
  change C.symm (F (sphereDifferential n a ha p v)) = fderiv ℝ (sphereParam a i s) y (K v)
  rw [hJ, hD]
  rfl


theorem sphereDifferential_injective (n : ℕ) (a : ℝ) (ha : 0 < a)
    (p : P202.SpaceFormData.Sphere n a) : Function.Injective (sphereDifferential n a ha p) := by
  obtain ⟨i, s, hp⟩ := SmoothManifolds.SphereTorus.hemisphere_cover n (sphereSquareHomeomorph n a ha p)
  have hpc : p ∈ (sphereChart ha i s).source := (sphereChart_source ha i s p).mpr hp
  have hy : squareSum (sphereChart ha i s p).val < 1 :=
    SmoothManifolds.SphereTorus.hemisphere_omit_mem i s _ hp
  intro v w hvw
  apply (sphereCoordinates ha i s p hpc).injective
  apply sphereParam_fderiv_injective ha i s _ hy
  rw [← sphereDifferential_coordinates ha i s p hpc v,
    ← sphereDifferential_coordinates ha i s p hpc w, hvw]

def sphereImmersion (n : ℕ) (a : ℝ) (ha : 0 < a) :
    SmoothImmersion (sphereManifold n a ha) (euclideanManifold (n+1)) Subtype.val where
  smooth := sphere_inclusion_smooth n a ha
  differential := sphereDifferential n a ha
  isDifferential := sphereDifferential_spec n a ha
  injective := sphereDifferential_injective n a ha

theorem sphere_tangent_range (n : ℕ) (a : ℝ) (ha : 0 < a)
    (p : P202.SpaceFormData.Sphere n a) (w : E (n+1)) :
    (∃ v, euclideanCoordinates (n+1) p.val ((sphereImmersion n a ha).differential p v) = w) ↔
      inner ℝ p.val w = 0 := by
  obtain ⟨i, s, hp⟩ := SmoothManifolds.SphereTorus.hemisphere_cover n (sphereSquareHomeomorph n a ha p)
  have hpc : p ∈ (sphereChart ha i s).source := (sphereChart_source ha i s p).mpr hp
  have hy : squareSum (sphereChart ha i s p).val < 1 :=
    SmoothManifolds.SphereTorus.hemisphere_omit_mem i s _ hp
  have hrange := sphereParam_fderiv_range ha i s (sphereChart ha i s p).val hy w
  rw [sphereChart_param_ambient ha i s p hpc] at hrange
  constructor
  · rintro ⟨v, hv⟩
    exact hrange.mp ⟨sphereCoordinates ha i s p hpc v,
      (sphereDifferential_coordinates ha i s p hpc v).symm.trans hv⟩
  · intro hw
    obtain ⟨z, hz⟩ := hrange.mpr hw
    refine ⟨(sphereCoordinates ha i s p hpc).symm z, ?_⟩
    change euclideanCoordinates (n+1) p.val (sphereDifferential n a ha p _) = w
    rw [sphereDifferential_coordinates ha i s p hpc, LinearEquiv.apply_symm_apply, hz]


def sphericalMetric (n : ℕ) (a : ℝ) (ha : 0 < a) :
    RiemannianMetric (sphereManifold n a ha) :=
  SmoothMetrics.pullbackMetric (euclideanMetric (n+1)) Subtype.val (sphereImmersion n a ha)

/-- The actual radius-a sphere with its induced metric and intrinsic LC connection. -/
def sphericalModel (n : ℕ) (a : ℝ) (ha : 0 < a) :
    SphericalModel n a (euclideanModel (n+1)) where
  manifold := sphereManifold n a ha
  inclusion := sphereImmersion n a ha
  tangent_range := sphere_tangent_range n a ha
  metric := sphericalMetric n a ha
  induced := by intro p v w; rfl
  connection := Classical.choose (LeviCivita.exists_unique (sphericalMetric n a ha))
  leviCivita := (Classical.choose_spec (LeviCivita.exists_unique (sphericalMetric n a ha))).1

end SphereConstruction

section SphericalPhases
open SmoothManifolds.TangentData P202.MetricData P202.GeodesicData

/-- The actual inclusion differential followed by Euclidean coordinates. -/
def ambientLinear {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a) :
    TangentSpace B.manifold p →ₗ[ℝ] E (n + 1) :=
  (A.coordinates p.val).toLinearMap.comp (B.inclusion.differential p)

theorem ambientLinear_injective {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a) :
    Function.Injective (ambientLinear B p) :=
  (A.coordinates p.val).injective.comp (B.inclusion.injective p)

/-- Position and ambient velocity determine an actual intrinsic phase. -/
theorem ambientPhase_injective {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) :
    Function.Injective (fun q : Phase B.manifold => (q.1.val, B.ambientVector q.1 q.2)) := by
  rintro ⟨p, v⟩ ⟨r, w⟩ h
  have hp : p = r := Subtype.ext (congrArg Prod.fst h)
  subst r
  have hv : v = w := ambientLinear_injective B p (congrArg Prod.snd h)
  subst w
  rfl

/-- The displayed great-circle velocity is orthogonal to its position. -/
theorem greatCircle_orthogonal {n : ℕ} (a : ℝ) (ha : a ≠ 0)
    (p u : E n) (hp : ‖p‖ = a) (hpu : inner ℝ p u = 0) (hu : ‖u‖ = 1)
    (t : ℝ) : inner ℝ (greatCircle a p u t) (greatCircleVelocity a p u t) = 0 := by
  have hup : inner ℝ u p = 0 := by rw [real_inner_comm]; exact hpu
  simp only [greatCircle, greatCircleVelocity, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hpu, hup,
    real_inner_self_eq_norm_sq, hp, hu]
  field_simp
  <;> ring

/-- All-speed curves have genuinely tangent ambient velocities. -/
theorem sphereCurve_orthogonal {n : ℕ} (a : ℝ) (ha : 0 < a)
    (p v : E n) (hp : ‖p‖ = a) (hpv : inner ℝ p v = 0) (t : ℝ) :
    inner ℝ (sphereCurve a p v t) (sphereCurveVelocity a p v t) = 0 := by
  by_cases hv : v = 0
  · simp [sphereCurve, sphereCurveVelocity, hv]
  · have hn : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    have ho : inner ℝ p (‖v‖⁻¹ • v) = 0 := by
      rw [real_inner_smul_right, hpv, mul_zero]
    simpa [sphereCurve, sphereCurveVelocity, hv, real_inner_smul_right] using
      congrArg (fun r : ℝ => ‖v‖ * r)
        (greatCircle_orthogonal a ha.ne' p (‖v‖⁻¹ • v) hp ho hn (‖v‖ * t))

/-- Tangent lifts exist in the original fibers, and realize every initial
velocity, including zero. This is a phase construction, not a claim yet of
vanishing intrinsic covariant acceleration. -/
theorem spherical_phase_exists {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
    (p : Sphere n a) (v : TangentSpace B.manifold p) :
    ∃ q : ℝ → Phase B.manifold, q 0 = ⟨p, v⟩ ∧ ∀ t,
      (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
      B.ambientVector (q t).1 (q t).2 = sphereCurveVelocity a p.val (B.ambientVector p v) t ∧
      tangentNorm B.metric (q t).1 (q t).2 = tangentNorm B.metric p v ∧
      HasDerivAt (fun s => (q s).1.val) (B.ambientVector (q t).1 (q t).2) t ∧
      HasDerivAt (fun s => B.ambientVector (q s).1 (q s).2)
        (-(‖B.ambientVector p v‖ ^ 2 / a ^ 2) • (q t).1.val) t := by
  have hp : ‖p.val‖ = a := mem_sphere_zero_iff_norm.mp p.property
  have ht := spherical_model_tangent B p v
  have hf := sphereCurve_formula (n + 1) a ha p.val (B.ambientVector p v) hp ht
  let r : ℝ → Sphere n a := fun t =>
    ⟨sphereCurve a p.val (B.ambientVector p v) t,
      mem_sphere_zero_iff_norm.mpr (hf.2.2 t).1⟩
  have hl (t : ℝ) : ∃ w : TangentSpace B.manifold (r t),
      B.ambientVector (r t) w = sphereCurveVelocity a p.val (B.ambientVector p v) t :=
    (B.tangent_range (r t) _).mpr
      (sphereCurve_orthogonal a ha p.val (B.ambientVector p v) hp ht t)
  let w := fun t => Classical.choose (hl t)
  have hw (t : ℝ) : B.ambientVector (r t) (w t) =
      sphereCurveVelocity a p.val (B.ambientVector p v) t := Classical.choose_spec (hl t)
  let q : ℝ → Phase B.manifold := fun t => ⟨r t, w t⟩
  have hpos (t : ℝ) : (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t := rfl
  have hvel (t : ℝ) : B.ambientVector (q t).1 (q t).2 =
      sphereCurveVelocity a p.val (B.ambientVector p v) t := hw t
  refine ⟨q, ?_, fun t => ⟨hpos t, hvel t, ?_, ?_, ?_⟩⟩
  · apply ambientPhase_injective B
    exact Prod.ext (hf.1) ((hvel 0).trans hf.2.1)
  · rw [spherical_model_norm, hvel, (hf.2.2 t).2.1, spherical_model_norm]
  · simpa only [hpos, hvel] using (hf.2.2 t).2.2.1
  · simpa only [hpos, hvel] using (hf.2.2 t).2.2.2

end SphericalPhases

-- Additional imports required before the implementation body:
-- import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
-- import Mathlib.Topology.Algebra.Module.FiniteDimension
-- Checked independently under Lean 4.33.1.
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData
open Set Filter
open scoped _root_.Topology

/-- A smooth immersion reflects first derivatives of continuous curves. No
smooth extension of the curve is required. -/
theorem immersion_reflects_velocity {n m : ℕ} {a b : SmoothManifolds.ModelKind}
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {f : M → N} (i : SmoothImmersion S T f)
    {c : ℝ → M} {t : ℝ} {v : TangentSpace S (c t)}
    (hc : ContinuousAt c t)
    (hv : HasVelocityAt T (f ∘ c) t (i.differential (c t) v)) :
    HasVelocityAt S c t v := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  obtain ⟨_, d, hd, hpd, hdv⟩ := hv
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := (i.smooth (c t)).2 e he d hd hp hpd
  let E := (tangentStructure S).fiberCoordinates.equiv e he (c t) hp
  let D := (tangentStructure T).fiberCoordinates.equiv d hd (f (c t)) hpd
  let F' := fderiv ℝ F (e (c t)).val
  have hj : ∀ w : TangentSpace S (c t), D (i.differential (c t) w) = F' (E w) :=
    SmoothManifolds.differential_jacobian S T f i.smooth (c t)
      (i.differential (c t)) (i.isDifferential (c t)) e d he hd hp hpd E D
      ((tangentStructure S).fiberCoordinates.isCoordinates e he (c t) hp)
      ((tangentStructure T).fiberCoordinates.isCoordinates d hd (f (c t)) hpd)
      U F hU hpU hF hrep
  have hi : Function.Injective F' := by
    intro x y hxy
    apply E.symm.injective
    apply i.injective (c t)
    apply D.injective
    simpa only [hj, LinearEquiv.apply_symm_apply] using hxy
  have hEmb : Topology.IsEmbedding F' :=
    (LinearMap.isClosedEmbedding_of_injective
      (f := F'.toLinearMap) (LinearMap.ker_eq_bot.mpr hi)).isEmbedding
  have hgc : ContinuousAt (fun s => (e (c s)).val) t :=
    (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).comp hc
  have hfd : HasFDerivAt F F' (e (c t)).val :=
    ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hhd : HasFDerivAt (fun s => (d (f (c s))).val)
      (F' ∘L ContinuousLinearMap.toSpanSingleton ℝ (E v)) t := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, ← hj, D, Function.comp_def] using hdv
  have hgd := HasFDerivAt.of_comp_of_isEmbedding hgc hfd hEmb hhd
    (hrep.comp_tendsto hc)
  refine ⟨hc, e, he, hp, ?_⟩
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hgd.hasDerivAt

open P202.SpaceFormData P202.CurveConnectionData

/-- The ambient derivative of a sphere-valued curve lifts to its actual
intrinsic velocity through the given smooth inclusion. -/
theorem spherical_velocity_lift {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) {c : ℝ → Sphere n a} {t : ℝ}
    {v : TangentSpace B.manifold (c t)}
    (hd : HasDerivAt (fun s => (c s).val) (B.ambientVector (c t) v) t) :
    HasVelocityWithinAt B.manifold c Set.univ t v := by
  have hA := (A.velocity (fun s => (c s).val) t (B.inclusion.differential (c t) v)).mpr hd
  have hA' : HasVelocityAt A.manifold (Subtype.val ∘ c) t
      (B.inclusion.differential (c t) v) := by
    simpa only [HasVelocityWithinAt, HasVelocityAt,
      continuousWithinAt_univ, hasDerivWithinAt_univ, Function.comp_def] using hA
  have hc : ContinuousAt c t := hd.continuousAt.codRestrict (fun s => (c s).property)
  have hB := immersion_reflects_velocity B.inclusion hc hA'
  simpa only [HasVelocityWithinAt, HasVelocityAt,
    continuousWithinAt_univ, hasDerivWithinAt_univ, Function.comp_def] using hB

open P202.SpaceFormData SmoothManifolds.TangentData P202.MetricData
  P202.GeodesicData P202.CurveConnectionData

/-- The explicit all-speed phase lifts have their actual intrinsic velocities.
The last derivative remains an ambient normal acceleration statement. -/
theorem spherical_phase_exists_with_velocity {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
    (p : Sphere n a) (v : TangentSpace B.manifold p) :
    ∃ q : ℝ → Phase B.manifold, q 0 = ⟨p, v⟩ ∧
      (∀ t, HasVelocityWithinAt B.manifold (fun s => (q s).1) Set.univ t (q t).2) ∧
      ∀ t,
      (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
      B.ambientVector (q t).1 (q t).2 = sphereCurveVelocity a p.val (B.ambientVector p v) t ∧
      tangentNorm B.metric (q t).1 (q t).2 = tangentNorm B.metric p v ∧
      HasDerivAt (fun s => (q s).1.val) (B.ambientVector (q t).1 (q t).2) t ∧
      HasDerivAt (fun s => B.ambientVector (q s).1 (q s).2)
        (-(‖B.ambientVector p v‖ ^ 2 / a ^ 2) • (q t).1.val) t := by
  obtain ⟨q, hq0, hq⟩ := spherical_phase_exists ha B p v
  exact ⟨q, hq0, fun t => spherical_velocity_lift B (hq t).2.2.2.1, hq⟩

section OrthogonalProjection
open SmoothManifolds.TangentData P202.MetricData

/-- Orthogonal ambient vectors, as a genuine linear subspace. -/
def orthogonalVectors {n : ℕ} (p : E n) : Submodule ℝ (E n) :=
  LinearMap.ker (innerₛₗ ℝ p)

/-- The original sphere tangent fiber is linearly identified with exactly
its ambient orthogonal subspace, using the inclusion differential. -/
def sphericalTangentCoordinates {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a) :
    TangentSpace B.manifold p ≃ₗ[ℝ] orthogonalVectors p.val :=
  LinearEquiv.ofBijective
    ((ambientLinear B p).codRestrict (orthogonalVectors p.val)
      (fun v => spherical_model_tangent B p v))
    ⟨fun v w h => ambientLinear_injective B p (congrArg Subtype.val h), by
      intro w
      obtain ⟨v, hv⟩ := (B.tangent_range p w.val).mpr w.property
      exact ⟨v, Subtype.ext hv⟩⟩

/-- Orthogonal projection in radius-a ambient coordinates. -/
def sphericalProjection {n : ℕ} (a : ℝ) (p w : E n) : E n :=
  w - (inner ℝ p w / a ^ 2) • p

theorem sphericalProjection_tangent {n : ℕ} (a : ℝ) (ha : a ≠ 0)
    (p w : E n) (hp : ‖p‖ = a) :
    inner ℝ p (sphericalProjection a p w) = 0 := by
  simp only [sphericalProjection, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hp]
  field_simp
  <;> ring

theorem sphericalProjection_of_tangent {n : ℕ} (a : ℝ) (p w : E n)
    (hw : inner ℝ p w = 0) : sphericalProjection a p w = w := by
  simp [sphericalProjection, hw]

theorem sphericalProjection_normal {n : ℕ} (a : ℝ) (ha : a ≠ 0)
    (p : E n) (hp : ‖p‖ = a) (c : ℝ) :
    sphericalProjection a p (c • p) = 0 := by
  simp only [sphericalProjection, real_inner_smul_right, real_inner_self_eq_norm_sq, hp]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 ha), sub_self]

/-- In particular the explicit all-speed accelerations have zero tangential
projection; identifying this with the intrinsic covariant derivative is a
separate geometric bridge. -/
theorem sphereCurve_projected_acceleration {n : ℕ} (a : ℝ) (ha : 0 < a)
    (p v : E n) (hp : ‖p‖ = a) (hpv : inner ℝ p v = 0) (t : ℝ) :
    sphericalProjection a (sphereCurve a p v t)
      (-(‖v‖ ^ 2 / a ^ 2) • sphereCurve a p v t) = 0 :=
  sphericalProjection_normal a ha.ne' _
    ((sphereCurve_formula n a ha p v hp hpv).2.2 t).1 _

end OrthogonalProjection

section CurvatureScalars
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurvatureData

/-- Positive definiteness makes the sectional denominator strictly positive
on every independent pair in the original tangent fiber. -/
theorem metric_gram_pos {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M)
    (X Y : TangentSpace S p) (h : LinearIndependent ℝ ![X, Y]) :
    0 < pairing g p X X * pairing g p Y Y - pairing g p X Y ^ 2 := by
  have hX : X ≠ 0 := h.ne_zero 0
  have hxx : 0 < pairing g p X X := g.positive p X hX
  let α := pairing g p X X
  let β := pairing g p X Y
  have hw : α • Y - β • X ≠ 0 := by
    intro hz
    have he : α • Y = β • X := sub_eq_zero.mp hz
    have hi : (1 : Fin 2) = 0 :=
      h.eq_of_smul_apply_eq_smul_apply α β 1 0 (ne_of_gt hxx) he
    exact (by decide : (1 : Fin 2) ≠ 0) hi
  have hwpos := g.positive p (α • Y - β • X) hw
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right] at hwpos
  rw [g.symmetric p Y X] at hwpos
  change 0 < α * (α * pairing g p Y Y - β * β) - β * (α * β - β * α) at hwpos
  change 0 < α * pairing g p Y Y - β ^ 2
  nlinarith

/-- Once the round tensor formula is established geometrically, its sectional
curvature is exactly the stated constant, with the source sign convention. -/
theorem sectionalCurvature_of_round_formula {n : ℕ} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (T : CurvatureTensor S) (κ : ℝ)
    (hT : ∀ p X Y Z, T.val p X Y Z =
      κ • (pairing g p Y Z • X - pairing g p X Z • Y))
    (p : M) (X Y : TangentSpace S p) (h : LinearIndependent ℝ ![X, Y]) :
    sectionalCurvature g T p X Y h = κ := by
  have hden := ne_of_gt (metric_gram_pos g p X Y h)
  unfold sectionalCurvature curvatureForm
  rw [hT]
  simp only [pairing, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.sub_left]
  rw [g.symmetric p Y X]
  exact (div_eq_iff hden).mpr (by dsimp only [pairing]; ring)

end CurvatureScalars

section CompactCompleteness
open SmoothManifolds.AtlasData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CompletenessData

/-- Compactness in the original topology implies completeness of the actual
length metric supplied by the upstream distance theorem. -/
theorem lengthMetricComplete_of_compact {n : ℕ} {M : Type} [TopologicalSpace M]
    [CompactSpace M] [ConnectedSpace M] {S : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) : LengthMetricComplete g := by
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  apply HopfRinow.complete_of_closedBoundedCompact g p
  intro K hK _hB
  exact hK.isCompact

theorem spherical_lengthMetricComplete {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A) :
    LengthMetricComplete B.metric := by
  letI : ConnectedSpace (Sphere n a) := (model_topology n hn a ha).2.1
  exact lengthMetricComplete_of_compact B.metric

theorem spherical_geodesicallyComplete {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A) :
    P202.HopfRinowData.GeodesicallyComplete B.manifold B.connection := by
  letI : ConnectedSpace (Sphere n a) := (model_topology n hn a ha).2.1
  exact MetricGeodesicCompleteness.metric_complete_geodesically_complete
    B.manifold B.metric B.connection B.leviCivita
    (spherical_lengthMetricComplete hn ha B)

/-- Actual global intrinsic maximal geodesics exist at every initial phase.
Identifying them with the explicit trigonometric curves remains separate. -/
theorem spherical_global_maximal_exists {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
    (w : Phase B.manifold) :
    ∃ q : ℝ → Phase B.manifold,
      IsMaximalThrough B.manifold B.connection w D13Unified.OpenTimeInterval.whole q := by
  obtain ⟨I, q, hq⟩ := GeodesicIVP.maximal_exists B.manifold B.metric B.connection B.leviCivita w
  have hI := spherical_geodesicallyComplete hn ha B w I q hq
  refine ⟨q, ?_⟩
  simpa only [IsMaximalThrough, hI, D13Unified.OpenTimeInterval.whole] using hq

end CompactCompleteness

-- Imports: P202.Geometry.GeodesicIVP and P202.Geometry.HopfRinow
-- Existing main helper reused: spherical_model_norm.
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
  P202.CurveConnectionData P202.GeodesicData P202.CurvatureData

/-- A geodesic defined for all real times has the actual universal maximality
property, by the accepted uniqueness theorem on overlapping intervals. -/
theorem maximalThrough_of_global_geodesic {n : ℕ} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n .euclidean M)
    (C : Connection (tangentBundle S)) (w : Phase S) (q : ℝ → Phase S)
    (hq0 : q 0 = w) (hq : IsGeodesicOn S C Set.univ q) :
    IsMaximalThrough S C w D13Unified.OpenTimeInterval.whole q := by
  refine ⟨by trivial, hq0, hq, ?_⟩
  intro J r hJ hr0 hr
  refine ⟨Set.subset_univ _, ?_⟩
  have heq := GeodesicIVP.overlap_unique S C
    D13Unified.OpenTimeInterval.whole J q r hq hr 0
    ⟨by trivial, hJ⟩ (hq0.trans hr0.symm)
  intro t ht
  exact heq ⟨by trivial, ht⟩

/-- An all-velocity global existence theorem implies completeness of the
original length metric, with its original topology. -/
theorem lengthMetricComplete_of_global_geodesics {n : ℕ} {M : Type}
    [TopologicalSpace M] [ConnectedSpace M] (S : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (h : ∀ w : Phase S, ∃ q : ℝ → Phase S,
      q 0 = w ∧ IsGeodesicOn S C Set.univ q) :
    P202.CompletenessData.LengthMetricComplete g := by
  apply HopfRinow.complete_of_geodesicallyComplete g C hC
  intro w I q hq
  obtain ⟨r, hr0, hr⟩ := h w
  have hi := (hq.2.2.2 D13Unified.OpenTimeInterval.whole r (by trivial) hr0 hr).1
  exact Set.Subset.antisymm (Set.subset_univ _) hi

/-- All intrinsic spherical curves with the displayed ambient position and
velocity formulas have constant metric speed and are the actual maximal
geodesics. The ambient theorem is used only for its proved norm identity. -/
theorem spherical_maximal_curves_of_global_geodesics {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
    (ha : 0 < a)
    (hformula : P202Specs.Geometry.EuclideanSphericalModels.arbitraryVelocityType)
    (h : ∀ p v, ∃ q : ℝ → Phase B.manifold,
      q 0 = ⟨p, v⟩ ∧ IsGeodesicOn B.manifold B.connection Set.univ q ∧
      ∀ t, (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
        B.ambientVector (q t).1 (q t).2 =
          sphereCurveVelocity a p.val (B.ambientVector p v) t) :
    ∀ p v, ∃ q : ℝ → Phase B.manifold,
      IsMaximalThrough B.manifold B.connection ⟨p, v⟩
        D13Unified.OpenTimeInterval.whole q ∧
      ∀ t, (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
        B.ambientVector (q t).1 (q t).2 =
          sphereCurveVelocity a p.val (B.ambientVector p v) t ∧
        tangentNorm B.metric (q t).1 (q t).2 = tangentNorm B.metric p v := by
  intro p v
  obtain ⟨q, hq0, hq, hf⟩ := h p v
  refine ⟨q, maximalThrough_of_global_geodesic B.manifold B.connection _ q hq0 hq, ?_⟩
  intro t
  have hn := hformula (n + 1) a ha p.val (B.ambientVector p v)
    (mem_sphere_zero_iff_norm.mp p.property)
    ((B.tangent_range p _).mp ⟨v, rfl⟩)
  refine ⟨(hf t).1, (hf t).2, ?_⟩
  rw [spherical_model_norm, (hf t).2, (hn.2.2 t).2.1,
    spherical_model_norm]

/-- The unit-speed displayed great circles follow from the all-velocity
intrinsic statement, using the equality between induced and ambient norms. -/
theorem spherical_unit_curves_of_all_velocities {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
    (h : ∀ p v, ∃ q : ℝ → Phase B.manifold,
      IsMaximalThrough B.manifold B.connection ⟨p, v⟩
        D13Unified.OpenTimeInterval.whole q ∧
      ∀ t, (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
        B.ambientVector (q t).1 (q t).2 =
          sphereCurveVelocity a p.val (B.ambientVector p v) t ∧
        tangentNorm B.metric (q t).1 (q t).2 = tangentNorm B.metric p v) :
    ∀ p u, tangentNorm B.metric p u = 1 → ∃ q : ℝ → Phase B.manifold,
      IsMaximalThrough B.manifold B.connection ⟨p, u⟩
        D13Unified.OpenTimeInterval.whole q ∧
      ∀ t, (q t).1.val = greatCircle a p.val (B.ambientVector p u) t ∧
        B.ambientVector (q t).1 (q t).2 =
          greatCircleVelocity a p.val (B.ambientVector p u) t ∧
        tangentNorm B.metric (q t).1 (q t).2 = 1 := by
  intro p u hu
  have hn : ‖B.ambientVector p u‖ = 1 := by
    rw [← spherical_model_norm, hu]
  have hv : B.ambientVector p u ≠ 0 := by
    intro hv
    simpa [hv] using hn
  obtain ⟨q, hq, hf⟩ := h p u
  refine ⟨q, hq, ?_⟩
  intro t
  simpa [sphereCurve, sphereCurveVelocity, hv, hn, hu] using hf t

/-- Formula and norm parts of the Euclidean conclusion require no further
ODE analysis once the global intrinsic geodesics have been constructed. -/
theorem euclidean_maximal_curves_of_global_geodesics {n : ℕ} (G : EuclideanModel n)
    (h : ∀ p v, ∃ q : ℝ → Phase G.manifold,
      q 0 = ⟨p, v⟩ ∧ IsGeodesicOn G.manifold G.connection Set.univ q ∧
      ∀ t, (q t).1 = line p (G.coordinates p v) t ∧
        G.coordinates (q t).1 (q t).2 = G.coordinates p v) :
    ∀ p v, ∃ q : ℝ → Phase G.manifold,
      IsMaximalThrough G.manifold G.connection ⟨p, v⟩
        D13Unified.OpenTimeInterval.whole q ∧
      ∀ t, (q t).1 = line p (G.coordinates p v) t ∧
        G.coordinates (q t).1 (q t).2 = G.coordinates p v ∧
        tangentNorm G.metric (q t).1 (q t).2 = ‖G.coordinates p v‖ := by
  intro p v
  obtain ⟨q, hq0, hq, hf⟩ := h p v
  refine ⟨q, maximalThrough_of_global_geodesic G.manifold G.connection _ q hq0 hq, ?_⟩
  intro t
  refine ⟨(hf t).1, (hf t).2, ?_⟩
  unfold tangentNorm
  rw [G.metric_standard, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _), (hf t).2]

/-- Complete Euclidean conclusion from curvature and global intrinsic straight
lines. The standard Euclidean topology supplies connectedness directly. -/
theorem euclidean_conclusion_of_flat_global_geodesics {n : ℕ}
    (G : EuclideanModel n)
    (hcurv : ∃ T : CurvatureTensor G.manifold,
      RepresentsCurvature G.connection T ∧
      ∀ p X Y h, sectionalCurvature G.metric T p X Y h = 0)
    (h : ∀ p v, ∃ q : ℝ → Phase G.manifold,
      q 0 = ⟨p, v⟩ ∧ IsGeodesicOn G.manifold G.connection Set.univ q ∧
      ∀ t, (q t).1 = line p (G.coordinates p v) t ∧
        G.coordinates (q t).1 (q t).2 = G.coordinates p v) : G.Conclusion := by
  have hc : P202.CompletenessData.LengthMetricComplete G.metric :=
    lengthMetricComplete_of_global_geodesics G.manifold G.metric G.connection G.leviCivita
      (by
        rintro ⟨p, v⟩
        obtain ⟨q, hq0, hq, _⟩ := h p v
        exact ⟨q, hq0, hq⟩)
  exact ⟨inferInstance, inferInstance, hc, hcurv,
    euclidean_maximal_curves_of_global_geodesics G h⟩

/-- Complete spherical conclusion from the original sphere topology, the
curvature computation and global intrinsic great circles for every velocity. -/
theorem spherical_conclusion_of_global_geodesics {n : ℕ} {a : ℝ}
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
    (ha : 0 < a)
    (htop : ConnectedSpace (Sphere n a) ∧ SimplyConnectedSpace (Sphere n a))
    (hformula : P202Specs.Geometry.EuclideanSphericalModels.arbitraryVelocityType)
    (hcurv : ∃ T : CurvatureTensor B.manifold,
      RepresentsCurvature B.connection T ∧
      ∀ p X Y h, sectionalCurvature B.metric T p X Y h = (a ^ 2)⁻¹)
    (h : ∀ p v, ∃ q : ℝ → Phase B.manifold,
      q 0 = ⟨p, v⟩ ∧ IsGeodesicOn B.manifold B.connection Set.univ q ∧
      ∀ t, (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
        B.ambientVector (q t).1 (q t).2 =
          sphereCurveVelocity a p.val (B.ambientVector p v) t) : B.Conclusion := by
  letI := htop.1
  have hc : P202.CompletenessData.LengthMetricComplete B.metric :=
    lengthMetricComplete_of_global_geodesics B.manifold B.metric B.connection B.leviCivita
      (by
        rintro ⟨p, v⟩
        obtain ⟨q, hq0, hq, _⟩ := h p v
        exact ⟨q, hq0, hq⟩)
  have hall := spherical_maximal_curves_of_global_geodesics B ha hformula h
  exact ⟨htop.1, htop.2, hc, hcurv, hall,
    spherical_unit_curves_of_all_velocities B hall⟩


/-- Both standard intrinsic realizations exist for every positive radius. -/
theorem model_constructions : constructionType := by
  intro n a ha
  exact ⟨⟨euclideanModel n⟩, ⟨euclideanModel (n + 1), ⟨sphericalModel n a ha⟩⟩⟩

/-- Sphere completeness concerns the induced Riemannian length metric and
actual maximal intrinsic geodesics. -/
theorem spherical_completeness : sphericalCompletenessType := by
  intro n hn a ha A B
  exact ⟨spherical_lengthMetricComplete hn ha B,
    spherical_geodesicallyComplete hn ha B,
    spherical_global_maximal_exists hn ha B⟩

/-- Full Euclidean geometry, including the original intrinsic geodesic
and length-metric conclusions. -/
theorem euclidean_models : euclideanModelType := by
  intro n
  exact ⟨euclideanModel n, euclidean_conclusion n⟩

-- Checked in research/ProjectionCurve.lean; import P202.Geometry.CurveCovariantDerivative.
section ProjectedCurveCovariance
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.FrameData P202.MetricData P202.ConnectionData
  P202.CurveConnectionData
open Set Filter
open scoped _root_.Topology

variable {n r s : ℕ} {a : SmoothManifolds.ModelKind} {M : Type}
  [TopologicalSpace M] {S : SmoothManifold n a M}
  {ι κ : Type} {E G : M → Type}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean s) G)]
  {B : SmoothVectorBundle S r ι E} {J : SmoothVectorBundle S s κ G}

private theorem covariantDerivative_congr_field (C : Connection B)
    {c : ℝ → M} {f g : (u : ℝ) → E (c u)} {t : ℝ} {D : E (c t)}
    (hD : HasCovariantDerivativeAt C c f t D) (hfg : ∀ᶠ u in 𝓝 t, f u = g u) :
    HasCovariantDerivativeAt C c g t D := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, hEq⟩ := hD
  have hcoeff : coefficientsAlong b c g =ᶠ[𝓝 t] coefficientsAlong b c f := by
    filter_upwards [hfg] with u hu
    simp only [coefficientsAlong, ← hu]
  refine ⟨V, hV, U, hU, b, hp, v', ?_, ?_⟩
  · exact hv.congr_of_eventuallyEq_of_mem (by simpa using hcoeff) (mem_univ t)
  · rw [hEq]
    unfold frameDerivative
    rw [hcoeff.self_of_nhds]

private theorem covariantDerivative_zero (C : Connection B)
    {c : ℝ → M} {t : ℝ} {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V) :
    HasCovariantDerivativeAt C c (fun u => (0 : E (c u))) t 0 := by
  have hz := CurveCovariantDerivative.derivative_section C (0 : Section B) (mem_univ t) hV
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have heq : pointDerivative C (0 : Section B).val (c t) V = 0 := by
    rw [← hX, ConnectionForms.pointDerivative_global B C]
    simp
  simpa only [heq, ConnectionForms.section_zero_apply] using hz

private theorem covariantDerivative_finset_sum (C : Connection B)
    {c : ℝ → M} {t : ℝ} {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    {A : Type} (F : Finset A) (f : A → (u : ℝ) → E (c u))
    (D : A → E (c t)) (hD : ∀ j ∈ F, HasCovariantDerivativeAt C c (f j) t (D j)) :
    HasCovariantDerivativeAt C c (fun u => ∑ j ∈ F, f j u) t (∑ j ∈ F, D j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using covariantDerivative_zero C hV
  | @insert j F hj ih =>
    simpa only [Finset.sum_insert hj] using
      (CurveCovariantDerivative.derivative_add C (mem_univ t) uniqueDiffWithinAt_univ
        (hD j (Finset.mem_insert_self _ _))
        (ih (fun k hk => hD k (Finset.mem_insert_of_mem hk))))

/-- A vector-valued smooth function is differentiable along an intrinsic C¹
curve at the parameter in question. -/
private theorem vectorSmoothAlong_hasDerivAt {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : ℝ → M} {t : ℝ} {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V) (f : M → F)
    (hf : VectorSmoothAt S.smoothStructure.val f (c t)) :
    ∃ v', HasDerivAt (f ∘ c) v' t := by
  obtain ⟨hc, e, he, hp, hd⟩ := hV
  obtain ⟨U, hU, hpU, H, hH, hrep⟩ := hf.2 e he hp
  have hh := ((hH.contDiffAt (hU.mem_nhds hpU)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivWithinAt t hd
  refine ⟨fderiv ℝ H (e (c t)).val
    (((tangentStructure S).fiberCoordinates.equiv e he (c t) hp) V), ?_⟩
  have hc' : ContinuousAt c t := by simpa only [continuousWithinAt_univ] using hc
  have hd' : HasDerivAt (fun u => H (e (c u)).val)
      (fderiv ℝ H (e (c t)).val
        (((tangentStructure S).fiberCoordinates.equiv e he (c t) hp) V)) t := by
    simpa only [hasDerivWithinAt_univ, Function.comp_def] using hh
  exact hd'.congr_of_eventuallyEq (hrep.comp_tendsto hc').symm

private theorem trivializationFrame_coordinates (i : ι) (p : M) (hp : p ∈ B.baseSet i)
    (v : E p) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame B i).basis ⟨p, hp⟩).equivFun v =
      B.fiberCoordinates i p hp v := by
  simp [SmoothManifolds.ConstantRankBundles.trivializationFrame]

/-- A smooth splitting reflects existence of covariant differentiation along
an arbitrary C¹ curve. The source connection can be any connection. -/
theorem covariantDerivative_exists_of_split_image
    (C : Connection B) (D : Connection J)
    (I : (p : M) → E p →ₗ[ℝ] G p)
    (R : SmoothManifolds.ConstantRankData.SmoothBundleMorphism J B)
    (hRI : ∀ p w, R.linearMap p (I p w) = w)
    {c : ℝ → M} {f : (u : ℝ) → E (c u)} {t : ℝ}
    {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    {Z : G (c t)}
    (hZ : HasCovariantDerivativeAt D c (fun u => I (c u) (f u)) t Z) :
    ∃ A : E (c t), HasCovariantDerivativeAt C c f t A := by
  classical
  obtain ⟨i, hi⟩ := B.covers (c t)
  obtain ⟨j, hj⟩ := J.covers (c t)
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  let d := SmoothManifolds.ConstantRankBundles.trivializationFrame J j
  obtain ⟨β', hβ⟩ := CurveCovariantDerivative.exists_coefficients_deriv D
    (mem_univ t) hZ d hj
  let β := coefficientsAlong d c (fun u => I (c u) (f u))
  let T := SmoothManifolds.ConstantRankBundles.morphismMatrix J B R j i
  have hT : VectorSmoothAt S.smoothStructure.val T (c t) :=
    SmoothManifolds.ConstantRankBundles.morphismMatrix_smoothAt J B R j i (c t) hj hi
  obtain ⟨T', hdT⟩ := vectorSmoothAlong_hasDerivAt hV T hT
  have hdβ : HasDerivAt β β' t := by
    simpa only [hasDerivWithinAt_univ] using hβ
  have hdγ := hdT.clm_apply hdβ
  have hc : ContinuousAt c t := by simpa only [continuousWithinAt_univ] using hV.1
  have hBi : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hJj : IsOpen (J.baseSet j) := J.trivialization_baseSet j ▸ (J.trivialization j).open_baseSet
  have heq : coefficientsAlong b c f =ᶠ[𝓝 t] (fun u => T (c u) (β u)) := by
    filter_upwards [hc (hBi.mem_nhds hi), hc (hJj.mem_nhds hj)] with u hui huj
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b c f u hui]
    change (b.basis ⟨c u, hui⟩).equivFun (f u) = T (c u) (β u)
    rw [trivializationFrame_coordinates]
    dsimp only [T]
    rw [SmoothManifolds.ConstantRankBundles.morphismMatrix_apply J B R j i (c u) huj hui]
    have hb : β u = J.fiberCoordinates j (c u) huj (I (c u) (f u)) := by
      change coefficientsAlong d c (fun z => I (c z) (f z)) u = _
      rw [CurveCovariantDerivative.coefficientsAlong_of_mem d c _ u huj,
        trivializationFrame_coordinates]
    rw [hb, LinearEquiv.symm_apply_apply, hRI]
  have hα := hdγ.congr_of_eventuallyEq heq
  exact ⟨_, V, hV, B.baseSet i, hBi, b, hi, _, hα.hasDerivWithinAt, rfl⟩

/-- The field-level projection identity for two connections extends to
arbitrary differentiable fields along a C¹ curve, whenever both covariant
 derivatives exist. No smooth extension of that curve or field is assumed. -/
theorem projected_connection_curve_identity
    (C : Connection B) (D : Connection J)
    (I : (p : M) → E p →ₗ[ℝ] G p) (R : (p : M) → G p →ₗ[ℝ] E p)
    (hRI : ∀ p w, R p (I p w) = w)
    (hproject : ∀ (X : Field S) (z : Section B), ∃ u : Section J,
      (∀ p, u.val p = I p (z.val p)) ∧
      (∀ p, (C.cov X z).val p = R p ((D.cov X u).val p)))
    {c : ℝ → M} {f : (u : ℝ) → E (c u)} {t : ℝ}
    {A : E (c t)} {Z : G (c t)}
    (hA : HasCovariantDerivativeAt C c f t A)
    (hZ : HasCovariantDerivativeAt D c (fun u => I (c u) (f u)) t Z) :
    A = R (c t) Z := by
  classical
  obtain ⟨V, hV, U, hU, b, hp, v', hv, hAeq⟩ := hA
  have hA : HasCovariantDerivativeAt C c f t A := ⟨V, hV, U, hU, b, hp, v', hv, hAeq⟩
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨c t, hp⟩
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  choose u hu hproj using fun j : Fin r => hproject X (e j)
  let α := coefficientsAlong b c f
  have hα : HasDerivAt α v' t := by simpa only [hasDerivWithinAt_univ] using hv
  let A' : E (c t) := ∑ j : Fin r,
    (v' j • (e j).val (c t) + α t j • pointDerivative C (e j).val (c t) V)
  let Z' : G (c t) := ∑ j : Fin r,
    (v' j • (u j).val (c t) + α t j • pointDerivative D (u j).val (c t) V)
  have hsrc : HasCovariantDerivativeAt C c
      (fun z => ∑ j : Fin r, α z j • (e j).val (c z)) t A' := by
    apply covariantDerivative_finset_sum C hV Finset.univ
      (fun j z => α z j • (e j).val (c z))
      (fun j => v' j • (e j).val (c t) + α t j • pointDerivative C (e j).val (c t) V)
    intro j _
    exact CurveCovariantDerivative.derivative_smul C
      (CurveCovariantDerivative.derivative_section C (e j) (mem_univ t) hV)
      (hasDerivAt_pi.mp hα j).hasDerivWithinAt
  have htgt : HasCovariantDerivativeAt D c
      (fun z => ∑ j : Fin r, α z j • (u j).val (c z)) t Z' := by
    apply covariantDerivative_finset_sum D hV Finset.univ
      (fun j z => α z j • (u j).val (c z))
      (fun j => v' j • (u j).val (c t) + α t j • pointDerivative D (u j).val (c t) V)
    intro j _
    exact CurveCovariantDerivative.derivative_smul D
      (CurveCovariantDerivative.derivative_section D (u j) (mem_univ t) hV)
      (hasDerivAt_pi.mp hα j).hasDerivWithinAt
  have hfg : ∀ᶠ z in 𝓝 t, (∑ j : Fin r, α z j • (e j).val (c z)) = f z := by
    have hc : ContinuousAt c t := by simpa only [continuousWithinAt_univ] using hV.1
    filter_upwards [hc (hU.mem_nhds hp), hc (Filter.eventually_all.mpr he)] with z hz hze
    simp only [α, CurveCovariantDerivative.coefficientsAlong_of_mem b c f z hz]
    have hev (j : Fin r) : (e j).val (c z) = b.basis ⟨c z, hz⟩ j := by
      simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ (c z) hz,
        b.basis_eq] using hze j
    simp_rw [hev]
    exact (b.basis ⟨c z, hz⟩).sum_equivFun (f z)
  have hIg : ∀ᶠ z in 𝓝 t, (∑ j : Fin r, α z j • (u j).val (c z)) =
      I (c z) (f z) := by
    filter_upwards [hfg] with z hz
    simpa only [hu, map_sum, map_smul] using congrArg (I (c z)) hz
  have hAA' : A = A' := CurveCovariantDerivative.covariantDerivative_unique C
    (mem_univ t) uniqueDiffWithinAt_univ hA (covariantDerivative_congr_field C hsrc hfg)
  have hZZ' : Z = Z' := CurveCovariantDerivative.covariantDerivative_unique D
    (mem_univ t) uniqueDiffWithinAt_univ hZ (covariantDerivative_congr_field D htgt hIg)
  rw [hAA', hZZ']
  simp only [A', Z', map_sum, map_add, map_smul, hu, hRI]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← hX, ConnectionForms.pointDerivative_global B C,
    ConnectionForms.pointDerivative_global J D, hproj]

/-- Smoothly split field-level projection is compatible with covariant
 differentiation of arbitrary C¹ fields along curves. -/
theorem projected_connection_curve_derivative
    (C : Connection B) (D : Connection J)
    (I : (p : M) → E p →ₗ[ℝ] G p)
    (R : SmoothManifolds.ConstantRankData.SmoothBundleMorphism J B)
    (hRI : ∀ p w, R.linearMap p (I p w) = w)
    (hproject : ∀ (X : Field S) (z : Section B), ∃ u : Section J,
      (∀ p, u.val p = I p (z.val p)) ∧
      (∀ p, (C.cov X z).val p = R.linearMap p ((D.cov X u).val p)))
    {c : ℝ → M} {f : (u : ℝ) → E (c u)} {t : ℝ}
    {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    {Z : G (c t)}
    (hZ : HasCovariantDerivativeAt D c (fun u => I (c u) (f u)) t Z) :
    HasCovariantDerivativeAt C c f t (R.linearMap (c t) Z) := by
  obtain ⟨A, hA⟩ := covariantDerivative_exists_of_split_image C D I R hRI hV hZ
  have hEq := projected_connection_curve_identity C D I R.linearMap hRI hproject hA hZ
  rw [← hEq]
  exact hA


end ProjectedCurveCovariance

-- Imports: P202.Geometry.PullbackConnections, P202.Geometry.GaussLemma
-- Generic arbitrary-C1 pullback covariance, checked directly with Lean 4.33.1.
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData
open Set Filter
open scoped _root_.Topology

/-- Pullback covariant differentiation along an arbitrary C¹ curve is the
original covariant differentiation along the composed curve. The field need
not extend to a smooth section on either manifold. -/
theorem pullback_covariantDerivative_iff
    {n m r : ℕ} {a b : SmoothManifolds.ModelKind} {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type} {E : M → Type} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (F : N → M) (hF : IsSmoothMap T S F)
    (P : PullbackBundle B T F) (C : Connection B)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : P202.PullbackData.IsPullback B C F hF P D)
    (c : ℝ → N) (f : (u : ℝ) → E (F (c u))) (t : ℝ)
    (V : TangentSpace T (c t)) (hV : HasVelocityWithinAt T c univ t V)
    (Z : E (F (c t))) :
    (letI := P.space.topology; HasCovariantDerivativeAt D c f t Z) ↔
      HasCovariantDerivativeAt C (F ∘ c) f t Z := by
  classical
  letI := P.space.topology
  obtain ⟨U, hU, hp, ⟨e⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (F (c t))
  let hO := hU.preimage (continuous_iff_continuousAt.mpr (fun q => (hF q).1))
  let d := PullbackConnections.pullFrame B F hF P hU e
  have hp' : c t ∈ F ⁻¹' U := hp
  have hFV := GaussLemma.velocity_smooth_postcomposition F hF (mem_univ t) hV
  have hcoeff : coefficientsAlong d c f = coefficientsAlong e (F ∘ c) f := by
    funext u
    unfold coefficientsAlong
    change (if h : F (c u) ∈ U then (d.basis ⟨c u, h⟩).equivFun (f u) else 0) =
      (if h : F (c u) ∈ U then (e.basis ⟨F (c u), h⟩).equivFun (f u) else 0)
    split_ifs <;> rfl
  have hmatrix : connectionMatrix D d ⟨c t, hp'⟩ V =
      connectionMatrix C e ⟨F (c t), hp⟩
        (SmoothManifolds.differential T S F hF (c t) V) := by
    ext i j
    exact PullbackConnections.frame_rule_of_isPullback B F hF P C D hD U hU hO e d
      (fun _ _ => rfl) ⟨c t, hp'⟩ V i j
  have hframe (v' : Euclidean r) :
      frameDerivative D d c f t hp' V v' =
        frameDerivative C e (F ∘ c) f t hp
          (SmoothManifolds.differential T S F hF (c t) V) v' := by
    unfold frameDerivative
    rw [hcoeff, hmatrix]
    rfl
  constructor
  · intro hd
    obtain ⟨v', hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv D
      (mem_univ t) hd d hp'
    have heq := CurveCovariantDerivative.local_formula D
      (mem_univ t) uniqueDiffWithinAt_univ hd d hp' hV hv
    refine ⟨_, hFV, U, hU, e, hp, v', ?_, heq.trans (hframe v')⟩
    rwa [hcoeff] at hv
  · intro hd
    obtain ⟨v', hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C
      (mem_univ t) hd e hp
    have heq := CurveCovariantDerivative.local_formula C
      (mem_univ t) uniqueDiffWithinAt_univ hd e hp hFV hv
    refine ⟨V, hV, F ⁻¹' U, hO, d, hp', v', ?_, heq.trans (hframe v').symm⟩
    rwa [hcoeff]


-- Required: import P202.Geometry.GaussWeingarten
-- Insert after pullback_covariantDerivative_iff and projected_connection_curve_derivative.
-- Both declarations checked independently against the compiled main module.
open P202.SpaceFormData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
open Set Filter
open scoped _root_.Topology

/-- A tangent field along the literal round sphere is intrinsically parallel
when its ambient derivative is radial. This uses the actual induced metric,
actual inclusion differential and original Levi–Civita connection. -/
theorem spherical_normal_acceleration {n : ℕ} {a : ℝ}
    (B : SphericalModel n a (euclideanModel (n + 1)))
    (c : ℝ → Sphere n a)
    (f : (u : ℝ) → TangentSpace B.manifold (c u)) (t : ℝ)
    (V : TangentSpace B.manifold (c t))
    (hV : HasVelocityWithinAt B.manifold c univ t V) (r : ℝ)
    (hd : HasDerivAt (fun u => B.ambientVector (c u) (f u)) (r • (c t).val) t) :
    HasCovariantDerivativeAt B.connection c f t 0 := by
  let A := euclideanModel (n + 1)
  let P := P202.PullbackData.bundle (tangentBundle A.manifold)
    B.manifold Subtype.val B.inclusion.smooth
  letI := P.space.topology
  obtain ⟨hP, D, W, hmetric, hD, hproject⟩ :=
    GaussWeingarten.projected_connections_exists B.metric A.metric Subtype.val
      B.inclusion B.induced B.connection A.connection B.leviCivita A.leviCivita P
  let R := GaussWeingarten.tangentProjectionMorphism B.inclusion P hP W
  have hRI : ∀ p w, R.linearMap p (B.inclusion.differential p w) = w :=
    GaussWeingarten.tangentProjection_image B.inclusion P hP W
  have hproj : ∀ (X : Field B.manifold) (z : Section (tangentBundle B.manifold)),
      ∃ u : Section P.space.bundle,
        (∀ p, u.val p = B.inclusion.differential p (z.val p)) ∧
        (∀ p, (B.connection.cov X z).val p = R.linearMap p ((D.cov X u).val p)) := by
    obtain ⟨_, _, _, _, h, _⟩ := hproject
    exact h
  let Z : TangentSpace A.manifold (c t).val :=
    (A.coordinates (c t).val).symm (r • (c t).val)
  have hFV := GaussLemma.velocity_smooth_postcomposition Subtype.val B.inclusion.smooth
    (mem_univ t) hV
  have hZambient : HasCovariantDerivativeAt A.connection
      (fun u => (c u).val) (fun u => B.inclusion.differential (c u) (f u)) t Z := by
    apply (euclidean_covariantDerivative_iff (n + 1) (fun u => (c u).val)
      (fun u => B.inclusion.differential (c u) (f u)) t _ Z hFV).mpr
    simpa only [Z, A, euclideanModel, SphericalModel.ambientVector,
      LinearEquiv.apply_symm_apply] using hd
  have hZ : HasCovariantDerivativeAt D c
      (fun u => B.inclusion.differential (c u) (f u)) t Z :=
    (pullback_covariantDerivative_iff (tangentBundle A.manifold) Subtype.val
      B.inclusion.smooth P A.connection D hD c
      (fun u => B.inclusion.differential (c u) (f u)) t V hV Z).mpr hZambient
  have hiP : ∀ p v w, hP.form p (B.inclusion.differential p v)
      (B.inclusion.differential p w) = pairing B.metric p v w := by
    intro p v w
    rw [hmetric p]
    exact B.induced p v w
  have hradial (w : TangentSpace B.manifold (c t)) :
      hP.form (c t) Z (B.inclusion.differential (c t) w) = 0 := by
    rw [hmetric (c t)]
    change pairing A.metric (c t).val Z (B.inclusion.differential (c t) w) = 0
    rw [A.metric_standard]
    change inner ℝ (A.coordinates (c t).val Z) (B.ambientVector (c t) w) = 0
    dsimp only [Z]
    rw [LinearEquiv.apply_symm_apply, real_inner_smul_left, spherical_model_tangent B,
      mul_zero]
  have hRZ : R.linearMap (c t) Z = 0 := by
    have hpair := GaussWeingarten.pairing_tangentProjection B.inclusion P hP W
      B.metric hiP (c t) Z (R.linearMap (c t) Z)
    rw [hradial] at hpair
    by_contra hne
    exact (ne_of_gt (B.metric.positive (c t) (R.linearMap (c t) Z) hne)) hpair.symm
  have hresult := projected_connection_curve_derivative B.connection D
    B.inclusion.differential R hRI hproj hV hZ
  rwa [hRZ] at hresult

/-- The displayed all-velocity sphere formulas are actual global intrinsic
geodesics, including their zero-velocity branch. -/
theorem spherical_global_geodesics {n : ℕ} {a : ℝ} (ha : 0 < a)
    (B : SphericalModel n a (euclideanModel (n + 1))) :
    ∀ p v, ∃ q : ℝ → Phase B.manifold,
      q 0 = ⟨p, v⟩ ∧ IsGeodesicOn B.manifold B.connection univ q ∧
      ∀ t, (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
        B.ambientVector (q t).1 (q t).2 =
          sphereCurveVelocity a p.val (B.ambientVector p v) t := by
  intro p v
  obtain ⟨q, hq0, hV, hq⟩ := spherical_phase_exists_with_velocity ha B p v
  refine ⟨q, hq0, ?_, fun t => ⟨(hq t).1, (hq t).2.1⟩⟩
  intro t _ht
  exact ⟨hV t, spherical_normal_acceleration B (fun u => (q u).1) (fun u => (q u).2)
    t (q t).2 (hV t) (-(‖B.ambientVector p v‖ ^ 2 / a ^ 2)) (hq t).2.2.2.2⟩


section SphericalSecondForm
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData P202.MetricData P202.ConnectionData
open Set Filter
open scoped _root_.Topology

theorem ambient_normal_eq {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A)
    (p : Sphere n a) (w : E (n+1))
    (hw : ∀ v : TangentSpace B.manifold p, inner ℝ (B.ambientVector p v) w = 0) :
    w = (inner ℝ p.val w / a^2) • p.val := by
  have hp : ‖p.val‖ = a := mem_sphere_zero_iff_norm.mp p.property
  let r := inner ℝ p.val w / a^2
  let q := w - r • p.val
  have hq : inner ℝ p.val q = 0 := by
    simp only [q, r, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hp]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 ha.ne'), sub_self]
  obtain ⟨v, hv⟩ := (B.tangent_range p q).mpr hq
  have hwq : inner ℝ q w = 0 := by rw [← hv]; exact hw v
  have hqp : inner ℝ q p.val = 0 := by rw [real_inner_comm]; exact hq
  have hself : inner ℝ q q = 0 := by
    calc
      _ = inner ℝ q (w - r • p.val) := rfl
      _ = 0 := by rw [inner_sub_right, real_inner_smul_right, hwq, hqp]; ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

set_option maxHeartbeats 1600000 in
theorem spherical_second_form_of_position_derivative
    {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n+1)} (B : SphericalModel n a A)
    (P : PullbackBundle (tangentBundle A.manifold) B.manifold Subtype.val)
    : letI := P.space.topology
    ∀ (hP : SmoothFiberMetric P.space.bundle)
    (D : Connection P.space.bundle)
    (II : (p : Sphere n a) → TangentSpace B.manifold p → TangentSpace B.manifold p →
      TangentSpace A.manifold p.val)
    (lift : Field B.manifold → Section P.space.bundle)
    (hlift : ∀ (Y : Field B.manifold) p, (lift Y).val p = B.inclusion.differential p (Y.val p))
    (hgauss : ∀ (X Y : Field B.manifold) p,
      (D.cov X (lift Y)).val p = B.inclusion.differential p ((B.connection.cov X Y).val p) +
        II p (X.val p) (Y.val p))
    (hnormal : ∀ p v w u, inner ℝ (B.ambientVector p u) (A.coordinates p.val (II p v w)) = 0)
    (hh : ∀ p v w, hP.form p v w =
      inner ℝ (A.coordinates p.val v) (A.coordinates p.val w))
    (hD : P202.TorsionMetricData.MetricCompatible P.space.bundle D hP)
    (R : Section P.space.bundle)
    (hR : ∀ p, A.coordinates p.val (R.val p) = p.val)
    (hDR : ∀ (X : Field B.manifold) p,
      A.coordinates p.val ((D.cov X R).val p) = B.ambientVector p (X.val p))
    (X Y : Field B.manifold) (p : Sphere n a),
    A.coordinates p.val (II p (X.val p) (Y.val p)) =
      (-(pairing B.metric p (X.val p) (Y.val p)) / a^2) • p.val := by
  letI := P.space.topology
  intro hP D II lift hlift hgauss hnormal hh hD R hR hDR X Y p
  let V := lift Y
  have hfun : (fun q => hP.form q (V.val q) (R.val q)) = fun _ => (0 : ℝ) := by
    funext q
    calc
      _ = inner ℝ (A.coordinates q.val (V.val q)) (A.coordinates q.val (R.val q)) := hh q _ _
      _ = inner ℝ (B.ambientVector q (Y.val q)) q.val :=
        congrArg₂ (fun (u w : E (n+1)) => inner ℝ u w)
          (congrArg (A.coordinates q.val) (hlift Y q)) (hR q)
      _ = 0 := (real_inner_comm _ _).trans ((B.tangent_range q _).mp ⟨Y.val q, rfl⟩)
  have hz : scalarDerivative B.manifold (fun q => hP.form q (V.val q) (R.val q)) p (X.val p) = 0 :=
    (congrArg (fun f : Sphere n a → ℝ => scalarDerivative B.manifold f p (X.val p)) hfun).trans
      (scalarDerivative_const B.manifold 0 p (X.val p))
  have hpair : inner ℝ (B.ambientVector p (Y.val p)) (B.ambientVector p (X.val p)) =
      pairing B.metric p (X.val p) (Y.val p) := by
    calc
      _ = pairing A.metric p.val (B.inclusion.differential p (Y.val p))
          (B.inclusion.differential p (X.val p)) := (A.metric_standard p.val _ _).symm
      _ = pairing B.metric p (Y.val p) (X.val p) := B.induced p _ _
      _ = _ := B.metric.symmetric p _ _
  have hleft : hP.form p ((D.cov X V).val p) (R.val p) =
      inner ℝ (A.coordinates p.val ((D.cov X V).val p)) p.val :=
    (hh p _ _).trans (congrArg
      (fun z : E (n+1) => inner ℝ (A.coordinates p.val ((D.cov X V).val p)) z) (hR p))
  have hright : hP.form p (V.val p) ((D.cov X R).val p) =
      pairing B.metric p (X.val p) (Y.val p) :=
    (hh p _ _).trans ((congrArg₂ (fun (u w : E (n+1)) => inner ℝ u w)
      (congrArg (A.coordinates p.val) (hlift Y p)) (hDR X p)).trans hpair)
  have hprod : 0 = inner ℝ (A.coordinates p.val ((D.cov X V).val p)) p.val +
      pairing B.metric p (X.val p) (Y.val p) :=
    hz.symm.trans ((hD X V R p).trans (congrArg₂ (fun u w : ℝ => u + w) hleft hright))
  have hdecomp : A.coordinates p.val ((D.cov X V).val p) =
      A.coordinates p.val (B.inclusion.differential p ((B.connection.cov X Y).val p)) +
        A.coordinates p.val (II p (X.val p) (Y.val p)) :=
    (congrArg (A.coordinates p.val) (hgauss X Y p)).trans ((A.coordinates p.val).map_add _ _)
  have htan : inner ℝ (A.coordinates p.val (B.inclusion.differential p ((B.connection.cov X Y).val p))) p.val = 0 :=
    (real_inner_comm _ _).trans ((B.tangent_range p _).mp ⟨_, rfl⟩)
  have hnormalpart : inner ℝ (A.coordinates p.val ((D.cov X V).val p)) p.val =
      inner ℝ (A.coordinates p.val (II p (X.val p) (Y.val p))) p.val := by
    rw [hdecomp, inner_add_left, htan, zero_add]
  have hcoeff : inner ℝ (A.coordinates p.val (II p (X.val p) (Y.val p))) p.val =
      -(pairing B.metric p (X.val p) (Y.val p)) := by
    rw [hnormalpart] at hprod
    linarith only [hprod]
  calc
    _ = (inner ℝ p.val (A.coordinates p.val (II p (X.val p) (Y.val p))) / a^2) • p.val :=
      ambient_normal_eq ha B p _ (hnormal p (X.val p) (Y.val p))
    _ = _ := congrArg (fun r : ℝ => (r / a^2) • p.val) ((real_inner_comm _ _).trans hcoeff)


end SphericalSecondForm

section SphericalRoundCurvature
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.CurvatureData

/-- The round tensor follows from Gauss' equation and the actual radius-sphere
second fundamental form. Only global fields are needed for the geometric inputs. -/
theorem sphere_round_curvature_of_gauss_formula {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Sphere n a)) (g : RiemannianMetric S)
    (T : CurvatureTensor S)
    (II : (p : Sphere n a) → TangentSpace S p → TangentSpace S p → E (n+1))
    (hII : ∀ (X Y : Field S) p, II p (X.val p) (Y.val p) =
      (-(pairing g p (X.val p) (Y.val p)) / a^2) • p.val)
    (hGauss : ∀ (X Y Z V : Field S) p,
      curvatureForm g T p (X.val p) (Y.val p) (Z.val p) (V.val p) =
        inner ℝ (II p (X.val p) (V.val p)) (II p (Y.val p) (Z.val p)) -
        inner ℝ (II p (Y.val p) (V.val p)) (II p (X.val p) (Z.val p))) :
    ∀ p X Y Z, T.val p X Y Z = (a^2)⁻¹ •
      (pairing g p Y Z • X - pairing g p X Z • Y) := by
  have hcalc (X Y Z V : Field S) (p : Sphere n a) :
      curvatureForm g T p (X.val p) (Y.val p) (Z.val p) (V.val p) =
        (a^2)⁻¹ * (pairing g p (X.val p) (V.val p) * pairing g p (Y.val p) (Z.val p) -
          pairing g p (Y.val p) (V.val p) * pairing g p (X.val p) (Z.val p)) := by
    rw [hGauss X Y Z V p, hII X V p, hII Y Z p, hII Y V p, hII X Z p]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp p.property]
    field_simp
  intro p x y z
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p x
  obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p y
  obtain ⟨Z, hZ⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p z
  apply LeviCivita.pairing_ext g p
  intro V
  have h := hcalc X Y Z V p
  rw [hX, hY, hZ] at h
  change curvatureForm g T p x y z (V.val p) = _
  rw [h]
  simp only [pairing, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.sub_left]
  ring

end SphericalRoundCurvature

section SphericalCurvatureAssembly
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

-- Required import: P202.Geometry.GaussCodazziRicci
-- Insert after sphere_round_curvature_of_gauss_formula.
-- Checked standalone against the compiled main and actual GCR implementation.
open P202.SpaceFormData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.GaussWeingartenData
  P202.CurvatureEquationsData
open Set Filter
open scoped _root_.Topology

/-- Gauss' actual curvature equation turns the computed second fundamental
form into the round tensor and sectional curvature, with the source sign. -/
theorem spherical_curvature_of_second_form
    {n : ℕ} {a : ℝ} (ha : 0 < a)
    (B : SphericalModel n a (euclideanModel (n+1)))
    (P : PullbackBundle (tangentBundle (euclideanModel (n+1)).manifold)
      B.manifold Subtype.val)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (W : AdaptedSplitting B.inclusion P hP)
    (G : Geometry B.inclusion P hP W B.metric B.connection D)
    (hmetric : letI := P.space.topology; ∀ p,
      hP.form p = (euclideanModel (n+1)).metric.form p.val)
    (hD : letI := P.space.topology; P202.PullbackData.IsPullback
      (tangentBundle (euclideanModel (n+1)).manifold) (euclideanModel (n+1)).connection
      Subtype.val B.inclusion.smooth P D)
    (hII : letI := P.space.topology; letI := W.orthogonal.right.topology;
      ∀ (X Y : Field B.manifold) p,
      (euclideanModel (n+1)).coordinates p.val (G.B p (X.val p) (Y.val p)).val =
        (-(pairing B.metric p (X.val p) (Y.val p)) / a^2) • p.val)
    (T : CurvatureTensor B.manifold) (hT : RepresentsCurvature B.connection T) :
    (∀ p X Y Z, T.val p X Y Z = (a^2)⁻¹ •
      (pairing B.metric p Y Z • X - pairing B.metric p X Z • Y)) ∧
    ∀ p X Y h, sectionalCurvature B.metric T p X Y h = (a^2)⁻¹ := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  let A := euclideanModel (n+1)
  have hiP : ∀ p v w, hP.form p (B.inclusion.differential p v)
      (B.inclusion.differential p w) = pairing B.metric p v w := by
    intro p v w
    rw [hmetric p]
    exact B.induced p v w
  have hE := GaussCodazziRicci.ambient_equations B.inclusion P hP W B.metric
    B.connection A.connection D B.leviCivita A.leviCivita.1 hiP hD T
    (euclideanCurvatureTensor (n+1)) hT (euclideanCurvatureTensor_represents (n+1)) G
  have hh (p : Sphere n a) (v w : TangentSpace A.manifold p.val) :
      hP.form p v w = inner ℝ (A.coordinates p.val v) (A.coordinates p.val w) := by
    rw [hmetric p]
    exact A.metric_standard p.val v w
  let II (p : Sphere n a) (v w : TangentSpace B.manifold p) : E (n+1) :=
    A.coordinates p.val (G.B p v w).val
  have hGauss : ∀ (X Y Z V : Field B.manifold) p,
      curvatureForm B.metric T p (X.val p) (Y.val p) (Z.val p) (V.val p) =
        inner ℝ (II p (X.val p) (V.val p)) (II p (Y.val p) (Z.val p)) -
        inner ℝ (II p (Y.val p) (V.val p)) (II p (X.val p) (Z.val p)) := by
    intro X Y Z V p
    have h := hE.1 X Y Z V p
    change curvatureForm B.metric T p (X.val p) (Y.val p) (Z.val p) (V.val p) =
      hP.form p 0 (B.inclusion.differential p (V.val p)) +
      hP.form p (G.B p (X.val p) (V.val p)).val (G.B p (Y.val p) (Z.val p)).val -
      hP.form p (G.B p (Y.val p) (V.val p)).val (G.B p (X.val p) (Z.val p)).val at h
    simpa only [hh, map_zero, LinearMap.zero_apply, Pi.zero_apply, inner_zero_left, zero_add, II] using h
  have hround := sphere_round_curvature_of_gauss_formula ha B.manifold B.metric T II hII hGauss
  exact ⟨hround, sectionalCurvature_of_round_formula B.metric T (a^2)⁻¹ hround⟩

/-- The curvature tensor is chosen from the proved intrinsic curvature
construction; the only remaining geometric input is the computed second form. -/
theorem spherical_sectional_curvature_of_second_form
    {n : ℕ} {a : ℝ} (ha : 0 < a)
    (B : SphericalModel n a (euclideanModel (n+1)))
    (P : PullbackBundle (tangentBundle (euclideanModel (n+1)).manifold)
      B.manifold Subtype.val)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (W : AdaptedSplitting B.inclusion P hP)
    (G : Geometry B.inclusion P hP W B.metric B.connection D)
    (hmetric : letI := P.space.topology; ∀ p,
      hP.form p = (euclideanModel (n+1)).metric.form p.val)
    (hD : letI := P.space.topology; P202.PullbackData.IsPullback
      (tangentBundle (euclideanModel (n+1)).manifold) (euclideanModel (n+1)).connection
      Subtype.val B.inclusion.smooth P D)
    (hII : letI := P.space.topology; letI := W.orthogonal.right.topology;
      ∀ (X Y : Field B.manifold) p,
      (euclideanModel (n+1)).coordinates p.val (G.B p (X.val p) (Y.val p)).val =
        (-(pairing B.metric p (X.val p) (Y.val p)) / a^2) • p.val)
 :
    ∃ T : CurvatureTensor B.manifold, RepresentsCurvature B.connection T ∧
      ∀ p X Y h, sectionalCurvature B.metric T p X Y h = (a^2)⁻¹ := by
  obtain ⟨T, hT, _⟩ := CurvatureAlgebra.tensor_exists_unique B.connection
  exact ⟨T, hT, (spherical_curvature_of_second_form ha B P hP D W G hmetric hD hII T hT).2⟩



theorem spherical_geometry_second_form {n : ℕ} {a : ℝ} (ha : 0 < a)
    (B : SphericalModel n a (euclideanModel (n+1)))
    (P : PullbackBundle (tangentBundle (euclideanModel (n+1)).manifold) B.manifold Subtype.val) :
    letI := P.space.topology
    ∀ (hP : SmoothFiberMetric P.space.bundle)
      (D : Connection P.space.bundle)
      (W : AdaptedSplitting B.inclusion P hP)
      (G : Geometry B.inclusion P hP W B.metric B.connection D)
      (hmetric : ∀ p, hP.form p = (euclideanModel (n+1)).metric.form p.val)
      (hDP : P202.PullbackData.IsPullback (tangentBundle (euclideanModel (n+1)).manifold)
        (euclideanModel (n+1)).connection Subtype.val B.inclusion.smooth P D),
    letI := W.orthogonal.right.topology
    ∀ (X Y : Field B.manifold) p,
      (euclideanModel (n+1)).coordinates p.val (G.B p (X.val p) (Y.val p)).val =
        (-(pairing B.metric p (X.val p) (Y.val p)) / a^2) • p.val := by
  letI := P.space.topology
  intro hP D W G hmetric hDP
  letI := W.orthogonal.right.topology
  let A := euclideanModel (n+1)
  have hh (p : Sphere n a) (v w : TangentSpace A.manifold p.val) :
      hP.form p v w = inner ℝ (A.coordinates p.val v) (A.coordinates p.val w) :=
    (congrArg (fun f : LinearMap.BilinForm ℝ (TangentSpace A.manifold p.val) => f v w)
      (hmetric p)).trans (A.metric_standard p.val v w)
  have hDc : P202.TorsionMetricData.MetricCompatible P.space.bundle D hP := by
    intro X s t p
    have hprod := P202.Geometry.TorsionAndMetric.metric_map_product (tangentBundle A.manifold)
      A.metric A.connection A.leviCivita.2 Subtype.val B.inclusion.smooth P D hDP X s t p
    have hf : (fun q => hP.form q (s.val q) (t.val q)) =
        (fun q => A.metric.form q.val (s.val q) (t.val q)) :=
      funext (fun q => congrArg (fun f : LinearMap.BilinForm ℝ (TangentSpace A.manifold q.val) =>
        f (s.val q) (t.val q)) (hmetric q))
    have h1 := congrArg (fun f : LinearMap.BilinForm ℝ (TangentSpace A.manifold p.val) =>
      f ((D.cov X s).val p) (t.val p)) (hmetric p)
    have h2 := congrArg (fun f : LinearMap.BilinForm ℝ (TangentSpace A.manifold p.val) =>
      f (s.val p) ((D.cov X t).val p)) (hmetric p)
    exact (congrArg (fun f : Sphere n a → ℝ => scalarDerivative B.manifold f p (X.val p)) hf).trans
      (hprod.trans (congrArg₂ (fun u v : ℝ => u + v) h1.symm h2.symm))
  obtain ⟨R, hR, hDR⟩ := spherical_position_pullback_exists B P D hDP
  let II := fun p v w => (G.B p v w).val
  have hgauss (X Y : Field B.manifold) (p : Sphere n a) :
      (D.cov X (G.tangentLift Y)).val p =
        B.inclusion.differential p ((B.connection.cov X Y).val p) + II p (X.val p) (Y.val p) := by
    have h := congrArg (fun s : Section P.space.bundle => s.val p) (G.gauss X Y)
    change (D.cov X (G.tangentLift Y)).val p =
      (G.tangentLift (B.connection.cov X Y)).val p + (G.normalLift (G.second X Y)).val p at h
    exact h.trans (congrArg₂ (fun u v : TangentSpace A.manifold p.val => u + v)
      (G.tangentLift_val (B.connection.cov X Y) p)
      ((G.normalLift_val (G.second X Y) p).trans
        (congrArg Subtype.val (G.second_val X Y p))))
  have hn (p : Sphere n a) (v w u : TangentSpace B.manifold p) :
      inner ℝ (B.ambientVector p u) (A.coordinates p.val (II p v w)) = 0 :=
    (hh p (B.inclusion.differential p u) (II p v w)).symm.trans
      ((G.B p v w).property (B.inclusion.differential p u) ⟨u, rfl⟩)
  intro X Y p
  exact spherical_second_form_of_position_derivative ha B P hP D II G.tangentLift
    G.tangentLift_val hgauss hn hh hDc R hR hDR X Y p


/-- The radius-a sphere with its literal induced metric has sectional
curvature a⁻² in the original intrinsic tangent fibers. -/
theorem spherical_curvature {n : ℕ} {a : ℝ} (ha : 0 < a)
    (B : SphericalModel n a (euclideanModel (n+1))) :
    ∃ T : CurvatureTensor B.manifold, RepresentsCurvature B.connection T ∧
      ∀ p X Y h, sectionalCurvature B.metric T p X Y h = (a^2)⁻¹ := by
  let A := euclideanModel (n+1)
  let P := P202.PullbackData.bundle (tangentBundle A.manifold)
    B.manifold Subtype.val B.inclusion.smooth
  letI := P.space.topology
  obtain ⟨hP, D, W, hmetric, hDP, ⟨G⟩⟩ :=
    GaussCodazziRicci.geometry_exists B.metric A.metric Subtype.val B.inclusion B.induced
      B.connection A.connection B.leviCivita A.leviCivita P
  have hII := spherical_geometry_second_form ha B P hP D W G hmetric hDP
  exact spherical_sectional_curvature_of_second_form ha B P hP D W G hmetric hDP hII

end SphericalCurvatureAssembly

/-- The complete spherical conclusions, in the actual induced geometry. -/
theorem spherical_conclusion {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    (B : SphericalModel n a (euclideanModel (n + 1))) : B.Conclusion := by
  exact spherical_conclusion_of_global_geodesics B ha (model_topology n hn a ha).2
    sphereCurve_formula (spherical_curvature ha B) (spherical_global_geodesics ha B)

/-- The Euclidean and spherical stages of the source model theorem. -/
theorem models : modelsType := by
  intro n hn a ha
  exact ⟨euclideanModel n, euclideanModel (n + 1), sphericalModel n a ha,
    euclidean_conclusion n, euclidean_conclusion (n + 1),
    spherical_conclusion hn ha (sphericalModel n a ha)⟩

end P202.Geometry.EuclideanSphericalModels
