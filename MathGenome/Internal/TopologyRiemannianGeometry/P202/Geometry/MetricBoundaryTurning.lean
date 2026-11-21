import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricBoundaryTurning
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneTangentComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ChartRegionStokes
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurveCovariantDerivative
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceBoundaryGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators unitInterval ContDiff
namespace P202.MetricBoundaryTurning
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.BundleData
open P202.ConnectionData P202.MetricData P202.SurfaceBoundaryData
open P202Specs.ChartRegionStokes (OneForm)
open P202Specs.PlanarRegionTopology P202Specs.MetricBoundaryTurning P202Specs.PlaneTurning
universe u
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
theorem scalarDerivative_eq_zero_of_eventually_const (f : M → ℝ) (p : M) (a : ℝ)
    (hf : f =ᶠ[𝓝 p] (fun _ => a)) (v : TangentSpace S p) :
    scalarDerivative S f p v = 0 := by
  let aS : SmoothManifolds.GlobalSmooth S := algebraMap ℝ (SmoothManifolds.GlobalSmooth S) a
  have haS : aS.val =ᶠ[𝓝 p] f := hf.symm
  rw [P202.Geometry.ConnectionForms.scalarDerivative_representative f aS p haS]
  change v.val (SmoothManifolds.globalToGerm S p (algebraMap ℝ (SmoothManifolds.GlobalSmooth S) a)) = 0
  rw [(SmoothManifolds.globalToGerm S p).commutes]
  exact SmoothManifolds.derivation_kills_constants _ v a


theorem orthonormalFrame_coefficient (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) (i : Fin 2) :
    (b.basis p).equivFun v i = pairing g p.val v (b.section_ i p) := by
  have he := (b.basis p).equivFun_symm_apply ((b.basis p).equivFun v)
  rw [LinearEquiv.symm_apply_apply] at he
  symm
  calc
    pairing g p.val v (b.section_ i p) =
        pairing g p.val (∑ k, (b.basis p).equivFun v k • b.section_ k p) (b.section_ i p) := by
      apply congrArg (fun w => pairing g p.val w (b.section_ i p))
      simpa only [b.basis_eq] using he
    _ = (b.basis p).equivFun v i := by
      simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, hon]
      simp

theorem local_metric_derivative_of_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} (hU : IsOpen U)
    (s t : LocalSection (tangentBundle S) U hU) (a : ℝ)
    (hconst : ∀ q : U, pairing g q.val (s.val q) (t.val q) = a)
    (p : U) (v : TangentSpace S p.val) :
    pairing g p.val
        (pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val v)
        (t.val p) +
      pairing g p.val (s.val p)
        (pointDerivative C (SmoothManifolds.SectionExtension.totalSection t.val) p.val v) = 0 := by
  obtain ⟨s', hs⟩ := P202.Geometry.ConnectionForms.exists_section_representative
    (tangentBundle S) U hU (SmoothManifolds.SectionExtension.totalSection s.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ s.property)
    p.val p.property
  obtain ⟨t', ht⟩ := P202.Geometry.ConnectionForms.exists_section_representative
    (tangentBundle S) U hU (SmoothManifolds.SectionExtension.totalSection t.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ t.property)
    p.val p.property
  have hsval : s'.val p.val = s.val p := by
    simpa using hs.self_of_nhds
  have htval : t'.val p.val = t.val p := by
    simpa using ht.self_of_nhds
  have hsD := P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle S) C
    s'.val (SmoothManifolds.SectionExtension.totalSection s.val) p.val
    ⟨s', Filter.Eventually.of_forall (fun _ => rfl)⟩ hs
  have htD := P202.Geometry.ConnectionForms.pointDerivative_congr (tangentBundle S) C
    t'.val (SmoothManifolds.SectionExtension.totalSection t.val) p.val
    ⟨t', Filter.Eventually.of_forall (fun _ => rfl)⟩ ht
  change pointDerivative C s'.val p.val =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val at hsD
  change pointDerivative C t'.val p.val =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection t.val) p.val at htD
  obtain ⟨X, hX⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
    (tangentBundle S) p.val v
  have hconst' : (fun q => pairing g q (s'.val q) (t'.val q)) =ᶠ[𝓝 p.val]
      (fun _ => a) := by
    filter_upwards [hs, ht, hU.mem_nhds p.property] with q hsq htq hq
    rw [hsq, htq]
    simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq] using hconst ⟨q, hq⟩
  have hm := hC X s' t' p.val
  rw [scalarDerivative_eq_zero_of_eventually_const _ _ a hconst'] at hm
  rw [← hsD, ← htD, ← hsval, ← htval, ← hX,
    P202.Geometry.ConnectionForms.pointDerivative_global,
    P202.Geometry.ConnectionForms.pointDerivative_global]
  exact hm.symm

theorem orthonormalFrame_connectionForm_skew (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) (i j : Fin 2) :
    connectionForm C b p i j v = -connectionForm C b p j i v := by
  have hm := local_metric_derivative_of_constant g C hC hU
    ⟨b.section_ j, b.smooth j⟩ ⟨b.section_ i, b.smooth i⟩
    (if j = i then 1 else 0) (fun q => hon q j i) p v
  change pairing g p.val
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val v)
      (b.section_ i p) +
    pairing g p.val (b.section_ j p)
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) p.val v) = 0 at hm
  change (b.basis p).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val v) i =
    -(b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) p.val v) j
  rw [orthonormalFrame_coefficient g b hon p _ i,
    orthonormalFrame_coefficient g b hon p _ j]
  have hsym := g.symmetric p.val (b.section_ j p)
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ i)) p.val v)
  change pairing g p.val (b.section_ j p) _ = pairing g p.val _ (b.section_ j p) at hsym
  rw [hsym] at hm
  linarith

theorem orthonormalFrame_connectionForm_diagonal (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) (i : Fin 2) :
    connectionForm C b p i i v = 0 := by
  linarith [orthonormalFrame_connectionForm_skew g C hC b hon p v i i]

/-- Straight interpolation used for a positive Gram–Schmidt coordinate change. -/
def triangularPath (a b d t : ℝ) : Plane →ₗ[ℝ] Plane :=
  upperTriangular (1 - t + t * a) (t * b) (1 - t + t * d)

theorem diagonalInterpolation_pos {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t + t * a := by
  by_cases ht0 : t = 0
  · simp [ht0]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha)

theorem upperTriangular_injective {a b d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Injective (upperTriangular a b d) := by
  intro v w h
  have h0 := congrArg (fun z : Plane => z 0) h
  have h1 := congrArg (fun z : Plane => z 1) h
  simp only [upperTriangular, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hvw1 : v 1 = w 1 := mul_left_cancel₀ hd h1
  rw [hvw1] at h0
  have hvw0 : v 0 = w 0 := mul_left_cancel₀ ha (add_right_cancel h0)
  ext i
  fin_cases i <;> assumption

theorem triangularPath_injective {a b d t : ℝ} (ha : 0 < a) (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) : Function.Injective (triangularPath a b d t) :=
  upperTriangular_injective (diagonalInterpolation_pos ha ht).ne'
    (diagonalInterpolation_pos hd ht).ne'

@[simp] theorem triangularPath_zero (a b d : ℝ) : triangularPath a b d 0 = LinearMap.id := by
  ext v i
  fin_cases i <;> simp [triangularPath, upperTriangular]

@[simp] theorem triangularPath_one (a b d : ℝ) :
    triangularPath a b d 1 = upperTriangular a b d := by
  simp [triangularPath]

/-- Explicit orientation determinant, including every intermediate map. -/
theorem upperTriangular_area (a b d : ℝ) (v w : Plane) :
    upperTriangular a b d v 0 * upperTriangular a b d w 1 -
      upperTriangular a b d v 1 * upperTriangular a b d w 0 =
        a * d * (v 0 * w 1 - v 1 * w 0) := by
  simp only [upperTriangular, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The determinant multiplier stays positive throughout the interpolation. -/
theorem triangularPath_positive {a d t : ℝ} (ha : 0 < a) (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (1 - t + t * a) * (1 - t + t * d) :=
  mul_pos (diagonalInterpolation_pos ha ht) (diagonalInterpolation_pos hd ht)

/-- Nonzero directions stay nonzero under the whole frame interpolation. -/
theorem triangularPath_ne_zero {a b d t : ℝ} (ha : 0 < a) (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) {v : Plane} (hv : v ≠ 0) :
    triangularPath a b d t v ≠ 0 := by
  intro h
  exact hv (triangularPath_injective ha hd ht (h.trans (map_zero _).symm))

/-- Equality of normalized nonzero vectors is equality up to positive scale. -/
theorem normalize_eq_iff_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    NormedSpace.normalize x = NormedSpace.normalize y ↔
      ∃ r : ℝ, 0 < r ∧ x = r • y := by
  constructor
  · intro h
    refine ⟨‖x‖ / ‖y‖, div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy), ?_⟩
    have hh := congrArg (fun z : E => ‖x‖ • z) h
    rw [NormedSpace.norm_smul_normalize] at hh
    simpa only [NormedSpace.normalize, smul_smul, div_eq_mul_inv] using hh
  · rintro ⟨r, hr, rfl⟩
    exact NormedSpace.normalize_smul_of_pos hr y

/-- An injective linear change cannot create a cusp. This handles independent
one-sided tangents as well as equal tangent directions. -/
theorem linearMap_preserves_noncuspidality
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ₗ[ℝ] F) (hf : Function.Injective f)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : NormedSpace.normalize x ≠ -NormedSpace.normalize y) :
    NormedSpace.normalize (f x) ≠ -NormedSpace.normalize (f y) := by
  have hfx : f x ≠ 0 := fun h => hx (hf (h.trans (map_zero f).symm))
  have hfy : -f y ≠ 0 := neg_ne_zero.mpr
    (fun h => hy (hf (h.trans (map_zero f).symm)))
  intro h
  rw [← NormedSpace.normalize_neg] at h
  obtain ⟨r, hr, he⟩ := (normalize_eq_iff_pos_smul hfx hfy).mp h
  have he' : x = r • (-y) := hf (by simpa using he)
  apply hxy
  rw [he', NormedSpace.normalize_smul_of_pos hr, NormedSpace.normalize_neg]

/-- In particular the entire positive triangular interpolation remains away
from the antipodal branch cut of the short signed corner rotation. -/
theorem triangularPath_preserves_noncuspidality {a b d t : ℝ}
    (ha : 0 < a) (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1)
    {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    NormedSpace.normalize (triangularPath a b d t v) ≠
      -NormedSpace.normalize (triangularPath a b d t w) :=
  linearMap_preserves_noncuspidality _ (triangularPath_injective ha hd ht) hv hw hvw

section FrameHomotopy
variable {X : Type*} [TopologicalSpace X]

/-- Normalization of a continuous nonvanishing vector field. -/
def normalizedMap (v : C(X, Plane)) (hv : ∀ x, v x ≠ 0) : C(X, Plane) where
  toFun x := NormedSpace.normalize (v x)
  continuous_toFun := (v.continuous.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hv x))).smul
    v.continuous

/-- A spatially varying upper triangular frame change on actual vectors. -/
def transformedMap (a b d : C(X, ℝ)) (v : C(X, Plane)) : C(X, Plane) where
  toFun x := upperTriangular (a x) (b x) (d x) (v x)
  continuous_toFun := by
    change Continuous (fun x => !₂[a x * v x 0 + b x * v x 1, d x * v x 1])
    fun_prop

theorem transformedMap_ne_zero (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0) (x : X) :
    transformedMap a b d v x ≠ 0 := by
  intro h
  exact hv x (upperTriangular_injective (ha x).ne' (hd x).ne'
    (h.trans (map_zero _).symm))

/-- The actual normalization homotopy for a positive triangular frame field.
Taking X to be the parameter circle gives a free homotopy of unit-vector
loops. This statement does not yet identify the transformed corner paths
with their metric short-rotation replacements. -/
def triangularHomotopy (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0) :
    ContinuousMap.Homotopy (normalizedMap v hv)
      (normalizedMap (transformedMap a b d v) (transformedMap_ne_zero a b d v ha hd hv)) where
  toFun p := NormedSpace.normalize (triangularPath (a p.2) (b p.2) (d p.2) p.1 (v p.2))
  continuous_toFun := by
    have hc : Continuous (fun p : unitInterval × X =>
        triangularPath (a p.2) (b p.2) (d p.2) p.1 (v p.2)) := by
      change Continuous (fun p : unitInterval × X =>
        !₂[(1 - (p.1 : ℝ) + (p.1 : ℝ) * a p.2) * v p.2 0 +
          ((p.1 : ℝ) * b p.2) * v p.2 1,
          (1 - (p.1 : ℝ) + (p.1 : ℝ) * d p.2) * v p.2 1])
      fun_prop
    exact (hc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr
      (triangularPath_ne_zero (ha p.2) (hd p.2) p.1.property (hv p.2)))).smul hc
  map_zero_left x := by
    change NormedSpace.normalize (triangularPath (a x) (b x) (d x) 0 (v x)) =
      NormedSpace.normalize (v x)
    rw [triangularPath_zero]
    rfl
  map_one_left x := by simp [normalizedMap, transformedMap]

/-- The homotopy stays in the unit circle, not merely in the whole plane. -/
theorem triangularHomotopy_unit (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0)
    (p : unitInterval × X) : ‖triangularHomotopy a b d v ha hd hv p‖ = 1 :=
  NormedSpace.norm_normalize
    (triangularPath_ne_zero (ha p.2) (hd p.2) p.1.property (hv p.2))

end FrameHomotopy

section UnitLoops
open P202Specs.PlaneTurning

lemma unitLoop_ne_zero (T : UnitDirectionLoop) (t : unitInterval) : T.map t ≠ 0 := by
  intro h
  have hu := T.unit t
  simpa [h] using hu

/-- A genuine closed unit-direction loop after a positive triangular frame
change whose coefficients agree at the closing parameter. -/
def triangularLoop (T : UnitDirectionLoop) (a b d : C(unitInterval, ℝ))
    (ha : ∀ t, 0 < a t) (hd : ∀ t, 0 < d t)
    (hclose : a 1 = a 0 ∧ b 1 = b 0 ∧ d 1 = d 0) : UnitDirectionLoop where
  map := normalizedMap (transformedMap a b d T.map)
    (transformedMap_ne_zero a b d T.map ha hd (unitLoop_ne_zero T))
  unit t := NormedSpace.norm_normalize
    (transformedMap_ne_zero a b d T.map ha hd (unitLoop_ne_zero T) t)
  closed := by
    change NormedSpace.normalize (upperTriangular (a 1) (b 1) (d 1) (T.map 1)) =
      NormedSpace.normalize (upperTriangular (a 0) (b 0) (d 0) (T.map 0))
    rw [hclose.1, hclose.2.1, hclose.2.2, T.closed]

/-- The closedness and unit-norm requirements of the upstream winding API
hold along the entire straight frame interpolation, including its endpoints. -/
def triangularLoopHomotopy (T : UnitDirectionLoop) (a b d : C(unitInterval, ℝ))
    (ha : ∀ t, 0 < a t) (hd : ∀ t, 0 < d t)
    (hclose : a 1 = a 0 ∧ b 1 = b 0 ∧ d 1 = d 0) :
    UnitDirectionHomotopy T (triangularLoop T a b d ha hd hclose) where
  map := (triangularHomotopy a b d T.map ha hd (unitLoop_ne_zero T)).toContinuousMap
  unit t u := triangularHomotopy_unit a b d T.map ha hd (unitLoop_ne_zero T) (t,u)
  at_zero t := by
    change NormedSpace.normalize (triangularPath (a t) (b t) (d t) 0 (T.map t)) = _
    rw [triangularPath_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (T.unit t)
  at_one t := by
    change NormedSpace.normalize (triangularPath (a t) (b t) (d t) 1 (T.map t)) = _
    rw [triangularPath_one]
    rfl
  closed t := by
    change NormedSpace.normalize (triangularPath (a 1) (b 1) (d 1) t (T.map 1)) =
      NormedSpace.normalize (triangularPath (a 0) (b 0) (d 0) t (T.map 0))
    rw [hclose.1, hclose.2.1, hclose.2.2, T.closed]

/-- Hence the actual circle winding is unchanged. To apply this to literal
metric short rotations one must additionally compare the corner paths. -/
theorem triangularLoop_winding (o : Orientation ℝ Plane (Fin 2))
    (T : UnitDirectionLoop) (a b d : C(unitInterval, ℝ))
    (ha : ∀ t, 0 < a t) (hd : ∀ t, 0 < d t)
    (hclose : a 1 = a 0 ∧ b 1 = b 0 ∧ d 1 = d 0) :
    P202Specs.PlaneTangentComparison.winding o T =
      P202Specs.PlaneTangentComparison.winding o (triangularLoop T a b d ha hd hclose) :=
  P202.PlaneTangentComparison.homotopyWinding o T _
    (triangularLoopHomotopy T a b d ha hd hclose)

end UnitLoops

section ShortRotationTransport
open _root_.Topology

lemma noncuspidal_oangle_ne_pi (o : Orientation ℝ Plane (Fin 2))
    {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (hn : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    o.oangle v w ≠ (Real.pi : Real.Angle) := by
  intro h
  have hr := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
  have he := hr.inv_norm_smul_eq hv (neg_ne_zero.mpr hw)
  exact hn (by simpa only [NormedSpace.normalize, norm_neg, smul_neg] using he)

/-- Literal short rotations between continuously varying noncuspidal directions
are continuous jointly in the direction parameter and the rotation parameter. -/
def shortRotationFamily {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x)) :
    C(X × unitInterval, Plane) where
  toFun z := o.rotation ((z.2 : ℝ) * (o.oangle (v z.1) (w z.1)).toReal : ℝ)
    (NormedSpace.normalize (v z.1))
  continuous_toFun := by
    have ha : Continuous (fun x : X => (o.oangle (v x) (w x)).toReal) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact ContinuousAt.comp (f := fun y : X => (v y, w y))
        (P202.PlaneTangentComparison.short_angle_continuousAt o (hv x) (hw x)
          (noncuspidal_oangle_ne_pi o (hv x) (hw x) (hn x)))
        (v.continuous.prodMk w.continuous).continuousAt
    have hnrm : Continuous (fun x : X => NormedSpace.normalize (v x)) :=
      (normalizedMap v hv).continuous
    simp only [Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
    have harg : Continuous (fun z : X × unitInterval =>
        (z.2 : ℝ) * (o.oangle (v z.1) (w z.1)).toReal) :=
      (continuous_subtype_val.comp continuous_snd).mul (ha.comp continuous_fst)
    exact ((Real.continuous_cos.comp harg).smul (hnrm.comp continuous_fst)).add
      ((Real.continuous_sin.comp harg).smul
        (o.rightAngleRotation.continuous.comp (hnrm.comp continuous_fst)))

lemma shortRotationFamily_unit {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x))
    (z : X × unitInterval) :
    ‖shortRotationFamily o v w hv hw hn z‖ = 1 := by
  change ‖o.rotation _ (NormedSpace.normalize (v z.1))‖ = 1
  rw [LinearIsometryEquiv.norm_map]
  exact NormedSpace.norm_normalize (hv z.1)

lemma shortRotationFamily_start {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x)) (x : X) :
    shortRotationFamily o v w hv hw hn (x, 0) = NormedSpace.normalize (v x) := by
  simp [shortRotationFamily, o.rotation_zero]

lemma shortRotationFamily_end {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (v w : C(X, Plane))
    (hv : ∀ x, v x ≠ 0) (hw : ∀ x, w x ≠ 0)
    (hn : ∀ x, NormedSpace.normalize (v x) ≠ -NormedSpace.normalize (w x)) (x : X) :
    shortRotationFamily o v w hv hw hn (x, 1) = NormedSpace.normalize (w x) := by
  have hangle : o.oangle (NormedSpace.normalize (v x)) (NormedSpace.normalize (w x)) =
      o.oangle (v x) (w x) := by
    rw [NormedSpace.normalize, NormedSpace.normalize]
    rw [o.oangle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr (hv x))),
      o.oangle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr (hw x)))]
  change o.rotation ((1 : ℝ) * (o.oangle (v x) (w x)).toReal : ℝ) _ = _
  rw [one_mul, Real.Angle.coe_toReal, ← hangle]
  exact (o.rotation_oangle_eq_iff_norm_eq _ _).mpr
    ((NormedSpace.norm_normalize (hv x)).trans (NormedSpace.norm_normalize (hw x)).symm)

/-- A positive triangular map cannot turn a nonzero vector through pi:
its diagonal entries are positive, so it has no negative real eigenvalue. -/
lemma upperTriangular_self_noncuspidal {a b d : ℝ}
    (ha : 0 < a) (hd : 0 < d) {v : Plane} (hv : v ≠ 0) :
    NormedSpace.normalize v ≠ -NormedSpace.normalize (upperTriangular a b d v) := by
  have hfv : upperTriangular a b d v ≠ 0 := by
    intro h
    exact hv (upperTriangular_injective ha.ne' hd.ne' (h.trans (map_zero _).symm))
  intro h
  rw [← NormedSpace.normalize_neg] at h
  obtain ⟨r, hr, he⟩ := (normalize_eq_iff_pos_smul hv (neg_ne_zero.mpr hfv)).mp h
  have h0 := congrArg (fun z : Plane => z 0) he
  have h1 := congrArg (fun z : Plane => z 1) he
  simp only [upperTriangular, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  have hv1 : v 1 = 0 := by
    have hp : (1 + r * d) * v 1 = 0 := by nlinarith [h1]
    exact (mul_eq_zero.mp hp).resolve_left (by positivity)
  have hv0 : v 0 = 0 := by
    rw [hv1] at h0
    have hp : (1 + r * a) * v 0 = 0 := by nlinarith [h0]
    exact (mul_eq_zero.mp hp).resolve_left (by positivity)
  apply hv
  ext i
  fin_cases i <;> assumption

lemma triangularPath_self_noncuspidal {a b d : ℝ}
    (ha : 0 < a) (hd : 0 < d) {v : Plane} (hv : v ≠ 0) (t : unitInterval) :
    NormedSpace.normalize v ≠ -NormedSpace.normalize (triangularPath a b d t v) :=
  upperTriangular_self_noncuspidal (diagonalInterpolation_pos ha t.property)
    (diagonalInterpolation_pos hd t.property) hv

/-- The path of an actual nonzero vector under the straight frame change. -/
def triangularVectorPath (a b d : ℝ) (v : Plane) : C(unitInterval, Plane) :=
  ⟨fun t => triangularPath a b d t v, by
    change Continuous (fun t : unitInterval =>
      !₂[(1 - (t : ℝ) + (t : ℝ) * a) * v 0 + ((t : ℝ) * b) * v 1,
        (1 - (t : ℝ) + (t : ℝ) * d) * v 1])
    fun_prop⟩

/-- Principal turns under a positive triangular frame change differ by the
endpoint direction corrections. No winding number is assumed in this identity. -/
lemma upperTriangular_corner_correction (o : Orientation ℝ Plane (Fin 2))
    {a b d : ℝ} (ha : 0 < a) (hd : 0 < d) {v w : Plane}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hn : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    (o.oangle (upperTriangular a b d v) (upperTriangular a b d w)).toReal =
      (o.oangle v w).toReal + (o.oangle w (upperTriangular a b d w)).toReal -
        (o.oangle v (upperTriangular a b d v)).toReal := by
  let V := triangularVectorPath a b d v
  let W := triangularVectorPath a b d w
  have hV : ∀ s, V s ≠ 0 := fun s => triangularPath_ne_zero ha hd s.property hv
  have hW : ∀ s, W s ≠ 0 := fun s => triangularPath_ne_zero ha hd s.property hw
  have hVW : ∀ s, NormedSpace.normalize (V s) ≠ -NormedSpace.normalize (W s) :=
    fun s => triangularPath_preserves_noncuspidality ha hd s.property hv hw hn
  have hcv : Continuous (fun s => (o.oangle v (V s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun t => (v, V t))
      (P202.PlaneTangentComparison.short_angle_continuousAt o hv (hV s)
        (noncuspidal_oangle_ne_pi o hv (hV s)
          (triangularPath_self_noncuspidal ha hd hv s)))
      (continuous_const.prodMk V.continuous).continuousAt
  have hcw : Continuous (fun s => (o.oangle w (W s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun t => (w, W t))
      (P202.PlaneTangentComparison.short_angle_continuousAt o hw (hW s)
        (noncuspidal_oangle_ne_pi o hw (hW s)
          (triangularPath_self_noncuspidal ha hd hw s)))
      (continuous_const.prodMk W.continuous).continuousAt
  have hcVW : Continuous (fun s => (o.oangle (V s) (W s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun t => (V t, W t))
      (P202.PlaneTangentComparison.short_angle_continuousAt o (hV s) (hW s)
        (noncuspidal_oangle_ne_pi o (hV s) (hW s) (hVW s)))
      (V.continuous.prodMk W.continuous).continuousAt
  let D : C(unitInterval, ℝ) :=
    ⟨fun s => (o.oangle (V s) (W s)).toReal - (o.oangle v w).toReal -
      (o.oangle w (W s)).toReal + (o.oangle v (V s)).toReal,
      ((hcVW.sub continuous_const).sub hcw).add hcv⟩
  have hD (s : unitInterval) : (D s : Real.Angle) = 0 := by
    change (((o.oangle (V s) (W s)).toReal - (o.oangle v w).toReal -
      (o.oangle w (W s)).toReal + (o.oangle v (V s)).toReal : ℝ) : Real.Angle) = 0
    rw [Real.Angle.coe_add, Real.Angle.coe_sub, Real.Angle.coe_sub]
    simp only [Real.Angle.coe_toReal]
    have hx := o.oangle_add hv hw (hW s)
    have hy := o.oangle_add hv (hV s) (hW s)
    rw [← hx] at hy
    have hz : o.oangle (V s) (W s) =
        o.oangle v w + o.oangle w (W s) - o.oangle v (V s) := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using hy
    rw [hz]
    abel
  have he := P202.PlaneTurning.radianCovering.const_of_comp D.continuous
    (fun s t => (hD s).trans (hD t).symm) (0 : unitInterval) 1
  have h0 : D 0 = 0 := by
    simp [D, V, W, triangularVectorPath, triangularPath_zero]
  have h1 : D 1 = 0 := he.symm.trans h0
  change (o.oangle (triangularPath a b d 1 v) (triangularPath a b d 1 w)).toReal -
    (o.oangle v w).toReal - (o.oangle w (triangularPath a b d 1 w)).toReal +
    (o.oangle v (triangularPath a b d 1 v)).toReal = 0 at h1
  rw [triangularPath_one] at h1
  linarith

/-- The canonical continuous real correction to the vector angle under a
positive triangular field of frames. -/
def triangularAngleCorrection {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0) : C(X, ℝ) where
  toFun x := (o.oangle (v x) (upperTriangular (a x) (b x) (d x) (v x))).toReal
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun y => (v y, transformedMap a b d v y))
      (P202.PlaneTangentComparison.short_angle_continuousAt o (hv x)
        (transformedMap_ne_zero a b d v ha hd hv x)
        (noncuspidal_oangle_ne_pi o (hv x)
          (transformedMap_ne_zero a b d v ha hd hv x)
          (upperTriangular_self_noncuspidal (ha x) (hd x) (hv x))))
      (v.continuous.prodMk (transformedMap a b d v).continuous).continuousAt

/-- Adding the continuous correction transports any real angle lift to the
literal transformed vector directions. -/
lemma triangularAngleCorrection_lift {X : Type*} [TopologicalSpace X]
    (o : Orientation ℝ Plane (Fin 2)) (a b d : C(X, ℝ)) (v : C(X, Plane))
    (ha : ∀ x, 0 < a x) (hd : ∀ x, 0 < d x) (hv : ∀ x, v x ≠ 0)
    (r : Plane) (hr : r ≠ 0) (θ : C(X, ℝ))
    (hθ : ∀ x, (θ x : Real.Angle) = o.oangle r (v x)) (x : X) :
    ((θ x + triangularAngleCorrection o a b d v ha hd hv x : ℝ) : Real.Angle) =
      o.oangle r (upperTriangular (a x) (b x) (d x) (v x)) := by
  rw [Real.Angle.coe_add, hθ]
  change o.oangle r (v x) +
    (((o.oangle (v x) (upperTriangular (a x) (b x) (d x) (v x))).toReal : ℝ) :
      Real.Angle) = _
  rw [Real.Angle.coe_toReal]
  exact o.oangle_add hr (hv x) (transformedMap_ne_zero a b d v ha hd hv x)

/-- Smooth angle increments plus literal short corner turns are invariant
under a positive triangular frame field that agrees at each joined endpoint.
The continuous angle correction above provides the corrected angle choices. -/
lemma upperTriangular_totalTurning_invariant {ι : Type*} [Fintype ι]
    (o : Orientation ℝ Plane (Fin 2)) (rotateIndex : Equiv.Perm ι)
    (v w : ι → Plane) (hv : ∀ i : ι, v i ≠ 0) (hw : ∀ i : ι, w i ≠ 0)
    (hn : ∀ i : ι, NormedSpace.normalize (w i) ≠ -NormedSpace.normalize (v (rotateIndex i)))
    (a0 b0 d0 a1 b1 d1 : ι → ℝ)
    (ha1 : ∀ i : ι, 0 < a1 i) (hd1 : ∀ i : ι, 0 < d1 i)
    (hjoin : ∀ i : ι, a1 i = a0 (rotateIndex i) ∧ b1 i = b0 (rotateIndex i) ∧ d1 i = d0 (rotateIndex i))
    (start finish : ι → ℝ) :
    (∑ i : ι, ((finish i + (o.oangle (w i) (upperTriangular (a1 i) (b1 i) (d1 i) (w i))).toReal) -
      (start i + (o.oangle (v i) (upperTriangular (a0 i) (b0 i) (d0 i) (v i))).toReal) +
      (o.oangle (upperTriangular (a1 i) (b1 i) (d1 i) (w i))
        (upperTriangular (a1 i) (b1 i) (d1 i) (v (rotateIndex i)))).toReal)) =
      ∑ i : ι, (finish i - start i + (o.oangle (w i) (v (rotateIndex i))).toReal) := by
  classical
  let δ : ι → ℝ := fun i =>
    (o.oangle (v i) (upperTriangular (a0 i) (b0 i) (d0 i) (v i))).toReal
  have he (i : ι) :
      (finish i + (o.oangle (w i) (upperTriangular (a1 i) (b1 i) (d1 i) (w i))).toReal) -
      (start i + (o.oangle (v i) (upperTriangular (a0 i) (b0 i) (d0 i) (v i))).toReal) +
      (o.oangle (upperTriangular (a1 i) (b1 i) (d1 i) (w i))
        (upperTriangular (a1 i) (b1 i) (d1 i) (v (rotateIndex i)))).toReal =
      (finish i - start i + (o.oangle (w i) (v (rotateIndex i))).toReal) +
        (δ (rotateIndex i) - δ i) := by
    rw [upperTriangular_corner_correction o (ha1 i) (hd1 i) (hw i) (hv (rotateIndex i)) (hn i)]
    rw [(hjoin i).1, (hjoin i).2.1, (hjoin i).2.2]
    dsimp [δ]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp rotateIndex δ, sub_self, add_zero]

end ShortRotationTransport

/-- Every boundary arc in a presentation is an arc of the original region. -/
theorem mappedAngle_bounds {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [Fact (Module.finrank ℝ F = 2)]
    (o : Orientation ℝ F (Fin 2)) (f : Plane →ₗ[ℝ] F)
    (hf : Function.Injective f) {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : NormedSpace.normalize v ≠ -NormedSpace.normalize w) :
    -Real.pi < (o.oangle (f v) (f w)).toReal ∧
      (o.oangle (f v) (f w)).toReal < Real.pi := by
  have hfv : f v ≠ 0 := fun h => hv (hf (h.trans (map_zero _).symm))
  have hfw : f w ≠ 0 := fun h => hw (hf (h.trans (map_zero _).symm))
  have hn := linearMap_preserves_noncuspidality f hf hv hw hvw
  have hpi : o.oangle (f v) (f w) ≠ (Real.pi : Real.Angle) := by
    intro h
    have hr := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
    have he := hr.inv_norm_smul_eq hfv (neg_ne_zero.mpr hfw)
    exact hn (by simpa only [NormedSpace.normalize, norm_neg, smul_neg] using he)
  exact ⟨Real.Angle.neg_pi_lt_toReal _,
    (Real.Angle.toReal_le_pi _).lt_of_ne
      (fun h => hpi (Real.Angle.toReal_eq_pi_iff.mp h))⟩

/-- Noncuspidality is retained by the actual inverse chart differential and
the actual Riemannian norm, at the common endpoint of each pair of arcs. -/
theorem arcIntegral_eq_parameterIntegral {c : RegularJordanCurve}
    (A : ArcPresentation c) (j : Fin A.count) (omega : OneForm) :
    (∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t)) =
      ∫ y in A.time j.castSucc..A.time j.succ,
        omega (realLift c.parametrization y) (deriv (realLift c.parametrization) y) := by
  let a := A.time j.castSucc
  let b := A.time j.succ
  let d := b - a
  have hab : a < b := A.strictMono j.castSucc_lt_succ
  have hd : 0 < d := sub_pos.mpr hab
  let f : ℝ → Plane := fun y => A.arc j ((y - a) / d)
  have he : EqOn f (realLift c.parametrization) (Ioo a b) := by
    intro y hy
    have ht : (y - a) / d ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hy.1.le) hd.le
      · exact (div_le_one hd).mpr (by dsimp [d]; linarith [hy.2])
    change A.arc j ((y - a) / d) = _
    rw [A.agrees j _ ht]
    congr 1
    change a + d * ((y - a) / d) = y
    field_simp
    ring
  have hder (y : ℝ) (hy : y ∈ Ioo a b) :
      deriv (realLift c.parametrization) y = d⁻¹ • velocity A j ((y - a) / d) := by
    obtain ⟨δ, hδ, hsm⟩ := A.smooth j
    have ht : (y - a) / d ∈ Ioo (-δ) (1 + δ) := by
      have ht0 : 0 < (y - a) / d := div_pos (sub_pos.mpr hy.1) hd
      have ht1 : (y - a) / d < 1 := (div_lt_one hd).mpr (by dsimp [d]; linarith [hy.2])
      constructor <;> linarith
    have hA := (hsm.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
    have hf : HasDerivAt f (d⁻¹ • velocity A j ((y - a) / d)) y := by
      convert! hA.hasDerivAt.scomp y
        (((hasDerivAt_id y).sub_const a).mul_const d⁻¹) using 1
      simp [velocity, div_eq_mul_inv]
    exact (he.deriv isOpen_Ioo hy).symm.trans hf.deriv
  have hchange :
      (∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t)) =
      d * ∫ t in (0 : ℝ)..1,
        omega (realLift c.parametrization (a + d * t))
          (deriv (realLift c.parametrization) (a + d * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    have hy : a + d * t ∈ Ioo a b := by
      constructor
      · linarith [mul_pos hd ht.1]
      · have hdt : d * t < d := mul_lt_of_lt_one_right hd ht.2
        dsimp [d] at hdt
        linarith
    dsimp only
    rw [hder _ hy]
    have harg : (a + d * t - a) / d = t := by field_simp; ring
    rw [harg, ← A.agrees j t ⟨ht.1.le, ht.2.le⟩]
    simp only [map_smul, smul_eq_mul]
    field_simp
  rw [hchange]
  have hi := intervalIntegral.smul_integral_comp_add_mul
    (fun y => omega (realLift c.parametrization y) (deriv (realLift c.parametrization) y))
    (a := (0 : ℝ)) (b := (1 : ℝ)) d a
  simpa [smul_eq_mul, d] using hi


/-- A finite positive partition of a period splits an integrable function. -/
theorem integral_eq_sum_presentation {c : RegularJordanCurve} (A : ArcPresentation c)
    {f : ℝ → ℝ} (hint : IntervalIntegrable f volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t) =
      ∑ j : Fin A.count, ∫ t in A.time j.castSucc..A.time j.succ, f t := by
  have htime (k : Fin (A.count + 1)) : A.time k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← A.first]
      exact A.strictMono.monotone (Fin.zero_le k)
    · rw [← A.last]
      exact A.strictMono.monotone (Fin.le_last k)
  have hi (k : Fin (A.count + 1)) : IntervalIntegrable f volume 0 (A.time k) :=
    hint.mono_set (uIcc_subset_uIcc (by simp)
      (by simpa only [uIcc_of_le zero_le_one] using htime k))
  let F : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, f t
  have harc (j : Fin A.count) :
      (∫ t in A.time j.castSucc..A.time j.succ, f t) =
        F (A.time j.succ) - F (A.time j.castSucc) :=
    (intervalIntegral.integral_interval_sub_left (hi j.succ) (hi j.castSucc)).symm
  simp_rw [harc]
  rw [Finset.sum_sub_distrib]
  have hleft := Fin.sum_univ_succ (fun k : Fin (A.count + 1) => F (A.time k))
  have hright := Fin.sum_univ_castSucc (fun k : Fin (A.count + 1) => F (A.time k))
  simp only [A.first, A.last, F, intervalIntegral.integral_same] at hleft hright
  linarith


/-- The masked original component integral equals the sum over every actual
arc presentation. Only a finite set of corner parameters is discarded. -/
theorem componentIntegral_eq_arcs_of_integrable {q : RegularJordanCurve}
    (A : ArcPresentation q) (omega : OneForm)
    (hint : IntervalIntegrable (P202Specs.ChartRegionStokes.boundaryIntegrand omega q)
      volume 0 1) :
    P202Specs.ChartRegionStokes.componentIntegral omega q =
      ∑ j, ∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t) := by
  have hint' := hint.congr_ae (by
    simpa only [uIoc_of_le zero_le_one] using
      P202.ChartRegionStokes.boundaryIntegrand_ae_eq omega q)
  rw [P202.ChartRegionStokes.componentIntegral_eq_unmasked,
    integral_eq_sum_presentation A hint']
  exact Finset.sum_congr rfl (fun j _ => (arcIntegral_eq_parameterIntegral A j omega).symm)


section AngleLiftDifferentiation
/-- A continuous real angle is differentiable whenever its sine and cosine
are differentiable. This is local and requires no preselected principal branch. -/
theorem hasDerivAt_angle_of_cos_sin {θ : ℝ → ℝ} {t c' s' : ℝ}
    (hcont : ContinuousAt θ t)
    (hcos : HasDerivAt (fun s => Real.cos (θ s)) c' t)
    (hsin : HasDerivAt (fun s => Real.sin (θ s)) s' t) :
    HasDerivAt θ (Real.cos (θ t) * s' - Real.sin (θ t) * c') t := by
  let f : ℝ → ℝ := fun s => Real.sin (θ s) * Real.cos (θ t) -
    Real.cos (θ s) * Real.sin (θ t)
  have hf : HasDerivAt f (Real.cos (θ t) * s' - Real.sin (θ t) * c') t := by
    convert (hsin.mul_const (Real.cos (θ t))).sub (hcos.mul_const (Real.sin (θ t))) using 1 <;> ring
  have hft : f t = 0 := by dsimp [f]; ring
  have ha : HasDerivAt Real.arcsin 1 (f t) := by
    rw [hft]
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  have hg := (ha.comp t hf).add_const (θ t)
  simp only [one_mul] at hg
  apply hg.congr_of_eventuallyEq
  have hn : ∀ᶠ s in 𝓝 t, θ s - θ t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    (hcont.sub_const (θ t)).eventually
      (isOpen_Ioo.mem_nhds (by simp only [sub_self, mem_Ioo]; constructor <;> linarith [Real.pi_pos]))
  filter_upwards [hn] with s hs
  dsimp [f]
  rw [← Real.sin_sub, Real.arcsin_sin hs.1.le hs.2.le]
  ring

/-- The same local inverse argument works for one-sided arc endpoints. -/
theorem hasDerivWithinAt_angle_of_cos_sin {θ : ℝ → ℝ} {J : Set ℝ} {t c' s' : ℝ}
    (hcont : ContinuousWithinAt θ J t)
    (hcos : HasDerivWithinAt (fun s => Real.cos (θ s)) c' J t)
    (hsin : HasDerivWithinAt (fun s => Real.sin (θ s)) s' J t) :
    HasDerivWithinAt θ (Real.cos (θ t) * s' - Real.sin (θ t) * c') J t := by
  let f : ℝ → ℝ := fun s => Real.sin (θ s) * Real.cos (θ t) -
    Real.cos (θ s) * Real.sin (θ t)
  have hf : HasDerivWithinAt f (Real.cos (θ t) * s' - Real.sin (θ t) * c') J t := by
    convert (hsin.mul_const (Real.cos (θ t))).sub (hcos.mul_const (Real.sin (θ t))) using 1 <;> ring
  have hft : f t = 0 := by dsimp [f]; ring
  have ha : HasDerivAt Real.arcsin 1 (f t) := by
    rw [hft]
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  have hg := (ha.comp_hasDerivWithinAt t hf).add_const (θ t)
  simp only [one_mul] at hg
  apply hg.congr_of_eventuallyEq _ (by change θ t = Real.arcsin (f t) + θ t; rw [hft, Real.arcsin_zero, zero_add])
  have hn : ∀ᶠ s in 𝓝[J] t, θ s - θ t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    (hcont.sub_const (θ t)).eventually
      (isOpen_Ioo.mem_nhds (by simp only [sub_self, mem_Ioo]; constructor <;> linarith [Real.pi_pos]))
  filter_upwards [hn] with s hs
  dsimp [f]
  rw [← Real.sin_sub, Real.arcsin_sin hs.1.le hs.2.le]
  ring

end AngleLiftDifferentiation

section IntrinsicBoundaryCalculus
open scoped RealInnerProductSpace
open SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
open P202.CurveConnectionData

/-- Actual positive orthonormal tangent vectors have the prescribed rotation. -/
theorem rotation_of_positive_orthonormal_pair (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (X Y : TangentSpace S p)
    (hXX : pairing g p X X = 1) (hYY : pairing g p Y Y = 1)
    (hXY : pairing g p X Y = 0)
    (hpos : PositiveBoundaryOrientation o p X Y) :
    rotation g o p X = Y := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let q := planeOrientation g o p
  have hTT : ⟪X, X⟫ = 1 := hXX
  have hNN : ⟪Y, Y⟫ = 1 := hYY
  have hTN : ⟪X, Y⟫ = 0 := hXY
  have ha : 0 < q.areaForm X Y := (P202.Geometry.SurfaceBoundaryGeometry.orientation_bridge g p o X Y).mp hpos
  have he := q.inner_sq_add_areaForm_sq X Y
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hTT, hNN, hTN] at he
  have ha1 : q.areaForm X Y = 1 := by nlinarith
  have hJN : ⟪q.rightAngleRotation X, Y⟫ = 1 := by
    rw [q.inner_rightAngleRotation_left, ha1]
  have hNJ : ⟪Y, q.rightAngleRotation X⟫ = 1 := by rw [real_inner_comm]; exact hJN
  have hz : ⟪Y - q.rightAngleRotation X, Y - q.rightAngleRotation X⟫ = 0 := by
    rw [inner_sub_sub_self, hNN, hNJ, hJN, q.inner_comp_rightAngleRotation, hTT]
    norm_num
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp hz)).symm

open SmoothManifolds.BundleData

theorem orthonormalFrame_rotation_first (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0)
    (p : U)
    (hpos : PositiveBoundaryOrientation o p.val (b.section_ 0 p) (b.section_ 1 p)) :
    rotation g o p.val (b.section_ 0 p) = b.section_ 1 p := by
  exact rotation_of_positive_orthonormal_pair g o p.val _ _
    (by simpa using hon p 0 0) (by simpa using hon p 1 1)
    (by simpa using hon p 0 1) hpos


/-- The actual intrinsic curve derivative in an orthonormal frame has the
moving-frame coefficient θ′ + Γ₁₀(γ′). The coefficient hypothesis is local at
the parameter, so it applies to genuine tangent-angle lifts on each smooth arc. -/
theorem frame_trig_covariantDerivative
    (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    (hdiag : ∀ i : Fin 2, connectionForm C b ⟨c t, hp⟩ i i V = 0)
    (hskew : connectionForm C b ⟨c t, hp⟩ 0 1 V =
      -connectionForm C b ⟨c t, hp⟩ 1 0 V)
    {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' t)
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)])) :
    covariantDerivative C c f t =
      (θ' + connectionForm C b ⟨c t, hp⟩ 1 0 V) •
        ((-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
          Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩) := by
  let v' : Euclidean 2 := ![-Real.sin (θ t) * θ', Real.cos (θ t) * θ']
  have hv : HasDerivAt (coefficientsAlong b c f) v' t := by
    have hh : HasDerivAt (fun s => ![Real.cos (θ s), Real.sin (θ s)]) v' t := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact hθ.cos
      · exact hθ.sin
    exact hh.congr_of_eventuallyEq hcoeff
  have hD : HasCovariantDerivativeAt C c f t
      (frameDerivative C b c f t hp V v') :=
    ⟨V, hV, U, hU, b, hp, v', hv.hasDerivWithinAt, rfl⟩
  dsimp only [covariantDerivative]
  rw [P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq C
    (mem_univ t) (uniqueDiffWithinAt_univ) hD]
  apply (b.basis ⟨c t, hp⟩).equivFun.injective
  simp only [frameDerivative, LinearEquiv.apply_symm_apply, map_smul, map_add]
  have hfval := hcoeff.eq_of_nhds
  rw [hfval]
  ext i
  fin_cases i <;>
    simp [v', Matrix.mulVec, dotProduct, Fin.sum_univ_two, connectionMatrix,
      ← b.basis_eq, hdiag, hskew] <;> ring

/-- The positive-frame rotation acts on the actual field, as read from its
literal frame coefficients. -/
theorem frame_trig_rotation (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {θ : ℝ → ℝ}
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)]))
    (hrot0 : rotation g o (c t) (b.section_ 0 ⟨c t, hp⟩) = b.section_ 1 ⟨c t, hp⟩) :
    rotation g o (c t) (f t) =
      (-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
        Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩ := by
  have hrot1 : rotation g o (c t) (b.section_ 1 ⟨c t, hp⟩) =
      -b.section_ 0 ⟨c t, hp⟩ := by
    letI := (metricCore g (c t)).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (metricCore g (c t)).toCore
    letI := (SmoothManifolds.tangent_dimension S (c t)).1
    letI : Fact (Module.finrank ℝ (TangentSpace S (c t)) = 2) :=
      ⟨(SmoothManifolds.tangent_dimension S (c t)).2⟩
    have hJ := (planeOrientation g o (c t)).rightAngleRotation_rightAngleRotation
      (b.section_ 0 ⟨c t, hp⟩)
    change rotation g o (c t) (rotation g o (c t) (b.section_ 0 ⟨c t, hp⟩)) =
      -b.section_ 0 ⟨c t, hp⟩ at hJ
    rwa [hrot0] at hJ
  have hval := hcoeff.eq_of_nhds
  rw [P202.Geometry.CurveCovariantDerivative.coefficientsAlong_of_mem b c f t hp] at hval
  have he := (b.basis ⟨c t, hp⟩).equivFun_symm_apply
    ((b.basis ⟨c t, hp⟩).equivFun (f t))
  rw [LinearEquiv.symm_apply_apply, hval, Fin.sum_univ_two] at he
  have hf : f t = Real.cos (θ t) • b.section_ 0 ⟨c t, hp⟩ +
      Real.sin (θ t) • b.section_ 1 ⟨c t, hp⟩ := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, b.basis_eq] using he
  rw [hf, map_add, map_smul, map_smul, hrot0, hrot1]
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  change Real.cos (θ t) * (b.section_ 1 ⟨c t, hp⟩).val z +
    Real.sin (θ t) * (-(b.section_ 0 ⟨c t, hp⟩).val z) =
    (-Real.sin (θ t)) * (b.section_ 0 ⟨c t, hp⟩).val z +
    Real.cos (θ t) * (b.section_ 1 ⟨c t, hp⟩).val z
  ring

/-- In a positive orthonormal frame the intrinsic geodesic-curvature pairing
is the derivative of the real angle plus the actual connection form. -/
theorem frame_trig_geodesic_pairing (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    (hdiag : ∀ i : Fin 2, connectionForm C b ⟨c t, hp⟩ i i V = 0)
    (hskew : connectionForm C b ⟨c t, hp⟩ 0 1 V =
      -connectionForm C b ⟨c t, hp⟩ 1 0 V)
    {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' t)
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)]))
    (hrot0 : rotation g o (c t) (b.section_ 0 ⟨c t, hp⟩) =
      b.section_ 1 ⟨c t, hp⟩) :
    pairing g (c t) (covariantDerivative C c f t) (rotation g o (c t) (f t)) =
      θ' + connectionForm C b ⟨c t, hp⟩ 1 0 V := by
  rw [frame_trig_covariantDerivative C b hp hV hdiag hskew hθ hcoeff,
    frame_trig_rotation g o b hp hcoeff hrot0]
  have hn : pairing g (c t)
      ((-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
        Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩)
      ((-Real.sin (θ t)) • b.section_ 0 ⟨c t, hp⟩ +
        Real.cos (θ t) • b.section_ 1 ⟨c t, hp⟩) = 1 := by
    simp only [pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    change (-Real.sin (θ t)) * ((-Real.sin (θ t)) * pairing g (c t) _ _ +
      Real.cos (θ t) * pairing g (c t) _ _) +
      Real.cos (θ t) * ((-Real.sin (θ t)) * pairing g (c t) _ _ +
      Real.cos (θ t) * pairing g (c t) _ _) = 1
    rw [hon ⟨c t, hp⟩ 0 0, hon ⟨c t, hp⟩ 0 1,
      hon ⟨c t, hp⟩ 1 0, hon ⟨c t, hp⟩ 1 1]
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq (θ t)]
  simp only [pairing, LinearMap.BilinForm.smul_left] at hn ⊢
  rw [hn, mul_one]


/-- The actual metric-compatible connection and positive frame discharge
all connection-matrix and rotation premises in the moving-frame formula. -/
theorem orthonormalFrame_trig_geodesic_pairing (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsMetricCompatible g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0)
    {c : ℝ → M} {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c univ t V)
    {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' t)
    (hcoeff : coefficientsAlong b c f =ᶠ[𝓝 t]
      (fun s => ![Real.cos (θ s), Real.sin (θ s)]))
    (hpos : PositiveBoundaryOrientation o (c t)
      (b.section_ 0 ⟨c t, hp⟩) (b.section_ 1 ⟨c t, hp⟩)) :
    pairing g (c t) (covariantDerivative C c f t) (rotation g o (c t) (f t)) =
      θ' + connectionForm C b ⟨c t, hp⟩ 1 0 V := by
  exact frame_trig_geodesic_pairing g C o b hon hp hV
    (orthonormalFrame_connectionForm_diagonal g C hC b hon ⟨c t, hp⟩ V)
    (orthonormalFrame_connectionForm_skew g C hC b hon ⟨c t, hp⟩ V 0 1)
    hθ hcoeff (orthonormalFrame_rotation_first g o b hon ⟨c t, hp⟩ hpos)

end IntrinsicBoundaryCalculus


section ActualArcs
open P202.CurveConnectionData

/-- Continuity of the coordinate-model inclusion uses the literal L2-to-Pi
coordinate equivalence, with no scale or orientation change. -/
theorem continuous_modelPoint : Continuous P202Specs.ChartRegionStokes.modelPoint := by
  exact (EuclideanSpace.equiv (Fin 2) ℝ).continuous.subtype_mk (fun _ => mem_univ _)

theorem isOpen_chartTarget (c : ModelChart 2 .euclidean M) :
    IsOpen (P202Specs.ChartRegionStokes.chartTarget c) :=
  c.open_target.preimage continuous_modelPoint

theorem chartPoint_continuousAt (c : ModelChart 2 .euclidean M) {x : Plane}
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    ContinuousAt (chartPoint c) x :=
  (c.continuousAt_symm hx).comp continuous_modelPoint.continuousAt

theorem arc_mem_trace {q : RegularJordanCurve} (A : ArcPresentation q)
    (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : A.arc j t ∈ q.trace := by
  rw [A.agrees j t ht]
  exact ⟨_, rfl⟩

theorem arc_contDiffAt {q : RegularJordanCurve} (A : ArcPresentation q)
    (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (A.arc j) t := by
  obtain ⟨delta, hdelta, hsm⟩ := A.smooth j
  apply hsm.contDiffAt (isOpen_Ioo.mem_nhds ?_)
  constructor <;> linarith [ht.1, ht.2]

/-- Every extended presentation arc remains in the chart target on a genuine
open parameter neighborhood of each endpoint as well as each interior point. -/
theorem arc_eventually_chartTarget {q : RegularJordanCurve}
    (c : ModelChart 2 .euclidean M)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝 t, A.arc j s ∈ P202Specs.ChartRegionStokes.chartTarget c :=
  (arc_contDiffAt A j ht).continuousAt.eventually
    ((isOpen_chartTarget c).mem_nhds (hq (arc_mem_trace A j ht)))

/-- The intrinsic velocity is literally the inverse chart differential of
the coordinate velocity, including on the actual smooth endpoint extensions. -/
theorem arc_hasVelocity {q : RegularJordanCurve}
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasVelocityWithinAt S (surfaceArc c A j) univ t (arcVelocity c hc A j t) := by
  have hx := hq (arc_mem_trace A j ht)
  have hx' : P202Specs.ChartRegionStokes.modelPoint (A.arc j t) ∈ c.target := hx
  have hA := arc_contDiffAt A j ht
  have hp : surfaceArc c A j t ∈ c.source := c.map_target hx
  have hcurve : ContinuousAt (surfaceArc c A j) t :=
    (chartPoint_continuousAt c hx).comp hA.continuousAt
  refine ⟨hcurve.continuousWithinAt, c, hc, hp, ?_⟩
  have hd := (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t (hA.differentiableAt (by simp)).hasDerivAt
  have he : (fun s => (c (surfaceArc c A j s)).val) =ᶠ[𝓝 t]
      (fun s => EuclideanSpace.equiv (Fin 2) ℝ (A.arc j s)) := by
    filter_upwards [arc_eventually_chartTarget c hq A j ht] with s hs
    exact congrArg Subtype.val (c.right_inv hs)
  have hv : (tangentStructure S).fiberCoordinates.equiv c hc
      (surfaceArc c A j t) hp (arcVelocity c hc A j t) =
      EuclideanSpace.equiv (Fin 2) ℝ (deriv (A.arc j) t) := by
    simp only [arcVelocity, chartVector, dite_eq_left hx', surfaceArc]
    exact ((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c (A.arc j t))
      (c.map_target hx')).apply_symm_apply _
  rw [hv]
  exact (hd.congr_of_eventuallyEq he).hasDerivWithinAt

/-- Nonzero original coordinate vectors remain nonzero in the actual fiber. -/
theorem chartVector_ne_zero (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x v : Plane)
    (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target) (hv : v ≠ 0) :
    chartVector c hc x v ≠ 0 := by
  rw [chartVector, dite_eq_left hx]
  intro h
  have hh := congrArg ((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
    (c.map_target hx)) h
  simp only [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact hv ((EuclideanSpace.equiv (Fin 2) ℝ).injective (hh.trans (map_zero _).symm))

theorem arcSpeed_pos {q : RegularJordanCurve} (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < arcSpeed g c hc A j t := by
  apply Real.sqrt_pos.mpr
  apply g.positive
  exact chartVector_ne_zero c hc _ _ (hq (arc_mem_trace A j ht)) (A.regular j t ht)

/-- Actual curvature times unsigned speed, with its reciprocal cancelled. -/
theorem geodesicIntegrand_eq_pairing {q : RegularJordanCurve} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    geodesicIntegrand g C o c hc A j t =
      pairing g (surfaceArc c A j t)
        (covariantDerivative C (surfaceArc c A j)
          (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) t)
        (rotation g o (surfaceArc c A j t)
          (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j) t)) := by
  have hs := (arcSpeed_pos g c hc hq A j ht).ne'
  unfold geodesicIntegrand signedCurveCurvature signedCurvature curvatureVector
  simp only [pairing, LinearMap.BilinForm.smul_left]
  field_simp

/-- The pullback is the actual scalar connection form, evaluated on the
actual inverse differential, wherever the chart applies. -/
theorem frameOneForm_apply (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    frameOneForm C c hc b x v =
      connectionForm C b ⟨chartPoint c x, c.map_target hx⟩ 1 0 (chartVector c hc x v) := by
  have hx' : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target := hx
  simp only [frameOneForm, chartVector, dite_eq_left hx']
  rfl

/-- The actual arcs have ambient C1 chart extensions at their endpoints. -/
theorem surfaceArc_coordinateC1 {q : RegularJordanCurve}
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) :
    P202.CurveData.CoordinateC1On S (surfaceArc c A j) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hx := hq (arc_mem_trace A j ht)
  refine ⟨c, hc, c.map_target hx, fun s => EuclideanSpace.equiv (Fin 2) ℝ (A.arc j s), ?_, ?_, ?_⟩
  · exact ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp_contDiffAt t
      (arc_contDiffAt A j ht)).of_le (by simp)
  · exact (congrArg Subtype.val (c.right_inv hx)).symm
  · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [arc_eventually_chartTarget c hq A j ht] with s hs
    exact congrArg Subtype.val (c.right_inv hs)

theorem surfaceArc_continuous {q : RegularJordanCurve}
    (c : ModelChart 2 .euclidean M)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) :
    ContinuousOn (surfaceArc c A j) (Icc (0 : ℝ) 1) := by
  intro t ht
  exact ((chartPoint_continuousAt c (hq (arc_mem_trace A j ht))).comp
    (arc_contDiffAt A j ht).continuousAt).continuousWithinAt

end ActualArcs

section FrameArcRegularity
open P202.CurveConnectionData

/-- Squared metric norm is the sum of the two squared literal frame
coordinates; this is proved from the actual orthonormal frame hypothesis. -/
theorem pairing_self_eq_coordinate_sq (g : RiemannianMetric S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (hon : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
      if i = j then 1 else 0) (p : U) (v : TangentSpace S p.val) :
    pairing g p.val v v = ((b.basis p).equivFun v 0)^2 +
      ((b.basis p).equivFun v 1)^2 := by
  have he := (b.basis p).equivFun_symm_apply ((b.basis p).equivFun v)
  rw [LinearEquiv.symm_apply_apply, Fin.sum_univ_two] at he
  simp only [b.basis_eq] at he
  conv_lhs => rw [he]
  simp only [pairing, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  change _ * (_ * pairing g p.val _ _ + _ * pairing g p.val _ _) +
    _ * (_ * pairing g p.val _ _ + _ * pairing g p.val _ _) = _
  rw [hon p 0 0, hon p 0 1, hon p 1 0, hon p 1 1]
  norm_num
  ring

/-- Literal positive triangular coordinates of an arc velocity. -/
def frameArcVelocity {q : RegularJordanCurve} (a beta d : Plane → ℝ)
    (A : ArcPresentation q) (j : Fin A.count) (t : ℝ) : Euclidean 2 :=
  ![a (A.arc j t) * velocity A j t 0 + beta (A.arc j t) * velocity A j t 1,
    d (A.arc j t) * velocity A j t 1]

def normalizedFrameArcVelocity {q : RegularJordanCurve} (a beta d : Plane → ℝ)
    (A : ArcPresentation q) (j : Fin A.count) (t : ℝ) : Euclidean 2 :=
  (Real.sqrt ((frameArcVelocity a beta d A j t 0)^2 +
    (frameArcVelocity a beta d A j t 1)^2))⁻¹ • frameArcVelocity a beta d A j t

theorem arcSpeed_eq_frameNorm {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (A : ArcPresentation q) (j : Fin A.count) (t : ℝ)
    (hx : A.arc j t ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    arcSpeed g c hc A j t =
      Real.sqrt ((frameArcVelocity a beta d A j t 0)^2 +
        (frameArcVelocity a beta d A j t 1)^2) := by
  unfold arcSpeed tangentNorm surfaceArc arcVelocity
  have hh := pairing_self_eq_coordinate_sq g b H.orthonormal
    ⟨chartPoint c (A.arc j t), c.map_target hx⟩ (chartVector c hc (A.arc j t) (velocity A j t))
  rw [H.coordinates _ hx (velocity A j t)] at hh
  exact congrArg Real.sqrt hh

/-- No arbitrary field is substituted for the intrinsic unit tangent. -/
theorem tangentCoefficients_eq_normalized {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (A : ArcPresentation q) (j : Fin A.count) (t : ℝ)
    (hx : A.arc j t ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    tangentCoefficients g c hc b A j t = normalizedFrameArcVelocity a beta d A j t := by
  have hp : surfaceArc c A j t ∈ c.source := c.map_target hx
  have hv : (b.basis ⟨surfaceArc c A j t, hp⟩).equivFun (arcVelocity c hc A j t) =
      frameArcVelocity a beta d A j t := H.coordinates _ hx (velocity A j t)
  simp only [tangentCoefficients, coefficientsAlong, dite_eq_left hp, unitTangent, map_smul]
  rw [hv]
  change (arcSpeed g c hc A j t)⁻¹ • _ = _
  rw [arcSpeed_eq_frameNorm g o c hc b H A j t hx]
  rfl

theorem frameArcVelocity_contDiffAt {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (frameArcVelocity a beta d A j) t := by
  have hx := hq (arc_mem_trace A j ht)
  have hn := (isOpen_chartTarget c).mem_nhds hx
  have hA := arc_contDiffAt A j ht
  have ha := (H.smooth_a.contDiffAt hn).comp t hA
  have hb := (H.smooth_beta.contDiffAt hn).comp t hA
  have hd := (H.smooth_d.contDiffAt hn).comp t hA
  have hv : ContDiffAt ℝ ∞ (velocity A j) t := hA.derivWithin (by simp)
  have hv0 : ContDiffAt ℝ ∞ (fun s => velocity A j s 0) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp_contDiffAt t hv
  have hv1 : ContDiffAt ℝ ∞ (fun s => velocity A j s 1) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp_contDiffAt t hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (ha.mul hv0).add (hb.mul hv1)
  · exact hd.mul hv1

theorem normalizedFrameArcVelocity_contDiffAt {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (normalizedFrameArcVelocity a beta d A j) t := by
  have hz := frameArcVelocity_contDiffAt g o c hc b H hq A j ht
  have hz0 := (contDiffAt_pi.mp hz) 0
  have hz1 := (contDiffAt_pi.mp hz) 1
  have hn := (hz0.pow 2).add (hz1.pow 2)
  have hs := arcSpeed_pos g c hc hq A j ht
  rw [arcSpeed_eq_frameNorm g o c hc b H A j t (hq (arc_mem_trace A j ht))] at hs
  have hpos : 0 < (frameArcVelocity a beta d A j t 0)^2 +
      (frameArcVelocity a beta d A j t 1)^2 := Real.sqrt_pos.mp hs
  exact ((hn.sqrt hpos.ne').inv hs.ne').smul hz

/-- Coefficients of the actual normalized tangent are smooth on a genuine
ambient parameter germ. This supplies endpoint regularity as well. -/
theorem tangentCoefficients_contDiffAt {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (tangentCoefficients g c hc b A j) t := by
  apply (normalizedFrameArcVelocity_contDiffAt g o c hc b H hq A j ht).congr_of_eventuallyEq
  filter_upwards [arc_eventually_chartTarget c hq A j ht] with s hs
  exact tangentCoefficients_eq_normalized g o c hc b H A j s hs

/-- C1 along the actual original curve, in its actual tangent bundle. -/
theorem unitTangent_C1FieldOn {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) :
    C1FieldOn (B := tangentBundle S) (surfaceArc c A j)
      (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) (Icc (0 : ℝ) 1) := by
  intro t ht
  refine ⟨c.source, c.open_source, b, c.map_target (hq (arc_mem_trace A j ht)),
    tangentCoefficients g c hc b A j, ?_, rfl, Filter.EventuallyEq.rfl⟩
  exact (tangentCoefficients_contDiffAt g o c hc b H hq A j ht).of_le (by simp)

/-- Existence for the ordinary intrinsic covariant derivative is established
using the proved ambient smooth coefficient germ, even at the arc endpoints. -/
theorem unitTangent_hasCovariantDerivative {q : RegularJordanCurve} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ D, HasCovariantDerivativeAt C (surfaceArc c A j)
      (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) t D := by
  let hp := c.map_target (hq (arc_mem_trace A j ht))
  let z' := deriv (tangentCoefficients g c hc b A j) t
  refine ⟨frameDerivative C b (surfaceArc c A j)
    (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) t hp
      (arcVelocity c hc A j t) z',
    arcVelocity c hc A j t, arc_hasVelocity c hc hq A j ht,
    c.source, c.open_source, b, hp, z', ?_, rfl⟩
  exact ((tangentCoefficients_contDiffAt g o c hc b H hq A j ht).differentiableAt
    (by simp)).hasDerivAt.hasDerivWithinAt

end FrameArcRegularity

section ActualAngleCalculus
open P202.CurveConnectionData

/-- Every continuous real angle of the actual unit tangent is differentiable
on the smooth arc interior. Its smoothness is derived from its cosine and
sine, using a local inverse, and is never assumed of the lift. -/
theorem tangentAngle_hasDerivAt {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count)
    {J : Set ℝ} (hJ : IsOpen J) (hJI : J ⊆ Ioo (0 : ℝ) 1)
    {theta : ℝ → ℝ} (htheta : IsTangentAngle g c hc b A j theta J)
    {t : ℝ} (ht : t ∈ J) : HasDerivAt theta (deriv theta t) t := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨(hJI ht).1.le, (hJI ht).2.le⟩
  have hz := tangentCoefficients_contDiffAt g o c hc b H hq A j htI
  have hz0 := ((contDiffAt_pi.mp hz) 0).differentiableAt (by simp)
  have hz1 := ((contDiffAt_pi.mp hz) 1).differentiableAt (by simp)
  have he0 : (fun s => Real.cos (theta s)) =ᶠ[𝓝 t]
      (fun s => tangentCoefficients g c hc b A j s 0) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    simpa only [htheta.2 s hs, Matrix.cons_val_zero]
  have he1 : (fun s => Real.sin (theta s)) =ᶠ[𝓝 t]
      (fun s => tangentCoefficients g c hc b A j s 1) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    simp only [htheta.2 s hs, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hd := hasDerivAt_angle_of_cos_sin
    ((htheta.1 t ht).continuousAt (hJ.mem_nhds ht))
    (hz0.hasDerivAt.congr_of_eventuallyEq he0)
    (hz1.hasDerivAt.congr_of_eventuallyEq he1)
  exact hd.differentiableAt.hasDerivAt

/-- The literal intrinsic identity on each original arc, with actual metric,
Levi-Civita connection, velocity, normalized tangent, and pulled-back Gamma10.
No connection-matrix identity, rotation certificate, or angle derivative is
an input: those facts are all established from the concrete frame. -/
theorem geodesicIntegrand_eq_angleDerivative_add_connection {q : RegularJordanCurve}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count)
    {J : Set ℝ} (hJ : IsOpen J) (hJI : J ⊆ Ioo (0 : ℝ) 1)
    {theta : ℝ → ℝ} (htheta : IsTangentAngle g c hc b A j theta J)
    {t : ℝ} (ht : t ∈ J) :
    geodesicIntegrand g C o c hc A j t = deriv theta t +
      frameOneForm C c hc b (A.arc j t) (velocity A j t) := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨(hJI ht).1.le, (hJI ht).2.le⟩
  have hx := hq (arc_mem_trace A j htI)
  have he : coefficientsAlong b (surfaceArc c A j)
      (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) =ᶠ[𝓝 t]
        (fun s => ![Real.cos (theta s), Real.sin (theta s)]) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact htheta.2 s hs
  rw [geodesicIntegrand_eq_pairing g C o c hc hq A j htI,
    frameOneForm_apply C c hc b _ hx]
  exact orthonormalFrame_trig_geodesic_pairing g C hC.2 o b H.orthonormal
    (c.map_target hx) (arc_hasVelocity c hc hq A j htI)
    (tangentAngle_hasDerivAt g o c hc b H hq A j hJ hJI htheta ht) he
    (H.positive ⟨_, c.map_target hx⟩)

end ActualAngleCalculus

/-- A smooth unit-vector germ has a real C1 angle on an actual open
neighborhood, obtained from a locally unambiguous arcsin branch. -/
theorem exists_local_smooth_angle {z : ℝ → Euclidean 2} {t : ℝ}
    (hz : ContDiffAt ℝ ∞ z t)
    (hu : ∀ᶠ s in 𝓝 t, (z s 0)^2 + (z s 1)^2 = 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ theta : ℝ → ℝ,
      ContDiffOn ℝ 1 theta (Ioo (t-delta) (t+delta)) ∧
      ∀ s ∈ Ioo (t-delta) (t+delta), z s = ![Real.cos (theta s), Real.sin (theta s)] := by
  have hut := hu.self_of_nhds
  let Z : ℂ := ⟨z t 0, z t 1⟩
  have hnorm : ‖Z‖ = 1 := by
    rw [Complex.norm_def]
    change Real.sqrt ((z t 0)*(z t 0)+(z t 1)*(z t 1)) = 1
    simpa only [pow_two, hut, Real.sqrt_one] using congrArg Real.sqrt hut
  have hne : Z ≠ 0 := by intro h; simp [h] at hnorm
  let theta0 := Complex.arg Z
  have hc0 : Real.cos theta0 = z t 0 := by simpa [hnorm, Z] using Complex.cos_arg hne
  have hs0 : Real.sin theta0 = z t 1 := by simpa [hnorm, Z] using Complex.sin_arg Z
  let f : ℝ → ℝ := fun s => z s 1 * Real.cos theta0 - z s 0 * Real.sin theta0
  let dot : ℝ → ℝ := fun s => z s 0 * Real.cos theta0 + z s 1 * Real.sin theta0
  have hft : f t = 0 := by dsimp [f]; rw [hc0, hs0]; ring
  have hdot : dot t = 1 := by dsimp [dot]; rw [hc0, hs0]; nlinarith [hut]
  have hz0 := (contDiffAt_pi.mp hz) 0
  have hz1 := (contDiffAt_pi.mp hz) 1
  have hf : ContDiffAt ℝ ∞ f t := (hz1.mul contDiffAt_const).sub (hz0.mul contDiffAt_const)
  have hd : ContinuousAt dot t :=
    ((hz0.mul contDiffAt_const).add (hz1.mul contDiffAt_const)).continuousAt
  let theta : ℝ → ℝ := fun s => theta0 + Real.arcsin (f s)
  have htheta : ContDiffAt ℝ 1 theta t := by
    apply contDiffAt_const.add
    apply (Real.contDiffAt_arcsin (x := f t) ?_ ?_).comp t (hf.of_le (by simp))
    · rw [hft]; norm_num
    · rw [hft]; norm_num
  have hg : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 1 theta s ∧
      z s = ![Real.cos (theta s), Real.sin (theta s)] := by
    have hdpos : ∀ᶠ s in 𝓝 t, 0 < dot s := hd.eventually (by rw [hdot]; exact Ioi_mem_nhds zero_lt_one)
    have hflt : ∀ᶠ s in 𝓝 t, f s ∈ Ioo (-1 : ℝ) 1 :=
      hf.continuousAt.eventually (isOpen_Ioo.mem_nhds (by rw [hft]; constructor <;> norm_num))
    filter_upwards [hu, hdpos, hflt, htheta.eventually (by norm_num)] with s hs hd hsF hsTheta
    refine ⟨hsTheta, ?_⟩
    have hid : (dot s)^2 + (f s)^2 = 1 := by
      calc
        (dot s)^2 + (f s)^2 = ((z s 0)^2 + (z s 1)^2) *
            ((Real.sin theta0)^2 + (Real.cos theta0)^2) := by dsimp [dot, f]; ring
        _ = 1 := by rw [hs, Real.sin_sq_add_cos_sq]; norm_num
    have hsqrt : Real.sqrt (1 - (f s)^2) = dot s := by
      have he : 1 - (f s)^2 = (dot s)^2 := by nlinarith [hid]
      rw [he, Real.sqrt_sq hd.le]
    have hca : Real.cos (theta s) = z s 0 := by
      dsimp [theta]
      rw [Real.cos_add, Real.cos_arcsin, Real.sin_arcsin hsF.1.le hsF.2.le, hsqrt]
      dsimp [dot, f]
      linear_combination (z s 0) * (Real.sin_sq_add_cos_sq theta0)
    have hsa : Real.sin (theta s) = z s 1 := by
      dsimp [theta]
      rw [Real.sin_add, Real.cos_arcsin, Real.sin_arcsin hsF.1.le hsF.2.le, hsqrt]
      dsimp [dot, f]
      linear_combination (z s 1) * (Real.sin_sq_add_cos_sq theta0)
    ext i
    fin_cases i <;> simp [hca, hsa]
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hg
  refine ⟨delta, hdelta, theta, ?_, ?_⟩
  · intro s hs
    have hsball : s ∈ Metric.ball t delta := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact (hball hsball).1.contDiffWithinAt
  · intro s hs
    apply (hball ?_).2
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]


section LocalTangentAngles
open P202.CurveConnectionData

/-- Normalizing the actual nonzero coordinate pair gives unit circle data. -/
theorem normalizedPair_unit (z : Euclidean 2) (h : 0 < z 0 ^ 2 + z 1 ^ 2) :
    (((Real.sqrt (z 0 ^ 2 + z 1 ^ 2))⁻¹ • z) 0)^2 +
      (((Real.sqrt (z 0 ^ 2 + z 1 ^ 2))⁻¹ • z) 1)^2 = 1 := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_pow, mul_pow, ← mul_add, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- The coefficient vector stays on the unit circle on an actual open germ,
not just at parameter values belonging to the closed boundary interval. -/
theorem tangentCoefficients_eventually_unit {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝 t, (tangentCoefficients g c hc b A j s 0)^2 +
      (tangentCoefficients g c hc b A j s 1)^2 = 1 := by
  have hz := frameArcVelocity_contDiffAt g o c hc b H hq A j ht
  have hz0 := ((contDiffAt_pi.mp hz) 0).continuousAt
  have hz1 := ((contDiffAt_pi.mp hz) 1).continuousAt
  have hcont := (hz0.pow 2).add (hz1.pow 2)
  have hs := arcSpeed_pos g c hc hq A j ht
  rw [arcSpeed_eq_frameNorm g o c hc b H A j t (hq (arc_mem_trace A j ht))] at hs
  have hs' : 0 < (frameArcVelocity a beta d A j t 0)^2 +
      (frameArcVelocity a beta d A j t 1)^2 := Real.sqrt_pos.mp hs
  have he : ∀ᶠ s in 𝓝 t, 0 < (frameArcVelocity a beta d A j s 0)^2 +
      (frameArcVelocity a beta d A j s 1)^2 := hcont.eventually (Ioi_mem_nhds hs')
  filter_upwards [he, arc_eventually_chartTarget c hq A j ht] with s hs htarget
  rw [tangentCoefficients_eq_normalized g o c hc b H A j s htarget]
  exact normalizedPair_unit (frameArcVelocity a beta d A j s) hs

/-- Existence of real C1 angle lifts for every actual normalized tangent,
including an ambient neighborhood of either smooth endpoint extension. -/
theorem localTangentAngle_exists {q : RegularJordanCurve} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ theta : ℝ → ℝ,
      IsTangentAngle g c hc b A j theta (Ioo (t-delta) (t+delta)) ∧
      ContDiffOn ℝ 1 theta (Ioo (t-delta) (t+delta)) := by
  obtain ⟨delta, hdelta, theta, hsm, he⟩ := exists_local_smooth_angle
    (tangentCoefficients_contDiffAt g o c hc b H hq A j ht)
    (tangentCoefficients_eventually_unit g o c hc b H hq A j ht)
  exact ⟨delta, hdelta, theta, ⟨hsm.continuousOn, he⟩, hsm⟩

end LocalTangentAngles


/-- All pointwise and regularity clauses for the original arcs, without any
integrability, angle-derivative, curvature, or turning certificates as input. -/
theorem arcCalculus : P202Specs.MetricBoundaryTurning.Expected.arcCalculus.{u} := by
  intro M inst S g C hC o c hc b a beta d H q hq A
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j t ht
    exact ⟨arc_hasVelocity c hc hq A j ht, arcSpeed_pos g c hc hq A j ht,
      unitTangent_hasCovariantDerivative g C o c hc b H hq A j ht⟩
  · intro j
    exact ⟨surfaceArc_coordinateC1 c hc hq A j, surfaceArc_continuous c hq A j,
      unitTangent_C1FieldOn g o c hc b H hq A j⟩
  · intro j t ht
    exact localTangentAngle_exists g o c hc b H hq A j ht
  · intro j J theta hJ hJI htheta t ht
    exact ⟨tangentAngle_hasDerivAt g o c hc b H hq A j hJ hJI htheta ht,
      geodesicIntegrand_eq_angleDerivative_add_connection g C hC o c hc b H hq A j
        hJ hJI htheta ht⟩

/-- Finite smooth angle changes and all principal corner rotations telescope. -/
theorem triangularTurning : P202Specs.MetricBoundaryTurning.Expected.triangularTurning.{u} :=
  @upperTriangular_totalTurning_invariant


section LiteralFormSmoothness
open SmoothManifolds.MapData

theorem cotangent_coordinates (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (alpha : Module.Dual ℝ (TangentSpace S p)) (i : Fin 2) :
    (((cotangentBundle S).trivialization ⟨c, hc⟩) ⟨p, alpha⟩).2 i =
      alpha (((tangentStructure S).fiberCoordinates.equiv c hc p hp).symm (Pi.single i 1)) := by
  have hb : p ∈ (tangentBundle S).baseSet ⟨c,hc⟩ := by
    rw [(tangentRealization S).baseSet]
    exact hp
  rw [(cotangentDual S).coordinates ⟨c,hc⟩ p hb alpha i]
  congr 1
  change ((tangentBundle S).fiberCoordinates ⟨c,hc⟩ p hb).symm _ = _
  have he : (tangentBundle S).fiberCoordinates ⟨c,hc⟩ p hb =
      (tangentStructure S).fiberCoordinates.equiv c hc p hp := by
    apply LinearEquiv.ext
    intro v
    exact (tangentRealization S).coordinates ⟨c,hc⟩ p hp v
  rw [he]

theorem covector_apply_eq_sum (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (alpha : Module.Dual ℝ (TangentSpace S p)) (v : Plane) :
    alpha (((tangentStructure S).fiberCoordinates.equiv c hc p hp).symm
      (EuclideanSpace.equiv (Fin 2) ℝ v)) =
      ∑ i : Fin 2, ((((cotangentBundle S).trivialization ⟨c, hc⟩) ⟨p, alpha⟩).2 i) * v i := by
  have hv : EuclideanSpace.equiv (Fin 2) ℝ v = ∑ i : Fin 2, v i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [cotangent_coordinates]
  exact mul_comm _ _

theorem frameOneForm_contDiffOn (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) :
    ContDiffOn ℝ ∞ (frameOneForm C c hc b) (P202Specs.ChartRegionStokes.chartTarget c) := by
  let alpha : (p : M) → Module.Dual ℝ (TangentSpace S p) :=
    SmoothManifolds.SectionExtension.totalSection
      (fun p : c.source => connectionForm C b p 1 0)
  let f : M → Euclidean 2 := fun p =>
    (((cotangentBundle S).trivialization ⟨c,hc⟩) ⟨p, alpha p⟩).2
  have hAlpha := P202.Geometry.ConnectionForms.connectionForm_smooth
    (tangentBundle S) C c.open_source b 1 0
  intro x hx
  let p := chartPoint c x
  have hp : p ∈ c.source := c.map_target hx
  have hb : p ∈ (cotangentBundle S).baseSet ⟨c,hc⟩ := by
    rw [(cotangentDual S).baseSet, (tangentRealization S).baseSet]
    exact hp
  have hf : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt (cotangentBundle S)
      ⟨c,hc⟩ ⟨p,alpha p⟩ hb).comp
      (g := fun q => (⟨q,alpha q⟩ : Bundle.TotalSpace (Euclidean 2)
        (fun p => Module.Dual ℝ (TangentSpace S p))))
      (cotangentBundle S).totalManifold.smoothStructure.property.1.1 (hAlpha p hp)
  obtain ⟨W,hW,hpW,G,hG,heG⟩ := hf.2 c hc hp
  have hxp : (c p).val = EuclideanSpace.equiv (Fin 2) ℝ x := by
    exact congrArg Subtype.val (c.right_inv hx)
  rw [hxp] at hpW
  have hpcont : ContinuousAt (chartPoint c) x := by
    have hm : ContinuousAt P202Specs.ChartRegionStokes.modelPoint x := by
      exact ((EuclideanSpace.equiv (Fin 2) ℝ).continuous.subtype_mk (fun _ => mem_univ _)).continuousAt
    exact (c.continuousAt_symm hx).comp hm
  have htarget : ∀ᶠ y in 𝓝 x, y ∈ P202Specs.ChartRegionStokes.chartTarget c := by
    have hm : Continuous P202Specs.ChartRegionStokes.modelPoint :=
      (EuclideanSpace.equiv (Fin 2) ℝ).continuous.subtype_mk (fun _ => mem_univ _)
    exact (c.open_target.preimage hm).mem_nhds hx
  have hGe : ∀ᶠ y in 𝓝 x, G (EuclideanSpace.equiv (Fin 2) ℝ y) = f (chartPoint c y) := by
    filter_upwards [heG.comp_tendsto hpcont, htarget] with y hy hyt
    have hcy : (c (chartPoint c y)).val = EuclideanSpace.equiv (Fin 2) ℝ y :=
      congrArg Subtype.val (c.right_inv hyt)
    change G (c (chartPoint c y)).val = f (chartPoint c y) at hy
    rw [hcy] at hy
    exact hy
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hg : ContDiffAt ℝ ∞ (fun y : Plane => G (EuclideanSpace.equiv (Fin 2) ℝ y)) x :=
    (hG.contDiffAt (hW.mem_nhds hpW)).comp x
      (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.contDiffAt
  have hs : ContDiffAt ℝ ∞ (fun y : Plane => ∑ i : Fin 2,
      G (EuclideanSpace.equiv (Fin 2) ℝ y) i * v i) x := by
    exact ContDiffAt.sum (fun i _ => ((contDiffAt_pi.mp hg) i).mul contDiffAt_const)
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [hGe, htarget] with y hy hyt
  have hyt' : P202Specs.ChartRegionStokes.modelPoint y ∈ c.target := hyt
  simp only [frameOneForm, dite_eq_left hyt']
  change connectionForm C b ⟨chartPoint c y,c.map_target hyt⟩ 1 0
    (((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c y)
      (c.map_target hyt)).symm (EuclideanSpace.equiv (Fin 2) ℝ v)) = _
  rw [hy]
  have halpha : alpha (chartPoint c y) = connectionForm C b ⟨chartPoint c y,c.map_target hyt⟩ 1 0 :=
    SmoothManifolds.SectionExtension.totalSection_of_mem _ _ (c.map_target hyt)
  simpa only [f, halpha] using covector_apply_eq_sum c hc (chartPoint c y)
    (c.map_target hyt) (alpha (chartPoint c y)) v

end LiteralFormSmoothness

section BoundaryIntegrability
open P202Specs.ChartRegionStokes

theorem jordanBoundary_intervalIntegrable {q : RegularJordanCurve} {U : Set Plane}
    {omega : OneForm} (hq : q.trace ⊆ U) (homega : ContinuousOn omega U) :
    IntervalIntegrable (boundaryIntegrand omega q) volume 0 1 := by
  let f : ℝ → Plane := realLift q.parametrization
  have hcoef : Continuous (fun t => omega (f t)) := homega.comp_continuous
    (P202.ChartRegionStokes.realLift_continuous q) (fun t => hq ⟨(t : ParameterCircle),rfl⟩)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image hcoef).isBounded.exists_norm_le
  obtain ⟨L, hL⟩ := P202.ChartRegionStokes.realLift_deriv_bounded q
  have hmeval : Measurable (fun z : (Plane →L[ℝ] ℝ) × Plane => z.1 z.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  have hm : AEStronglyMeasurable (fun t => omega (f t) (deriv f t))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hmeval.comp (hcoef.measurable.prodMk (measurable_deriv f))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖omega (f t) (deriv f t)‖ ≤ max B 0 * max L 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply ((omega (f t)).le_opNorm (deriv f t)).trans
    apply mul_le_mul
    · exact (hB _ ⟨t,ht,rfl⟩).trans (le_max_left _ _)
    · exact (hL t ht).trans (le_max_left _ _)
    · exact norm_nonneg _
    · exact le_max_right _ _
  have hint : IntegrableOn (fun t => omega (f t) (deriv f t)) (Icc (0 : ℝ) 1) volume :=
    IntegrableOn.of_bound isCompact_Icc.measure_lt_top hm (max B 0 * max L 0) hbound
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hint
  apply hi.congr_ae
  simpa only [uIoc_of_le zero_le_one] using
    (P202.ChartRegionStokes.boundaryIntegrand_ae_eq omega q).symm

/-- The original masked component integral splits over every actual arc
presentation once the form is continuous along the original trace. -/
theorem componentIntegral_eq_arcs_of_continuous {q : RegularJordanCurve}
    {U : Set Plane} (A : ArcPresentation q) (omega : OneForm)
    (hq : q.trace ⊆ U) (homega : ContinuousOn omega U) :
    P202Specs.ChartRegionStokes.componentIntegral omega q =
      ∑ j, ∫ t in (0 : ℝ)..1, omega (A.arc j t) (velocity A j t) := by
  exact componentIntegral_eq_arcs_of_integrable A omega
    (jordanBoundary_intervalIntegrable hq homega)

end BoundaryIntegrability

namespace FrameAngleCoordinates
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]

lemma areaForm_coordinates (o : Orientation ℝ V (Fin 2))
    (B : Module.Basis (Fin 2) ℝ V)
    (hon : ∀ i j, inner ℝ (B i) (B j) = if i = j then 1 else 0)
    (hrot : o.rightAngleRotation (B 0) = B 1) (v w : V) :
    o.areaForm v w = B.equivFun v 0 * B.equivFun w 1 -
      B.equivFun v 1 * B.equivFun w 0 := by
  have hB (z : V) : z = (B.equivFun z 0) • B 0 + (B.equivFun z 1) • B 1 := by
    have h := B.equivFun_symm_apply (B.equivFun z)
    rw [LinearEquiv.symm_apply_apply, Fin.sum_univ_two] at h
    exact h
  have harea01 : o.areaForm (B 0) (B 1) = 1 := by
    rw [← o.inner_rightAngleRotation_left, hrot, hon]
    simp
  conv_lhs => rw [hB v, hB w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, o.areaForm_apply_self, harea01,
    o.areaForm_swap (B 1) (B 0)]
  ring

lemma oangle_coordinates (o : Orientation ℝ V (Fin 2))
    (B : Module.Basis (Fin 2) ℝ V)
    (hon : ∀ i j, inner ℝ (B i) (B j) = if i = j then 1 else 0)
    (hrot : o.rightAngleRotation (B 0) = B 1)
    (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v) (v w : V) :
    o.oangle v w = op.oangle (WithLp.toLp 2 (B.equivFun v))
      (WithLp.toLp 2 (B.equivFun w)) := by
  have hB (z : V) : z = (B.equivFun z 0) • B 0 + (B.equivFun z 1) • B 1 := by
    have h := B.equivFun_symm_apply (B.equivFun z)
    rw [LinearEquiv.symm_apply_apply, Fin.sum_univ_two] at h
    exact h
  have hinner : inner ℝ v w = B.equivFun v 0 * B.equivFun w 0 +
      B.equivFun v 1 * B.equivFun w 1 := by
    conv_lhs => rw [hB v, hB w]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hon,
      ite_true, zero_ne_one, one_ne_zero, ite_false]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have harea01 : o.areaForm (B 0) (B 1) = 1 := by
    rw [← o.inner_rightAngleRotation_left, hrot, hon]
    simp
  have harea : o.areaForm v w = B.equivFun v 0 * B.equivFun w 1 -
      B.equivFun v 1 * B.equivFun w 0 := by
    conv_lhs => rw [hB v, hB w]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, o.areaForm_apply_self, harea01,
      o.areaForm_swap (B 1) (B 0)]
    ring
  have hpinner (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  have hparea (x y : Plane) : op.areaForm x y = x 0 * y 1 - x 1 * y 0 := by
    rw [← op.inner_rightAngleRotation_left, hop, hpinner]
    simp only [quarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [Orientation.oangle, Orientation.kahler_apply_apply, hinner, harea,
    hpinner, hparea]


lemma normalize_eq_trig_of_lift (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v)
    {v : Plane} (hv : v ≠ 0) {theta : ℝ}
    (htheta : (theta : Real.Angle) = op.oangle P202Specs.PlaneTurning.reference v) :
    NormedSpace.normalize v = !₂[Real.cos theta, Real.sin theta] := by
  have hn : ‖P202Specs.PlaneTurning.reference‖ = ‖NormedSpace.normalize v‖ := by
    rw [NormedSpace.norm_normalize hv]
    norm_num [P202Specs.PlaneTurning.reference, EuclideanSpace.norm_eq]
  have ha : op.oangle P202Specs.PlaneTurning.reference (NormedSpace.normalize v) =
      op.oangle P202Specs.PlaneTurning.reference v := by
    rw [NormedSpace.normalize, op.oangle_smul_right_of_pos _ _
      (inv_pos.mpr (norm_pos_iff.mpr hv))]
  have hr := (op.rotation_oangle_eq_iff_norm_eq P202Specs.PlaneTurning.reference
    (NormedSpace.normalize v)).mpr hn
  rw [ha, ← htheta] at hr
  rw [Orientation.rotation_apply, hop] at hr
  symm
  convert hr using 1
  ext i
  fin_cases i <;> simp [P202Specs.PlaneTurning.reference, quarterTurn]


lemma normalizedPair_eq_trig_of_lift (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v)
    (z : Fin 2 → ℝ) (hz : WithLp.toLp 2 z ≠ (0 : Plane)) {theta : ℝ}
    (htheta : (theta : Real.Angle) = op.oangle P202Specs.PlaneTurning.reference
      (WithLp.toLp 2 z)) :
    (Real.sqrt (z 0 ^ 2 + z 1 ^ 2))⁻¹ • z = ![Real.cos theta, Real.sin theta] := by
  have h := normalize_eq_trig_of_lift op hop hz htheta
  have hn : ‖WithLp.toLp 2 z‖ = Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  ext i
  have hi := congrArg (fun x : Plane => x i) h
  simpa only [NormedSpace.normalize, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul,
    hn] using hi


open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
open P202.MetricData P202.SurfaceBoundaryData P202.ConnectionData
open P202Specs.MetricBoundaryTurning P202Specs.PlaneTurning

lemma metricCornerAngle_eq_upperTriangular_of_rotation {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hrot : ∀ p : c.source, rotation g o p.val (b.section_ 0 p) = b.section_ 1 p)
    (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v)
    (A : ArcPresentation q) (j : Fin A.count)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    metricCornerAngle g o c hc A j =
      (op.oangle (upperTriangular (a (A.arc j 1)) (beta (A.arc j 1))
        (d (A.arc j 1)) (velocity A j 1))
        (upperTriangular (a (A.arc j 1)) (beta (A.arc j 1))
          (d (A.arc j 1)) (velocity A (finRotate A.count j) 0))).toReal := by
  let p : c.source := ⟨chartPoint c (A.arc j 1), c.map_target hx⟩
  letI := (metricCore g p.val).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p.val).toCore
  letI := (SmoothManifolds.tangent_dimension S p.val).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p.val) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p.val).2⟩
  have hb : ∀ i k, inner ℝ (b.basis p i) (b.basis p k) =
      if i = k then 1 else 0 := by
    intro i k
    change pairing g p.val (b.basis p i) (b.basis p k) = _
    simpa only [b.basis_eq] using H.orthonormal p i k
  have hr : (planeOrientation g o p.val).rightAngleRotation (b.basis p 0) =
      b.basis p 1 := by
    simpa only [rotation, b.basis_eq, LinearIsometryEquiv.coe_toLinearEquiv] using hrot p
  have he (v : Plane) :
      WithLp.toLp 2 ((b.basis p).equivFun (chartVector c hc (A.arc j 1) v)) =
        upperTriangular (a (A.arc j 1)) (beta (A.arc j 1)) (d (A.arc j 1)) v := by
    change WithLp.toLp 2 ((b.basis
      ⟨chartPoint c (A.arc j 1), c.map_target hx⟩).equivFun
      (chartVector c hc (A.arc j 1) v)) = _
    rw [H.coordinates _ hx v]
    rfl
  change ((planeOrientation g o p.val).oangle
    (chartVector c hc (A.arc j 1) (velocity A j 1))
    (chartVector c hc (A.arc j 1) (velocity A (finRotate A.count j) 0))).toReal = _
  rw [oangle_coordinates (planeOrientation g o p.val) (b.basis p) hb hr op hop, he, he]


/-- A real extension retaining every value on the closed unit interval. -/
def intervalAngleExtension (F : C(unitInterval, ℝ)) : ℝ → ℝ :=
  fun t => F (Set.projIcc 0 1 zero_le_one t)

lemma intervalAngleExtension_continuous (F : C(unitInterval, ℝ)) :
    Continuous (intervalAngleExtension F) :=
  F.continuous.comp continuous_projIcc

lemma intervalAngleExtension_coe (F : C(unitInterval, ℝ)) (t : unitInterval) :
    intervalAngleExtension F t = F t := by
  exact congrArg F (Set.projIcc_val zero_le_one t)

lemma intervalAngleExtension_isTangentAngle {q : RegularJordanCurve}
    (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (A : ArcPresentation q) (j : Fin A.count)
    (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v)
    (z : unitInterval → Fin 2 → ℝ)
    (hz : ∀ t, WithLp.toLp 2 (z t) ≠ (0 : Plane))
    (hcoeff : ∀ t : unitInterval, tangentCoefficients g c hc b A j t =
      (Real.sqrt ((z t 0)^2 + (z t 1)^2))⁻¹ • z t)
    (F : C(unitInterval, ℝ))
    (hF : ∀ t, (F t : Real.Angle) =
      op.oangle P202Specs.PlaneTurning.reference (WithLp.toLp 2 (z t))) :
    IsTangentAngle g c hc b A j (intervalAngleExtension F) (Icc (0 : ℝ) 1) := by
  refine ⟨(intervalAngleExtension_continuous F).continuousOn, ?_⟩
  intro t ht
  let u : unitInterval := ⟨t, ht⟩
  have hu : intervalAngleExtension F t = F u := intervalAngleExtension_coe F u
  rw [hu, hcoeff u]
  exact normalizedPair_eq_trig_of_lift op hop (z u) (hz u) (hF u)


lemma arc_join {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count) :
    A.arc j 1 = A.arc (finRotate A.count j) 0 := by
  letI : NeZero A.count := ⟨ne_of_gt A.positive⟩
  have hjrot : (finRotate A.count j).val = (j.val + 1) % A.count := by
    rw [finRotate_apply]
    change (j.val + 1 % A.count) % A.count = (j.val + 1) % A.count
    exact Nat.add_mod_mod _ _ _
  rw [A.agrees j 1 ⟨by norm_num, by norm_num⟩,
    A.agrees (finRotate A.count j) 0 ⟨by norm_num, by norm_num⟩]
  simp only [mul_one, mul_zero, add_zero, add_sub_cancel_left]
  by_cases hlast : j.val + 1 = A.count
  · have hj : j.succ = Fin.last A.count := Fin.ext hlast
    have hk : (finRotate A.count j).castSucc = 0 := by
      apply Fin.ext
      change (finRotate A.count j).val = 0
      rw [hjrot, hlast, Nat.mod_self]
    rw [hj, hk, A.first, A.last]
    simp [realLift, AddCircle.coe_period]
  · have hlt : j.val + 1 < A.count := by omega
    have hj : j.succ = (finRotate A.count j).castSucc := by
      apply Fin.ext
      change j.val + 1 = (finRotate A.count j).val
      rw [hjrot, Nat.mod_eq_of_lt hlt]
    rw [hj]
    congr 1
    ring


end FrameAngleCoordinates
open FrameAngleCoordinates

section CorrectedArcAngles

theorem chartVector_orientedArea
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (x u v : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    orientedArea g o (chartPoint c x) (chartVector c hc x u) (chartVector c hc x v) =
      (a x * d x) * (u 0 * v 1 - u 1 * v 0) := by
  let p : c.source := ⟨chartPoint c x, c.map_target hx⟩
  letI := (metricCore g p.val).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p.val).toCore
  letI := (SmoothManifolds.tangent_dimension S p.val).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p.val) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p.val).2⟩
  have hb : ∀ i k, inner ℝ (b.basis p i) (b.basis p k) =
      if i = k then 1 else 0 := by
    intro i k
    change pairing g p.val (b.basis p i) (b.basis p k) = _
    simpa only [b.basis_eq] using H.orthonormal p i k
  have hr : (planeOrientation g o p.val).rightAngleRotation (b.basis p 0) =
      b.basis p 1 := by
    simpa only [rotation, b.basis_eq, LinearIsometryEquiv.coe_toLinearEquiv] using
      orthonormalFrame_rotation_first g o b H.orthonormal p (H.positive p)
  change (planeOrientation g o p.val).areaForm (chartVector c hc x u)
    (chartVector c hc x v) = _
  rw [FrameAngleCoordinates.areaForm_coordinates (planeOrientation g o p.val) (b.basis p) hb hr]
  change (b.basis ⟨chartPoint c x, c.map_target hx⟩).equivFun (chartVector c hc x u) 0 *
      (b.basis ⟨chartPoint c x, c.map_target hx⟩).equivFun (chartVector c hc x v) 1 -
      (b.basis ⟨chartPoint c x, c.map_target hx⟩).equivFun (chartVector c hc x u) 1 *
      (b.basis ⟨chartPoint c x, c.map_target hx⟩).equivFun (chartVector c hc x v) 0 = _
  rw [H.coordinates x hx u, H.coordinates x hx v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring



theorem metricCornerAngle_eq_upperTriangular {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v)
    (A : ArcPresentation q) (j : Fin A.count)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    metricCornerAngle g o c hc A j =
      (op.oangle (upperTriangular (a (A.arc j 1)) (beta (A.arc j 1))
        (d (A.arc j 1)) (velocity A j 1))
        (upperTriangular (a (A.arc j 1)) (beta (A.arc j 1))
          (d (A.arc j 1)) (velocity A (finRotate A.count j) 0))).toReal :=
  metricCornerAngle_eq_upperTriangular_of_rotation g o c hc b H
    (fun p => orthonormalFrame_rotation_first g o b H.orthonormal p (H.positive p))
    op hop A j hx

/-- The original Euclidean lift receives the canonical continuous triangular
correction, and the resulting lift is literally an intrinsic tangent angle. -/
theorem exists_corrected_arcAngles {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v) (theta : AngleChoices op A) :
    ∃ psi : Fin A.count → ℝ → ℝ,
      (∀ j, IsTangentAngle g c hc b A j (psi j) (Icc (0 : ℝ) 1)) ∧
      ∀ (j : Fin A.count) (t : unitInterval), psi j t = theta.angle j t +
        (op.oangle (velocity A j t)
          (upperTriangular (a (A.arc j t)) (beta (A.arc j t)) (d (A.arc j t))
            (velocity A j t))).toReal := by
  have hA (j : Fin A.count) : Continuous (fun t : unitInterval => A.arc j t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (arc_contDiffAt A j t.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  let aa (j : Fin A.count) : C(unitInterval, ℝ) :=
    ⟨fun t => a (A.arc j t), H.smooth_a.continuousOn.comp_continuous (hA j)
      (fun t => hq (arc_mem_trace A j t.property))⟩
  let bb (j : Fin A.count) : C(unitInterval, ℝ) :=
    ⟨fun t => beta (A.arc j t), H.smooth_beta.continuousOn.comp_continuous (hA j)
      (fun t => hq (arc_mem_trace A j t.property))⟩
  let dd (j : Fin A.count) : C(unitInterval, ℝ) :=
    ⟨fun t => d (A.arc j t), H.smooth_d.continuousOn.comp_continuous (hA j)
      (fun t => hq (arc_mem_trace A j t.property))⟩
  let vv (j : Fin A.count) : C(unitInterval, Plane) :=
    ⟨fun t => velocity A j t, P202.PlaneTurning.velocity_continuous A j⟩
  have haa (j : Fin A.count) (t : unitInterval) : 0 < aa j t :=
    H.pos_a _ (hq (arc_mem_trace A j t.property))
  have hdd (j : Fin A.count) (t : unitInterval) : 0 < dd j t :=
    H.pos_d _ (hq (arc_mem_trace A j t.property))
  have hvv (j : Fin A.count) (t : unitInterval) : vv j t ≠ 0 :=
    A.regular j t t.property
  let delta (j : Fin A.count) : C(unitInterval, ℝ) :=
    triangularAngleCorrection op (aa j) (bb j) (dd j) (vv j) (haa j) (hdd j) (hvv j)
  let F (j : Fin A.count) : C(unitInterval, ℝ) := theta.angle j + delta j
  refine ⟨fun j => intervalAngleExtension (F j), ?_, ?_⟩
  · intro j
    apply intervalAngleExtension_isTangentAngle g c hc b A j op hop
      (fun t => frameArcVelocity a beta d A j t)
    · intro t
      exact transformedMap_ne_zero (aa j) (bb j) (dd j) (vv j)
        (haa j) (hdd j) (hvv j) t
    · intro t
      exact tangentCoefficients_eq_normalized g o c hc b H A j t
        (hq (arc_mem_trace A j t.property))
    · intro t
      exact triangularAngleCorrection_lift op (aa j) (bb j) (dd j) (vv j)
        (haa j) (hdd j) (hvv j) P202Specs.PlaneTurning.reference
        P202.PlaneTurning.reference_ne_zero (theta.angle j) (theta.lifts j) t
  · intro j t
    change intervalAngleExtension (F j) t = _
    rw [intervalAngleExtension_coe]
    rfl


end CorrectedArcAngles

section IntegratedArcCalculus
open P202.CurveConnectionData

/-- The intrinsic formula applies at closed-arc endpoints whenever the real
angle is differentiable on the actual smooth extension germ. -/
theorem geodesicIntegrand_eq_of_angle_germ {q : RegularJordanCurve}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {theta : ℝ → ℝ} {theta' : ℝ}
    (hder : HasDerivAt theta theta' t)
    (he : tangentCoefficients g c hc b A j =ᶠ[𝓝 t]
      (fun s => ![Real.cos (theta s), Real.sin (theta s)])) :
    geodesicIntegrand g C o c hc A j t = theta' +
      frameOneForm C c hc b (A.arc j t) (velocity A j t) := by
  have hx := hq (arc_mem_trace A j ht)
  rw [geodesicIntegrand_eq_pairing g C o c hc hq A j ht,
    frameOneForm_apply C c hc b _ hx]
  exact orthonormalFrame_trig_geodesic_pairing g C hC.2 o b H.orthonormal
    (c.map_target hx) (arc_hasVelocity c hc hq A j ht) hder he
    (H.positive ⟨_, c.map_target hx⟩)

/-- Evaluation of a continuous one-form along any smooth presentation arc
is continuous up to both endpoints. -/
theorem oneForm_arc_continuousOn {q : RegularJordanCurve}
    (c : ModelChart 2 .euclidean M)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (j : Fin A.count) (omega : OneForm)
    (homega : ContinuousOn omega (P202Specs.ChartRegionStokes.chartTarget c)) :
    ContinuousOn (fun t => omega (A.arc j t) (velocity A j t)) (Icc (0 : ℝ) 1) := by
  have hA : ContinuousOn (A.arc j) (Icc (0 : ℝ) 1) :=
    fun t ht => (arc_contDiffAt A j ht).continuousAt.continuousWithinAt
  have hv : ContinuousOn (velocity A j) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hd : ContDiffAt ℝ ∞ (velocity A j) t := (arc_contDiffAt A j ht).derivWithin (by simp)
    exact hd.continuousAt.continuousWithinAt
  exact (homega.comp hA (fun t ht => hq (arc_mem_trace A j ht))).clm_apply hv

/-- The intrinsic geodesic integrand is continuous at the arc endpoints too:
local smooth angle lifts express it as a continuous angular rate plus the
literal connection-form evaluation. -/
theorem geodesicIntegrand_continuousOn {q : RegularJordanCurve}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (homega : ContinuousOn (frameOneForm C c hc b) (P202Specs.ChartRegionStokes.chartTarget c))
    (A : ArcPresentation q) (j : Fin A.count) :
    ContinuousOn (geodesicIntegrand g C o c hc A j) (Icc (0 : ℝ) 1) := by
  have hw := oneForm_arc_continuousOn c hq A j _ homega
  intro t ht
  obtain ⟨delta, hdelta, theta, htheta, hsm⟩ :=
    localTangentAngle_exists g o c hc b H hq A j ht
  have htJ : t ∈ Ioo (t-delta) (t+delta) := by constructor <;> linarith
  have hd := hsm.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hcont := ((hd.continuousAt (isOpen_Ioo.mem_nhds htJ)).continuousWithinAt
    (s := Icc (0 : ℝ) 1)).add (hw t ht)
  apply hcont.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (isOpen_Ioo.mem_nhds htJ)] with s hs hsJ
  apply geodesicIntegrand_eq_of_angle_germ g C hC o c hc b H hq A j hs
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hsJ)).differentiableAt (by simp)).hasDerivAt
  filter_upwards [isOpen_Ioo.mem_nhds hsJ] with r hr
  exact htheta.2 r hr

/-- Integrating an arbitrary continuous real lift gives its actual endpoint
increment. Differentiability is derived from the unit tangent coordinates. -/
theorem arcIntegral_eq_angleIncrement {q : RegularJordanCurve}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (homega : ContinuousOn (frameOneForm C c hc b) (P202Specs.ChartRegionStokes.chartTarget c))
    (A : ArcPresentation q) (j : Fin A.count) {theta : ℝ → ℝ}
    (htheta : IsTangentAngle g c hc b A j theta (Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc A j t) =
      theta 1 - theta 0 +
        ∫ t in (0 : ℝ)..1, frameOneForm C c hc b (A.arc j t) (velocity A j t) := by
  let f := geodesicIntegrand g C o c hc A j
  let w := fun t => frameOneForm C c hc b (A.arc j t) (velocity A j t)
  have hf : IntervalIntegrable f volume 0 1 :=
    (geodesicIntegrand_continuousOn g C hC o c hc b H hq homega A j).intervalIntegrable_of_Icc zero_le_one
  have hw : IntervalIntegrable w volume 0 1 :=
    (oneForm_arc_continuousOn c hq A j _ homega).intervalIntegrable_of_Icc zero_le_one
  have hthetaI : IsTangentAngle g c hc b A j theta (Ioo (0 : ℝ) 1) :=
    ⟨htheta.1.mono Ioo_subset_Icc_self, fun t ht => htheta.2 t (Ioo_subset_Icc_self ht)⟩
  have hFTC : (∫ t in (0 : ℝ)..1, (f t - w t)) = theta 1 - theta 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one htheta.1 _ (hf.sub hw)
    intro t ht
    have hd := tangentAngle_hasDerivAt g o c hc b H hq A j isOpen_Ioo
      (fun _ ht => ht) hthetaI ht
    have he := geodesicIntegrand_eq_angleDerivative_add_connection g C hC o c hc b H hq A j
      isOpen_Ioo (fun _ ht => ht) hthetaI ht
    convert hd using 1
    dsimp [f, w]
    linarith [he]
  rw [intervalIntegral.integral_sub hf hw] at hFTC
  dsimp [f, w] at hFTC
  linarith


end IntegratedArcCalculus

namespace SectorGeometry

def positiveRep (theta : Real.Angle) : ℝ :=
  if 0 < theta.toReal then theta.toReal else theta.toReal + 2 * Real.pi

lemma positiveRep_coe {r : ℝ} (hr : 0 < r) (hr' : r < 2 * Real.pi) :
    positiveRep (r : Real.Angle) = r := by
  unfold positiveRep
  by_cases hpi : r ≤ Real.pi
  · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], hpi⟩]
    simp only [hr, ↓reduceIte]
  · have heq : (r : Real.Angle).toReal = r - 2 * Real.pi :=
      Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr ⟨lt_of_not_ge hpi, by linarith [Real.pi_pos]⟩
    rw [heq, if_neg (by linarith)]
    ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

lemma sectorWidth_forward (o : Orientation ℝ V (Fin 2)) {u v : V}
    (hu : u ≠ 0) (hv : v ≠ 0) (hn : o.oangle u v ≠ (Real.pi : Real.Angle)) :
    positiveRep (o.oangle v (-u)) = Real.pi - (o.oangle u v).toReal := by
  have hlo := Real.Angle.neg_pi_lt_toReal (o.oangle u v)
  have hhi : (o.oangle u v).toReal < Real.pi :=
    (Real.Angle.toReal_le_pi _).lt_of_ne (fun h => hn (Real.Angle.toReal_eq_pi_iff.mp h))
  have heq : o.oangle v (-u) = (Real.pi - (o.oangle u v).toReal : ℝ) := by
    rw [o.oangle_neg_right hv hu, o.oangle_rev, Real.Angle.coe_sub, Real.Angle.coe_toReal]
    abel
  rw [heq]
  exact positiveRep_coe (by linarith) (by linarith)

lemma sectorWidth_reverse (o : Orientation ℝ V (Fin 2)) {u v : V}
    (hu : u ≠ 0) (hv : v ≠ 0) (hn : o.oangle u v ≠ (Real.pi : Real.Angle)) :
    positiveRep (o.oangle (-u) v) = Real.pi + (o.oangle u v).toReal := by
  have hlo := Real.Angle.neg_pi_lt_toReal (o.oangle u v)
  have hhi : (o.oangle u v).toReal < Real.pi :=
    (Real.Angle.toReal_le_pi _).lt_of_ne (fun h => hn (Real.Angle.toReal_eq_pi_iff.mp h))
  have heq : o.oangle (-u) v = (Real.pi + (o.oangle u v).toReal : ℝ) := by
    rw [o.oangle_neg_left hu hv, Real.Angle.coe_add, Real.Angle.coe_toReal]
    abel
  rw [heq]
  exact positiveRep_coe (by linarith) (by linarith)


lemma sin_nonpos_on_pi_two_pi {t : ℝ} (h1 : Real.pi ≤ t) (h2 : t ≤ 2 * Real.pi) :
    Real.sin t ≤ 0 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := t - Real.pi)
    (by linarith) (by linarith)
  have he : Real.sin t = -Real.sin (t - Real.pi) := by
    calc Real.sin t = Real.sin ((t - Real.pi) + Real.pi) := by congr 1; ring
         _ = _ := Real.sin_add_pi _
  rw [he]
  linarith

lemma sin_pos_iff_on_zero_two_pi {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 2 * Real.pi) :
    0 < Real.sin t ↔ t < Real.pi := by
  constructor
  · intro hs
    by_contra ht
    exact (not_lt_of_ge (sin_nonpos_on_pi_two_pi (le_of_not_gt ht) h2)) hs
  · exact Real.sin_pos_of_pos_of_lt_pi h0

/-- The full directed sector, including reflex sectors, is detected by the
left halfplanes of its two positively traversed incident tangent vectors. -/
lemma real_sector_criterion {delta t : ℝ}
    (hd0 : -Real.pi < delta) (hd1 : delta < Real.pi)
    (ht0 : 0 < t) (ht2 : t ≤ 2 * Real.pi) :
    (t < Real.pi - delta) ↔
      if 0 ≤ delta then
        (0 < Real.sin t ∧ 0 < Real.sin (delta + t))
      else (0 < Real.sin t ∨ 0 < Real.sin (delta + t)) := by
  have ht := sin_pos_iff_on_zero_two_pi ht0 ht2
  by_cases hd : 0 ≤ delta
  · rw [if_pos hd]
    by_cases htp : t < Real.pi
    · have hdts : 0 < Real.sin (delta + t) ↔ delta + t < Real.pi :=
        sin_pos_iff_on_zero_two_pi (by linarith) (by linarith)
      rw [ht, hdts]
      constructor
      · intro h; exact ⟨htp, by linarith⟩
      · intro h; linarith [h.2]
    · rw [ht]
      constructor
      · intro h; exact False.elim (htp (by linarith))
      · intro h; exact False.elim (htp h.1)
  · rw [if_neg hd]
    have hd' : delta < 0 := lt_of_not_ge hd
    by_cases htp : t < Real.pi
    · rw [ht]
      exact ⟨fun _ => Or.inl htp, fun _ => by linarith⟩
    · have hdts : 0 < Real.sin (delta + t) ↔ delta + t < Real.pi :=
        sin_pos_iff_on_zero_two_pi (by linarith) (by linarith)
      rw [ht, hdts]
      exact ⟨fun h => Or.inr (by linarith), fun h => by rcases h with h | h; contradiction; linarith⟩


lemma positiveRep_bounds (theta : Real.Angle) :
    0 < positiveRep theta ∧ positiveRep theta ≤ 2 * Real.pi := by
  unfold positiveRep
  split_ifs with h
  · exact ⟨h, by linarith [theta.toReal_le_pi, Real.pi_pos]⟩
  · exact ⟨by linarith [theta.neg_pi_lt_toReal, Real.pi_pos], by linarith⟩

lemma coe_positiveRep (theta : Real.Angle) : (positiveRep theta : Real.Angle) = theta := by
  unfold positiveRep
  split_ifs
  · exact Real.Angle.coe_toReal theta
  · rw [Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_two_pi, add_zero]


lemma sin_oangle (o : Orientation ℝ V (Fin 2)) (x y : V) :
    Real.Angle.sin (o.oangle x y) = o.areaForm x y / (‖x‖ * ‖y‖) := by
  rw [Orientation.oangle, Real.Angle.sin_coe, Complex.sin_arg, o.norm_kahler]
  simp [o.kahler_apply_apply]

lemma areaForm_pos_iff_sin_oangle_pos (o : Orientation ℝ V (Fin 2))
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 < o.areaForm x y ↔ 0 < Real.Angle.sin (o.oangle x y) := by
  rw [sin_oangle]
  exact (div_pos_iff_of_pos_right (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))).symm

lemma sector_criterion (o : Orientation ℝ V (Fin 2)) {u w v : V}
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hn : NormedSpace.normalize u ≠ -NormedSpace.normalize w) :
    (positiveRep (o.oangle w v) < Real.pi - (o.oangle u w).toReal) ↔
      if 0 ≤ (o.oangle u w).toReal then
        (0 < o.areaForm u v ∧ 0 < o.areaForm w v)
      else (0 < o.areaForm u v ∨ 0 < o.areaForm w v) := by
  have hpi : o.oangle u w ≠ (Real.pi : Real.Angle) := by
    intro h
    have hr := (o.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
    have he := hr.inv_norm_smul_eq hu (neg_ne_zero.mpr hw)
    exact hn (by simpa only [NormedSpace.normalize, norm_neg, smul_neg] using he)
  have hdel : (o.oangle u w).toReal < Real.pi :=
    (Real.Angle.toReal_le_pi _).lt_of_ne (fun h => hpi (Real.Angle.toReal_eq_pi_iff.mp h))
  have he := real_sector_criterion (Real.Angle.neg_pi_lt_toReal _) hdel
    (positiveRep_bounds (o.oangle w v)).1 (positiveRep_bounds (o.oangle w v)).2
  have hsinw : Real.sin (positiveRep (o.oangle w v)) = Real.Angle.sin (o.oangle w v) := by
    rw [← Real.Angle.sin_coe, coe_positiveRep]
  have hsinu : Real.sin ((o.oangle u w).toReal + positiveRep (o.oangle w v)) =
      Real.Angle.sin (o.oangle u v) := by
    rw [← Real.Angle.sin_coe, Real.Angle.coe_add, Real.Angle.coe_toReal,
      coe_positiveRep, o.oangle_add hu hw hv]
  rw [hsinw, hsinu] at he
  rw [← areaForm_pos_iff_sin_oangle_pos o hw hv,
    ← areaForm_pos_iff_sin_oangle_pos o hu hv] at he
  simpa only [and_comm, or_comm] using he


lemma oangle_toReal_nonneg_iff_areaForm_nonneg (o : Orientation ℝ V (Fin 2))
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 ≤ (o.oangle x y).toReal ↔ 0 ≤ o.areaForm x y := by
  rw [Real.Angle.toReal_nonneg_iff_sign_nonneg, Real.Angle.sign,
    sign_nonneg_iff, sin_oangle,
    le_div_iff₀ (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)), zero_mul]

lemma sector_area_criterion (o : Orientation ℝ V (Fin 2)) {u w v : V}
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hn : NormedSpace.normalize u ≠ -NormedSpace.normalize w) :
    (positiveRep (o.oangle w v) < Real.pi - (o.oangle u w).toReal) ↔
      if 0 ≤ o.areaForm u w then
        (0 < o.areaForm u v ∧ 0 < o.areaForm w v)
      else (0 < o.areaForm u v ∨ 0 < o.areaForm w v) := by
  rw [sector_criterion o hu hw hv hn]
  simp only [oangle_toReal_nonneg_iff_areaForm_nonneg o hu hw]

lemma graph_slope_criterion {ux uy wx wy x y : ℝ} (hu : 0 < ux) (hw : 0 < wx) :
    (0 < y - (if 0 < x then wy / wx else uy / ux) * x) ↔
      if 0 ≤ ux * wy - uy * wx then
        (0 < ux * y - uy * x ∧ 0 < wx * y - wy * x)
      else (0 < ux * y - uy * x ∨ 0 < wx * y - wy * x) := by
  have hU : ux * y - uy * x = ux * (y - uy / ux * x) := by
    field_simp
    <;> ring
  have hW : wx * y - wy * x = wx * (y - wy / wx * x) := by
    field_simp
    <;> ring
  have hdu : (0 < ux * y - uy * x) ↔ 0 < y - uy / ux * x := by
    rw [hU, mul_pos_iff_of_pos_left hu]
  have hdw : (0 < wx * y - wy * x) ↔ 0 < y - wy / wx * x := by
    rw [hW, mul_pos_iff_of_pos_left hw]
  have horder : (0 ≤ ux * wy - uy * wx) ↔ uy / ux ≤ wy / wx := by
    rw [div_le_div_iff₀ hu hw]
    constructor <;> intro h <;> nlinarith
  simp only [hdu, hdw, horder]
  by_cases h : uy / ux ≤ wy / wx
  · rw [if_pos h]
    by_cases hx : 0 < x
    · rw [if_pos hx]
      have hm := mul_le_mul_of_nonneg_right h hx.le
      constructor
      · intro hy; exact ⟨by linarith, hy⟩
      · exact fun hy => hy.2
    · rw [if_neg hx]
      have hm := mul_le_mul_of_nonpos_right h (le_of_not_gt hx)
      constructor
      · intro hy; exact ⟨hy, by linarith⟩
      · exact fun hy => hy.1
  · rw [if_neg h]
    have h' : wy / wx ≤ uy / ux := (lt_of_not_ge h).le
    by_cases hx : 0 < x
    · rw [if_pos hx]
      have hm := mul_le_mul_of_nonneg_right h' hx.le
      constructor
      · exact fun hy => Or.inr hy
      · intro hy; rcases hy with hy | hy <;> linarith
    · rw [if_neg hx]
      have hm := mul_le_mul_of_nonpos_right h' (le_of_not_gt hx)
      constructor
      · exact fun hy => Or.inl hy
      · intro hy; rcases hy with hy | hy <;> linarith


open P202Specs.PlanarRegionTopology
lemma graphFrame_determinant (axis u v : Plane) (haxis : ‖axis‖ = 1) :
    inner ℝ axis u * inner ℝ (quarterTurn axis) v -
      inner ℝ (quarterTurn axis) u * inner ℝ axis v =
        u 0 * v 1 - u 1 * v 0 := by
  have hs : axis 0 ^ 2 + axis 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq axis
    rw [haxis] at h
    simpa only [one_pow, Fin.sum_univ_two] using h.symm
  calc
    _ = (axis 0 ^ 2 + axis 1 ^ 2) * (u 0 * v 1 - u 1 * v 0) := by
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
        conj_trivial, quarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one,
        WithLp.ofLp_toLp]
      ring
    _ = _ := by rw [hs, one_mul]


lemma hasDerivWithinAt_inverse {f g : ℝ → ℝ} {D a : ℝ} {s : Set ℝ}
    (hg : ContinuousAt g a) (hf : HasDerivAt f D (g a)) (hD : D ≠ 0)
    (ha : a ∈ s) (hfg : ∀ᶠ x in 𝓝[s] a, f (g x) = x) :
    HasDerivWithinAt g D⁻¹ s a := by
  have hg' : Tendsto g (𝓝[s] a) (𝓝[(univ : Set ℝ)] (g a)) := by
    simpa only [nhdsWithin_univ] using hg.tendsto.mono_left nhdsWithin_le_nhds
  have h := hf.hasFDerivAt.hasFDerivWithinAt.of_comp_of_leftInverse hg'
    (hasDerivWithinAt_id a s).hasFDerivWithinAt hfg
    (f'symm := ContinuousLinearMap.toSpanSingleton ℝ D⁻¹)
    (fun x => by simp [hD]) ha
  convert h.hasDerivWithinAt using 1 <;> simp

lemma ray_sign_of_hasDerivWithinAt {f : ℝ → ℝ} {D : ℝ}
    (hf : HasDerivWithinAt f D (Ioi 0) 0) (hzero : f 0 = 0) (hD : D ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, (0 < f r ↔ 0 < D) := by
  have hs : Tendsto (fun r : ℝ => r⁻¹ * f r) (𝓝[>] 0) (𝓝 D) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hf
    convert h using 1
    funext r
    simp [slope_def_field, hzero, div_eq_mul_inv, mul_comm]
  rcases lt_or_gt_of_ne hD with hD | hD
  · filter_upwards [hs.eventually (eventually_lt_nhds hD), self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : 0 < r := hrpos
    have hneg : f r < 0 := (mul_neg_iff.mp hr).resolve_right
      (fun h => (not_lt_of_ge (inv_pos.mpr hrpos').le) h.1) |>.2
    exact iff_of_false (not_lt_of_ge hneg.le) (not_lt_of_ge hD.le)
  · filter_upwards [hs.eventually (eventually_gt_nhds hD), self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : 0 < r := hrpos
    exact ⟨fun _ => hD, fun _ => (mul_pos_iff_of_pos_left (inv_pos.mpr hrpos')).mp hr⟩

lemma continuous_clamped_inverse {u : ℝ → ℝ} {q δ : ℝ}
    (hu : Continuous u) (hδ : 0 < δ)
    (hm : StrictMonoOn u (Icc (q - δ) (q + δ))) :
    ∃ inv : ℝ → ℝ, Continuous inv ∧ inv (u q) = q ∧
      (∀ x, inv x ∈ Icc (q - δ) (q + δ)) ∧
      (∀ᶠ x in 𝓝 (u q), u (inv x) = x) := by
  let parameterInterval : Set ℝ := Icc (q - δ) (q + δ)
  let J : Set ℝ := Icc (u (q - δ)) (u (q + δ))
  have hab : q - δ ≤ q + δ := by linarith
  have himage : u '' parameterInterval = J :=
    hu.continuousOn.image_Icc_of_monotoneOn hab hm.monotoneOn
  let p : parameterInterval → J := fun t => ⟨u t.val, himage ▸ mem_image_of_mem u t.property⟩
  have hp : Continuous p := (hu.comp continuous_subtype_val).subtype_mk _
  have hpinj : Function.Injective p := by
    intro x y hxy
    exact Subtype.ext (hm.injOn x.property y.property (congrArg Subtype.val hxy))
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨x, hx, he⟩ := (himage.symm ▸ y.property : y.val ∈ u '' parameterInterval)
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let e : parameterInterval ≃ₜ J := hp.isClosedEmbedding hpinj |>.isEmbedding.toHomeomorphOfSurjective hpsurj
  have hends : u (q - δ) ≤ u (q + δ) := hm.monotoneOn
    ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  let inv : ℝ → ℝ := fun x => (e.symm (projIcc _ _ hends x)).val
  have hi : Continuous inv := continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)
  have hqI : q ∈ parameterInterval := ⟨by linarith, by linarith⟩
  have hqJ : u q ∈ J := himage ▸ mem_image_of_mem u hqI
  have hqinv : inv (u q) = q := by
    have heq : projIcc _ _ hends (u q) = e ⟨q, hqI⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val (projIcc_of_mem hends hqJ)
    simp only [inv, heq, e.symm_apply_apply]
  refine ⟨inv, hi, hqinv, (fun x => (e.symm (projIcc _ _ hends x)).property), ?_⟩
  have hlt : u (q - δ) < u q := hm ⟨le_rfl, hab⟩ hqI (by linarith)
  have hgt : u q < u (q + δ) := hm hqI ⟨hab, le_rfl⟩ (by linarith)
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hlt, hgt⟩] with x hx
  have hxJ : x ∈ J := ⟨hx.1.le, hx.2.le⟩
  have hid := congrArg Subtype.val (e.apply_symm_apply (projIcc _ _ hends x))
  change u (inv x) = (projIcc _ _ hends x).val at hid
  exact hid.trans (congrArg Subtype.val (projIcc_of_mem hends hxJ))

lemma continuous_clamped_inverse_antitone {u : ℝ → ℝ} {q δ : ℝ}
    (hu : Continuous u) (hδ : 0 < δ)
    (hm : StrictAntiOn u (Icc (q - δ) (q + δ))) :
    ∃ inv : ℝ → ℝ, Continuous inv ∧ inv (u q) = q ∧
      (∀ x, inv x ∈ Icc (q - δ) (q + δ)) ∧
      (∀ᶠ x in 𝓝 (u q), u (inv x) = x) := by
  have hmneg : StrictMonoOn (fun z => -u z) (Icc (q - δ) (q + δ)) := fun a ha b hb hab =>
    neg_lt_neg (hm ha hb hab)
  obtain ⟨inv, hi, hiq, hiI, hinv⟩ := continuous_clamped_inverse hu.neg hδ hmneg
  refine ⟨fun x => inv (-x), hi.comp continuous_neg, hiq, (fun x => hiI (-x)), ?_⟩
  have ht : Tendsto (fun x : ℝ => -x) (𝓝 (u q)) (𝓝 (-u q)) := continuous_neg.continuousAt.tendsto
  filter_upwards [ht.eventually hinv] with x hx
  exact neg_injective hx


lemma graph_right_derivative_of_parametrization
    {u uR vR height : ℝ → ℝ} {q δ du dv : ℝ}
    (hu : Continuous u) (hδ : 0 < δ)
    (hm : StrictMonoOn u (Icc (q - δ) (q + δ)))
    (huR : HasDerivAt uR du q) (hdu : du ≠ 0) (hvR : HasDerivAt vR dv q)
    (huReq : EqOn uR u (Icc q (q + δ)))
    (hgraph : EqOn (fun z => height (u z)) vR (Icc q (q + δ))) :
    HasDerivWithinAt height (dv / du) (Ici (u q)) (u q) := by
  obtain ⟨inv, hi, hiq, hiI, hinv⟩ := continuous_clamped_inverse hu hδ hm
  have hqI : q ∈ Icc (q - δ) (q + δ) := ⟨by linarith, by linarith⟩
  have hright : ∀ᶠ x in 𝓝[≥] (u q),
      inv x ∈ Icc q (q + δ) ∧ u (inv x) = x := by
    filter_upwards [hinv.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxq
    refine ⟨⟨?_, (hiI x).2⟩, hx⟩
    by_contra h
    have hh := hm (hiI x) hqI (lt_of_not_ge h)
    rw [hx] at hh
    exact (not_lt_of_ge hxq) hh
  have hfg : ∀ᶠ x in 𝓝[≥] (u q), uR (inv x) = x := by
    filter_upwards [hright] with x hx
    exact (huReq hx.1).trans hx.2
  have huR' : HasDerivAt uR du (inv (u q)) := hiq.symm ▸ huR
  have hdi : HasDerivWithinAt inv du⁻¹ (Ici (u q)) (u q) :=
    hasDerivWithinAt_inverse hi.continuousAt huR' hdu (by simp) hfg
  have heq : height =ᶠ[𝓝[≥] (u q)] (vR ∘ inv) := by
    filter_upwards [hright] with x hx
    simpa only [Function.comp_apply, hx.2] using hgraph hx.1
  have hvR' : HasDerivAt vR dv (inv (u q)) := hiq.symm ▸ hvR
  simpa only [div_eq_mul_inv] using
    (hvR'.comp_hasDerivWithinAt (u q) hdi).congr_of_eventuallyEq_of_mem heq (by simp)

lemma graph_left_derivative_of_parametrization
    {u uL vL height : ℝ → ℝ} {q δ du dv : ℝ}
    (hu : Continuous u) (hδ : 0 < δ)
    (hm : StrictMonoOn u (Icc (q - δ) (q + δ)))
    (huL : HasDerivAt uL du q) (hdu : du ≠ 0) (hvL : HasDerivAt vL dv q)
    (huLeq : EqOn uL u (Icc (q - δ) q))
    (hgraph : EqOn (fun z => height (u z)) vL (Icc (q - δ) q)) :
    HasDerivWithinAt height (dv / du) (Iic (u q)) (u q) := by
  obtain ⟨inv, hi, hiq, hiI, hinv⟩ := continuous_clamped_inverse hu hδ hm
  have hqI : q ∈ Icc (q - δ) (q + δ) := ⟨by linarith, by linarith⟩
  have hleft : ∀ᶠ x in 𝓝[≤] (u q),
      inv x ∈ Icc (q - δ) q ∧ u (inv x) = x := by
    filter_upwards [hinv.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxq
    refine ⟨⟨(hiI x).1, ?_⟩, hx⟩
    by_contra h
    have hh := hm hqI (hiI x) (lt_of_not_ge h)
    rw [hx] at hh
    exact (not_lt_of_ge hxq) hh
  have hfg : ∀ᶠ x in 𝓝[≤] (u q), uL (inv x) = x := by
    filter_upwards [hleft] with x hx
    exact (huLeq hx.1).trans hx.2
  have huL' : HasDerivAt uL du (inv (u q)) := hiq.symm ▸ huL
  have hdi : HasDerivWithinAt inv du⁻¹ (Iic (u q)) (u q) :=
    hasDerivWithinAt_inverse hi.continuousAt huL' hdu (by simp) hfg
  have heq : height =ᶠ[𝓝[≤] (u q)] (vL ∘ inv) := by
    filter_upwards [hleft] with x hx
    simpa only [Function.comp_apply, hx.2] using hgraph hx.1
  have hvL' : HasDerivAt vL dv (inv (u q)) := hiq.symm ▸ hvL
  simpa only [div_eq_mul_inv] using
    (hvL'.comp_hasDerivWithinAt (u q) hdi).congr_of_eventuallyEq_of_mem heq (by simp)

lemma graph_right_derivative_of_antitone_parametrization
    {u uR vR height : ℝ → ℝ} {q δ du dv : ℝ}
    (hu : Continuous u) (hδ : 0 < δ)
    (hm : StrictAntiOn u (Icc (q - δ) (q + δ)))
    (huR : HasDerivAt uR du q) (hdu : du ≠ 0) (hvR : HasDerivAt vR dv q)
    (huReq : EqOn uR u (Icc (q - δ) q))
    (hgraph : EqOn (fun z => height (u z)) vR (Icc (q - δ) q)) :
    HasDerivWithinAt height (dv / du) (Ici (u q)) (u q) := by
  obtain ⟨inv, hi, hiq, hiI, hinv⟩ := continuous_clamped_inverse_antitone hu hδ hm
  have hqI : q ∈ Icc (q - δ) (q + δ) := ⟨by linarith, by linarith⟩
  have hright : ∀ᶠ x in 𝓝[≥] (u q),
      inv x ∈ Icc (q - δ) q ∧ u (inv x) = x := by
    filter_upwards [hinv.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxq
    refine ⟨⟨(hiI x).1, ?_⟩, hx⟩
    by_contra h
    have hh := hm hqI (hiI x) (lt_of_not_ge h)
    rw [hx] at hh
    exact (not_lt_of_ge hxq) hh
  have hfg : ∀ᶠ x in 𝓝[≥] (u q), uR (inv x) = x := by
    filter_upwards [hright] with x hx
    exact (huReq hx.1).trans hx.2
  have huR' : HasDerivAt uR du (inv (u q)) := hiq.symm ▸ huR
  have hdi : HasDerivWithinAt inv du⁻¹ (Ici (u q)) (u q) :=
    hasDerivWithinAt_inverse hi.continuousAt huR' hdu (by simp) hfg
  have heq : height =ᶠ[𝓝[≥] (u q)] (vR ∘ inv) := by
    filter_upwards [hright] with x hx
    simpa only [Function.comp_apply, hx.2] using hgraph hx.1
  have hvR' : HasDerivAt vR dv (inv (u q)) := hiq.symm ▸ hvR
  simpa only [div_eq_mul_inv] using
    (hvR'.comp_hasDerivWithinAt (u q) hdi).congr_of_eventuallyEq_of_mem heq (by simp)

lemma graph_left_derivative_of_antitone_parametrization
    {u uL vL height : ℝ → ℝ} {q δ du dv : ℝ}
    (hu : Continuous u) (hδ : 0 < δ)
    (hm : StrictAntiOn u (Icc (q - δ) (q + δ)))
    (huL : HasDerivAt uL du q) (hdu : du ≠ 0) (hvL : HasDerivAt vL dv q)
    (huLeq : EqOn uL u (Icc q (q + δ)))
    (hgraph : EqOn (fun z => height (u z)) vL (Icc q (q + δ))) :
    HasDerivWithinAt height (dv / du) (Iic (u q)) (u q) := by
  obtain ⟨inv, hi, hiq, hiI, hinv⟩ := continuous_clamped_inverse_antitone hu hδ hm
  have hqI : q ∈ Icc (q - δ) (q + δ) := ⟨by linarith, by linarith⟩
  have hleft : ∀ᶠ x in 𝓝[≤] (u q),
      inv x ∈ Icc q (q + δ) ∧ u (inv x) = x := by
    filter_upwards [hinv.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxq
    refine ⟨⟨?_, (hiI x).2⟩, hx⟩
    by_contra h
    have hh := hm (hiI x) hqI (lt_of_not_ge h)
    rw [hx] at hh
    exact (not_lt_of_ge hxq) hh
  have hfg : ∀ᶠ x in 𝓝[≤] (u q), uL (inv x) = x := by
    filter_upwards [hleft] with x hx
    exact (huLeq hx.1).trans hx.2
  have huL' : HasDerivAt uL du (inv (u q)) := hiq.symm ▸ huL
  have hdi : HasDerivWithinAt inv du⁻¹ (Iic (u q)) (u q) :=
    hasDerivWithinAt_inverse hi.continuousAt huL' hdu (by simp) hfg
  have heq : height =ᶠ[𝓝[≤] (u q)] (vL ∘ inv) := by
    filter_upwards [hleft] with x hx
    simpa only [Function.comp_apply, hx.2] using hgraph hx.1
  have hvL' : HasDerivAt vL dv (inv (u q)) := hiq.symm ▸ hvL
  simpa only [div_eq_mul_inv] using
    (hvL'.comp_hasDerivWithinAt (u q) hdi).congr_of_eventuallyEq_of_mem heq (by simp)

lemma graph_ray_sign_at {f : ℝ → ℝ} {a mL mR x y : ℝ}
    (hL : HasDerivWithinAt f mL (Iic a) a)
    (hR : HasDerivWithinAt f mR (Ici a) a)
    (htrans : y - (if 0 < x then mR else mL) * x ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (f (a + r * x) < f a + r * y ↔ 0 < y - (if 0 < x then mR else mL) * x) := by
  have hline : HasDerivWithinAt (fun r : ℝ => a + r * x) x (Ioi 0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const x).const_add a).hasDerivWithinAt
  have hcomp : HasDerivWithinAt (fun r : ℝ => f (a + r * x))
      ((if 0 < x then mR else mL) * x) (Ioi 0) 0 := by
    rcases lt_trichotomy x 0 with hx | hx | hx
    · convert hL.comp_of_eq 0 hline
        (fun r hr => by have hh := (mul_neg_of_pos_of_neg hr hx).le; change a + r * x ≤ a; linarith)
        (by simp) using 1
      · rfl
      · simp only [not_lt_of_ge hx.le, ↓reduceIte]
    · subst x
      simpa using (hasDerivWithinAt_const (0 : ℝ) (Ioi 0) (f a))
    · convert hR.comp_of_eq 0 hline
        (fun r hr => by have hh := (mul_pos hr hx).le; change a ≤ a + r * x; linarith)
        (by simp) using 1
      · rfl
      · simp only [hx, ↓reduceIte]
  have hbase : HasDerivWithinAt (fun r : ℝ => f a + r * y) y (Ioi 0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const y).const_add (f a)).hasDerivWithinAt
  have hdiff : HasDerivWithinAt (fun r : ℝ => f a + r * y - f (a + r * x))
      (y - (if 0 < x then mR else mL) * x) (Ioi 0) 0 := by
    convert hbase.sub hcomp using 1
  simpa only [sub_pos] using ray_sign_of_hasDerivWithinAt hdiff (by simp) htrans


end SectorGeometry

section IntrinsicSectorWidths

lemma chartVector_neg (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    chartVector c hc x (-v) = -chartVector c hc x v := by
  have hx' : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target := hx
  simp only [chartVector, dite_eq_left hx', map_neg]

def chartVectorEquiv (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    Plane ≃ₗ[ℝ] TangentSpace S (chartPoint c x) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans
    ((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x) (c.map_target hx)).symm

@[simp] lemma chartVectorEquiv_apply (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane)
    (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c) (v : Plane) :
    chartVectorEquiv c hc x hx v = chartVector c hc x v := by
  have hx' : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target := hx
  simp only [chartVectorEquiv, chartVector, dite_eq_left hx']
  rfl

lemma interiorAngle_bounds_of_corner_bounds {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (j : Fin A.count) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hbound : -Real.pi < metricCornerAngle g o c hc A j ∧
      metricCornerAngle g o c hc A j < Real.pi) :
    0 < interiorAngle g o c hc A s j ∧ interiorAngle g o c hc A s j < 2 * Real.pi := by
  rcases hs with rfl | rfl <;> unfold interiorAngle <;> constructor <;> linarith [hbound.1,hbound.2]

lemma metric_width_of_corner_bounds {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (j : Fin A.count) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c)
    (hbound : -Real.pi < metricCornerAngle g o c hc A j ∧
      metricCornerAngle g o c hc A j < Real.pi) :
    positiveMetricAngle g o c hc (A.arc j 1) (outgoingRay A s j) (incomingRay A s j) =
      interiorAngle g o c hc A s j := by
  let p := chartPoint c (A.arc j 1)
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let u := chartVector c hc (A.arc j 1) (velocity A j 1)
  let v := chartVector c hc (A.arc j 1) (velocity A (finRotate A.count j) 0)
  let op := planeOrientation g o p
  have hu : u ≠ 0 := by
    change chartVector c hc (A.arc j 1) (velocity A j 1) ≠ 0
    rw [← chartVectorEquiv_apply c hc _ hx]
    intro he
    apply A.regular j 1 (by simp)
    exact (chartVectorEquiv c hc _ hx).injective (he.trans (map_zero _).symm)
  have hv : v ≠ 0 := by
    change chartVector c hc (A.arc j 1) (velocity A (finRotate A.count j) 0) ≠ 0
    rw [← chartVectorEquiv_apply c hc _ hx]
    intro he
    apply A.regular (finRotate A.count j) 0 (by simp)
    exact (chartVectorEquiv c hc _ hx).injective (he.trans (map_zero _).symm)
  have hang : metricCornerAngle g o c hc A j = (op.oangle u v).toReal := rfl
  have hpi : op.oangle u v ≠ (Real.pi : Real.Angle) := by
    intro he
    have hre := Real.Angle.toReal_eq_pi_iff.mpr he
    rw [← hang] at hre
    exact hbound.2.ne hre
  rcases hs with rfl | rfl
  · simp only [outgoingRay, incomingRay, if_pos rfl]
    change SectorGeometry.positiveRep (op.oangle v
      (chartVector c hc (A.arc j 1) (-velocity A j 1))) =
      Real.pi - 1 * (op.oangle u v).toReal
    rw [chartVector_neg c hc _ hx]
    simpa only [one_mul] using SectorGeometry.sectorWidth_forward op hu hv hpi
  · have hneg : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [outgoingRay, incomingRay, if_neg hneg]
    change SectorGeometry.positiveRep (op.oangle
      (chartVector c hc (A.arc j 1) (-velocity A j 1)) v) =
      Real.pi - (-1) * (op.oangle u v).toReal
    rw [chartVector_neg c hc _ hx]
    simpa only [neg_one_mul, sub_neg_eq_add] using
      SectorGeometry.sectorWidth_reverse op hu hv hpi

/-- Every actual metric principal corner is strictly between -pi and pi. -/
lemma metricCornerAngle_bounds {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (j : Fin A.count)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    -Real.pi < metricCornerAngle g o c hc A j ∧
      metricCornerAngle g o c hc A j < Real.pi := by
  let p := chartPoint c (A.arc j 1)
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  have h := P202.MetricBoundaryTurning.mappedAngle_bounds (planeOrientation g o p)
    (chartVectorEquiv c hc (A.arc j 1) hx).toLinearMap
    (chartVectorEquiv c hc (A.arc j 1) hx).injective
    (A.regular j 1 (by simp)) (A.regular (finRotate A.count j) 0 (by simp)) (A.noncuspidal j)
  change -Real.pi < ((planeOrientation g o p).oangle
    (chartVector c hc (A.arc j 1) (velocity A j 1))
    (chartVector c hc (A.arc j 1) (velocity A (finRotate A.count j) 0))).toReal ∧
    ((planeOrientation g o p).oangle
      (chartVector c hc (A.arc j 1) (velocity A j 1))
      (chartVector c hc (A.arc j 1) (velocity A (finRotate A.count j) 0))).toReal < Real.pi
  simpa only [LinearEquiv.coe_coe, chartVectorEquiv_apply, velocity] using h

lemma interiorAngle_bounds {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (j : Fin A.count) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    0 < interiorAngle g o c hc A s j ∧ interiorAngle g o c hc A s j < 2 * Real.pi :=
  interiorAngle_bounds_of_corner_bounds g o c hc A j s hs (metricCornerAngle_bounds g o c hc A j hx)

lemma metric_width {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (j : Fin A.count) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c) :
    positiveMetricAngle g o c hc (A.arc j 1) (outgoingRay A s j) (incomingRay A s j) =
      interiorAngle g o c hc A s j :=
  metric_width_of_corner_bounds g o c hc A j s hs hx (metricCornerAngle_bounds g o c hc A j hx)

end IntrinsicSectorWidths

/-- The intrinsic component formula for every original presentation and every
coordinate angle choice, including all principal short corner rotations. -/
theorem component_formula {q : RegularJordanCurve}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (hq : q.trace ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (A : ArcPresentation q) (op : Orientation ℝ Plane (Fin 2))
    (hop : ∀ v, op.rightAngleRotation v = quarterTurn v) (theta : AngleChoices op A) :
    (∑ j, ∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc A j t) +
      (∑ j, metricCornerAngle g o c hc A j) =
      totalTurning theta + P202Specs.ChartRegionStokes.componentIntegral (frameOneForm C c hc b) q := by
  have homega := (frameOneForm_contDiffOn C c hc b).continuousOn
  obtain ⟨psi, hpsi, hpsiEq⟩ := exists_corrected_arcAngles g o c hc b H hq A op hop theta
  have hjoin (j : Fin A.count) :
      a (A.arc j 1) = a (A.arc (finRotate A.count j) 0) ∧
      beta (A.arc j 1) = beta (A.arc (finRotate A.count j) 0) ∧
      d (A.arc j 1) = d (A.arc (finRotate A.count j) 0) := by
    rw [← arc_join A j]
    exact ⟨rfl, rfl, rfl⟩
  have hturn := upperTriangular_totalTurning_invariant op (finRotate A.count)
    (fun j => velocity A j 0) (fun j => velocity A j 1)
    (fun j => A.regular j 0 (by simp)) (fun j => A.regular j 1 (by simp)) A.noncuspidal
    (fun j => a (A.arc j 0)) (fun j => beta (A.arc j 0)) (fun j => d (A.arc j 0))
    (fun j => a (A.arc j 1)) (fun j => beta (A.arc j 1)) (fun j => d (A.arc j 1))
    (fun j => H.pos_a _ (hq (arc_mem_trace A j (by simp))))
    (fun j => H.pos_d _ (hq (arc_mem_trace A j (by simp)))) hjoin
    (fun j => theta.angle j 0) (fun j => theta.angle j 1)
  have hsum : (∑ j, (psi j 1 - psi j 0 + metricCornerAngle g o c hc A j)) =
      totalTurning theta := by
    convert hturn using 1
    apply Finset.sum_congr rfl
    intro j _
    have h0 := hpsiEq j 0
    have h1 := hpsiEq j 1
    norm_num at h0 h1
    rw [h1, h0,
      metricCornerAngle_eq_upperTriangular g o c hc b H op hop A j
        (hq (arc_mem_trace A j (by simp)))]
    rfl
  have hI (j : Fin A.count) :=
    arcIntegral_eq_angleIncrement g C hC o c hc b H hq homega A j (hpsi j)
  rw [componentIntegral_eq_arcs_of_continuous A _ hq homega]
  calc
    _ = (∑ j, (psi j 1 - psi j 0 + metricCornerAngle g o c hc A j)) +
        ∑ j, ∫ t in (0 : ℝ)..1, frameOneForm C c hc b (A.arc j t) (velocity A j t) := by
      simp_rw [hI]
      simp only [Finset.sum_add_distrib]
      ring
    _ = _ := by rw [hsum]

/-- All analytic clauses of the original intrinsic boundary theorem. -/
theorem componentCalculus : P202Specs.MetricBoundaryTurning.Expected.componentCalculus.{u} := by
  intro M inst S g C hC o c hc hpositive b a beta d H
  refine ⟨frameOneForm_contDiffOn C c hc b, ?_⟩
  intro q hq A
  obtain ⟨hvelocity, hregularity, hlocalAngle, hidentity⟩ :=
    arcCalculus S g C hC o c hc b a beta d H q hq A
  refine ⟨?_, hregularity, ?_, hlocalAngle, hidentity, ?_⟩
  · intro j t ht
    exact ⟨(hvelocity j t ht).1, (hvelocity j t ht).2.1⟩
  · intro j
    exact (geodesicIntegrand_continuousOn g C hC o c hc b H hq
      (frameOneForm_contDiffOn C c hc b).continuousOn A j).intervalIntegrable_of_Icc zero_le_one
  · intro op hop theta
    exact component_formula g C hC o c hc b H hq A op hop theta

lemma metric_sector_criterion
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (x U W v : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c)
    (hU : U ≠ 0) (hW : W ≠ 0) (hv : v ≠ 0)
    (hn : NormedSpace.normalize U ≠ -NormedSpace.normalize W) :
    (positiveMetricAngle g o c hc x W v < positiveMetricAngle g o c hc x W (-U)) ↔
      if 0 ≤ U 0 * W 1 - U 1 * W 0 then
        (0 < U 0 * v 1 - U 1 * v 0 ∧ 0 < W 0 * v 1 - W 1 * v 0)
      else (0 < U 0 * v 1 - U 1 * v 0 ∨ 0 < W 0 * v 1 - W 1 * v 0) := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let q := planeOrientation g o p
  let f := chartVectorEquiv c hc x hx
  have hnonzero (z : Plane) (hz : z ≠ 0) : chartVector c hc x z ≠ 0 := by
    rw [← chartVectorEquiv_apply c hc x hx]
    intro he
    exact hz (f.injective (he.trans (map_zero _).symm))
  have hU' := hnonzero U hU
  have hW' := hnonzero W hW
  have hv' := hnonzero v hv
  have hn' : NormedSpace.normalize (chartVector c hc x U) ≠
      -NormedSpace.normalize (chartVector c hc x W) := by
    simpa only [f, LinearEquiv.coe_coe, chartVectorEquiv_apply] using
      linearMap_preserves_noncuspidality f.toLinearMap f.injective hU hW hn
  have hpi : q.oangle (chartVector c hc x U) (chartVector c hc x W) ≠
      (Real.pi : Real.Angle) := by
    intro h
    have hr := (q.oangle_eq_pi_iff_sameRay_neg.mp h).2.2
    have he := hr.inv_norm_smul_eq hU' (neg_ne_zero.mpr hW')
    exact hn' (by simpa only [NormedSpace.normalize, norm_neg, smul_neg] using he)
  have hsec := SectorGeometry.sector_area_criterion q hU' hW' hv' hn'
  have hwidth : SectorGeometry.positiveRep
      (q.oangle (chartVector c hc x W) (-chartVector c hc x U)) =
      Real.pi - (q.oangle (chartVector c hc x U) (chartVector c hc x W)).toReal :=
    SectorGeometry.sectorWidth_forward q hU' hW' hpi
  have harea (z z' : Plane) : q.areaForm (chartVector c hc x z) (chartVector c hc x z') =
      (a x * d x) * (z 0 * z' 1 - z 1 * z' 0) :=
    chartVector_orientedArea g o c hc b H x z z' hx
  have hscale : 0 < a x * d x := mul_pos (H.pos_a x hx) (H.pos_d x hx)
  change (SectorGeometry.positiveRep (q.oangle (chartVector c hc x W) (chartVector c hc x v)) <
    SectorGeometry.positiveRep (q.oangle (chartVector c hc x W) (chartVector c hc x (-U)))) ↔ _
  rw [chartVector_neg c hc x hx U, hwidth, hsec]
  simp only [harea, mul_nonneg_iff_of_pos_left hscale, mul_pos_iff_of_pos_left hscale]


lemma metric_sector_graph_criterion
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (x U W v axis : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c)
    (hU : U ≠ 0) (hW : W ≠ 0) (hv : v ≠ 0)
    (hn : NormedSpace.normalize U ≠ -NormedSpace.normalize W)
    (haxis : ‖axis‖ = 1) (hUX : 0 < inner ℝ axis U) (hWX : 0 < inner ℝ axis W) :
    (positiveMetricAngle g o c hc x W v < positiveMetricAngle g o c hc x W (-U)) ↔
      0 < inner ℝ (quarterTurn axis) v -
        (if 0 < inner ℝ axis v then
          inner ℝ (quarterTurn axis) W / inner ℝ axis W
        else inner ℝ (quarterTurn axis) U / inner ℝ axis U) * inner ℝ axis v := by
  have h := SectorGeometry.graph_slope_criterion
    (uy := inner ℝ (quarterTurn axis) U) (wy := inner ℝ (quarterTurn axis) W)
    (x := inner ℝ axis v) (y := inner ℝ (quarterTurn axis) v) hUX hWX
  simp only [SectorGeometry.graphFrame_determinant axis U W haxis,
    SectorGeometry.graphFrame_determinant axis U v haxis,
    SectorGeometry.graphFrame_determinant axis W v haxis] at h
  exact (metric_sector_criterion g o c hc b H x U W v hx hU hW hv hn).trans h.symm


namespace BoundarySectorGraph
open P202Specs.BoundaryGraphDirections P202.BoundaryGraphDirections SectorGeometry
set_option maxHeartbeats 1200000

lemma height_one_sided_derivatives
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hσ : s i = 1) :
    HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (deriv G.arc.leftExtension t) /
        inner ℝ G.arc.axis (deriv G.arc.leftExtension t))
      (Iic (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t) ∧
    HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (deriv G.arc.rightExtension t) /
        inner ℝ G.arc.axis (deriv G.arc.rightExtension t))
      (Ici (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t) := by
  let c := R.curve i
  let e := G.arc.axis
  let u := arcProjection c e
  have hut : Continuous u := continuous_const.inner
    (c.parametrization.continuous.comp continuous_quotient_mk')
  have hm : StrictMonoOn u (Icc (t - G.arc.radius) (t + G.arc.radius)) := G.increasing hσ
  have ht : t ∈ Ioo (t - G.arc.extensionRadius) (t + G.arc.extensionRadius) := by
    have := G.arc.radius_pos
    have := G.arc.radius_lt
    constructor <;> linarith
  have hL : DifferentiableAt ℝ G.arc.leftExtension t :=
    (G.arc.left_smooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hR : DifferentiableAt ℝ G.arc.rightExtension t :=
    (G.arc.right_smooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hprojL : HasDerivAt (fun z => inner ℝ e (G.arc.leftExtension z))
      (inner ℝ e (deriv G.arc.leftExtension t)) t := by
    simpa using (hasDerivAt_const t e).inner ℝ hL.hasDerivAt
  have hprojR : HasDerivAt (fun z => inner ℝ e (G.arc.rightExtension z))
      (inner ℝ e (deriv G.arc.rightExtension t)) t := by
    simpa using (hasDerivAt_const t e).inner ℝ hR.hasDerivAt
  have hvertL : HasDerivAt (fun z => inner ℝ (quarterTurn e) (G.arc.leftExtension z))
      (inner ℝ (quarterTurn e) (deriv G.arc.leftExtension t)) t := by
    simpa using (hasDerivAt_const t (quarterTurn e)).inner ℝ hL.hasDerivAt
  have hvertR : HasDerivAt (fun z => inner ℝ (quarterTurn e) (G.arc.rightExtension z))
      (inner ℝ (quarterTurn e) (deriv G.arc.rightExtension t)) t := by
    simpa using (hasDerivAt_const t (quarterTurn e)).inner ℝ hR.hasDerivAt
  have hnL : inner ℝ e (deriv G.arc.leftExtension t) ≠ 0 := by
    have hh := G.arc.left_positive t ⟨by linarith [G.arc.radius_pos], le_rfl⟩
    simpa only [hσ, one_mul] using hh.ne'
  have hnR : inner ℝ e (deriv G.arc.rightExtension t) ≠ 0 := by
    have hh := G.arc.right_positive t ⟨le_rfl, by linarith [G.arc.radius_pos]⟩
    simpa only [hσ, one_mul] using hh.ne'
  have hheight : ∀ z ∈ Icc (t - G.arc.radius) (t + G.arc.radius),
      G.height (u z) = inner ℝ (quarterTurn e) (realLift c.parametrization z) := by
    intro z hz
    have hh := congrArg (fun p => inner ℝ (quarterTurn e) p) (G.arc_identity z hz)
    simpa only [frame_vertical G.arc.unit_axis G.frame, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, c, u, e] using hh.symm
  constructor
  · apply graph_left_derivative_of_parametrization hut G.arc.radius_pos hm hprojL hnL hvertL
    · intro z hz
      simp only [u, arcProjection]
      rw [G.arc.left_eq hz]
    · intro z hz
      dsimp only
      rw [hheight z ⟨hz.1, by linarith [hz.2, G.arc.radius_pos]⟩, G.arc.left_eq hz]
  · apply graph_right_derivative_of_parametrization hut G.arc.radius_pos hm hprojR hnR hvertR
    · intro z hz
      simp only [u, arcProjection]
      rw [G.arc.right_eq hz]
    · intro z hz
      dsimp only
      rw [hheight z ⟨by linarith [hz.1, G.arc.radius_pos], hz.2⟩, G.arc.right_eq hz]
lemma height_one_sided_derivatives_reverse
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hσ : s i = -1) :
    HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (deriv G.arc.rightExtension t) /
        inner ℝ G.arc.axis (deriv G.arc.rightExtension t))
      (Iic (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t) ∧
    HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (deriv G.arc.leftExtension t) /
        inner ℝ G.arc.axis (deriv G.arc.leftExtension t))
      (Ici (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t) := by
  let c := R.curve i
  let e := G.arc.axis
  let u := arcProjection c e
  have hut : Continuous u := continuous_const.inner
    (c.parametrization.continuous.comp continuous_quotient_mk')
  have hm : StrictAntiOn u (Icc (t - G.arc.radius) (t + G.arc.radius)) := G.decreasing hσ
  have ht : t ∈ Ioo (t - G.arc.extensionRadius) (t + G.arc.extensionRadius) := by
    have := G.arc.radius_pos
    have := G.arc.radius_lt
    constructor <;> linarith
  have hL : DifferentiableAt ℝ G.arc.leftExtension t :=
    (G.arc.left_smooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hR : DifferentiableAt ℝ G.arc.rightExtension t :=
    (G.arc.right_smooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hprojL : HasDerivAt (fun z => inner ℝ e (G.arc.leftExtension z))
      (inner ℝ e (deriv G.arc.leftExtension t)) t := by
    simpa using (hasDerivAt_const t e).inner ℝ hL.hasDerivAt
  have hprojR : HasDerivAt (fun z => inner ℝ e (G.arc.rightExtension z))
      (inner ℝ e (deriv G.arc.rightExtension t)) t := by
    simpa using (hasDerivAt_const t e).inner ℝ hR.hasDerivAt
  have hvertL : HasDerivAt (fun z => inner ℝ (quarterTurn e) (G.arc.leftExtension z))
      (inner ℝ (quarterTurn e) (deriv G.arc.leftExtension t)) t := by
    simpa using (hasDerivAt_const t (quarterTurn e)).inner ℝ hL.hasDerivAt
  have hvertR : HasDerivAt (fun z => inner ℝ (quarterTurn e) (G.arc.rightExtension z))
      (inner ℝ (quarterTurn e) (deriv G.arc.rightExtension t)) t := by
    simpa using (hasDerivAt_const t (quarterTurn e)).inner ℝ hR.hasDerivAt
  have hnL : inner ℝ e (deriv G.arc.leftExtension t) ≠ 0 := by
    have hh := G.arc.left_positive t ⟨by linarith [G.arc.radius_pos], le_rfl⟩
    intro hz
    have hh' := hh
    change 0 < s i * inner ℝ e _ at hh'
    rw [hz, mul_zero] at hh'
    exact lt_irrefl _ hh'
  have hnR : inner ℝ e (deriv G.arc.rightExtension t) ≠ 0 := by
    have hh := G.arc.right_positive t ⟨le_rfl, by linarith [G.arc.radius_pos]⟩
    intro hz
    have hh' := hh
    change 0 < s i * inner ℝ e _ at hh'
    rw [hz, mul_zero] at hh'
    exact lt_irrefl _ hh'
  have hheight : ∀ z ∈ Icc (t - G.arc.radius) (t + G.arc.radius),
      G.height (u z) = inner ℝ (quarterTurn e) (realLift c.parametrization z) := by
    intro z hz
    have hh := congrArg (fun p => inner ℝ (quarterTurn e) p) (G.arc_identity z hz)
    simpa only [frame_vertical G.arc.unit_axis G.frame, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, c, u, e] using hh.symm
  constructor
  · apply graph_left_derivative_of_antitone_parametrization hut G.arc.radius_pos hm hprojR hnR hvertR
    · intro z hz
      simp only [u, arcProjection]
      rw [G.arc.right_eq hz]
    · intro z hz
      dsimp only
      rw [hheight z ⟨by linarith [hz.1, G.arc.radius_pos], hz.2⟩, G.arc.right_eq hz]
  · apply graph_right_derivative_of_antitone_parametrization hut G.arc.radius_pos hm hprojL hnL hvertL
    · intro z hz
      simp only [u, arcProjection]
      rw [G.arc.left_eq hz]
    · intro z hz
      dsimp only
      rw [hheight z ⟨hz.1, by linarith [hz.2, G.arc.radius_pos]⟩, G.arc.left_eq hz]

/-- Exact eventual membership of every transverse ray in the original domain,
from the two one-sided derivatives of its actual local boundary graph. -/
lemma ray_test_of_height_derivatives
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O)
    (hpO : realLift (R.curve i).parametrization t ∈ O)
    {mL mR : ℝ} {v : Plane}
    (hL : HasDerivWithinAt G.height mL
      (Iic (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t))
    (hR : HasDerivWithinAt G.height mR
      (Ici (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t))
    (htrans : inner ℝ (quarterTurn G.arc.axis) v -
      (if 0 < inner ℝ G.arc.axis v then mR else mL) * inner ℝ G.arc.axis v ≠ 0) :
    (∀ᶠ r : ℝ in 𝓝[>] 0,
      realLift (R.curve i).parametrization t + r • v ∈ R.domain) ↔
      0 < inner ℝ (quarterTurn G.arc.axis) v -
        (if 0 < inner ℝ G.arc.axis v then mR else mL) * inner ℝ G.arc.axis v := by
  let p := realLift (R.curve i).parametrization t
  let e := G.arc.axis
  let a := arcProjection (R.curve i) e t
  have hpa : inner ℝ e p = a := rfl
  have hpb : inner ℝ (quarterTurn e) p = G.height a := by
    have hh := congrArg (fun z => inner ℝ (quarterTurn e) z)
      (G.arc_identity t ⟨by linarith [G.arc.radius_pos], by linarith [G.arc.radius_pos]⟩)
    simpa only [p, e, a, frame_vertical G.arc.unit_axis G.frame,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using hh
  have hdom : ∀ x ∈ O, x ∈ R.domain ↔
      G.height (inner ℝ e x) < inner ℝ (quarterTurn e) x := by
    intro x hx
    have hh := congrArg (fun A : Set Plane => x ∈ A) G.domain_eq
    have hi : (x ∈ R.domain) ↔ x ∈ G.frame.map '' {z : Plane | G.height (z 0) < z 1} := by
      simpa only [mem_inter_iff, hx, and_true] using (Iff.of_eq hh)
    exact hi.trans (frame_epigraph_iff G.arc.unit_axis G.frame G.height x)
  have htend : Tendsto (fun r : ℝ => p + r • v) (𝓝[>] 0) (𝓝 p) := by
    have hc : ContinuousAt (fun r : ℝ => p + r • v) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsign := graph_ray_sign_at hL hR htrans
  have heq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (p + r • v ∈ R.domain ↔
        0 < inner ℝ (quarterTurn e) v -
          (if 0 < inner ℝ e v then mR else mL) * inner ℝ e v) := by
    filter_upwards [htend.eventually (hO.mem_nhds hpO), hsign] with r hr hs
    rw [hdom _ hr]
    simpa only [inner_add_right, inner_smul_right, hpa, hpb, a, e] using hs
  simpa only [eventually_const, p, e] using (eventually_congr heq)

lemma eq_smul_of_same_graph_slope {e u v : Plane} (he : ‖e‖ = 1)
    (hux : inner ℝ e u ≠ 0)
    (hs : inner ℝ (quarterTurn e) v =
      (inner ℝ (quarterTurn e) u / inner ℝ e u) * inner ℝ e v) :
    v = (inner ℝ e v / inner ℝ e u) • u := by
  calc
    v = inner ℝ e v • e + inner ℝ (quarterTurn e) v • quarterTurn e :=
      (frame_reconstruct he v).symm
    _ = (inner ℝ e v / inner ℝ e u) •
        (inner ℝ e u • e + inner ℝ (quarterTurn e) u • quarterTurn e) := by
      rw [smul_add, smul_smul, smul_smul]
      congr 1
      · field_simp
      · rw [hs]
        congr 1
        ring
    _ = (inner ℝ e v / inner ℝ e u) • u := by rw [frame_reconstruct he u]

/-- Excluding exactly the two outward boundary rays makes the graph ray test transverse.
The opposite rays along each tangent remain permitted. -/
lemma graph_ray_transverse {e U W v : Plane} (he : ‖e‖ = 1)
    (hU : 0 < inner ℝ e U) (hW : 0 < inner ℝ e W) (hv : v ≠ 0)
    (hvo : NormedSpace.normalize v ≠ NormedSpace.normalize W)
    (hvi : NormedSpace.normalize v ≠ NormedSpace.normalize (-U)) :
    inner ℝ (quarterTurn e) v -
      (if 0 < inner ℝ e v then
        inner ℝ (quarterTurn e) W / inner ℝ e W
       else inner ℝ (quarterTurn e) U / inner ℝ e U) * inner ℝ e v ≠ 0 := by
  intro hz
  by_cases hx : 0 < inner ℝ e v
  · have hs : inner ℝ (quarterTurn e) v =
        (inner ℝ (quarterTurn e) W / inner ℝ e W) * inner ℝ e v := by
      simpa only [hx, ↓reduceIte, sub_eq_zero] using hz
    have heq := eq_smul_of_same_graph_slope he hW.ne' hs
    apply hvo
    rw [heq, NormedSpace.normalize_smul_of_pos (div_pos hx hW)]
  · have hs : inner ℝ (quarterTurn e) v =
        (inner ℝ (quarterTurn e) U / inner ℝ e U) * inner ℝ e v := by
      simpa only [hx, ↓reduceIte, sub_eq_zero] using hz
    have heq := eq_smul_of_same_graph_slope he hU.ne' hs
    have hxn : inner ℝ e v < 0 := by
      refine lt_of_le_of_ne (le_of_not_gt hx) ?_
      intro hzero
      exact hv (by simpa [hzero] using heq)
    apply hvi
    rw [heq, NormedSpace.normalize_smul_of_neg (div_neg_of_neg_of_pos hxn hU), NormedSpace.normalize_neg]

lemma projection_slope_smul {e v : Plane} {k : ℝ} (hk : k ≠ 0) :
    inner ℝ (quarterTurn e) (k • v) / inner ℝ e (k • v) =
      inner ℝ (quarterTurn e) v / inner ℝ e v := by
  simp only [inner_smul_right]
  exact mul_div_mul_left _ _ hk

lemma ray_test_with_forward_tangents
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O)
    (hpO : realLift (R.curve i).parametrization t ∈ O) (hσ : s i = 1)
    {u w : Plane} {kL kR : ℝ} (hkL : 0 < kL) (hkR : 0 < kR)
    (hleft : deriv G.arc.leftExtension t = kL • u)
    (hright : deriv G.arc.rightExtension t = kR • w) :
    0 < inner ℝ G.arc.axis u ∧ 0 < inner ℝ G.arc.axis w ∧
    ∀ v : Plane, v ≠ 0 →
      NormedSpace.normalize v ≠ NormedSpace.normalize w →
      NormedSpace.normalize v ≠ NormedSpace.normalize (-u) →
      ((∀ᶠ r : ℝ in 𝓝[>] 0,
          realLift (R.curve i).parametrization t + r • v ∈ R.domain) ↔
        0 < inner ℝ (quarterTurn G.arc.axis) v -
          (if 0 < inner ℝ G.arc.axis v then
            inner ℝ (quarterTurn G.arc.axis) w / inner ℝ G.arc.axis w
           else inner ℝ (quarterTurn G.arc.axis) u / inner ℝ G.arc.axis u) * inner ℝ G.arc.axis v) := by
  have hU : 0 < inner ℝ G.arc.axis u := by
    have hh := G.arc.left_positive t ⟨by linarith [G.arc.radius_pos], le_rfl⟩
    have hp : 0 < kL * inner ℝ G.arc.axis u := by
      simpa only [hσ, one_mul, hleft, inner_smul_right] using hh
    exact (mul_pos_iff_of_pos_left hkL).mp hp
  have hW : 0 < inner ℝ G.arc.axis w := by
    have hh := G.arc.right_positive t ⟨le_rfl, by linarith [G.arc.radius_pos]⟩
    have hp : 0 < kR * inner ℝ G.arc.axis w := by
      simpa only [hσ, one_mul, hright, inner_smul_right] using hh
    exact (mul_pos_iff_of_pos_left hkR).mp hp
  obtain ⟨hL, hR⟩ := height_one_sided_derivatives G hσ
  rw [hleft, projection_slope_smul hkL.ne'] at hL
  rw [hright, projection_slope_smul hkR.ne'] at hR
  refine ⟨hU, hW, ?_⟩
  intro v hv hvo hvi
  exact ray_test_of_height_derivatives G hO hpO hL hR
    (graph_ray_transverse G.arc.unit_axis hU hW hv hvo hvi)

lemma ray_test_with_reverse_tangents
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O)
    (hpO : realLift (R.curve i).parametrization t ∈ O) (hσ : s i = -1)
    {u w : Plane} {kL kR : ℝ} (hkL : 0 < kL) (hkR : 0 < kR)
    (hleft : deriv G.arc.leftExtension t = kL • u)
    (hright : deriv G.arc.rightExtension t = kR • w) :
    0 < inner ℝ G.arc.axis (-w) ∧ 0 < inner ℝ G.arc.axis (-u) ∧
    ∀ v : Plane, v ≠ 0 →
      NormedSpace.normalize v ≠ NormedSpace.normalize (-u) →
      NormedSpace.normalize v ≠ NormedSpace.normalize w →
      ((∀ᶠ r : ℝ in 𝓝[>] 0,
          realLift (R.curve i).parametrization t + r • v ∈ R.domain) ↔
        0 < inner ℝ (quarterTurn G.arc.axis) v -
          (if 0 < inner ℝ G.arc.axis v then
            inner ℝ (quarterTurn G.arc.axis) (-u) / inner ℝ G.arc.axis (-u)
           else inner ℝ (quarterTurn G.arc.axis) (-w) / inner ℝ G.arc.axis (-w)) * inner ℝ G.arc.axis v) := by
  have hU : 0 < inner ℝ G.arc.axis (-w) := by
    have hh := G.arc.right_positive t ⟨le_rfl, by linarith [G.arc.radius_pos]⟩
    have hp : 0 < kR * inner ℝ G.arc.axis (-w) := by
      simpa only [hσ, neg_one_mul, hright, inner_smul_right, inner_neg_right, mul_neg, neg_mul, one_mul] using hh
    exact (mul_pos_iff_of_pos_left hkR).mp hp
  have hW : 0 < inner ℝ G.arc.axis (-u) := by
    have hh := G.arc.left_positive t ⟨by linarith [G.arc.radius_pos], le_rfl⟩
    have hp : 0 < kL * inner ℝ G.arc.axis (-u) := by
      simpa only [hσ, neg_one_mul, hleft, inner_smul_right, inner_neg_right, mul_neg, neg_mul, one_mul] using hh
    exact (mul_pos_iff_of_pos_left hkL).mp hp
  obtain ⟨hL, hR⟩ := height_one_sided_derivatives_reverse G hσ
  rw [hright, projection_slope_smul hkR.ne'] at hL
  rw [hleft, projection_slope_smul hkL.ne'] at hR
  have hL' : HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (-w) / inner ℝ G.arc.axis (-w))
      (Iic (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t) := by simpa only [inner_neg_right, neg_div_neg_eq] using hL
  have hR' : HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (-u) / inner ℝ G.arc.axis (-u))
      (Ici (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t) := by simpa only [inner_neg_right, neg_div_neg_eq] using hR
  refine ⟨hU, hW, ?_⟩
  intro v hv hvo hvi
  simpa only [neg_neg] using ray_test_of_height_derivatives G hO hpO hL' hR'
    (graph_ray_transverse G.arc.unit_axis hU hW hv hvo (by simpa only [neg_neg] using hvi))

lemma exists_directed_boundary_graph (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (t : ℝ) :
    ∃ (O : Set Plane) (G : LocalDirectedBoundaryGraph R s i t O),
      IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O := by
  obtain ⟨arcs, _⟩ := twoDirectedProjectionArcs (R.curve i) (s i) t (hs i).1
  have hσ : s i ≠ 0 := by rcases (hs i).1 with h | h <;> simp only [h, ne_eq, one_ne_zero, neg_eq_zero, not_false_eq_true]
  obtain ⟨O, G, hO, hpO, _⟩ := localDirectedBoundaryGraph_of_arc R s i t hσ (hs i).2 (arcs 0)
  exact ⟨O, G, hO, hpO⟩


end BoundarySectorGraph

section OccupiedSectorAssembly
open P202Specs.BoundaryGraphDirections BoundarySectorGraph
set_option maxHeartbeats 1200000

lemma occupiedSectorAngle_of_tangent_matches
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count)
    (t : ℝ) (O : Set Plane) (G : LocalDirectedBoundaryGraph R s i t O)
    (hO : IsOpen O) (hpO : realLift (R.curve i).parametrization t ∈ O)
    (hp : realLift (R.curve i).parametrization t = A.arc j 1)
    {kL kR : ℝ} (hkL : 0 < kL) (hkR : 0 < kR)
    (hleft : deriv G.arc.leftExtension t = kL • velocity A j 1)
    (hright : deriv G.arc.rightExtension t = kR • velocity A (finRotate A.count j) 0) :
    IsOccupiedSectorAngle g o c hc R i A (s i) j (interiorAngle g o c hc A (s i) j) := by
  have hx : A.arc j 1 ∈ P202Specs.ChartRegionStokes.chartTarget c := by
    apply hR
    apply frontier_subset_closure
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, arc_mem_trace A j (by simp)⟩
  have hbounds := interiorAngle_bounds g o c hc A j (s i) (hs i).1 hx
  have hwidth := metric_width g o c hc A j (s i) (hs i).1 hx
  have hu : velocity A j 1 ≠ 0 := A.regular j 1 (by simp)
  have hw : velocity A (finRotate A.count j) 0 ≠ 0 := A.regular _ 0 (by simp)
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  intro v hv hvo hvi
  rcases (hs i).1 with hσ | hσ
  · obtain ⟨hUX, hWX, hgeom⟩ := ray_test_with_forward_tangents G hO hpO hσ hkL hkR hleft hright
    have hvo' : NormedSpace.normalize v ≠ NormedSpace.normalize (velocity A (finRotate A.count j) 0) := by
      simpa only [outgoingRay, hσ, ↓reduceIte] using hvo
    have hvi' : NormedSpace.normalize v ≠ NormedSpace.normalize (-velocity A j 1) := by
      simpa only [incomingRay, hσ, ↓reduceIte] using hvi
    have hm := metric_sector_graph_criterion g o c hc b H
      (A.arc j 1) (velocity A j 1) (velocity A (finRotate A.count j) 0) v G.arc.axis
      hx hu hw hv (A.noncuspidal j) G.arc.unit_axis hUX hWX
    have hg := hgeom v hv hvo' hvi'
    rw [hp] at hg
    have hw' : positiveMetricAngle g o c hc (A.arc j 1)
        (velocity A (finRotate A.count j) 0) (-velocity A j 1) =
        interiorAngle g o c hc A (s i) j := by
      simpa only [outgoingRay, incomingRay, hσ, ↓reduceIte] using hwidth
    exact hg.trans (by simpa only [outgoingRay, hσ, ↓reduceIte, hw'] using hm.symm)
  · obtain ⟨hUX, hWX, hgeom⟩ := ray_test_with_reverse_tangents G hO hpO hσ hkL hkR hleft hright
    have hsone : s i ≠ 1 := by rw [hσ]; norm_num
    have hvo' : NormedSpace.normalize v ≠ NormedSpace.normalize (-velocity A j 1) := by
      simpa only [outgoingRay, hsone, ↓reduceIte] using hvo
    have hvi' : NormedSpace.normalize v ≠ NormedSpace.normalize (velocity A (finRotate A.count j) 0) := by
      simpa only [incomingRay, hsone, ↓reduceIte] using hvi
    have hn : NormedSpace.normalize (-velocity A (finRotate A.count j) 0) ≠
        -NormedSpace.normalize (-velocity A j 1) := by
      intro hh
      apply A.noncuspidal j
      simpa only [NormedSpace.normalize_neg, neg_neg, velocity] using hh.symm
    have hm := metric_sector_graph_criterion g o c hc b H
      (A.arc j 1) (-velocity A (finRotate A.count j) 0) (-velocity A j 1) v G.arc.axis
      hx (neg_ne_zero.mpr hw) (neg_ne_zero.mpr hu) hv hn G.arc.unit_axis hUX hWX
    have hg := hgeom v hv hvo' hvi'
    rw [hp] at hg
    have hw' : positiveMetricAngle g o c hc (A.arc j 1)
        (-velocity A j 1) (velocity A (finRotate A.count j) 0) =
        interiorAngle g o c hc A (s i) j := by
      simpa only [outgoingRay, incomingRay, hsone, ↓reduceIte] using hwidth
    exact hg.trans (by simpa only [outgoingRay, hsone, ↓reduceIte, neg_neg, hw'] using hm.symm)


end OccupiedSectorAssembly


namespace PeriodicEndpoint
set_option maxHeartbeats 800000

lemma right_derivative_at_seam {q : RegularJordanCurve}
    (A : ArcPresentation q) (f : ℝ → Plane) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableAt ℝ f 1)
    (heq : EqOn f (realLift q.parametrization) (Icc 1 (1 + r))) :
    let j : Fin A.count := ⟨0, A.positive⟩
    deriv f 1 = (A.time j.succ - A.time j.castSucc)⁻¹ • velocity A j 0 := by
  let j : Fin A.count := ⟨0, A.positive⟩
  let d := A.time j.succ - A.time j.castSucc
  have hd : 0 < d := sub_pos.mpr (A.strictMono j.castSucc_lt_succ)
  have hj : j.castSucc = 0 := Fin.ext rfl
  have hfirst : A.time j.castSucc = 0 := hj ▸ A.first
  let B : ℝ → Plane := fun s => A.arc j ((s - 1) / d)
  have hAffine : HasDerivAt (fun s : ℝ => (s - 1) / d) d⁻¹ 1 := by
    convert! ((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const d using 1 <;> simp [one_div]
  have hArc : HasDerivAt (A.arc j) (velocity A j 0) (((1 : ℝ) - 1) / d) := by
    convert! (arc_contDiffAt A j (by simp : (0 : ℝ) ∈ Icc 0 1)).differentiableAt (by simp) |>.hasDerivAt using 1 <;> simp [velocity]
  have hB : HasDerivAt B (d⁻¹ • velocity A j 0) 1 := hArc.scomp 1 hAffine
  have hsmall : ∀ᶠ s : ℝ in 𝓝[≥] (1 : ℝ), s < 1 + r ∧ s < 1 + d :=
    ((eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + r)).and
      (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + d))).filter_mono nhdsWithin_le_nhds
  have hEq : f =ᶠ[𝓝[≥] (1 : ℝ)] B := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hge
    have ht : (s - 1) / d ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hge) hd.le
      · exact (div_le_one hd).mpr (by linarith [hs.2])
    rw [heq ⟨hge, hs.1.le⟩]
    dsimp [B]
    rw [A.agrees j _ ht]
    have hparam : A.time j.castSucc +
        (A.time j.succ - A.time j.castSucc) * ((s - 1) / d) = s - 1 := by
      change A.time j.castSucc + d * ((s - 1) / d) = s - 1
      rw [hfirst, mul_div_cancel₀ _ hd.ne', zero_add]
    rw [hparam]
    simp only [realLift, AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  have hf' : HasDerivWithinAt f (d⁻¹ • velocity A j 0) (Ici 1) 1 :=
    hB.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hEq (by simp)
  exact (uniqueDiffWithinAt_Ici 1).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt hf'



end PeriodicEndpoint

namespace PresentationTangents
open P202Specs.BoundaryGraphDirections
set_option maxHeartbeats 1000000

def parameterArc {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count) : ℝ → Plane :=
  fun y => A.arc j ((y - A.time j.castSucc) / (A.time j.succ - A.time j.castSucc))

lemma parameterArc_agrees {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count) :
    EqOn (parameterArc A j) (realLift q.parametrization) (Icc (A.time j.castSucc) (A.time j.succ)) := by
  let a := A.time j.castSucc
  let b := A.time j.succ
  have hd : 0 < b-a := sub_pos.mpr (A.strictMono j.castSucc_lt_succ)
  intro y hy
  have ht : (y-a)/(b-a) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy.1) hd.le
    · exact (div_le_one hd).mpr (by linarith [hy.2])
  change A.arc j ((y-a)/(b-a)) = _
  rw [A.agrees j _ ht]
  congr 1
  change a+(b-a)*((y-a)/(b-a))=y
  field_simp
  ring

lemma parameterArc_hasDerivAt {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count)
    (y : ℝ) (hy : (y-A.time j.castSucc)/(A.time j.succ-A.time j.castSucc) ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (parameterArc A j)
      ((A.time j.succ-A.time j.castSucc)⁻¹ •
        velocity A j ((y-A.time j.castSucc)/(A.time j.succ-A.time j.castSucc))) y := by
  have hA := ((arc_contDiffAt A j hy).differentiableAt (by simp)).hasDerivAt
  convert! hA.scomp y
    (((hasDerivAt_id y).sub_const (A.time j.castSucc)).mul_const
      (A.time j.succ-A.time j.castSucc)⁻¹) using 1
  simp [parameterArc, velocity, div_eq_mul_inv]

lemma parameterArc_hasDerivAt_finish {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count) :
    HasDerivAt (parameterArc A j)
      ((A.time j.succ-A.time j.castSucc)⁻¹ • velocity A j 1) (A.time j.succ) := by
  have hd : A.time j.succ-A.time j.castSucc ≠ 0 :=
    (sub_pos.mpr (A.strictMono j.castSucc_lt_succ)).ne'
  simpa only [div_self hd] using parameterArc_hasDerivAt A j (A.time j.succ) (by simp [hd])

lemma parameterArc_hasDerivAt_start {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count) :
    HasDerivAt (parameterArc A j)
      ((A.time j.succ-A.time j.castSucc)⁻¹ • velocity A j 0) (A.time j.castSucc) := by
  simpa only [sub_self, zero_div] using
    parameterArc_hasDerivAt A j (A.time j.castSucc) (by simp)

lemma directedProjectionArc_left_deriv {q : RegularJordanCurve} (A : ArcPresentation q)
    (j : Fin A.count) (sigma : ℝ) (D : DirectedProjectionArc q sigma (A.time j.succ)) :
    deriv D.leftExtension (A.time j.succ) =
      (A.time j.succ-A.time j.castSucc)⁻¹ • velocity A j 1 := by
  have hD : DifferentiableAt ℝ D.leftExtension (A.time j.succ) :=
    (D.left_smooth.contDiffAt (isOpen_Ioo.mem_nhds (by
      have := D.radius_pos; have := D.radius_lt
      constructor <;> linarith))).differentiableAt (by simp)
  have hP := parameterArc_hasDerivAt_finish A j
  have hDE := D.left_eq.eventuallyEq_of_mem
    (Icc_mem_nhdsLE (by linarith [D.radius_pos] : A.time j.succ-D.radius < A.time j.succ))
  have hPE := (parameterArc_agrees A j).eventuallyEq_of_mem
    (Icc_mem_nhdsLE (A.strictMono j.castSucc_lt_succ))
  exact (P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_le hD hP.differentiableAt
    (hDE.trans hPE.symm)).trans hP.deriv

lemma directedProjectionArc_right_deriv_of_join {q : RegularJordanCurve} (A : ArcPresentation q)
    (j k : Fin A.count) (sigma : ℝ) (D : DirectedProjectionArc q sigma (A.time j.succ))
    (hjoin : A.time k.castSucc = A.time j.succ) :
    deriv D.rightExtension (A.time j.succ) =
      (A.time k.succ-A.time k.castSucc)⁻¹ • velocity A k 0 := by
  have hD : DifferentiableAt ℝ D.rightExtension (A.time j.succ) :=
    (D.right_smooth.contDiffAt (isOpen_Ioo.mem_nhds (by
      have := D.radius_pos; have := D.radius_lt
      constructor <;> linarith))).differentiableAt (by simp)
  have hP := parameterArc_hasDerivAt_start A k
  have hDE := D.right_eq.eventuallyEq_of_mem
    (Icc_mem_nhdsGE (by linarith [D.radius_pos] : A.time j.succ < A.time j.succ+D.radius))
  have hPE := (parameterArc_agrees A k).eventuallyEq_of_mem
    (Icc_mem_nhdsGE (A.strictMono k.castSucc_lt_succ))
  rw [hjoin] at hP hPE
  rw [hjoin]
  exact (P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_ge hD hP.differentiableAt
    (hDE.trans hPE.symm)).trans hP.deriv

lemma time_rotated_start_of_not_last {q : RegularJordanCurve} (A : ArcPresentation q)
    (j : Fin A.count) (hj : j.val+1 < A.count) :
    A.time (finRotate A.count j).castSucc = A.time j.succ := by
  letI : NeZero A.count := ⟨A.positive.ne'⟩
  let k : Fin A.count := ⟨j.val+1,hj⟩
  have hrot : finRotate A.count j = k := by
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    exact Nat.mod_eq_of_lt hj
  rw [hrot]
  congr 1

lemma directedProjectionArc_right_deriv_of_not_last {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) (sigma : ℝ)
    (D : DirectedProjectionArc q sigma (A.time j.succ)) (hj : j.val+1 < A.count) :
    deriv D.rightExtension (A.time j.succ) =
      (A.time (finRotate A.count j).succ-A.time (finRotate A.count j).castSucc)⁻¹ •
        velocity A (finRotate A.count j) 0 :=
  directedProjectionArc_right_deriv_of_join A j _ sigma D (time_rotated_start_of_not_last A j hj)

lemma arc_finish_eq_original {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count) :
    A.arc j 1 = realLift q.parametrization (A.time j.succ) := by
  simpa only [mul_one, add_sub_cancel] using A.agrees j 1 (by simp)

lemma directedProjectionArc_right_deriv {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) (sigma : ℝ)
    (D : DirectedProjectionArc q sigma (A.time j.succ)) :
    deriv D.rightExtension (A.time j.succ) =
      (A.time (finRotate A.count j).succ-A.time (finRotate A.count j).castSucc)⁻¹ •
        velocity A (finRotate A.count j) 0 := by
  by_cases hj : j.val+1 < A.count
  · exact directedProjectionArc_right_deriv_of_not_last A j sigma D hj
  have hlast : j.val+1 = A.count := by omega
  have ht : A.time j.succ = 1 :=
    (congrArg A.time (Fin.ext hlast : j.succ = Fin.last A.count)).trans A.last
  let k : Fin A.count := ⟨0,A.positive⟩
  letI : NeZero A.count := ⟨A.positive.ne'⟩
  have hrot : finRotate A.count j = k := by
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    change (j.val+1) % A.count = 0
    rw [hlast,Nat.mod_self]
  have hD : DifferentiableAt ℝ D.rightExtension 1 := by
    have hd : DifferentiableAt ℝ D.rightExtension (A.time j.succ) :=
      (D.right_smooth.contDiffAt (isOpen_Ioo.mem_nhds (by
        have := D.radius_pos; have := D.radius_lt
        constructor <;> linarith))).differentiableAt (by simp)
    simpa only [ht] using hd
  have heq : EqOn D.rightExtension (realLift q.parametrization) (Icc 1 (1+D.radius)) := by
    simpa only [ht] using D.right_eq
  have hseam := PeriodicEndpoint.right_derivative_at_seam A D.rightExtension D.radius D.radius_pos hD heq
  simpa only [ht,hrot] using hseam

end PresentationTangents


section FullOccupiedSector
open BoundarySectorGraph

/-- The actual locally occupied metric sector, with the original induced
boundary sign and every original arc presentation, including reflex corners. -/
theorem occupiedSectorAngle
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    {a beta d : Plane → ℝ} (H : FrameCoefficients g o c hc b a beta d)
    (R : PlanarRegion) (hR : R.carrier ⊆ P202Specs.ChartRegionStokes.chartTarget c)
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count) :
    IsOccupiedSectorAngle g o c hc R i A (s i) j (interiorAngle g o c hc A (s i) j) := by
  obtain ⟨O, G, hO, hpO⟩ := exists_directed_boundary_graph R s hs i (A.time j.succ)
  have hkL : 0 < (A.time j.succ - A.time j.castSucc)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (A.strictMono j.castSucc_lt_succ))
  have hkR : 0 < (A.time (finRotate A.count j).succ -
      A.time (finRotate A.count j).castSucc)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (A.strictMono (finRotate A.count j).castSucc_lt_succ))
  exact occupiedSectorAngle_of_tangent_matches g o c hc b H R hR s hs i A j
    (A.time j.succ) O G hO hpO (PresentationTangents.arc_finish_eq_original A j).symm hkL hkR
    (PresentationTangents.directedProjectionArc_left_deriv A j (s i) G.arc)
    (PresentationTangents.directedProjectionArc_right_deriv A j (s i) G.arc)


end FullOccupiedSector

/-- The complete original intrinsic boundary obligation: literal smooth
connection form, all arc and integral clauses, and actual occupied sectors. -/
theorem boundaryCalculus : P202Specs.MetricBoundaryTurning.Expected.boundaryCalculus.{u} := by
  intro M inst S g C hC o c hc hpositive b a beta d H
  obtain ⟨hform, hcomponents⟩ :=
    componentCalculus S g C hC o c hc hpositive b a beta d H
  refine ⟨hform, hcomponents, ?_⟩
  intro R hR s hs i A j
  exact occupiedSectorAngle g o c hc b H R hR s hs i A j

end P202.MetricBoundaryTurning
