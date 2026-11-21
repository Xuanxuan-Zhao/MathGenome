import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SecondBianchi
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings
import Mathlib.LinearAlgebra.Trace

/-! Contractions in Theorem `thm:p202-sectional-recovery`, paper.tex
3616–3622 and 3640–3652. Trace is taken on the actual tangent fibers.
The derivative below contracts the established induced tensor derivative;
its evaluation rule is a separate obligation, not an assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace P202.RicciData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurvatureData P202.SecondBianchiData
universe u v

/-- Trace the first input against the vector output. -/
noncomputable def curvatureContraction {V : Type v} [AddCommMonoid V] [Module ℝ V]
    (A : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun y z => LinearMap.trace ℝ V
    { toFun := fun x => A x y z
      map_add' := by intros; simp only [map_add, LinearMap.add_apply]
      map_smul' := by intros; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] })
    (by
      intro y y' z
      rw [← map_add]
      congr 1
      ext x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply])
    (by
      intro c y z
      rw [← map_smul]
      congr 1
      ext x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply, RingHom.id_apply])
    (by
      intro y z z'
      rw [← map_add]
      congr 1
      ext x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply])
    (by
      intro c y z
      rw [← map_smul]
      congr 1
      ext x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply, RingHom.id_apply])

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Ricci, canonically defined before any basis is chosen. -/
noncomputable def ricci (T : CurvatureTensor S) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace S p) := curvatureContraction (T.val p)

/-- Metric trace; the inverse metric is the inverse of the metric-to-dual map. -/
noncomputable def metricTrace (g : RiemannianMetric S) (p : M)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p)) : ℝ :=
  LinearMap.trace ℝ (TangentSpace S p)
    (((SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm.toLinearMap).comp B)

noncomputable def scalarCurvature (g : RiemannianMetric S) (T : CurvatureTensor S)
    (p : M) : ℝ := metricTrace g p (ricci T p)

/-- A basis orthonormal for the given intrinsic tangent metric. -/
def IsOrthonormalBasis (g : RiemannianMetric S) (p : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace S p)) : Prop :=
  ∀ i j, pairing g p (b i) (b j) = if i = j then 1 else 0

/-- Contraction of the actual induced derivative, with the derivative slot
retained. The evaluation rule in the Specs identifies it with ∇Ric. -/
noncomputable def ricciDerivative (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (p : M) (X : TangentSpace S p) :
    LinearMap.BilinForm ℝ (TangentSpace S p) :=
  curvatureContraction (covariantDerivative C T p X)

/-- The metric contraction in the derivative and first Ricci slots. -/
noncomputable def divergenceRicci (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (T : CurvatureTensor S) (p : M)
    (Z : TangentSpace S p) : ℝ :=
  metricTrace g p (LinearMap.mk₂ ℝ
    (fun X Y => ricciDerivative C T p X Y Z)
    (by
      intros
      simp only [ricciDerivative, curvatureContraction, LinearMap.mk₂_apply,
        map_add, LinearMap.add_apply]
      rw [← (LinearMap.trace ℝ (TangentSpace S p)).map_add]; congr 1)
    (by
      intros
      simp only [ricciDerivative, curvatureContraction, LinearMap.mk₂_apply,
        map_smul, LinearMap.smul_apply]
      rw [← (LinearMap.trace ℝ (TangentSpace S p)).map_smul]; congr 1)
    (by intros; simp only [map_add, LinearMap.add_apply])
    (by intros; simp only [map_smul, LinearMap.smul_apply]))

end P202.RicciData

namespace P202Specs.Geometry.RicciScalarBianchi
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.CurvatureData P202.SecondBianchiData P202.RicciData
universe u

def ricciType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → CurvatureTensor S → (p : M) →
    LinearMap.BilinForm ℝ (TangentSpace S p)
noncomputable def ricciValue : ricciType := @ricci

def scalarCurvatureType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
    RiemannianMetric S → CurvatureTensor S → M → ℝ
noncomputable def scalarCurvatureValue : scalarCurvatureType := @scalarCurvature

def ricciDerivativeType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
    Connection (tangentBundle S) → CurvatureTensor S → (p : M) →
      TangentSpace S p → LinearMap.BilinForm ℝ (TangentSpace S p)
noncomputable def ricciDerivativeValue : ricciDerivativeType := @ricciDerivative

def divergenceRicciType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
    RiemannianMetric S → Connection (tangentBundle S) → CurvatureTensor S →
      (p : M) → TangentSpace S p → ℝ
noncomputable def divergenceRicciValue : divergenceRicciType := @divergenceRicci

def orthonormal_contractionsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (T : CurvatureTensor S)
    (p : M) (b : Module.Basis (Fin n) ℝ (TangentSpace S p)),
    IsOrthonormalBasis g p b →
    (∀ Y Z, ricci T p Y Z = ∑ i, curvatureForm g T p (b i) Y Z (b i)) ∧
    scalarCurvature g T p = ∑ i, ricci T p (b i) (b i)

def frame_independenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (T : CurvatureTensor S)
    (p : M) (b c : Module.Basis (Fin n) ℝ (TangentSpace S p)),
    IsOrthonormalBasis g p b → IsOrthonormalBasis g p c →
    (∀ Y Z, (∑ i, curvatureForm g T p (b i) Y Z (b i)) =
      ∑ i, curvatureForm g T p (c i) Y Z (c i)) ∧
    (∑ i, ricci T p (b i) (b i)) = ∑ i, ricci T p (c i) (c i)

def ricci_symmetricType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (Y Z : TangentSpace S p), ricci T p Y Z = ricci T p Z Y

def ricci_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (T : CurvatureTensor S) (Y Z : Field S),
    (fun p => ricci T p (Y.val p) (Z.val p)) ∈ SmoothManifolds.globalSmoothAlgebra S

def scalar_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (T : CurvatureTensor S),
    scalarCurvature g T ∈ SmoothManifolds.globalSmoothAlgebra S

/-- This is the tensor covariant derivative rule, with the original scalar
differential and connection, rather than a formal component derivative. -/
def ricci_derivative_ruleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z : Field S) (p : M),
    ricciDerivative C T p (X.val p) (Y.val p) (Z.val p) =
      scalarDerivative S (fun q => ricci T q (Y.val q) (Z.val q)) p (X.val p) -
        ricci T p ((C.cov X Y).val p) (Z.val p) -
        ricci T p (Y.val p) ((C.cov X Z).val p)

def scalar_derivative_ruleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S) (p : M) (X : TangentSpace S p),
    scalarDerivative S (scalarCurvature g T) p X =
      metricTrace g p (ricciDerivative C T p X)

/-- The intrinsic contracted second Bianchi identity, including n=0 and n=1. -/
def contracted_bianchiType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (Z : TangentSpace S p),
      divergenceRicci g C T p Z =
        (1 / 2 : ℝ) * scalarDerivative S (scalarCurvature g T) p Z

/-- Explicit inverse-metric contraction in every canonical tangent chart. -/
def coordinate_contractionsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (T : CurvatureTensor S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M),
    p ∈ (tangentBundle S).baseSet c →
    (scalarCurvature g T p = ∑ i, ∑ j, (metricMatrix g c p)⁻¹ i j *
      ricci T p (coordinateVector c i p) (coordinateVector c j p)) ∧
    (∀ Z, divergenceRicci g C T p Z =
      ∑ i, ∑ j, (metricMatrix g c p)⁻¹ i j *
        ricciDerivative C T p (coordinateVector c i p) (coordinateVector c j p) Z)

def contracted_bianchi_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M),
    p ∈ (tangentBundle S).baseSet c → ∀ k : Fin n,
      (∑ i, ∑ j, (metricMatrix g c p)⁻¹ i j *
        ricciDerivative C T p (coordinateVector c i p) (coordinateVector c j p)
          (coordinateVector c k p)) =
      (1 / 2 : ℝ) * scalarDerivative S (scalarCurvature g T) p (coordinateVector c k p)

end P202Specs.Geometry.RicciScalarBianchi
