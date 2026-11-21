import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SectionalRecovery
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RicciScalarBianchi

/-! Theorem 7.2, paper.tex:3613–3666. No regularity of the supplied
pointwise sectional value is assumed. All contractions and differentials
are the canonical upstream objects. -/
set_option autoImplicit false
namespace P202.SchurData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurvatureData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

def PointwiseSectional (g : RiemannianMetric S) (T : CurvatureTensor S)
    (κ : M → ℝ) : Prop :=
  ∀ (p : M) (x y : TangentSpace S p) (h : LinearIndependent ℝ ![x, y]),
    sectionalCurvature g T p x y h = κ p
end P202.SchurData

namespace P202Specs.Geometry.Schur
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.CurvatureData P202.RicciData P202.SchurData
universe u

def pointwise_formulasType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (κ : M → ℝ), PointwiseSectional g T κ →
    ∀ p : M,
      (∀ x y z w, curvatureForm g T p x y z w =
        κ p * (pairing g p y z * pairing g p x w - pairing g p x z * pairing g p y w)) ∧
      (∀ y z, ricci T p y z = ((n : ℝ) - 1) * κ p * pairing g p y z) ∧
      scalarCurvature g T p = (n : ℝ) * ((n : ℝ) - 1) * κ p

def common_value_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    3 ≤ n → ∀ (κ : M → ℝ), PointwiseSectional g T κ →
    κ ∈ SmoothManifolds.globalSmoothAlgebra S

def common_value_differentialType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    3 ≤ n → ∀ (κ : M → ℝ), PointwiseSectional g T κ →
    ∀ (p : M) (X : TangentSpace S p), scalarDerivative S κ p X = 0

/-- Connectedness is used only after deriving smoothness and zero differential.
The hypothesis allows the common value to be chosen separately at each point.
Preconnectedness also permits the empty manifold, where the conclusion is vacuous. -/
def schurType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [PreconnectedSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T → 3 ≤ n →
    (∀ p : M, ∃ k : ℝ, ∀ (x y : TangentSpace S p)
      (h : LinearIndependent ℝ ![x, y]), sectionalCurvature g T p x y h = k) →
    ∃ k₀ : ℝ, ∀ (p : M) (x y : TangentSpace S p)
      (h : LinearIndependent ℝ ![x, y]), sectionalCurvature g T p x y h = k₀

/-- The complete recovery/contraction theorem retains the prerequisite
pointwise recovery, Ricci symmetry, and intrinsic and coordinate Bianchi laws. -/
def complete_theoremType : Prop :=
  P202Specs.Geometry.SectionalRecovery.recoveryType.{u} ∧
  P202Specs.Geometry.RicciScalarBianchi.ricci_symmetricType.{u} ∧
  P202Specs.Geometry.RicciScalarBianchi.contracted_bianchiType.{u} ∧
  P202Specs.Geometry.RicciScalarBianchi.contracted_bianchi_coordinatesType.{u} ∧
  pointwise_formulasType.{u} ∧ common_value_smoothType.{u} ∧
  common_value_differentialType.{u} ∧ schurType.{u}
end P202Specs.Geometry.Schur
