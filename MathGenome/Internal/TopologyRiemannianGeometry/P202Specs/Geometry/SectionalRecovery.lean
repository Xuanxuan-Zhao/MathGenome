import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! Pointwise part of `thm:p202-sectional-recovery`, paper.tex:3611–3638.
The curried linear maps are arbitrary real multilinear four-tensors on the
original tangent fiber. No positive dimension or existence of a plane is assumed. -/
set_option autoImplicit false
namespace P202.SectionalData
universe u
abbrev FourTensor (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ

/-- The two skew symmetries, pair interchange, and first Bianchi identity. -/
def CurvatureSymmetries {V : Type u} (r : V → V → V → V → ℝ) : Prop :=
  (∀ x y z w, r x y z w = -r y x z w) ∧
  (∀ x y z w, r x y z w = -r x y w z) ∧
  (∀ x y z w, r x y z w = r z w x y) ∧
  (∀ x y z w, r x y z w + r y z x w + r z x y w = 0)
end P202.SectionalData

namespace P202Specs.Geometry.SectionalRecovery
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurvatureData P202.SectionalData
universe u

def recoveryType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)
    (r s : FourTensor (TangentSpace S p)),
    CurvatureSymmetries (fun x y z w => r x y z w) →
    CurvatureSymmetries (fun x y z w => s x y z w) →
    (∀ (x y : TangentSpace S p), LinearIndependent ℝ ![x, y] →
      r x y y x / (pairing g p x x * pairing g p y y - pairing g p x y ^ 2) =
      s x y y x / (pairing g p x x * pairing g p y y - pairing g p x y ^ 2)) → r = s

def constant_sectionalType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)
    (r : FourTensor (TangentSpace S p)) (κ : ℝ),
    CurvatureSymmetries (fun x y z w => r x y z w) →
    (∀ (x y : TangentSpace S p), LinearIndependent ℝ ![x, y] →
      r x y y x / (pairing g p x x * pairing g p y y - pairing g p x y ^ 2) = κ) →
    ∀ x y z w, r x y z w =
      κ * (pairing g p y z * pairing g p x w - pairing g p x z * pairing g p y w)

/-- In particular a fiber with no independent pair has zero curvature tensor.
This includes the zero- and one-dimensional fibers. -/
def no_planesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (p : M)
    (r : FourTensor (TangentSpace S p)),
    CurvatureSymmetries (fun x y z w => r x y z w) →
    (∀ x y : TangentSpace S p, ¬LinearIndependent ℝ ![x, y]) → r = 0

/-- Both dimension zero and dimension one have forced zero curvature. -/
def low_dimensionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (p : M)
    (r : FourTensor (TangentSpace S p)),
    CurvatureSymmetries (fun x y z w => r x y z w) → n ≤ 1 → r = 0

def curvature_constantType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : P202.ConnectionData.Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (κ : ℝ),
    (∀ (x y : TangentSpace S p) (h : LinearIndependent ℝ ![x, y]),
      sectionalCurvature g T p x y h = κ) →
    ∀ x y z w, curvatureForm g T p x y z w =
      κ * (pairing g p y z * pairing g p x w - pairing g p x z * pairing g p y w)
end P202Specs.Geometry.SectionalRecovery
